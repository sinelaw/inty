//! Bundle emission: walks the module graph in dependency order and
//! produces a single self-contained JS blob plus a v3 source map.
//!
//! Each module is wrapped in an IIFE that builds an `__exports`
//! object and returns it. Cross-module references go through a
//! shared registry `__mods` keyed on the module's canonical path.
//!
//! Output shape (one entry module, one dep):
//!
//! ```js
//! (function () {
//!   var __mods = {};
//!   __mods["/abs/dep.js"] = (function () {
//!     var __exports = {};
//!     // rewritten body of dep.js
//!     return __exports;
//!   })();
//!   // rewritten body of entry.js — its top-level statements
//!   // execute at eval time so the entry's effects fire.
//! })();
//! ```

use std::path::{Path, PathBuf};

use inty::parser::ast::{ExportDecl, ExportFromKind, Expr, ImportSpecifier, Stmt, VarKind};
use inty::parser::pretty;
use sourcemap::SourceMapBuilder;

use crate::graph::{Module, ModuleGraph};

/// Final bundler output.
#[derive(Debug, Clone)]
pub struct BundleOutput {
    /// JavaScript blob — feed to `eval` or write to disk.
    pub code: String,
    /// v3 source map JSON. Always emitted alongside `code`.
    pub source_map: String,
}

#[derive(Debug)]
pub enum EmitError {
    /// A statement shape we can't yet rewrite (e.g. dynamic
    /// `import()` once that lands in the parser, or an unsupported
    /// destructuring form). Carries a short message so users see
    /// what's missing rather than a panic.
    Unsupported { message: String, path: PathBuf },
    /// Re-export `export … from "./x.js"` named a binding the
    /// target module doesn't expose at the bundler level (e.g. it
    /// re-exports from yet another module via `export *`). We
    /// currently resolve `export * from` only against the named
    /// exports in the immediate target's source.
    UnknownReexport {
        from: PathBuf,
        target: PathBuf,
        name: String,
    },
}

impl std::fmt::Display for EmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitError::Unsupported { message, path } => {
                write!(f, "{}: {}", path.display(), message)
            }
            EmitError::UnknownReexport { from, target, name } => write!(
                f,
                "{} re-exports {:?} from {} but the target does not appear to export it",
                from.display(),
                name,
                target.display()
            ),
        }
    }
}

impl std::error::Error for EmitError {}

/// Emit the bundle and source map.
pub fn emit_bundle(
    graph: &ModuleGraph,
    order: &[PathBuf],
    entry: &Path,
) -> Result<BundleOutput, EmitError> {
    let mut buf = Buffer::new();
    let mut smap = SourceMapBuilder::new(None);

    // Register every module's source for the source map. The index
    // returned is what we put in each mapping's source_id.
    let mut source_ids: std::collections::HashMap<PathBuf, u32> = std::collections::HashMap::new();
    for path in order {
        if let Some(m) = graph.get(path) {
            let id = smap.add_source(&path.to_string_lossy());
            smap.set_source_contents(id, Some(&m.source));
            source_ids.insert(path.clone(), id);
        }
    }

    buf.line("(function () {");
    buf.line("  var __mods = {};");

    for path in order {
        let module = graph.get(path).ok_or_else(|| EmitError::Unsupported {
            message: "graph is missing a module that load_module added".to_string(),
            path: path.clone(),
        })?;

        let is_entry = path == entry;
        if is_entry {
            // The entry module's body runs in the outer IIFE so its
            // top-level effects fire at eval time. Imports are still
            // rewritten — exports become harmless `__exports` writes
            // we discard.
            buf.line(&format!("  // entry: {}", path.display()));
            emit_module_body(
                &mut buf,
                &mut smap,
                module,
                graph,
                source_ids[path],
                /*is_entry=*/ true,
            )?;
        } else {
            buf.line(&format!(
                "  __mods[{}] = (function () {{",
                js_string(&path.to_string_lossy())
            ));
            buf.line("    var __exports = {};");
            emit_module_body(
                &mut buf,
                &mut smap,
                module,
                graph,
                source_ids[path],
                /*is_entry=*/ false,
            )?;
            buf.line("    return __exports;");
            buf.line("  })();");
        }
    }

    buf.line("})();");

    let mut sm_buf: Vec<u8> = Vec::new();
    smap.into_sourcemap()
        .to_writer(&mut sm_buf)
        .map_err(|e| EmitError::Unsupported {
            message: format!("source-map write failed: {}", e),
            path: entry.to_path_buf(),
        })?;
    let source_map = String::from_utf8(sm_buf).map_err(|e| EmitError::Unsupported {
        message: format!("source map produced non-UTF-8 bytes: {}", e),
        path: entry.to_path_buf(),
    })?;

    Ok(BundleOutput {
        code: buf.into_string(),
        source_map,
    })
}

/// Emit one module's body — imports rewritten to local declarations
/// against `__mods`, exports rewritten to assignments on
/// `__exports`. Other statements pass through unchanged.
fn emit_module_body(
    buf: &mut Buffer,
    smap: &mut SourceMapBuilder,
    module: &Module,
    graph: &ModuleGraph,
    source_id: u32,
    is_entry: bool,
) -> Result<(), EmitError> {
    let indent = if is_entry { "  " } else { "    " };

    for stmt in &module.program.statements {
        match stmt {
            Stmt::Import {
                specifiers,
                source: spec,
                span,
            } => {
                let target_path = module.specifier_resolution.get(spec).ok_or_else(|| {
                    EmitError::Unsupported {
                        message: format!(
                            "import {:?} has no resolved target — internal bundler bug",
                            spec
                        ),
                        path: module.path.clone(),
                    }
                })?;
                let target_lit = js_string(&target_path.to_string_lossy());
                add_mapping(smap, buf, source_id, *span);
                if specifiers.is_empty() {
                    // Side-effect only — the dep IIFE already ran.
                    buf.line(&format!(
                        "{}/* import {} (side-effect) */",
                        indent, target_lit
                    ));
                    continue;
                }
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named {
                            imported, local, ..
                        } => {
                            buf.line(&format!(
                                "{}var {} = __mods[{}].{};",
                                indent, local, target_lit, imported
                            ));
                        }
                        ImportSpecifier::Default { local, .. } => {
                            buf.line(&format!(
                                "{}var {} = __mods[{}].default;",
                                indent, local, target_lit
                            ));
                        }
                        ImportSpecifier::Namespace { local, .. } => {
                            buf.line(&format!(
                                "{}var {} = __mods[{}];",
                                indent, local, target_lit
                            ));
                        }
                    }
                }
            }

            Stmt::Export { declaration, span } => {
                add_mapping(smap, buf, source_id, *span);
                emit_export_decl(buf, indent, declaration, module, graph, is_entry)?;
            }

            other => {
                add_mapping(smap, buf, source_id, other.span());
                let printed = pretty::print_stmt(other);
                for line in printed.lines() {
                    buf.line(&format!("{}{}", indent, line));
                }
            }
        }
    }
    Ok(())
}

fn emit_export_decl(
    buf: &mut Buffer,
    indent: &str,
    decl: &ExportDecl,
    module: &Module,
    graph: &ModuleGraph,
    is_entry: bool,
) -> Result<(), EmitError> {
    let writes_exports = !is_entry;

    match decl {
        ExportDecl::Var {
            kind,
            declarations,
            span: _,
        } => {
            // Print the var/let/const declaration verbatim, then
            // assign each binding into __exports.
            let kw = match kind {
                VarKind::Var => "var",
                VarKind::Let => "let",
                VarKind::Const => "const",
            };
            for d in declarations {
                if d.name.starts_with("$destr$") {
                    // Destructuring temp — emit the underlying
                    // declarator without exporting it.
                    let init = d
                        .init
                        .as_ref()
                        .map(|e| pretty::print_expr(e))
                        .unwrap_or_else(|| "undefined".to_string());
                    buf.line(&format!("{}{} {} = {};", indent, kw, d.name, init));
                    continue;
                }
                let init = d
                    .init
                    .as_ref()
                    .map(|e| pretty::print_expr(e))
                    .unwrap_or_else(|| "undefined".to_string());
                buf.line(&format!("{}{} {} = {};", indent, kw, d.name, init));
                if writes_exports {
                    buf.line(&format!("{}__exports.{} = {};", indent, d.name, d.name));
                }
            }
        }

        ExportDecl::Function {
            name,
            params,
            body,
            type_annotation: _,
            span,
        } => {
            // Reconstruct as a plain function declaration. We use
            // the pretty-printer for the body and parameters by
            // pretending the export is a regular Stmt::FunctionDecl.
            let synth = Stmt::FunctionDecl {
                name: name.clone(),
                params: params.clone(),
                body: body.clone(),
                type_annotation: None,
                span: *span,
            };
            for line in pretty::print_stmt(&synth).lines() {
                buf.line(&format!("{}{}", indent, line));
            }
            if writes_exports {
                buf.line(&format!("{}__exports.{} = {};", indent, name, name));
            }
        }

        ExportDecl::Default { value, span: _ } => {
            // Anonymous: `__exports.default = <expr>;`
            // Named function: `function f() {} __exports.default = f;`
            match value {
                Expr::Function {
                    name: Some(fname), ..
                } => {
                    let synth = Stmt::Expr {
                        expression: value.clone(),
                        span: value.span(),
                    };
                    for line in pretty::print_stmt(&synth).lines() {
                        buf.line(&format!("{}{}", indent, line));
                    }
                    if writes_exports {
                        buf.line(&format!("{}__exports.default = {};", indent, fname));
                    }
                }
                _ => {
                    let printed = pretty::print_expr(value);
                    if writes_exports {
                        buf.line(&format!("{}__exports.default = {};", indent, printed));
                    } else {
                        buf.line(&format!("{}{};", indent, printed));
                    }
                }
            }
        }

        ExportDecl::List {
            specifiers,
            span: _,
        } => {
            if writes_exports {
                for s in specifiers {
                    buf.line(&format!(
                        "{}__exports.{} = {};",
                        indent, s.exported, s.local
                    ));
                }
            }
        }

        ExportDecl::From {
            kind,
            source: spec,
            span: _,
        } => {
            let target_path =
                module
                    .specifier_resolution
                    .get(spec)
                    .ok_or_else(|| EmitError::Unsupported {
                        message: format!(
                            "re-export {:?} has no resolved target — internal bundler bug",
                            spec
                        ),
                        path: module.path.clone(),
                    })?;
            let target_lit = js_string(&target_path.to_string_lossy());
            match kind {
                ExportFromKind::Named(specs) => {
                    if writes_exports {
                        for s in specs {
                            buf.line(&format!(
                                "{}__exports.{} = __mods[{}].{};",
                                indent, s.exported, target_lit, s.local
                            ));
                        }
                    }
                }
                ExportFromKind::All => {
                    // `export *` re-exports every named export of
                    // the target except `default`. We resolve by
                    // walking the target's export list — anything
                    // we can name in the source-level export
                    // statements gets re-exported.
                    if writes_exports {
                        let names = named_exports_of(graph, target_path).ok_or_else(|| {
                            EmitError::UnknownReexport {
                                from: module.path.clone(),
                                target: target_path.clone(),
                                name: "*".to_string(),
                            }
                        })?;
                        for n in names {
                            if n == "default" {
                                continue;
                            }
                            buf.line(&format!(
                                "{}__exports.{} = __mods[{}].{};",
                                indent, n, target_lit, n
                            ));
                        }
                    }
                }
                ExportFromKind::AllAs(name) => {
                    if writes_exports {
                        buf.line(&format!(
                            "{}__exports.{} = __mods[{}];",
                            indent, name, target_lit
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Walk a module's source-level export statements and return the
/// names it exports — used to expand `export * from "./x.js"`.
/// Returns `None` for sources we can't statically inspect (e.g. a
/// transitive `export *` chain we'd need to resolve recursively).
fn named_exports_of(graph: &ModuleGraph, path: &Path) -> Option<Vec<String>> {
    let m = graph.get(path)?;
    let mut out: Vec<String> = Vec::new();
    let mut had_star = false;
    for stmt in &m.program.statements {
        if let Stmt::Export { declaration, .. } = stmt {
            match declaration {
                ExportDecl::Var { declarations, .. } => {
                    for d in declarations {
                        if !d.name.starts_with("$destr$") {
                            out.push(d.name.clone());
                        }
                    }
                }
                ExportDecl::Function { name, .. } => out.push(name.clone()),
                ExportDecl::Default { .. } => out.push("default".to_string()),
                ExportDecl::List { specifiers, .. } => {
                    for s in specifiers {
                        out.push(s.exported.clone());
                    }
                }
                ExportDecl::From { kind, .. } => match kind {
                    ExportFromKind::Named(specs) => {
                        for s in specs {
                            out.push(s.exported.clone());
                        }
                    }
                    ExportFromKind::All => {
                        had_star = true;
                    }
                    ExportFromKind::AllAs(name) => out.push(name.clone()),
                },
            }
        }
    }
    if had_star {
        // We don't currently expand transitive `export *` chains.
        // Up to the caller to decide whether that's an error.
        return None;
    }
    Some(out)
}

/// Internal write buffer. Tracks the current line count so source-map
/// mappings can attach to the right output position.
struct Buffer {
    out: String,
    line: u32,
}

impl Buffer {
    fn new() -> Self {
        Buffer {
            out: String::new(),
            line: 0,
        }
    }
    fn line(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
        self.line += 1;
    }
    fn current_line(&self) -> u32 {
        self.line
    }
    fn into_string(self) -> String {
        self.out
    }
}

/// Add a single source-map mapping pointing the current output line
/// at the source span. Column granularity is line-only for v1; the
/// pretty printer doesn't expose per-token columns.
fn add_mapping(smap: &mut SourceMapBuilder, buf: &Buffer, source_id: u32, span: inty::lexer::Span) {
    // Convert byte offset to (line, col) by scanning isn't free, but
    // mapping count is small (one per top-level statement) so we
    // just register the line at byte 0 and let consumers derive
    // columns from the source text.
    smap.add_raw(
        buf.current_line(),
        0,
        0,
        span.start as u32,
        Some(source_id),
        None,
        false,
    );
}

/// Quote a string as a JavaScript string literal. Handles the
/// minimal escape set the bundler needs (it never re-encodes the
/// program's own string literals — those are printed verbatim by
/// the pretty printer).
fn js_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
