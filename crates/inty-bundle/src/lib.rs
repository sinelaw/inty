//! Single-file bundler for `inty`-checked ES modules.
//!
//! Reads an entry `.js` file, resolves every `import` reachable from
//! it (re-using the module graph in [`inty::modules`]), and emits a
//! single JS blob that QuickJS can `eval`. Each module is wrapped in
//! an IIFE that returns its export table; cross-module references
//! become local lookups against the importer's IIFE scope. A v3
//! source map is emitted alongside, mapping each output line/column
//! back to the originating file and span.
//!
//! The bundler runs **after** successful type checking. It assumes
//! the program type-checks and does not re-validate semantics.
//!
//! # Public API
//!
//! ```ignore
//! pub fn bundle(entry: &Path) -> Result<BundleOutput, BundleError>;
//! pub struct BundleOutput { pub code: String, pub source_map: String }
//! ```
//!
//! Cycle handling: import cycles are rejected with a clear
//! diagnostic in v1.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use inty::ast::{ExportDecl, ImportSpecifier, Program, Stmt};

mod emit;
mod graph;

pub use emit::{BundleOutput, EmitError};

/// Top-level error type returned by [`bundle`]. Wraps lower-level
/// causes from parsing, module resolution, and emission so callers
/// only have to match against one error.
#[derive(Debug)]
pub enum BundleError {
    /// I/O error reading a source file.
    Io { path: PathBuf, message: String },
    /// Parser or scanner rejected a source file.
    Parse { path: PathBuf, message: String },
    /// Import graph contains a cycle.
    ImportCycle { path: PathBuf },
    /// A relative import couldn't be resolved against the disk.
    UnresolvedImport { from: PathBuf, specifier: String },
    /// Bare specifiers (`import _ from "lodash"`) aren't supported
    /// by the bundler today — the source resolver only understands
    /// relative paths.
    BareSpecifier { from: PathBuf, specifier: String },
    /// Emit-time failure (most often "this declaration shape is not
    /// supported in v1 — please open an issue").
    Emit(EmitError),
}

impl std::fmt::Display for BundleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BundleError::Io { path, message } => {
                write!(f, "I/O error on {}: {}", path.display(), message)
            }
            BundleError::Parse { path, message } => {
                write!(f, "parse error in {}: {}", path.display(), message)
            }
            BundleError::ImportCycle { path } => {
                write!(f, "import cycle involving {}", path.display())
            }
            BundleError::UnresolvedImport { from, specifier } => write!(
                f,
                "{} imports {:?} which does not resolve to a file on disk",
                from.display(),
                specifier
            ),
            BundleError::BareSpecifier { from, specifier } => write!(
                f,
                "{} uses a bare specifier {:?} (only relative paths are supported)",
                from.display(),
                specifier
            ),
            BundleError::Emit(e) => write!(f, "emit error: {}", e),
        }
    }
}

impl std::error::Error for BundleError {}

/// Bundle the program rooted at `entry`, returning the bundled JS
/// blob and its v3 source map.
pub fn bundle(entry: &Path) -> Result<BundleOutput, BundleError> {
    let canonical_entry = canonicalise(entry).ok_or_else(|| BundleError::Io {
        path: entry.to_path_buf(),
        message: "could not canonicalise path".to_string(),
    })?;

    let mut graph = graph::ModuleGraph::default();
    let mut visiting: HashSet<PathBuf> = HashSet::new();
    load_module(&canonical_entry, &mut graph, &mut visiting)?;

    let order = graph.dependency_order(&canonical_entry);
    emit::emit_bundle(&graph, &order, &canonical_entry).map_err(BundleError::Emit)
}

fn canonicalise(p: &Path) -> Option<PathBuf> {
    p.canonicalize().ok()
}

/// Load a module file off disk, parse it, walk its imports, and
/// stash everything in `graph`. Cycle-detected via `visiting`.
fn load_module(
    path: &Path,
    graph: &mut graph::ModuleGraph,
    visiting: &mut HashSet<PathBuf>,
) -> Result<(), BundleError> {
    if graph.contains(path) {
        return Ok(());
    }
    if !visiting.insert(path.to_path_buf()) {
        return Err(BundleError::ImportCycle {
            path: path.to_path_buf(),
        });
    }

    let source = std::fs::read_to_string(path).map_err(|e| BundleError::Io {
        path: path.to_path_buf(),
        message: e.to_string(),
    })?;

    let program = inty::frontends::javascript::parse(&source).map_err(|e| BundleError::Parse {
        path: path.to_path_buf(),
        message: format!("{:?}", e),
    })?;

    let base_dir = path
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));

    let imports = collect_imports(&program);
    let mut resolved_imports: Vec<(String, PathBuf)> = Vec::new();
    let mut export_resolutions: HashMap<String, PathBuf> = HashMap::new();

    for spec in imports {
        if !spec.starts_with('.') && !spec.starts_with('/') {
            return Err(BundleError::BareSpecifier {
                from: path.to_path_buf(),
                specifier: spec.clone(),
            });
        }
        let resolved =
            resolve_path(&base_dir, &spec).ok_or_else(|| BundleError::UnresolvedImport {
                from: path.to_path_buf(),
                specifier: spec.clone(),
            })?;
        resolved_imports.push((spec.clone(), resolved.clone()));
        export_resolutions.insert(spec, resolved);
    }

    // Also resolve re-export-from specifiers so the emitter can
    // walk them.
    for stmt in &program.statements {
        if let Stmt::Export {
            declaration: ExportDecl::From { source: src, .. },
            ..
        } = stmt
        {
            if !src.starts_with('.') && !src.starts_with('/') {
                return Err(BundleError::BareSpecifier {
                    from: path.to_path_buf(),
                    specifier: src.clone(),
                });
            }
            let resolved =
                resolve_path(&base_dir, src).ok_or_else(|| BundleError::UnresolvedImport {
                    from: path.to_path_buf(),
                    specifier: src.clone(),
                })?;
            resolved_imports.push((src.clone(), resolved.clone()));
            export_resolutions.insert(src.clone(), resolved);
        }
    }

    let import_targets: Vec<PathBuf> = resolved_imports.iter().map(|(_, p)| p.clone()).collect();

    // Recurse into dependencies BEFORE inserting this module, so a
    // back-edge caught by the `visiting` set fires as a cycle
    // diagnostic rather than a benign "already loaded" early return.
    for target in &import_targets {
        load_module(target, graph, visiting)?;
    }

    graph.insert(graph::Module {
        path: path.to_path_buf(),
        source,
        program,
        import_targets,
        specifier_resolution: export_resolutions,
    });

    visiting.remove(path);
    Ok(())
}

fn collect_imports(program: &Program) -> Vec<String> {
    let mut out = Vec::new();
    for stmt in &program.statements {
        match stmt {
            Stmt::Import { source, .. } => {
                let _ = ImportSpecifier::Default {
                    local: String::new(),
                    span: inty::span::Span::new(0, 0),
                };
                out.push(source.clone());
            }
            Stmt::Export {
                declaration: ExportDecl::From { source, .. },
                ..
            } => out.push(source.clone()),
            _ => {}
        }
    }
    out
}

/// Resolve a relative import specifier to a canonical path. Tries
/// the literal path, the path with `.js` appended, and `.d.js`
/// appended — same resolution policy `inty::modules` uses.
fn resolve_path(base_dir: &Path, source: &str) -> Option<PathBuf> {
    let raw = Path::new(source);
    let candidate = if raw.is_absolute() {
        raw.to_path_buf()
    } else {
        base_dir.join(raw)
    };
    for suffix in ["", ".js", ".d.js"] {
        let with_suffix = if suffix.is_empty() {
            candidate.clone()
        } else {
            candidate.with_extension(suffix.trim_start_matches('.'))
        };
        if with_suffix.is_file() {
            return with_suffix.canonicalize().ok();
        }
    }
    None
}
