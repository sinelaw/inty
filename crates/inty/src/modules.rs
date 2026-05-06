//! File-based module resolution for ES6 `import` / `export` statements.
//!
//! Walks the program's AST, resolves every `import "./path.js"` relative to
//! the importing file's directory, loads the target, recursively resolves
//! its imports, runs inference on it, and merges the **exported** bindings
//! into the environment that the main program is then checked against.
//! Cycles are rejected with an error rather than silently ignored.
//!
//! Visibility is driven by an explicit per-module exports table whose
//! entries are produced by `compute_export_table`. For local declarations
//! (`export var/const/function/default/{ … }`) the entry points back at a
//! local binding by name; for re-exports (`export { … } from`,
//! `export * from`, `export * as ns from`) the target module is loaded
//! and the resulting scheme is stored *inline* in the entry, so the
//! importer never has to know whether a name came from this module or
//! transitively. Either way the resolver only ever looks at the exports
//! table — unexported top-level bindings are unreachable.
//!
//! Supported surface today:
//! - `import "./foo.js";`              (side-effect — merges all exports)
//! - `import { a, b as c } from "./foo.js";`
//! - `import name from "./foo.js";`    (default)
//! - `import * as ns from "./foo.js";` (namespace, as `Type::Module`)
//! - `import name, { a } from "./foo.js";`
//! - `import name, * as ns from "./foo.js";`
//! - `export var/let/const/function …;`
//! - `export default …;`               (expression or named function)
//! - `export { a, b as c };`           (export list, optionally renamed)
//! - `export { a, b as c } from "./foo.js";`
//! - `export * from "./foo.js";`       (excludes default, per ESM spec)
//! - `export * as ns from "./foo.js";`
//!
//! ## Known limitations / future work
//!
//! See `modules.md` for the full design plan. The pieces this module
//! still has to grow:
//!
//! - **Bare specifiers (modules.md §6).** `import _ from "lodash";`
//!   currently fails at `resolve_path` because the resolver only knows
//!   how to treat `source` as a file path. A registry mapping bare
//!   specifier → resolved path would slot in at the top of `resolve_path`.
//! - **Dynamic `import()` (§7).** No `Expr::DynamicImport` variant; the
//!   plan is to require a string-literal argument and return
//!   `Promise<Type::Module>` so the existing module machinery is reused.
//! - **Import attributes (§8).** `import data from "./d.json" with
//!   { type: "json" };` would need an attributes field on `Stmt::Import`
//!   and a JSON branch in `load_module` that infers the file as a closed
//!   object literal under the default export.
//! - **Cross-module type-class instances (§9).** Today instances live in
//!   a process-global table. If a user module ever exports an instance,
//!   `Type::Module` is the obvious carrier — add an `instances` field to
//!   `ModuleType` and merge at import time, with conflicts at the merge
//!   point as an error.
//!
//! ## Known rough edges in the current implementation
//!
//! - **Re-export error spans are imprecise.** When `compute_export_table`
//!   loads a target via `load_module` and that load fails (e.g. the
//!   target re-exports a name that doesn't exist further down the chain),
//!   the error bubbles up with whichever span the inner failure carried,
//!   not the span of the `export … from` clause that caused the load.
//!   The diagnostic *message* still names the offending module, so users
//!   can find the bug, but the highlighted source location can be a few
//!   files away from the actual `from` clause. Wrapping inner errors in
//!   a "while resolving export … from `…`" frame would tighten this.
//! - **Module-field assignment is silently allowed.** `Type::Module`
//!   has no field-assignment rule, but a `ns.foo = bar` expression
//!   currently goes through `infer_member`/assignment without being
//!   rejected by an explicit module-immutability check. The right home
//!   for that check is `infer_assign` for `Expr::Member` whose object
//!   resolves to `Type::Module(_)`. Today the gap is benign because
//!   `Type::Module` doesn't unify with anything the assignment RHS would
//!   produce, but it should fail with a clear "cannot assign to module
//!   export" error rather than a unification mismatch.
//! - **Importer's env leaks into loaded modules.** `load_module` passes
//!   the caller's `starting_env` through to `resolve_imports` for the
//!   target, so a module loaded in the middle of a chain sees whatever
//!   bindings the importer happened to have at that point. ESM modules
//!   are isolated. Today nothing user-visible breaks because module
//!   bindings don't shadow stdlib names in practice, but the right fix
//!   is to always use `crate::builtins::initial_env()` (or a shared
//!   immutable base) as the starting env for `load_module`, regardless
//!   of who's calling it.
//! - **No module cache.** A diamond `main → a, main → b, a → c, b → c`
//!   re-parses, re-resolves, and re-infers `c.js` twice. `Type::Module`'s
//!   nominal-by-source identity means the two passes still unify
//!   correctly, but the work is wasted. A `HashMap<PathBuf, (TypeEnv,
//!   ExportTable)>` keyed on the canonical path would eliminate it; the
//!   `visiting` set already gives us the right key shape.

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};

use crate::error::IntyError;
use crate::infer::{InferState, TypeEnv};
use crate::parser::ast::{
    ExportDecl, ExportFromKind, Expr, ImportSpecifier, Program, Stmt,
};
use crate::parser::parse;
use crate::types::{ModuleType, Type, TypeScheme};

/// One entry of a module's export table.
#[derive(Debug, Clone)]
pub struct ExportEntry {
    /// The name an importer would write.
    pub exported: String,
    /// What the entry points at — either a local binding by name, or a
    /// scheme already extracted from another module (used for re-exports).
    pub binding: ExportBinding,
}

/// What an export entry points at.
#[derive(Debug, Clone)]
pub enum ExportBinding {
    /// Name of a local binding in the same module's `TypeEnv`.
    Local(String),
    /// Scheme already extracted from somewhere else (re-export target).
    Inline(TypeScheme),
}

/// A module's exports — order follows source order; the resolver looks
/// up by name and the first match wins.
pub type ExportTable = Vec<ExportEntry>;

/// Resolve an export entry to a concrete scheme. Returns `None` only if
/// `Local(name)` doesn't exist in `module_env`, which is a programmer
/// error in the module itself (caught by inference's List validation).
fn export_scheme(entry: &ExportEntry, module_env: &TypeEnv) -> Option<TypeScheme> {
    match &entry.binding {
        ExportBinding::Local(name) => module_env.lookup(name).cloned(),
        ExportBinding::Inline(s) => Some(s.clone()),
    }
}

/// Build a `Type::Module` from a fully-resolved (env, exports) pair. Used
/// for `import * as ns` and for `export * as ns from`.
fn build_namespace_type(
    source_id: String,
    module_env: &TypeEnv,
    exports: &ExportTable,
    err_span: crate::lexer::Span,
    err_source: &str,
) -> Result<Type, IntyError> {
    let mut export_schemes: BTreeMap<String, TypeScheme> = BTreeMap::new();
    for entry in exports {
        let scheme = export_scheme(entry, module_env).ok_or_else(|| {
            IntyError::Type(crate::error::TypeError::Module {
                message: format!(
                    "module {:?} declares export {:?} but its local binding is missing",
                    err_source, entry.exported
                ),
                span: err_span,
            })
        })?;
        export_schemes.insert(entry.exported.clone(), scheme);
    }
    Ok(Type::Module(ModuleType {
        source: source_id,
        exports: export_schemes,
    }))
}

/// Compute the effective export table of an inferred module. For local
/// `Stmt::Export` forms the entry is a `Local(name)`; for `export … from`
/// re-exports the target is loaded and the entry is `Inline(scheme)`.
fn compute_export_table(
    state: &mut InferState,
    starting_env: &TypeEnv,
    program: &Program,
    base_dir: &Path,
    visiting: &mut HashSet<PathBuf>,
) -> Result<ExportTable, IntyError> {
    let mut out = ExportTable::new();
    for stmt in &program.statements {
        let Stmt::Export { declaration, .. } = stmt else {
            continue;
        };
        match declaration {
            ExportDecl::Var { declarations, .. } => {
                for d in declarations {
                    if d.name.starts_with("$destr$") {
                        continue;
                    }
                    out.push(ExportEntry {
                        exported: d.name.clone(),
                        binding: ExportBinding::Local(d.name.clone()),
                    });
                }
            }
            ExportDecl::Function { name, .. } => {
                out.push(ExportEntry {
                    exported: name.clone(),
                    binding: ExportBinding::Local(name.clone()),
                });
            }
            ExportDecl::Default { value, .. } => {
                let local = match value {
                    Expr::Function { name: Some(n), .. } => n.clone(),
                    _ => "default".to_string(),
                };
                out.push(ExportEntry {
                    exported: "default".to_string(),
                    binding: ExportBinding::Local(local),
                });
            }
            ExportDecl::List { specifiers, .. } => {
                for s in specifiers {
                    out.push(ExportEntry {
                        exported: s.exported.clone(),
                        binding: ExportBinding::Local(s.local.clone()),
                    });
                }
            }
            ExportDecl::From { kind, source, span } => {
                let resolved_path = resolve_path(base_dir, source).map_err(|msg| {
                    IntyError::Type(crate::error::TypeError::Module {
                        message: format!("cannot resolve re-export {:?}: {}", source, msg),
                        span: *span,
                    })
                })?;
                if visiting.contains(&resolved_path) {
                    return Err(IntyError::Type(crate::error::TypeError::Module {
                        message: format!(
                            "circular re-export involving {}",
                            resolved_path.display()
                        ),
                        span: *span,
                    }));
                }
                let (target_env, target_exports) = load_module(
                    state,
                    starting_env.clone(),
                    &resolved_path,
                    visiting,
                )?;

                let resolve_target = |name: &str| -> Option<TypeScheme> {
                    target_exports
                        .iter()
                        .find(|e| e.exported == name)
                        .and_then(|e| export_scheme(e, &target_env))
                };

                match kind {
                    ExportFromKind::Named(specs) => {
                        for spec in specs {
                            let scheme = resolve_target(&spec.local).ok_or_else(|| {
                                IntyError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no export named {:?}",
                                        source, spec.local
                                    ),
                                    span: spec.span,
                                })
                            })?;
                            out.push(ExportEntry {
                                exported: spec.exported.clone(),
                                binding: ExportBinding::Inline(scheme),
                            });
                        }
                    }
                    ExportFromKind::All => {
                        // ESM: `export *` re-exports all *named* exports
                        // and intentionally excludes `default`.
                        for entry in &target_exports {
                            if entry.exported == "default" {
                                continue;
                            }
                            let scheme = export_scheme(entry, &target_env).ok_or_else(|| {
                                IntyError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} export {:?} has no resolvable scheme",
                                        source, entry.exported
                                    ),
                                    span: *span,
                                })
                            })?;
                            out.push(ExportEntry {
                                exported: entry.exported.clone(),
                                binding: ExportBinding::Inline(scheme),
                            });
                        }
                    }
                    ExportFromKind::AllAs(ns_name) => {
                        let module_ty = build_namespace_type(
                            resolved_path.to_string_lossy().into_owned(),
                            &target_env,
                            &target_exports,
                            *span,
                            source,
                        )?;
                        out.push(ExportEntry {
                            exported: ns_name.clone(),
                            binding: ExportBinding::Inline(TypeScheme::mono(module_ty)),
                        });
                    }
                }
            }
        }
    }
    Ok(out)
}

/// Resolve every `import` in `program` relative to `base_dir`, merge the
/// resulting bindings into `env`, and return the extended environment.
///
/// `state` is threaded through so type variable IDs remain unique across
/// every module checked by this call. `visiting` is the set of canonicalised
/// paths currently being resolved, used for cycle detection; top-level
/// callers pass an empty set.
pub fn resolve_imports(
    state: &mut InferState,
    env: TypeEnv,
    program: &Program,
    base_dir: &Path,
    visiting: &mut HashSet<PathBuf>,
) -> Result<TypeEnv, IntyError> {
    let mut env = env;
    for stmt in &program.statements {
        if let Stmt::Import {
            specifiers,
            source,
            span,
        } = stmt
        {
            let resolved_path = resolve_path(base_dir, source).map_err(|msg| {
                IntyError::Type(crate::error::TypeError::Module {
                    message: format!("cannot resolve import {:?}: {}", source, msg),
                    span: *span,
                })
            })?;

            if visiting.contains(&resolved_path) {
                return Err(IntyError::Type(crate::error::TypeError::Module {
                    message: format!(
                        "circular import involving {}",
                        resolved_path.display()
                    ),
                    span: *span,
                }));
            }

            let (module_env, exports) =
                load_module(state, env.clone(), &resolved_path, visiting)?;

            let lookup_export_scheme = |name: &str| -> Option<TypeScheme> {
                exports
                    .iter()
                    .find(|e| e.exported == name)
                    .and_then(|e| export_scheme(e, &module_env))
            };

            if specifiers.is_empty() {
                // Side-effect import: merge every export from the module
                // into the current env, under its exported name.
                for entry in &exports {
                    if let Some(scheme) = export_scheme(entry, &module_env) {
                        env = env.extend(entry.exported.clone(), scheme);
                    }
                }
            } else {
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named {
                            imported, local, ..
                        } => {
                            let scheme = lookup_export_scheme(imported).ok_or_else(|| {
                                IntyError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no export named {:?}",
                                        source, imported
                                    ),
                                    span: *span,
                                })
                            })?;
                            env = env.extend(local.clone(), scheme);
                        }
                        ImportSpecifier::Default { local, span } => {
                            let scheme = lookup_export_scheme("default").ok_or_else(|| {
                                IntyError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no default export",
                                        source
                                    ),
                                    span: *span,
                                })
                            })?;
                            env = env.extend(local.clone(), scheme);
                        }
                        ImportSpecifier::Namespace { local, span } => {
                            let module_ty = build_namespace_type(
                                resolved_path.to_string_lossy().into_owned(),
                                &module_env,
                                &exports,
                                *span,
                                source,
                            )?;
                            env = env
                                .extend(local.clone(), TypeScheme::mono(module_ty));
                        }
                    }
                }
            }
        }
    }
    Ok(env)
}

/// Parse and type-check a single module file from disk, returning the
/// inferred environment and the effective export table.
///
/// This is the public entry point downstream consumers use when they
/// need both halves of a checked module (typically to render a `.d.js`
/// declarations file via [`crate::declarations::emit_declarations`]).
/// Equivalent to the internal `load_module` but exposed and not gated
/// on a caller-supplied cycle-detection set — top-level callers always
/// start from an empty `visiting` set.
pub fn check_module(
    state: &mut InferState,
    starting_env: TypeEnv,
    path: &Path,
) -> Result<(TypeEnv, ExportTable), IntyError> {
    let mut visiting = HashSet::new();
    load_module(state, starting_env, path, &mut visiting)
}

/// Parse and infer a single module file, returning the inferred env and
/// the module's effective export table (with re-exports resolved).
fn load_module(
    state: &mut InferState,
    starting_env: TypeEnv,
    path: &Path,
    visiting: &mut HashSet<PathBuf>,
) -> Result<(TypeEnv, ExportTable), IntyError> {
    let source = std::fs::read_to_string(path).map_err(|e| {
        IntyError::Type(crate::error::TypeError::Module {
            message: format!("failed to read {}: {}", path.display(), e),
            span: crate::lexer::Span::new(0, 0),
        })
    })?;

    let program = parse(&source)?;

    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    visiting.insert(canonical.clone());

    let base_dir = path
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));

    // Resolve imports, then infer, then resolve re-exports. The cycle set
    // is shared with both passes.
    let env_with_imports =
        resolve_imports(state, starting_env.clone(), &program, &base_dir, visiting)?;
    let (_ty, module_env) = state.infer_program_with_env(&env_with_imports, &program)?;

    let exports = compute_export_table(
        state,
        &starting_env,
        &program,
        &base_dir,
        visiting,
    )?;

    visiting.remove(&canonical);

    Ok((module_env, exports))
}

/// Resolve a relative-or-absolute `source` path to an existing `.js` file
/// under `base_dir`. Tries, in order: the literal path, the path with `.js`
/// appended, and `.d.js` appended. Returns a canonicalised absolute path.
fn resolve_path(base_dir: &Path, source: &str) -> Result<PathBuf, String> {
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
            return with_suffix
                .canonicalize()
                .map_err(|e| format!("canonicalising {}: {}", with_suffix.display(), e));
        }
    }

    Err(format!(
        "no such file (tried {}, {}.js, {}.d.js)",
        candidate.display(),
        candidate.display(),
        candidate.display()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(content.as_bytes()).unwrap();
        path
    }

    fn resolve(dir: &Path, main: &str) -> Result<TypeEnv, IntyError> {
        let main_path = dir.join(main);
        let source = std::fs::read_to_string(&main_path).unwrap();
        let program = parse(&source).unwrap();
        let mut state = InferState::new();
        let mut visiting = HashSet::new();
        resolve_imports(
            &mut state,
            crate::builtins::initial_env(),
            &program,
            main_path.parent().unwrap(),
            &mut visiting,
        )
    }

    fn check(dir: &Path, main: &str) -> Result<(), IntyError> {
        let main_path = dir.join(main);
        let source = std::fs::read_to_string(&main_path).unwrap();
        let program = parse(&source).unwrap();
        let mut state = InferState::new();
        let mut visiting = HashSet::new();
        let env = resolve_imports(
            &mut state,
            crate::builtins::initial_env(),
            &program,
            main_path.parent().unwrap(),
            &mut visiting,
        )?;
        state.infer_program_with_env(&env, &program)?;
        Ok(())
    }

    #[test]
    fn named_import_resolves() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "export function add(a, b) { return a + b; }",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { add } from \"./lib.js\"; var r = add(1, 2);",
        );
        let env = resolve(dir.path(), "main.js").unwrap();
        assert!(env.lookup("add").is_some(), "add should be imported");
    }

    #[test]
    fn default_import_resolves() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "export default function greet(name) { return \"hi \" + name; }",
        );
        write_file(
            dir.path(),
            "main.js",
            "import greet from \"./lib.js\"; var r = greet(\"world\");",
        );
        let env = resolve(dir.path(), "main.js").unwrap();
        assert!(env.lookup("greet").is_some(), "greet should be imported");
    }

    #[test]
    fn default_export_expression_resolves() {
        let dir = tempdir();
        write_file(dir.path(), "lib.js", "export default 42;");
        write_file(dir.path(), "main.js", "import answer from \"./lib.js\";");
        let env = resolve(dir.path(), "main.js").unwrap();
        assert!(env.lookup("answer").is_some(), "answer should be imported");
    }

    #[test]
    fn default_import_without_export_errors() {
        let dir = tempdir();
        write_file(dir.path(), "lib.js", "export const x = 1;");
        write_file(dir.path(), "main.js", "import x from \"./lib.js\";");
        let err = resolve(dir.path(), "main.js")
            .expect_err("missing default export should error");
        assert!(format!("{}", err).contains("default export"));
    }

    #[test]
    fn private_const_is_not_importable() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "const secret = 42; export const visible = \"ok\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { secret } from \"./lib.js\";",
        );
        let err = resolve(dir.path(), "main.js")
            .expect_err("importing a non-exported binding should error");
        assert!(
            format!("{}", err).contains("no export named"),
            "expected 'no export named' error, got: {}",
            err
        );
    }

    #[test]
    fn renamed_export_works_under_export_name_only() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "function square(n) { return n * n; } export { square as sq };",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { sq } from \"./lib.js\"; var r = sq(3);",
        );
        let env = resolve(dir.path(), "main.js").unwrap();
        assert!(env.lookup("sq").is_some(), "sq should be imported");

        let dir2 = tempdir();
        write_file(
            dir2.path(),
            "lib.js",
            "function square(n) { return n * n; } export { square as sq };",
        );
        write_file(
            dir2.path(),
            "main.js",
            "import { square } from \"./lib.js\";",
        );
        let err = resolve(dir2.path(), "main.js")
            .expect_err("importing the local name of a renamed export should fail");
        assert!(format!("{}", err).contains("no export named"));
    }

    #[test]
    fn export_list_undeclared_local_errors() {
        let dir = tempdir();
        write_file(dir.path(), "lib.js", "export { ghost };");
        write_file(
            dir.path(),
            "main.js",
            "import { ghost } from \"./lib.js\";",
        );
        let err = resolve(dir.path(), "main.js")
            .expect_err("exporting an undeclared local should error");
        assert!(format!("{}", err).contains("not declared"));
    }

    #[test]
    fn namespace_import_member_access_works() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "export function add(a, b) { return a + b; } export const PI = 3.14;",
        );
        write_file(
            dir.path(),
            "main.js",
            "import * as lib from \"./lib.js\"; var s = lib.add(1, 2); var p = lib.PI;",
        );
        check(dir.path(), "main.js").unwrap();
    }

    #[test]
    fn namespace_member_missing_is_module_error() {
        let dir = tempdir();
        write_file(dir.path(), "lib.js", "export const visible = 1;");
        write_file(
            dir.path(),
            "main.js",
            "import * as lib from \"./lib.js\"; var x = lib.bogus;",
        );
        let err = check(dir.path(), "main.js")
            .expect_err("accessing a non-export through a namespace must error");
        assert!(
            format!("{}", err).contains("no export named"),
            "expected 'no export named' error, got: {}",
            err
        );
    }

    #[test]
    fn namespace_preserves_polymorphism_across_uses() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "export function id(x) { return x; }",
        );
        write_file(
            dir.path(),
            "main.js",
            "import * as ns from \"./lib.js\"; var n = ns.id(1); var s = ns.id(\"hello\");",
        );
        check(dir.path(), "main.js")
            .expect("namespace polymorphism should resolve");
    }

    #[test]
    fn private_const_not_in_namespace() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "const secret = 42; export const visible = \"ok\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import * as ns from \"./lib.js\"; var s = ns.secret;",
        );
        let err = check(dir.path(), "main.js")
            .expect_err("private bindings must not be reachable through a namespace");
        assert!(format!("{}", err).contains("no export named"));
    }

    #[test]
    fn default_plus_namespace_import_resolves() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "lib.js",
            "export default function greet(name) { return \"hi \" + name; } export const VERSION = \"1.0\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import greet, * as lib from \"./lib.js\"; var a = greet(\"x\"); var v = lib.VERSION;",
        );
        let env = resolve(dir.path(), "main.js").unwrap();
        assert!(env.lookup("greet").is_some(), "default should bind");
        assert!(env.lookup("lib").is_some(), "namespace should bind");
    }

    // --- §4 re-exports ---

    #[test]
    fn re_export_named_works() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "inner.js",
            "export function add(a, b) { return a + b; }",
        );
        write_file(
            dir.path(),
            "outer.js",
            "export { add } from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { add } from \"./outer.js\"; var r = add(1, 2);",
        );
        check(dir.path(), "main.js").unwrap();
    }

    #[test]
    fn re_export_renames() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "inner.js",
            "export function add(a, b) { return a + b; }",
        );
        write_file(
            dir.path(),
            "outer.js",
            "export { add as plus } from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { plus } from \"./outer.js\"; var r = plus(1, 2);",
        );
        check(dir.path(), "main.js").unwrap();

        // The original name `add` is *not* exported by `outer.js`.
        let dir2 = tempdir();
        write_file(
            dir2.path(),
            "inner.js",
            "export function add(a, b) { return a + b; }",
        );
        write_file(
            dir2.path(),
            "outer.js",
            "export { add as plus } from \"./inner.js\";",
        );
        write_file(
            dir2.path(),
            "main.js",
            "import { add } from \"./outer.js\";",
        );
        let err = check(dir2.path(), "main.js")
            .expect_err("renamed re-export should hide the original name");
        assert!(format!("{}", err).contains("no export named"));
    }

    #[test]
    fn re_export_named_missing_in_target_errors() {
        let dir = tempdir();
        write_file(dir.path(), "inner.js", "export const x = 1;");
        write_file(
            dir.path(),
            "outer.js",
            "export { ghost } from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { ghost } from \"./outer.js\";",
        );
        let err = check(dir.path(), "main.js")
            .expect_err("re-exporting a name the target doesn't have should error");
        assert!(format!("{}", err).contains("no export named"));
    }

    #[test]
    fn re_export_star_excludes_default() {
        // Per ESM, `export *` re-exports all named exports but not `default`.
        let dir = tempdir();
        write_file(
            dir.path(),
            "inner.js",
            "export const a = 1; export const b = 2; export default 999;",
        );
        write_file(
            dir.path(),
            "outer.js",
            "export * from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { a, b } from \"./outer.js\";",
        );
        check(dir.path(), "main.js").unwrap();

        let dir2 = tempdir();
        write_file(
            dir2.path(),
            "inner.js",
            "export const a = 1; export default 999;",
        );
        write_file(
            dir2.path(),
            "outer.js",
            "export * from \"./inner.js\";",
        );
        write_file(
            dir2.path(),
            "main.js",
            "import x from \"./outer.js\";",
        );
        let err = check(dir2.path(), "main.js")
            .expect_err("`export *` must not propagate the target's default");
        assert!(format!("{}", err).contains("default"));
    }

    #[test]
    fn re_export_star_as_namespace_works() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "inner.js",
            "export function id(x) { return x; }",
        );
        write_file(
            dir.path(),
            "outer.js",
            "export * as inner from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { inner } from \"./outer.js\"; var n = inner.id(1); var s = inner.id(\"hi\");",
        );
        check(dir.path(), "main.js").unwrap();
    }

    #[test]
    fn re_export_default_named_works() {
        // `export { default } from "./mod.js"` re-exports target's default
        // as our default; `export { default as alias } from` renames it.
        let dir = tempdir();
        write_file(
            dir.path(),
            "inner.js",
            "export default function greet(n) { return \"hi \" + n; }",
        );
        write_file(
            dir.path(),
            "outer.js",
            "export { default } from \"./inner.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import g from \"./outer.js\"; var s = g(\"world\");",
        );
        check(dir.path(), "main.js").unwrap();

        let dir2 = tempdir();
        write_file(
            dir2.path(),
            "inner.js",
            "export default 42;",
        );
        write_file(
            dir2.path(),
            "outer.js",
            "export { default as answer } from \"./inner.js\";",
        );
        write_file(
            dir2.path(),
            "main.js",
            "import { answer } from \"./outer.js\";",
        );
        check(dir2.path(), "main.js").unwrap();
    }

    #[test]
    fn re_export_through_two_hops_works() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "a.js",
            "export const value = 100;",
        );
        write_file(
            dir.path(),
            "b.js",
            "export { value } from \"./a.js\";",
        );
        write_file(
            dir.path(),
            "c.js",
            "export { value } from \"./b.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { value } from \"./c.js\";",
        );
        check(dir.path(), "main.js").unwrap();
    }

    #[test]
    fn re_export_cycle_is_rejected() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "a.js",
            "export * from \"./b.js\";",
        );
        write_file(
            dir.path(),
            "b.js",
            "export * from \"./a.js\";",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { x } from \"./a.js\";",
        );
        let err = check(dir.path(), "main.js")
            .expect_err("re-export cycle should error");
        assert!(format!("{}", err).contains("circular"));
    }

    #[test]
    fn cycle_is_rejected() {
        let dir = tempdir();
        write_file(
            dir.path(),
            "a.js",
            "import { x } from \"./b.js\"; export var y = x;",
        );
        write_file(
            dir.path(),
            "b.js",
            "import { y } from \"./a.js\"; export var x = y;",
        );
        write_file(
            dir.path(),
            "main.js",
            "import { y } from \"./a.js\";",
        );
        let err = resolve(dir.path(), "main.js").expect_err("cycle should error");
        assert!(format!("{}", err).contains("circular"));
    }

    fn tempdir() -> TempDir {
        TempDir::new()
    }

    struct TempDir {
        path: PathBuf,
    }
    impl TempDir {
        fn new() -> Self {
            let base = std::env::temp_dir();
            let pid = std::process::id();
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = base.join(format!("inty-test-{}-{}", pid, nanos));
            std::fs::create_dir_all(&path).unwrap();
            TempDir { path }
        }
        fn path(&self) -> &Path {
            &self.path
        }
    }
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }
}
