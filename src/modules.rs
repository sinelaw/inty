//! File-based module resolution for ES6 `import` statements.
//!
//! Walks the program's AST, resolves every `import "./path.js"` relative to
//! the importing file's directory, loads the target, recursively resolves
//! its imports, runs inference on it, and merges the **exported** bindings
//! into the environment that the main program is then checked against.
//! Cycles are rejected with an error rather than silently ignored.
//!
//! Visibility is driven by an explicit per-module exports map collected
//! from `Stmt::Export` nodes, *not* by diffing the env. A module's
//! top-level `const x = …;` without an `export` clause is therefore
//! invisible to importers — only declarations actually marked `export`
//! reach the resolver. This matches ES module semantics.
//!
//! Supported surface today:
//! - `import "./foo.js";`              (side-effect — merges all exports)
//! - `import { a, b as c } from "./foo.js";`
//! - `import name from "./foo.js";`    (default)
//! - `export var/let/const/function …;`
//! - `export default …;`               (expression or named function)
//! - `export { a, b as c };`           (export list, optionally renamed)
//!
//! Namespace imports (`import * as ns`) and re-exports (`export … from`)
//! are not handled yet.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::error::MinfernError;
use crate::infer::{InferState, TypeEnv};
use crate::parser::ast::{ExportDecl, Expr, ImportSpecifier, Program, Stmt};
use crate::parser::parse;

/// One entry of a module's export table: the name an importer would write
/// (`exported`) paired with the local binding it points to (`local`).
/// For `export const x = 1;` both are `"x"`; for `export { foo as bar };`
/// they differ; for `export default …` the exported name is `"default"`.
#[derive(Debug, Clone)]
pub struct ExportEntry {
    pub exported: String,
    pub local: String,
}

/// A module's exports — gathered by walking the AST, independently of
/// inference. Order follows source order; duplicates are not deduplicated
/// here (the resolver looks up by name and the first match wins, which
/// matches how shadowing reads in source).
pub type ExportTable = Vec<ExportEntry>;

/// Walk a program's top-level statements and collect every `export`-marked
/// binding. This is purely syntactic: no inference, no env, no IO.
pub fn collect_exports(program: &Program) -> ExportTable {
    let mut out = ExportTable::new();
    for stmt in &program.statements {
        if let Stmt::Export { declaration, .. } = stmt {
            match declaration {
                ExportDecl::Var { declarations, .. } => {
                    for d in declarations {
                        if d.name.starts_with("$destr$") {
                            continue;
                        }
                        out.push(ExportEntry {
                            exported: d.name.clone(),
                            local: d.name.clone(),
                        });
                    }
                }
                ExportDecl::Function { name, .. } => {
                    out.push(ExportEntry {
                        exported: name.clone(),
                        local: name.clone(),
                    });
                }
                ExportDecl::Default { value, .. } => {
                    // The local backing the default export is the binding
                    // that inference creates: `default` for an expression
                    // RHS, or the function's own name for a named function
                    // expression (which we then alias to `default` too —
                    // either lookup name resolves the same scheme).
                    let local = match value {
                        Expr::Function { name: Some(n), .. } => n.clone(),
                        _ => "default".to_string(),
                    };
                    out.push(ExportEntry {
                        exported: "default".to_string(),
                        local,
                    });
                }
                ExportDecl::List { specifiers, .. } => {
                    for s in specifiers {
                        out.push(ExportEntry {
                            exported: s.exported.clone(),
                            local: s.local.clone(),
                        });
                    }
                }
            }
        }
    }
    out
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
) -> Result<TypeEnv, MinfernError> {
    let mut env = env;
    for stmt in &program.statements {
        if let Stmt::Import {
            specifiers,
            source,
            span,
        } = stmt
        {
            let resolved_path = resolve_path(base_dir, source).map_err(|msg| {
                MinfernError::Type(crate::error::TypeError::Module {
                    message: format!("cannot resolve import {:?}: {}", source, msg),
                    span: *span,
                })
            })?;

            if visiting.contains(&resolved_path) {
                return Err(MinfernError::Type(crate::error::TypeError::Module {
                    message: format!(
                        "circular import involving {}",
                        resolved_path.display()
                    ),
                    span: *span,
                }));
            }

            let (module_env, exports) =
                load_module(state, env.clone(), &resolved_path, visiting)?;

            let lookup_export = |name: &str| -> Option<String> {
                exports
                    .iter()
                    .find(|e| e.exported == name)
                    .map(|e| e.local.clone())
            };

            if specifiers.is_empty() {
                // Side-effect import: merge every export from the module
                // into the current env, under its exported name.
                for entry in &exports {
                    if let Some(scheme) = module_env.lookup(&entry.local) {
                        env = env.extend(entry.exported.clone(), scheme.clone());
                    }
                }
            } else {
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named {
                            imported, local, ..
                        } => {
                            let local_in_module = lookup_export(imported).ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no export named {:?}",
                                        source, imported
                                    ),
                                    span: *span,
                                })
                            })?;
                            let scheme = module_env.lookup(&local_in_module).ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} exports {:?} but its local binding {:?} is missing",
                                        source, imported, local_in_module
                                    ),
                                    span: *span,
                                })
                            })?;
                            env = env.extend(local.clone(), scheme.clone());
                        }
                        ImportSpecifier::Default { local, span } => {
                            let local_in_module = lookup_export("default").ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no default export",
                                        source
                                    ),
                                    span: *span,
                                })
                            })?;
                            let scheme = module_env.lookup(&local_in_module).ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} declares a default export but its local binding {:?} is missing",
                                        source, local_in_module
                                    ),
                                    span: *span,
                                })
                            })?;
                            env = env.extend(local.clone(), scheme.clone());
                        }
                        ImportSpecifier::Namespace { span, .. } => {
                            return Err(MinfernError::Type(
                                crate::error::TypeError::Module {
                                    message: "namespace imports are not supported".to_string(),
                                    span: *span,
                                },
                            ));
                        }
                    }
                }
            }
        }
    }
    Ok(env)
}

/// Parse and infer a single module file, returning the inferred env and
/// the module's export table. Recursively resolves nested imports.
fn load_module(
    state: &mut InferState,
    starting_env: TypeEnv,
    path: &Path,
    visiting: &mut HashSet<PathBuf>,
) -> Result<(TypeEnv, ExportTable), MinfernError> {
    let source = std::fs::read_to_string(path).map_err(|e| {
        MinfernError::Type(crate::error::TypeError::Module {
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

    // First resolve imports of THIS module, then infer it.
    let env_with_imports =
        resolve_imports(state, starting_env, &program, &base_dir, visiting)?;
    let (_ty, module_env) = state.infer_program_with_env(&env_with_imports, &program)?;

    visiting.remove(&canonical);

    let exports = collect_exports(&program);
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

    fn resolve(dir: &Path, main: &str) -> Result<TypeEnv, MinfernError> {
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
        // Regression: prior behaviour silently allowed importing any
        // top-level binding by diffing the env. The exports table now
        // gates visibility — only `visible` is reachable.
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

        // The local name is not exported, so importing it must fail.
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
            let path = base.join(format!("minfern-test-{}-{}", pid, nanos));
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
