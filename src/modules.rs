//! File-based module resolution for ES6 `import` statements.
//!
//! Walks the program's AST, resolves every `import "./path.js"` relative to
//! the importing file's directory, loads the target, recursively resolves
//! its imports, runs inference on it, and merges the named / side-effect
//! bindings into the environment that the main program is then checked
//! against. Cycles are rejected with an error rather than silently ignored.
//!
//! Only the subset needed for simple multi-file projects is supported:
//! side-effect imports (`import "./foo.js"`), named imports
//! (`import { a, b as c } from "./foo.js"`), and default imports
//! (`import name from "./foo.js"`). Namespace imports and re-exports
//! are not handled yet.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::error::MinfernError;
use crate::infer::{InferState, TypeEnv};
use crate::parser::ast::{ImportSpecifier, Program, Stmt};
use crate::parser::parse;

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

            let module_env = load_module(state, env.clone(), &resolved_path, visiting)?;

            if specifiers.is_empty() {
                // Side-effect import: merge every top-level binding from the
                // module into the current env.
                for (name, scheme) in module_env.iter() {
                    if env.lookup(name).is_none() {
                        env = env.extend(name.clone(), scheme.clone());
                    }
                }
            } else {
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named {
                            imported, local, ..
                        } => {
                            let scheme = module_env.lookup(imported).ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no export named {:?}",
                                        source, imported
                                    ),
                                    span: *span,
                                })
                            })?;
                            env = env.extend(local.clone(), scheme.clone());
                        }
                        ImportSpecifier::Default { local, span } => {
                            let scheme = module_env.lookup("default").ok_or_else(|| {
                                MinfernError::Type(crate::error::TypeError::Module {
                                    message: format!(
                                        "module {:?} has no default export",
                                        source
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

/// Parse and infer a single module file, returning the env that results
/// from inferring it (minus the caller-provided starting env). Recursively
/// resolves nested imports. Returns only the top-level bindings introduced
/// by the module itself so the caller can merge them selectively.
fn load_module(
    state: &mut InferState,
    starting_env: TypeEnv,
    path: &Path,
    visiting: &mut HashSet<PathBuf>,
) -> Result<TypeEnv, MinfernError> {
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
        resolve_imports(state, starting_env.clone(), &program, &base_dir, visiting)?;
    let (_ty, module_env) =
        state.infer_program_with_env(&env_with_imports, &program)?;

    visiting.remove(&canonical);

    // Compute the bindings that THIS module introduced, relative to the
    // starting env we were given. Those are the things the caller can
    // import (either by name or via a side-effect import).
    Ok(diff_env(&starting_env, &module_env))
}

/// Compute `new_env` minus `base_env`: the bindings in `new_env` that
/// weren't in `base_env`, or that shadow a differently-bound name in
/// `base_env`. Used to pick out what a module actually exported.
fn diff_env(base_env: &TypeEnv, new_env: &TypeEnv) -> TypeEnv {
    let mut out = TypeEnv::empty();
    for (name, scheme) in new_env.iter() {
        let keep = match base_env.lookup(name) {
            None => true,
            // Compare by debug repr — good enough to filter out bindings the
            // starting env already supplied (DOM, stdlib, etc.) while keeping
            // anything the module actually defined or shadowed.
            Some(base_scheme) => format!("{:?}", base_scheme) != format!("{:?}", scheme),
        };
        if keep {
            out = out.extend(name.clone(), scheme.clone());
        }
    }
    out
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

    #[test]
    fn named_import_resolves() {
        let dir = tempdir();
        let _lib = write_file(
            dir.path(),
            "lib.js",
            "export function add(a, b) { return a + b; }",
        );
        let main_path = write_file(
            dir.path(),
            "main.js",
            "import { add } from \"./lib.js\"; var r = add(1, 2);",
        );
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
        )
        .unwrap();

        assert!(env.lookup("add").is_some(), "add should be imported");
    }

    #[test]
    fn default_import_resolves() {
        let dir = tempdir();
        let _lib = write_file(
            dir.path(),
            "lib.js",
            "export default function greet(name) { return \"hi \" + name; }",
        );
        let main_path = write_file(
            dir.path(),
            "main.js",
            "import greet from \"./lib.js\"; var r = greet(\"world\");",
        );
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
        )
        .unwrap();

        assert!(env.lookup("greet").is_some(), "greet should be imported");
    }

    #[test]
    fn default_export_expression_resolves() {
        let dir = tempdir();
        let _lib = write_file(
            dir.path(),
            "lib.js",
            "export default 42;",
        );
        let main_path = write_file(
            dir.path(),
            "main.js",
            "import answer from \"./lib.js\";",
        );
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
        )
        .unwrap();

        assert!(env.lookup("answer").is_some(), "answer should be imported");
    }

    #[test]
    fn default_import_without_export_errors() {
        let dir = tempdir();
        let _lib = write_file(
            dir.path(),
            "lib.js",
            "export const x = 1;",
        );
        let main_path = write_file(
            dir.path(),
            "main.js",
            "import x from \"./lib.js\";",
        );
        let source = std::fs::read_to_string(&main_path).unwrap();
        let program = parse(&source).unwrap();

        let mut state = InferState::new();
        let mut visiting = HashSet::new();
        let err = resolve_imports(
            &mut state,
            crate::builtins::initial_env(),
            &program,
            main_path.parent().unwrap(),
            &mut visiting,
        )
        .expect_err("missing default export should error");
        assert!(format!("{}", err).contains("default export"));
    }

    #[test]
    fn cycle_is_rejected() {
        let dir = tempdir();
        let _a = write_file(
            dir.path(),
            "a.js",
            "import { x } from \"./b.js\"; export var y = x;",
        );
        let _b = write_file(
            dir.path(),
            "b.js",
            "import { y } from \"./a.js\"; export var x = y;",
        );
        let main_path = write_file(
            dir.path(),
            "main.js",
            "import { y } from \"./a.js\";",
        );
        let source = std::fs::read_to_string(&main_path).unwrap();
        let program = parse(&source).unwrap();

        let mut state = InferState::new();
        let mut visiting = HashSet::new();
        let err = resolve_imports(
            &mut state,
            crate::builtins::initial_env(),
            &program,
            main_path.parent().unwrap(),
            &mut visiting,
        )
        .expect_err("cycle should error");
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
