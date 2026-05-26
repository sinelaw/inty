//! Python import resolution.
//!
//! Resolves the `Stmt::Import` nodes the Python frontend produces to
//! files on disk and binds the imported names into the type environment.
//! Two kinds of target are supported:
//!
//!   - **`.py` modules** — parsed, their own imports resolved, then
//!     type-checked; the module's public top-level names become its
//!     exports (Python has no `export` keyword — everything not prefixed
//!     `_` is importable).
//!   - **`.pyi` stubs** — read declaratively by [`super::pyi`], mapping
//!     Bucket-A type declarations to schemes (no inference).
//!
//! Resolution searches, in order, the configured `search_paths` (the
//! "typeshed / site-packages" roots) and then the importing file's own
//! directory, trying `<mod>.pyi`, `<mod>.py`, and the package forms
//! `<mod>/__init__.pyi|.py`. Stubs win over implementations. Relative
//! imports (`from . import x`, `from ..pkg import y`) anchor at the
//! importing file's directory and ascend one level per leading dot.
//!
//! Anything that cannot be resolved or modelled degrades rather than
//! aborting the whole check where reasonable (see the per-call notes);
//! a genuinely missing module is still an error.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::ast::{ImportSpecifier, Program, Stmt};
use crate::error::{IntyError, TypeError};
use crate::infer::{InferState, TypeEnv};
use crate::types::{Type, TypeScheme};

/// One module's public exports.
type Exports = Vec<(String, TypeScheme)>;

/// Resolve every `import` in `program`, returning `env` extended with the
/// imported bindings. `search_paths` are the absolute roots to search for
/// absolute (non-relative) imports; `base_dir` is the importing file's
/// directory, used for relative imports and as a final search fallback.
pub fn resolve_python_imports(
    state: &mut InferState,
    env: TypeEnv,
    program: &Program,
    base_dir: &Path,
    search_paths: &[PathBuf],
    visiting: &mut HashSet<PathBuf>,
) -> Result<TypeEnv, IntyError> {
    let mut env = env;
    for stmt in &program.statements {
        let Stmt::Import {
            specifiers,
            source,
            span,
        } = stmt
        else {
            continue;
        };

        let module_err = |msg: String| {
            IntyError::Type(TypeError::Module {
                message: msg,
                span: *span,
            })
        };

        if specifiers.is_empty() {
            // `from m import *` — merge all of m's exports.
            let path = resolve_module(source, base_dir, search_paths)
                .ok_or_else(|| module_err(format!("cannot resolve import {:?}", source)))?;
            let exports = load_module(state, &env, &path, search_paths, visiting)?;
            for (name, scheme) in exports {
                if !name.starts_with('_') {
                    env = env.extend(name, scheme);
                }
            }
            continue;
        }

        for spec in specifiers {
            match spec {
                ImportSpecifier::Named {
                    imported, local, ..
                } => {
                    let path = resolve_module(source, base_dir, search_paths)
                        .ok_or_else(|| module_err(format!("cannot resolve import {:?}", source)))?;
                    let exports = load_module(state, &env, &path, search_paths, visiting)?;
                    if let Some((_, scheme)) =
                        exports.iter().find(|(n, _)| n == imported)
                    {
                        env = env.extend(local.clone(), scheme.clone());
                    } else if let Some(sub) =
                        resolve_submodule(source, imported, base_dir, search_paths)
                    {
                        // `from pkg import submod` where `submod` is a
                        // module file, not a name exported by `pkg`.
                        let sub_exports =
                            load_module(state, &env, &sub, search_paths, visiting)?;
                        env = env.extend(local.clone(), namespace_scheme(&sub_exports));
                    } else {
                        return Err(module_err(format!(
                            "module {:?} has no export named {:?}",
                            source, imported
                        )));
                    }
                }
                ImportSpecifier::Namespace { local, .. } => {
                    // `import m` / `import a.b.c as m` — bind the module
                    // namespace as a row of its exports.
                    let path = resolve_module(source, base_dir, search_paths)
                        .ok_or_else(|| module_err(format!("cannot resolve import {:?}", source)))?;
                    let exports = load_module(state, &env, &path, search_paths, visiting)?;
                    env = env.extend(local.clone(), namespace_scheme(&exports));
                }
                ImportSpecifier::Default { local, span } => {
                    // Python has no default imports; treat defensively.
                    return Err(IntyError::Type(TypeError::Module {
                        message: format!("unexpected default import {:?}", local),
                        span: *span,
                    }));
                }
            }
        }
    }
    Ok(env)
}

/// Build a namespace binding from a module's exports: a closed object row
/// `{name: T, …}` so `ns.member` reads resolve. Polymorphism of exported
/// functions is flattened to their body type (sufficient for member
/// access in this slice).
fn namespace_scheme(exports: &Exports) -> TypeScheme {
    let row = Type::object(
        exports
            .iter()
            .filter(|(n, _)| !n.starts_with('_'))
            .map(|(n, s)| (n.clone(), s.body.ty.clone())),
    );
    TypeScheme::mono(row)
}

/// Load a module file's public exports, dispatching on extension. `.py`
/// files are parsed + inferred; `.pyi` stubs are read declaratively.
fn load_module(
    state: &mut InferState,
    env: &TypeEnv,
    path: &Path,
    search_paths: &[PathBuf],
    visiting: &mut HashSet<PathBuf>,
) -> Result<Exports, IntyError> {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if visiting.contains(&canonical) {
        return Err(IntyError::Type(TypeError::Module {
            message: format!("circular import involving {}", canonical.display()),
            span: crate::span::Span::new(0, 0),
        }));
    }

    let source = std::fs::read_to_string(path).map_err(|e| {
        IntyError::Type(TypeError::Module {
            message: format!("failed to read {}: {}", path.display(), e),
            span: crate::span::Span::new(0, 0),
        })
    })?;

    if path.extension().and_then(|e| e.to_str()) == Some("pyi") {
        // Stubs are self-contained declarations; no recursion / inference.
        return super::pyi::read_stub(state, &source);
    }

    // A `.py` implementation module: parse, resolve its imports, infer,
    // then surface its public top-level bindings as exports.
    let program = super::parse_source(&source)?;
    visiting.insert(canonical.clone());

    let mod_base = path
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));

    let base_names: HashSet<String> = env.names().cloned().collect();
    let env_with_imports =
        resolve_python_imports(state, env.clone(), &program, &mod_base, search_paths, visiting)?;
    let (_ty, module_env) = state.infer_program_with_env(&env_with_imports, &program)?;

    visiting.remove(&canonical);

    let exports = module_env
        .iter()
        .filter(|(name, _)| !base_names.contains(*name) && !name.starts_with('_'))
        .map(|(name, scheme)| (name.clone(), scheme.clone()))
        .collect();
    Ok(exports)
}

/// Resolve an (absolute or relative) module spec to a file. Tries stub
/// before implementation, and the `__init__` package forms.
fn resolve_module(spec: &str, base_dir: &Path, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let (anchor, rest) = anchor_for_spec(spec, base_dir)?;
    if rest.is_empty() {
        // `from . import x` — the package itself; resolve its __init__.
        return file_candidates(&anchor, &[]);
    }
    let parts: Vec<&str> = rest.split('.').filter(|s| !s.is_empty()).collect();

    if spec.starts_with('.') {
        // Relative: only the anchored directory is searched.
        return file_candidates(&anchor, &parts);
    }
    // Absolute: search the configured roots first, then the file's dir.
    for root in search_paths.iter().chain(std::iter::once(&base_dir.to_path_buf())) {
        if let Some(hit) = file_candidates(root, &parts) {
            return Some(hit);
        }
    }
    None
}

/// Resolve `<pkg>.<name>` as a submodule file (used when `name` isn't a
/// value exported by `pkg`, e.g. `from pkg import submod`).
fn resolve_submodule(
    pkg: &str,
    name: &str,
    base_dir: &Path,
    search_paths: &[PathBuf],
) -> Option<PathBuf> {
    let joined = if pkg.ends_with('.') || pkg.is_empty() {
        format!("{}{}", pkg, name)
    } else {
        format!("{}.{}", pkg, name)
    };
    resolve_module(&joined, base_dir, search_paths)
}

/// Split a spec into its anchoring directory and the remaining dotted
/// path. For a relative spec the anchor ascends one directory per leading
/// dot beyond the first; for an absolute spec the anchor is unused (the
/// caller searches roots) and `rest == spec`.
fn anchor_for_spec(spec: &str, base_dir: &Path) -> Option<(PathBuf, String)> {
    if !spec.starts_with('.') {
        return Some((base_dir.to_path_buf(), spec.to_string()));
    }
    let dots = spec.chars().take_while(|&c| c == '.').count();
    let rest = spec[dots..].to_string();
    let mut anchor = base_dir.to_path_buf();
    // One dot == current package; each extra dot ascends a level.
    for _ in 0..dots.saturating_sub(1) {
        anchor = anchor.parent()?.to_path_buf();
    }
    Some((anchor, rest))
}

/// Try the file forms for a dotted module under `root`: `a/b/c.pyi`,
/// `a/b/c.py`, then the package forms `a/b/c/__init__.pyi|.py`. With empty
/// `parts`, only the package `__init__` forms under `root` are tried.
fn file_candidates(root: &Path, parts: &[&str]) -> Option<PathBuf> {
    let mut dir = root.to_path_buf();
    if parts.is_empty() {
        for init in ["__init__.pyi", "__init__.py"] {
            let p = dir.join(init);
            if p.is_file() {
                return Some(p);
            }
        }
        return None;
    }
    for seg in &parts[..parts.len() - 1] {
        dir.push(seg);
    }
    let last = parts[parts.len() - 1];
    for ext in ["pyi", "py"] {
        let p = dir.join(format!("{}.{}", last, ext));
        if p.is_file() {
            return Some(p);
        }
    }
    let pkg = dir.join(last);
    for init in ["__init__.pyi", "__init__.py"] {
        let p = pkg.join(init);
        if p.is_file() {
            return Some(p);
        }
    }
    None
}
