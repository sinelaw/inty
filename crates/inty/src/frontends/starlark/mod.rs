//! Starlark frontend.
//!
//! Starlark (<https://starlark-lang.org/>) is the Python dialect used by
//! Bazel, Buck2 and others for build files and extensions. It is close to
//! a subset of Python, so it shares the Python lexer and parser
//! ([`crate::frontends::python`]) run in a Starlark mode, and its programs
//! are inferred exactly as Python programs are (`SourceLanguage::Python`).
//!
//! What the Starlark mode changes:
//!
//! - It rejects what Starlark leaves out of Python: `class`, `try` /
//!   `raise`, `while`, `import` / `from`, `global`, `with`, decorators,
//!   `is`, `**`, f-strings, and the statement keywords the Python subset
//!   already rejects (`yield`, `del`, …).
//! - It enforces Starlark's static rules: no `if` / `for` at the top level,
//!   a global is bound once (no reassignment, no second `def` of a name),
//!   and no recursion.
//! - `load("label", "name", local = "name")` imports names from another
//!   Starlark file. [`resolve_loads`] resolves the label to a file:
//!   `//pkg:file.bzl` from the workspace root (the nearest directory up
//!   with a `MODULE.bazel`, `REPO.bazel`, `WORKSPACE`, `WORKSPACE.bazel`
//!   or `.buckconfig`), `:file.bzl` from the loading file's package (the
//!   nearest directory up with a `BUILD`, `BUILD.bazel` or `BUCK` file,
//!   else the file's own directory). A label in another repository
//!   (`@repo//…`) can't be read, so its names are bound opaquely.
//! - `fail(…)` as a statement is lowered to a `throw`, and
//!   `struct(a = 1, b = x)` to the record `{a: 1, b: x}`.
//!
//! The prelude ([`prelude`]) is the Starlark builtins, taken from the
//! Python prelude, plus `fail`, `struct` and `dir`. A `.bzl` file also
//! gets Bazel's globals (`rule`, `attr`, `native`, `provider`, …), bound
//! opaquely for now.
//!
//! Files are recognised by extension: `.star`, `.sky` and `.bzl`. `BUILD`
//! and `BUCK` files are left out until inty has declarations for the
//! native rules they call as bare globals.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::ast::{ImportSpecifier, Program, Stmt};
use crate::error::{IntyError, Result, SourceFile, TypeError};
use crate::infer::{InferState, TypeEnv};
use crate::types::TypeScheme;

/// Parse Starlark source into the shared AST.
pub fn parse_source(source: &str) -> Result<Program> {
    crate::frontends::python::parse_starlark_source(source)
}

/// Whether a path names a Bazel extension file (`.bzl`), which gets
/// Bazel's globals in its prelude.
pub fn is_bazel_file(path: &Path) -> bool {
    path.extension().and_then(|e| e.to_str()) == Some("bzl")
}

/// The Starlark builtin namespace.
pub mod prelude {
    use super::*;
    use crate::frontends::python::pyi::read_stub;

    /// The builtins of the Starlark specification that the Python prelude
    /// provides (with the same signatures).
    const FROM_PYTHON: &[&str] = &[
        "any",
        "all",
        "bool",
        "dict",
        "enumerate",
        "float",
        "getattr",
        "hasattr",
        "hash",
        "int",
        "len",
        "list",
        "max",
        "min",
        "print",
        "range",
        "repr",
        "reversed",
        "sorted",
        "str",
        "tuple",
        "type",
        "zip",
    ];

    const STARLARK: &str = include_str!("builtins.pyi");
    const BAZEL: &str = include_str!("bazel.pyi");

    /// Extend `env` with the Starlark builtins, and with Bazel's globals
    /// when `bazel` (a `.bzl` file).
    pub fn load(state: &mut InferState, mut env: TypeEnv, bazel: bool) -> Result<TypeEnv> {
        state.set_language(crate::ast::SourceLanguage::Python);
        let python = read_stub(state, crate::frontends::python::prelude::PRELUDE)?;
        for (name, scheme) in python.exports {
            if FROM_PYTHON.contains(&name.as_str()) {
                env = env.extend(name, scheme);
            }
        }
        let mut stubs = vec![STARLARK];
        if bazel {
            stubs.push(BAZEL);
        }
        for stub in stubs {
            for (name, scheme) in read_stub(state, stub)?.exports {
                env = env.extend(name, scheme);
            }
        }
        Ok(env)
    }
}

/// Where a `load` label points.
#[derive(Debug, PartialEq, Eq)]
pub enum LoadTarget {
    /// A file of this workspace.
    File(PathBuf),
    /// A file in another repository (`@repo//…`), which isn't read.
    External,
}

/// Resolve a `load` label, written in the file `from`, to its target.
/// `None` when the label needs a workspace root (`//pkg:f.bzl`) and none
/// was found, or the label is malformed.
pub fn resolve_label(label: &str, from: &Path) -> Option<LoadTarget> {
    let from_dir = match from.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let root = workspace_root(from_dir);
    let mut rest = label;
    if let Some(after) = rest.strip_prefix('@') {
        let after = after.strip_prefix('@').unwrap_or(after);
        let (repo, path) = after.split_once("//")?;
        if !repo.is_empty() {
            return Some(LoadTarget::External);
        }
        rest = path;
        return Some(LoadTarget::File(in_package(&root?, rest)));
    }
    if let Some(path) = rest.strip_prefix("//") {
        return Some(LoadTarget::File(in_package(&root?, path)));
    }
    // A relative label (`:f.bzl`, `f.bzl`): in the loading file's package.
    let name = rest.strip_prefix(':').unwrap_or(rest);
    if name.is_empty() {
        return None;
    }
    let pkg = package_dir(from_dir, root.as_deref());
    Some(LoadTarget::File(pkg.join(name)))
}

/// `pkg/sub:name` (or `pkg/sub`, naming `pkg/sub/sub`) under `root`.
fn in_package(root: &Path, path: &str) -> PathBuf {
    let (pkg, name) = match path.split_once(':') {
        Some((pkg, name)) => (pkg, name.to_string()),
        None => (path, path.rsplit('/').next().unwrap_or(path).to_string()),
    };
    let mut p = root.to_path_buf();
    if !pkg.is_empty() {
        p.push(pkg);
    }
    p.push(name);
    p
}

/// The nearest directory at or above `dir` that marks a workspace root.
fn workspace_root(dir: &Path) -> Option<PathBuf> {
    const MARKERS: &[&str] = &[
        "MODULE.bazel",
        "REPO.bazel",
        "WORKSPACE",
        "WORKSPACE.bazel",
        ".buckconfig",
    ];
    let dir = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    dir.ancestors()
        .find(|d| MARKERS.iter().any(|m| d.join(m).is_file()))
        .map(Path::to_path_buf)
}

/// The package directory of a file in `dir`: the nearest directory at or
/// above it (and not above `root`) with a `BUILD`, `BUILD.bazel` or `BUCK`
/// file, else `dir` itself.
fn package_dir(dir: &Path, root: Option<&Path>) -> PathBuf {
    const MARKERS: &[&str] = &["BUILD", "BUILD.bazel", "BUCK"];
    let dir = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    for d in dir.ancestors() {
        if MARKERS.iter().any(|m| d.join(m).is_file()) {
            return d.to_path_buf();
        }
        if Some(d) == root {
            break;
        }
    }
    dir
}

/// One file's exported names (its top-level names not starting with `_`).
type Exports = Vec<(String, TypeScheme)>;

/// Loaded files and the files being loaded, shared across one check.
#[derive(Default)]
pub struct Loader {
    cache: HashMap<PathBuf, Exports>,
    visiting: HashSet<PathBuf>,
}

impl Loader {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Resolve every `load` in `program` (the file at `path`) and return `env`
/// extended with the loaded names. Each loaded file is parsed, its own
/// loads resolved, and inferred with `base` (the prelude, without the
/// loading file's names) as its environment; a file is read once per
/// [`Loader`].
pub fn resolve_loads(
    state: &mut InferState,
    base: &TypeEnv,
    env: TypeEnv,
    program: &Program,
    path: &Path,
    loader: &mut Loader,
) -> Result<TypeEnv> {
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
        let module_err = |message: String| {
            IntyError::from(TypeError::Module {
                message,
                span: *span,
            })
        };
        let exports = match resolve_label(source, path) {
            Some(LoadTarget::File(file)) => {
                if !file.is_file() {
                    return Err(module_err(format!(
                        "cannot load {source:?}: no file {}",
                        file.display()
                    )));
                }
                load_file(state, base, &file, loader)?
            }
            Some(LoadTarget::External) => {
                // Another repository: bind each name opaquely.
                let stub: String = specifiers
                    .iter()
                    .filter_map(|s| match s {
                        ImportSpecifier::Named { imported, .. } => {
                            Some(format!("{imported}: object\n"))
                        }
                        _ => None,
                    })
                    .collect();
                crate::frontends::python::pyi::read_stub(state, &stub)?.exports
            }
            None => {
                return Err(module_err(format!(
                    "cannot load {source:?}: no workspace root (a directory with \
                     MODULE.bazel, REPO.bazel, WORKSPACE or .buckconfig) above {}",
                    path.display()
                )))
            }
        };
        for spec in specifiers {
            if let ImportSpecifier::Named {
                imported, local, ..
            } = spec
            {
                let (_, scheme) = exports
                    .iter()
                    .find(|(n, _)| n == imported)
                    .ok_or_else(|| module_err(format!("{source:?} has no symbol {imported:?}")))?;
                env = env.extend(local.clone(), scheme.clone());
            }
        }
    }
    Ok(env)
}

/// Bind every name `program` loads opaquely, without reading the files:
/// for a caller that has no file path to resolve labels against (the
/// language server, the playground).
pub fn bind_loads_opaquely(
    state: &mut InferState,
    env: TypeEnv,
    program: &Program,
) -> Result<TypeEnv> {
    let stub: String = program
        .statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Import { specifiers, .. } => Some(specifiers),
            _ => None,
        })
        .flatten()
        .filter_map(|s| match s {
            ImportSpecifier::Named { local, .. } => Some(format!("{local}: object\n")),
            _ => None,
        })
        .collect();
    let mut env = env;
    for (name, scheme) in crate::frontends::python::pyi::read_stub(state, &stub)?.exports {
        env = env.extend(name, scheme);
    }
    Ok(env)
}

/// Parse, resolve and infer the file at `path`, returning its exports.
fn load_file(
    state: &mut InferState,
    base: &TypeEnv,
    path: &Path,
    loader: &mut Loader,
) -> Result<Exports> {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if let Some(exports) = loader.cache.get(&canonical) {
        return Ok(exports.clone());
    }
    let module_err = |message: String| {
        IntyError::from(TypeError::Module {
            message,
            span: crate::span::Span::new(0, 0),
        })
    };
    if !loader.visiting.insert(canonical.clone()) {
        return Err(module_err(format!(
            "load cycle involving {}",
            canonical.display()
        )));
    }
    let text = std::fs::read_to_string(path)
        .map_err(|e| module_err(format!("failed to read {}: {e}", path.display())))?;
    let module_src = SourceFile {
        path: path.display().to_string(),
        text: text.clone(),
    };
    let program = match parse_source(&text) {
        Ok(p) => p,
        Err(e) => {
            state.set_current_source(Some(module_src));
            return Err(e);
        }
    };
    // A loaded file sees the prelude and its own loads, never the names of
    // the file that loads it.
    let env = resolve_loads(state, base, base.clone(), &program, path, loader)?;
    let base_names: HashSet<String> = env.names().cloned().collect();
    let prev = state.set_current_source(Some(module_src));
    let (_, module_env) = state.infer_program_with_env(&env, &program)?;
    state.set_current_source(prev);
    loader.visiting.remove(&canonical);
    let exports: Exports = module_env
        .iter()
        .filter(|(name, _)| !base_names.contains(*name) && !name.starts_with('_'))
        .map(|(name, scheme)| (name.clone(), scheme.clone()))
        .collect();
    loader.cache.insert(canonical, exports.clone());
    Ok(exports)
}

#[cfg(test)]
mod tests;
