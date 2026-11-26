//! Language frontends.
//!
//! A frontend turns source text in some surface language into the shared
//! [`crate::ast`]. Everything downstream — inference, the operational
//! semantics, decoration — works on that AST and is language-agnostic.
//!
//! Each frontend lowers its own surface syntax (and, where the syntax is
//! richer than the type system can express, a deliberately limited subset
//! of it) onto the same core nodes. JavaScript is just one frontend here;
//! Lua and Python are peers, and Starlark is a dialect of the Python one.

pub mod javascript;
pub mod lua;
pub mod python;
pub mod starlark;

use std::path::Path;

use crate::ast::Program;
use crate::error::Result;
use crate::infer::{InferState, TypeEnv};

/// The surface language a source file is written in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Language {
    JavaScript,
    Lua,
    Python,
    Starlark,
}

impl Language {
    /// Guess the language from a file-name extension. `None` for unknown
    /// extensions; callers decide the default.
    pub fn from_extension(ext: &str) -> Option<Language> {
        match ext.rsplit('.').next().unwrap_or(ext) {
            "js" | "mjs" | "cjs" | "jsx" => Some(Language::JavaScript),
            "lua" => Some(Language::Lua),
            "py" | "pyi" => Some(Language::Python),
            "star" | "sky" | "bzl" => Some(Language::Starlark),
            _ => None,
        }
    }

    /// Guess the language from a path's extension.
    pub fn from_path(path: &str) -> Option<Language> {
        let ext = path.rsplit('.').next()?;
        if ext == path {
            return None;
        }
        Language::from_extension(ext)
    }
}

/// Parse source written in `language` into the shared AST.
pub fn parse(language: Language, source: &str) -> Result<Program> {
    match language {
        Language::JavaScript => javascript::parse_source(source),
        Language::Lua => lua::parse_source(source),
        Language::Python => python::parse_source(source),
        Language::Starlark => starlark::parse_source(source),
    }
}

/// The environment `program` is checked in: `base` (the built-ins and
/// any libraries) with its language's prelude, a JavaScript project's
/// libs (`inty.json` `"libs"`), and what it imports resolved from the
/// file at `path`. Without a path (source from stdin,
/// an editor buffer not yet saved) imports are left unresolved, and a
/// Starlark program's `load`ed names are bound unchecked.
///
/// The CLI and the language server both build the environment here, so
/// the editor checks exactly what `inty FILE` does.
pub fn program_env(
    state: &mut InferState,
    base: TypeEnv,
    program: &Program,
    language: Language,
    path: Option<&Path>,
) -> Result<TypeEnv> {
    let base_dir = || {
        path.and_then(Path::parent)
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf()
    };
    let mut visiting = std::collections::HashSet::new();
    match language {
        Language::JavaScript => Ok(match path {
            Some(path) => {
                let base = crate::modules::with_project_libs(state, base, path);
                crate::modules::resolve_imports(state, base, program, &base_dir(), &mut visiting)
            }
            None => base,
        }),
        Language::Python => match path {
            Some(_) => python::modules::resolve_python_imports(
                state,
                base,
                program,
                &base_dir(),
                &python::modules::search_paths(),
                &mut visiting,
            ),
            None => python::prelude::load(state, base),
        },
        // Starlark starts from its own prelude, not `base`. A `.bzl`
        // file (or one with no path) sees Bazel's globals.
        Language::Starlark => {
            let bazel = path.is_none_or(starlark::is_bazel_file);
            let prelude = starlark::prelude::load(state, crate::builtins::initial_env(), bazel)?;
            match path {
                Some(path) => starlark::resolve_loads(
                    state,
                    prelude,
                    program,
                    path,
                    &mut starlark::Loader::new(),
                ),
                None => starlark::bind_loads_opaquely(state, prelude, program),
            }
        }
        Language::Lua => Ok(base),
    }
}
