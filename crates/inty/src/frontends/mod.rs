//! Language frontends.
//!
//! A frontend turns source text in some surface language into the shared
//! [`crate::ast`]. Everything downstream — inference, the operational
//! semantics, decoration — works on that AST and is language-agnostic.
//!
//! Each frontend lowers its own surface syntax (and, where the syntax is
//! richer than the type system can express, a deliberately limited subset
//! of it) onto the same core nodes. JavaScript is just one frontend here;
//! Lua and Python are peers.

pub mod javascript;
pub mod lua;
pub mod python;

use crate::ast::Program;
use crate::error::Result;

/// The surface language a source file is written in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Language {
    JavaScript,
    Lua,
    Python,
}

impl Language {
    /// Guess the language from a file-name extension. `None` for unknown
    /// extensions; callers decide the default.
    pub fn from_extension(ext: &str) -> Option<Language> {
        match ext.rsplit('.').next().unwrap_or(ext) {
            "js" | "mjs" | "cjs" | "jsx" => Some(Language::JavaScript),
            "lua" => Some(Language::Lua),
            "py" | "pyi" => Some(Language::Python),
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
    }
}
