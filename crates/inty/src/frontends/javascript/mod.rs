//! JavaScript frontend.
//!
//! Lexes and parses a JavaScript subset (mquickjs-compatible) and lowers
//! it to the shared [`crate::ast`]. JavaScript is one frontend among
//! several; Lua and Python are its peers under [`crate::frontends`].

pub mod lexer;
pub mod parser;

pub use parser::{parse, Parser};

use crate::ast::Program;
use crate::error::Result;

/// Parse JavaScript source into the shared AST.
pub fn parse_source(source: &str) -> Result<Program> {
    parser::parse(source)
}
