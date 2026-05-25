//! Python frontend (subset). Implemented in a later stage.

use crate::ast::Program;
use crate::error::Result;
use crate::span::Span;

/// Parse Python source into the shared AST.
pub fn parse_source(_source: &str) -> Result<Program> {
    Err(crate::error::ParseError::Unsupported {
        feature: "Python frontend not yet implemented".to_string(),
        span: Span::new(0, 0),
    }
    .into())
}
