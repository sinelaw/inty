//! Lua frontend (subset).
//!
//! Lexes and parses a deliberately limited subset of Lua and lowers it
//! onto the shared [`crate::ast`]. The subset is chosen so that every
//! construct maps cleanly onto inty's type system; anything that doesn't
//! is rejected with a `ParseError::Unsupported` rather than mis-typed.
//!
//! Supported: `local`/assignment (single- and matched-arity multiple),
//! `function`/`local function`/method (`t:m`) definitions, `if/elseif/else`,
//! `while`, `repeat/until`, numeric `for`, `do` blocks, `break`, single-value
//! `return`, calls (including `f"s"` / `f{...}` sugar), table constructors
//! (array *or* record, not mixed), and the usual operators.
//!
//! Lowerings worth noting:
//! - `nil` → the null literal; `==`/`~=` are non-coercive (a natural fit
//!   for inty's strict equality).
//! - `..` (concat) → `+`, reusing the `Plus` type class on strings.
//! - `#x` (length) → a `.length` member read.
//! - `//` (floor division) → `/` (the floor step is dropped).
//! - `repeat B until c` → a do-while with the negated condition.
//! - method calls `t:m(a)` pass the receiver as `this`.
//!
//! Rejected (use a simpler form): multiple return values, varargs `...`,
//! generic `for ... in`, mixed-shape tables, `goto`/labels, and metatables
//! (there is no surface syntax for them — `setmetatable` is just a call and
//! is left to the type checker).

mod lexer;
mod parser;

use crate::ast::Program;
use crate::error::Result;

/// Parse Lua source into the shared AST.
pub fn parse_source(source: &str) -> Result<Program> {
    let tokens = lexer::tokenize(source)?;
    parser::Parser::new(tokens).parse_program()
}

#[cfg(test)]
mod tests;
