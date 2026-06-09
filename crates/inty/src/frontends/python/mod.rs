//! Python frontend (subset).
//!
//! Lexes (with the off-side rule) and parses a limited subset of Python and
//! lowers it onto the shared [`crate::ast`]. As with the other frontends,
//! constructs the type system can't express are rejected with a
//! `ParseError::Unsupported` rather than mis-typed.
//!
//! Supported: `def` (positional params), assignment (plain, chained,
//! augmented, matched-arity tuple), `if/elif/else`, `while`, `for ... in`
//! (single target), `pass`/`break`/`continue`, single-value `return`,
//! `lambda`, ternary `a if c else b`, calls, lists, dicts (literal keys),
//! and the usual operators.
//!
//! Classes support single inheritance: `class Sub(Base):` lowers to a
//! factory that constructs and spreads a base instance, so base fields and
//! methods are inherited via the structural row merge. `super().__init__(…)`
//! drives the base construction and `super().m(…)` calls a base method.
//! Inheritance is structural — a subclass instance carries its base's
//! fields, so a base-shaped parameter accepts a subclass by row
//! polymorphism. (Known gap: calling an *inherited, non-overridden* method
//! directly on a subclass instance is not yet accepted — see the parser's
//! `class_stmt`.) Multiple inheritance is rejected.
//!
//! Lowerings worth noting:
//! - `None` → the null literal; `True`/`False` → booleans.
//! - Python has no `var`/`local`, so the first assignment to a bare name
//!   becomes a hoisted `var` (inty scopes `var` to the function, matching
//!   Python's function scoping); later assignments become plain assignments.
//! - `/` and `//` both map to `/`; `**` → `**` (Pow).
//! - type annotations (`x: int`, `def f(a: int) -> str:`) are parsed and
//!   discarded — inty infers types instead.
//!
//! Rejected (use a simpler form): `*args`/`**kwargs`, comprehensions,
//! slicing, `is`/`in`, chained comparisons, and the statement keywords
//! `with`/`try`/`global`/`del`/`yield`/… .

mod lexer;
pub mod modules;
mod parser;
pub mod prelude;
pub mod pyi;
mod stubs;
pub mod type_expr;

use crate::ast::Program;
use crate::error::Result;

/// Parse Python source into the shared AST.
pub fn parse_source(source: &str) -> Result<Program> {
    let tokens = lexer::tokenize(source)?;
    parser::Parser::new(tokens).parse_program()
}

#[cfg(test)]
mod tests;
