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
//! `global`, `lambda`, ternary `a if c else b`, calls, lists, dicts
//! (literal keys), and the usual operators.
//!
//! Lowerings worth noting:
//! - `None` → the null literal; `True`/`False` → booleans.
//! - Python has no `var`/`local`, so the first assignment to a bare name
//!   becomes a hoisted `var` (inty scopes `var` to the function, matching
//!   Python's function scoping); later assignments become plain assignments.
//! - Scoping follows Python's local-by-default rule: a name assigned inside
//!   a function is a fresh local that shadows any same-named module/enclosing
//!   binding. To rebind a module-level variable, declare it `global` (then
//!   assignments lower against the module binding). An augmented assignment
//!   (`x += 1`) to a name that isn't yet bound in the function — and isn't
//!   declared `global` — is rejected as a referenced-before-assignment.
//! - `/` and `//` both map to `/`; `**` → `**` (Pow).
//! - type annotations (`x: int`, `def f(a: int) -> str:`) are parsed and
//!   discarded — inty infers types instead.
//!
//! Rejected (use a simpler form): `*args`/`**kwargs`, comprehensions,
//! slicing, `is`/`in`, chained comparisons, and the statement keywords
//! `nonlocal`/`del`/`yield`/… .

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
