//! Python frontend (subset).
//!
//! Lexes (with the off-side rule) and parses a limited subset of Python and
//! lowers it onto the shared [`crate::ast`]. As with the other frontends,
//! constructs the type system can't express are rejected with a
//! `ParseError::Unsupported` rather than mis-typed.
//!
//! Supported: `def` (positional, default and keyword-only parameters),
//! assignment (plain, chained, augmented, matched-arity tuple),
//! `if/elif/else`, `while`, `for ... in`, `pass`/`break`/`continue`,
//! `return`, `global`, `lambda`, ternary `a if c else b`, calls (with
//! keyword arguments), lists, list comprehensions, slices, dicts (literal
//! keys), and the usual operators.
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
//! - type annotations (`x: int`, `def f(a: int) -> str:`), and PEP 484
//!   type comments (`x = []  # type: list[str]`, `# type: (int) -> str`
//!   after a `def` header), declare types that inference checks.
//! - `[e for x in xs if c]` → an immediately-called arrow function that
//!   loops and appends, so the loop variables stay local to it; a
//!   generator expression passed as the sole argument of a call that only
//!   iterates it (`any(x > 0 for x in xs)`, `sum`, `sorted`, `join`, …) is
//!   lowered the same way. Any other generator expression is rejected: it
//!   can't be indexed or measured as a list can.
//! - `xs[a:b:c]` → a call of an internal slice method (`None` for an
//!   omitted bound), which the `str` and `list` surfaces give the
//!   receiver's own type. A tuple can't be sliced.
//! - `def f(a, *, b)`: parameters after the bare `*` are ordinary named
//!   parameters (passing them by position isn't rejected).
//!
//! Rejected (use a simpler form): `*args`/`**kwargs`, dict and set
//! comprehensions, chained comparisons, and the statement keywords
//! `nonlocal`/`del`/`yield`/… .
//!
//! The parser also has a Starlark mode; see [`crate::frontends::starlark`].

mod lexer;
pub mod modules;
mod parser;
pub use parser::SLICE_METHOD;
pub mod prelude;
pub mod pyi;
mod stubs;
pub mod type_expr;

use crate::ast::Program;
use crate::error::Result;

/// Parse Python source into the shared AST.
pub fn parse_source(source: &str) -> Result<Program> {
    let (tokens, comments) = lexer::tokenize_with_type_comments(source)?;
    parser::Parser::new(tokens)
        .with_type_comments(comments)
        .parse_program()
}

/// Parse Starlark source (the Python dialect; see
/// [`crate::frontends::starlark`]) into the shared AST.
pub fn parse_starlark_source(source: &str) -> Result<Program> {
    let (tokens, comments) = lexer::tokenize_with_type_comments(source)?;
    parser::Parser::new_starlark(tokens)
        .with_type_comments(comments)
        .parse_program()
}

#[cfg(test)]
mod tests;
