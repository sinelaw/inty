//! Frontend-neutral IR for type annotations / type expressions.
//!
//! Each frontend (JavaScript/TypeScript, Python, `.pyi` stubs) parses its
//! own surface type syntax into this allocator-free tree; inference then
//! turns it into a real [`crate::types::Type`] via
//! `InferState::lower_type_ast`, which is the single place the semantic
//! decisions (fresh-variable allocation, union normalisation, …) live.
//!
//! Keeping the IR allocator-free is what lets a *parser* build it without
//! an `InferState`: type variables aren't minted here, they're minted when
//! the tree is lowered. See `docs/pyi-import-mapping.md` §8 for the
//! design rationale.

use super::ty::LitValue;

/// A parsed-but-not-yet-resolved type expression.
///
/// This is intentionally small: it covers the structural type space inty
/// can express, plus [`TypeAst::Opaque`] for anything a frontend can't (or
/// chooses not to) model precisely, which lowers to a fresh unconstrained
/// variable. New nodes are added as frontends need them.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeAst {
    Number,
    String,
    Boolean,
    Null,
    /// Unknown / unmodelled type (`Any`, an unknown name, a forward ref).
    /// Lowers to a fresh type variable, so it imposes no constraint and
    /// never produces a false positive.
    Opaque,
    Array(Box<TypeAst>),
    /// String-keyed map (`dict[str, V]`).
    Map(Box<TypeAst>),
    /// A union; lowering delegates normalisation (flatten, dedup, sort,
    /// singleton-collapse) to `Type::union`.
    Union(Vec<TypeAst>),
    /// A singleton-literal type (`"a"`, `42`, `true`).
    Lit(LitValue),
    /// A function type `(params) => ret`. Parameters are required
    /// (the surfaces that produce this — e.g. `Callable[[A, B], R]` —
    /// have no optionality).
    Func(Vec<TypeAst>, Box<TypeAst>),
}
