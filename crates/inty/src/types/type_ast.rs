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
    /// A named type variable (`T` from `Generic[T]` / a `TypeVar`).
    /// Unlike [`TypeAst::Opaque`], all occurrences of the same name within
    /// one lowering scope share a single variable, so a generic container
    /// `class Box(Generic[T])` ties its `T`-typed fields together.
    Var(String),
    /// A reference to a named type — a user type alias, possibly with type
    /// arguments (`BumpType`, `Pair[int, str]`). Lowering resolves it
    /// against the inference state's alias table (inlining a structural
    /// alias, or producing the brand of a nominal one); an unknown name
    /// lowers to a fresh variable, so it imposes no constraint.
    Ref(String, Vec<TypeAst>),
    Array(Box<TypeAst>),
    /// String-keyed map (`dict[str, V]`).
    Map(Box<TypeAst>),
    /// A union; lowering delegates normalisation (flatten, dedup, sort,
    /// singleton-collapse) to `Type::union`.
    Union(Vec<TypeAst>),
    /// A singleton-literal type (`"a"`, `42`, `true`).
    Lit(LitValue),
    /// A fixed-arity heterogeneous tuple `(T0, T1, …)` (Python
    /// `tuple[A, B]`). Lowers to [`crate::types::Type::Tuple`]. Note the
    /// homogeneous variadic `tuple[T, ...]` is parsed to [`TypeAst::Array`]
    /// instead.
    Tuple(Vec<TypeAst>),
    /// A function type `(params) => ret`. Parameters are required
    /// (the surfaces that produce this — e.g. `Callable[[A, B], R]` —
    /// have no optionality).
    Func(Vec<TypeAst>, Box<TypeAst>),
    /// A record of exactly these fields, `{name: str, pid: int}` in a
    /// Python or Starlark annotation or type comment. Lowers to a closed
    /// row, as an object literal's type is.
    Record(Vec<(String, TypeAst)>),
}

impl TypeAst {
    /// The names this type refers to ([`TypeAst::Ref`]s), at any depth,
    /// in order with repeats: what an alias's body depends on.
    pub fn ref_names(&self) -> Vec<&str> {
        let mut out = Vec::new();
        self.collect_refs(&mut out);
        out
    }

    fn collect_refs<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            TypeAst::Ref(name, args) => {
                out.push(name);
                args.iter().for_each(|a| a.collect_refs(out));
            }
            TypeAst::Array(t) | TypeAst::Map(t) => t.collect_refs(out),
            TypeAst::Union(ts) | TypeAst::Tuple(ts) => ts.iter().for_each(|t| t.collect_refs(out)),
            TypeAst::Func(ps, r) => {
                ps.iter().for_each(|p| p.collect_refs(out));
                r.collect_refs(out);
            }
            TypeAst::Record(fields) => fields.iter().for_each(|(_, t)| t.collect_refs(out)),
            TypeAst::Number
            | TypeAst::String
            | TypeAst::Boolean
            | TypeAst::Null
            | TypeAst::Opaque
            | TypeAst::Var(_)
            | TypeAst::Lit(_) => {}
        }
    }
}
