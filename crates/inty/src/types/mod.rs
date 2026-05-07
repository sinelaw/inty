//! Type system module for inty.
//!
//! This module provides the core type definitions, substitution implementation,
//! and pretty-printing for the HMF-based type inference system.

mod pretty;
mod subst;
mod ty;

pub use pretty::PrettyContext;
pub use subst::{Subst, Substitutable};
pub use ty::{
    ClassName, LitValue, ModuleType, PropName, QualType, RowTail, RowType, TVarId, TVarName, Type,
    TypeDef, TypeId, TypePred, TypeScheme,
};

/// Reserved property name for the call signature of a callable row.
///
/// A row carrying this field acts as a function value: calling such a
/// row peels the field's `Type::Func` and uses it as the callable. The
/// key starts with a NUL byte so it cannot be produced by inty's
/// parser from JS source — `PropKey::Ident` and `PropKey::String`
/// don't tokenise control characters as part of identifiers, and the
/// type-annotation parser only emits this key via the dedicated
/// keyless-call-signature arm. That makes the field reachable
/// internally (via member-access and unification rules that look it
/// up by exact name) but unreachable from user code.
///
/// See `examples/fizzy/design.md` § "Callable rows" for the design
/// rationale.
pub const CALLABLE_KEY: &str = "\x01call\x01";

/// True when the given property name is the reserved callable-row
/// sentinel. Hidden by the pretty printer and never produced from
/// user-written JS.
pub fn is_callable_key(name: &PropName) -> bool {
    name.0 == CALLABLE_KEY
}
