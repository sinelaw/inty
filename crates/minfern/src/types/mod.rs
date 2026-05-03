//! Type system module for minfern.
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
