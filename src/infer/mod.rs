//! Type inference module for minfern.
//!
//! This module provides the core type inference implementation:
//! - `state`: Inference state with fresh variable generation and substitution
//! - `env`: Type environment for variable bindings
//! - `unify`: Unification algorithm with occurs check
//! - `infer`: Core type inference for expressions and statements
//! - `type_parser`: Parser for TypeScript-style type annotations
//! - `decorate`: AST decoration with inferred types

mod decorate;
mod env;
mod infer;
mod narrow;
mod state;
mod type_parser;
mod unify;

pub use decorate::decorate_with_types;
pub use env::TypeEnv;
pub use infer::InferResult;
pub use narrow::{apply_narrowing, Narrowing, Path};
pub use state::{InferState, InferWarning, PendingConstraint, TypeClass};
pub use type_parser::parse_type_annotation;
pub use unify::UnifyResult;
