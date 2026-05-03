//! Minfern: HMF-based type inference for mquickjs JavaScript subset.
//!
//! This library provides static type inference for mquickjs, a minimal
//! JavaScript subset. It features:
//!
//! - **Row polymorphism** for structural typing of objects
//! - **Equi-recursive types** for self-referential structures
//! - **Type classes** (Plus, Indexable) for overloaded operators
//! - **HMF-based inference** with first-class polymorphism support
//! - **Type annotations in comments** using `/*: Type */` syntax

pub mod builtins;
pub mod classes;
pub mod diagnostics;
pub mod dynamics;
pub mod error;
pub mod infer;
pub mod lexer;
pub mod meta;
pub mod modules;
pub mod operators;
pub mod parser;
pub mod stdlib;
pub mod types;

#[cfg(feature = "wasm")]
pub mod wasm;
