//! Per-feature inference logic.
//!
//! Each submodule extends `InferState` with the inference rules for one
//! feature family (scalars, arrays, rows, functions, operators, control
//! flow, bindings). The `infer_expr` / `infer_stmt` dispatchers in
//! `super::mod` match on AST shape and delegate to these methods.

pub(super) mod arrays;
pub(super) mod bindings;
pub(super) mod control;
pub(super) mod functions;
pub(super) mod nullish;
pub(super) mod operators;
pub(super) mod rows;
pub(super) mod scalars;
