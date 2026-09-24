//! Proof-of-concept Go backend for inty.
//!
//! Translates a type-checked JavaScript program into a single, standalone
//! Go `main` package. The point is to show what full static types buy at
//! runtime: once inty has proved every expression has one concrete type,
//! a JavaScript `number` can become a Go `float64` register value, an
//! object literal a Go struct, and a property access a fixed-offset load
//! — no hidden classes, inline caches, deoptimisation guards or JIT
//! warm-up.
//!
//! # Pipeline
//!
//! 1. Parse with the regular JavaScript frontend.
//! 2. Type-check with inty as usual, with full let-polymorphism,
//!    recording the synthesised type of every expression
//!    ([`inty::infer::InferState::expr_types`]) and how every use of a
//!    polymorphic binding was instantiated
//!    ([`inty::infer::InferState::instantiations`]).
//! 3. Walk the AST and emit Go from those types (see `emit.rs`),
//!    *monomorphising* as it goes. Each function is emitted once per
//!    distinct concrete instantiation reachable from `main`, so
//!    `function first(xs)` used on a `number[]` and on a `string[]`
//!    becomes two Go functions. Functions nothing reaches are not
//!    emitted.
//!
//! # Semantics
//!
//! `number` is IEEE-754 double in both languages, so arithmetic is
//! bit-for-bit identical; the runtime prelude (`runtime.go`) supplies
//! the JS-specific pieces (Number→string formatting, `%` on doubles,
//! ToInt32 for bitwise operators). Constant sub-expressions are folded in
//! Rust with f64 arithmetic because Go evaluates constant expressions
//! with arbitrary precision (`0.1 + 0.2 == 0.3` in Go constants).
//!
//! Anything outside the supported subset is reported as an
//! "unsupported construct" diagnostic pointing at the source span, never
//! silently mistranslated. Known deliberate gaps are listed in
//! `examples/go-backend/README.md`.

mod emit;
mod types;

use std::collections::HashMap;

use inty::error::{IntyError, ParseError};
use inty::span::Span;

/// Result of a successful translation.
pub struct GoOutput {
    /// A complete `package main` Go source file.
    pub code: String,
}

/// Parse, type-check and translate `source` to Go.
///
/// On failure, returns every diagnostic collected: type errors from
/// inference, or a single "unsupported construct" error from the Go
/// emitter. Spans index into `source`.
pub fn compile(source: &str) -> std::result::Result<GoOutput, Vec<IntyError>> {
    let program = inty::frontends::javascript::parse_source(source).map_err(|e| vec![e])?;

    let (env, mut state) = inty::stdlib::initial_env_with_stdlib().map_err(|e| vec![e])?;
    // Record only for the user program, not for the stdlib loaded above.
    state.config.exhaustiveness_warnings = false;
    state.expr_types = Some(HashMap::new());
    state.instantiations = Some(HashMap::new());

    // Deeply nested programs need the same stack headroom the CLI gives
    // the checker (see `inty::worker`); the emitter recurses as deeply.
    let code = inty::worker::run_with_inference_stack("inty-go", move || {
        let result = state.infer_program_with_env(&env, &program);
        let mut errors: Vec<IntyError> = state.take_errors();
        if let Err(e) = result {
            if errors.is_empty() {
                errors.push(e);
            }
        } else if errors.is_empty() {
            if let Err(e) = state.resolve_constraints() {
                errors.push(e);
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        emit::emit_program(&program, &mut state).map_err(|e| vec![e])
    })?;
    Ok(GoOutput { code })
}

/// Build the "this construct isn't supported by the Go backend" error.
/// Reuses the parser's `Unsupported` variant so the CLI renders it with
/// the usual source-snippet diagnostics.
pub(crate) fn unsupported(what: impl Into<String>, span: Span) -> IntyError {
    IntyError::Parse(ParseError::Unsupported {
        feature: format!("{} (not supported by the Go backend yet)", what.into()),
        span,
    })
}

pub(crate) type Result<T> = std::result::Result<T, IntyError>;
