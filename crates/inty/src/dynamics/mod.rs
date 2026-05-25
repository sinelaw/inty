//! Small-step operational semantics for the typed subset of mquickjs.
//!
//! This is *not* a JS engine. It's a reference reduction relation that
//! exists so the typing rules in `crate::infer` have something
//! falsifiable to be consistent with. Phase 4's blame meta-test cross-
//! checks the two; phase 5 runs typed programs through it and asserts
//! they never get "stuck" (a stuck typed term is a soundness violation).
//!
//! Public API:
//! - [`State`] / [`run_to_end`] — drive a program to completion under a
//!   fuel bound.
//! - [`is_stuck`] — given a state and an expression, return a reason
//!   the expression can't take a step (or `None` if it's a value or
//!   reduces).
//! - [`Stuck`] / [`StmtOutcome`] / [`Value`] — building blocks.
//!
//! Limitations (deliberate; documented inline):
//! - `await` is identity on `Promise<T>` and identity on non-promises.
//!   Phase 3 does not model the event loop.
//! - Regex literals raise `Stuck::NotImplemented`.
//! - `instanceof` and `in` raise `Stuck::NotImplemented` (no prototype
//!   chain in this model).
//! - Getters/setters raise `Stuck::NotImplemented`.

pub mod env;
pub mod heap;
pub mod step;
pub mod value;

#[cfg(test)]
mod tests;

pub use env::RuntimeEnv;
pub use heap::{Cell, Heap, Loc};
pub use step::{eval_expr, eval_stmt, run_program, State, StmtOutcome, Stuck};
pub use value::{Closure, Value};

use crate::ast::{Expr, Program};

/// Default fuel for `run_to_end`. Loops decrement fuel each iteration;
/// recursive calls each consume one. Tests fail with
/// `Stuck::FuelExhausted` rather than hanging.
pub const DEFAULT_FUEL: usize = 10_000;

/// Run a program to completion under the default fuel bound.
pub fn run_to_end(program: &Program) -> Result<Value, Stuck> {
    run_to_end_with_fuel(program, DEFAULT_FUEL)
}

pub fn run_to_end_with_fuel(program: &Program, fuel: usize) -> Result<Value, Stuck> {
    let mut state = State::new(fuel);
    let env = RuntimeEnv::new();
    run_program(&mut state, &env, program)
}

/// "Is this expression stuck under this state?" — returns
/// `Some(reason)` when no operational rule applies. A pure value
/// returns `None` (it's already reduced); an expression that successfully
/// takes a step also returns `None` (it could reduce — not stuck).
///
/// Used by phase 5's soundness probe: if a typed program reduces to a
/// term `e` for which `is_stuck` returns `Some`, the typing rule that
/// allowed forming `e` is unsound.
pub fn is_stuck(state: &mut State, env: &RuntimeEnv, expr: &Expr) -> Option<Stuck> {
    match eval_expr(state, env, expr) {
        Ok(_) => None,
        Err(Stuck::FuelExhausted) => None, // not stuck — just out of fuel
        Err(reason) => Some(reason),
    }
}
