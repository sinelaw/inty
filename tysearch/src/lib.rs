//! tysearch: discover a type system for an operational semantics, by search.
//!
//! See DESIGN.md for the problem, the theory it rests on and the plan, and
//! ITERATIONS.md for what each round of the search has found.

pub mod discover;
pub mod enumerate;
pub mod infer;
pub mod lang;
pub mod search;
pub mod semantics;
pub mod types;

pub mod langs {
    pub mod arith;
    pub mod core;
    pub mod model;
}
