//! tysearch: discover a type system for an operational semantics, by search.
//!
//! See DESIGN.md for the problem, the theory it rests on and the plan; this
//! crate is the first prototype of it, for first-order languages.

pub mod discover;
pub mod enumerate;
pub mod lang;
pub mod rules;
pub mod sorts;

pub mod langs {
    pub mod arith;
    pub mod core;
}
