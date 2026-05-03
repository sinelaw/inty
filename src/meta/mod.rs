//! Meta-tests cross-checking the type system against itself.
//!
//! - `blame`: cross-checks the operator catalog (`crate::operators`)
//!   against the operational semantics (`crate::dynamics`). For every
//!   operator/input-shape combination the typing arm accepts, asserts
//!   the dynamics actually delivers a value.

pub mod blame;

pub use blame::{all_blame_triples, blame_triples_for_op, BlameTriple, ConfigSnapshot};
