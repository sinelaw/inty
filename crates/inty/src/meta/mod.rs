//! Meta-tests cross-checking the type system against itself.
//!
//! - `blame`: cross-checks the operator catalog (`crate::operators`)
//!   against the operational semantics (`crate::dynamics`). For every
//!   operator/input-shape combination the typing arm accepts, asserts
//!   the dynamics actually delivers a value.
//! - `soundness`: generates well-typed programs by construction,
//!   reduces them through the dynamics, and asserts they never get
//!   stuck. The randomised counterpart to the catalog-driven blame
//!   meta-test.

pub mod blame;
pub mod config;
pub mod soundness;
pub mod surface;

pub use blame::{all_blame_triples, blame_triples_for_op, BlameTriple, ConfigSnapshot};
pub use soundness::{check_program, SynthType};
pub use surface::{is_surface_expr, is_surface_stmt};
