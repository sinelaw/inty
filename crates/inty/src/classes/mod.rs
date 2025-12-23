//! Type-class instance tables (phase 7b).
//!
//! Currently this module only houses the static instance tables. The
//! constraint-resolution logic still lives in `crate::builtins`; the
//! tables exist so the blame meta-test can expand `AnyOfClass(Class)`
//! probes from a single declarative source.

pub mod instances;

pub use instances::{instances_of, InstanceDecl, INDEXABLE_INSTANCES, PLUS_INSTANCES};
