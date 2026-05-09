//! Static type-class instance tables (phase 7b).
//!
//! The constraint solver in `src/builtins/mod.rs` still owns the
//! resolution logic — these tables are the *declarative* source of
//! truth for which instances exist. The blame meta-test
//! (`crate::meta::blame`) consults them to expand `AnyOfClass(Class)`
//! probes; documentation tooling can render them; future PRs that
//! add an instance only need to add a row here plus the matching arm
//! in the resolver.
//!
//! Adding an instance is a one-line change to one of the static
//! arrays below.

use crate::operators::{BaseType, TypeShape};
use crate::types::ClassName;

/// One declared instance of a type class.
///
/// `class` is the class name; `inputs` is the list of type shapes
/// that satisfy the instance, in the order the class declares them.
/// (For unary classes like `Plus`, that's a one-element list.)
#[derive(Copy, Clone, Debug)]
pub struct InstanceDecl {
    pub class: ClassName,
    pub inputs: &'static [TypeShape],
}

/// Instances of `Plus` — types that support `+`.
pub static PLUS_INSTANCES: &[InstanceDecl] = &[
    InstanceDecl {
        class: ClassName::Plus,
        inputs: &[TypeShape::Concrete(BaseType::Number)],
    },
    InstanceDecl {
        class: ClassName::Plus,
        inputs: &[TypeShape::Concrete(BaseType::String)],
    },
];

/// Instances of `Indexable` — types `T` such that `T[I] = E` for some
/// pair of `I, E`. Recorded as `(container, index, element)` shape
/// triples.
pub static INDEXABLE_INSTANCES: &[InstanceDecl] = &[
    // Array<E>[Number] = E — recorded as a wildcard container/element
    // because the catalog can't say "Array<wildcard>" without a
    // dedicated TypeShape constructor.
    InstanceDecl {
        class: ClassName::Indexable,
        inputs: &[
            TypeShape::Wildcard,
            TypeShape::Concrete(BaseType::Number),
            TypeShape::Wildcard,
        ],
    },
    // Map<E>[String] = E
    InstanceDecl {
        class: ClassName::Indexable,
        inputs: &[
            TypeShape::Wildcard,
            TypeShape::Concrete(BaseType::String),
            TypeShape::Wildcard,
        ],
    },
    // String[Number] = String
    InstanceDecl {
        class: ClassName::Indexable,
        inputs: &[
            TypeShape::Concrete(BaseType::String),
            TypeShape::Concrete(BaseType::Number),
            TypeShape::Concrete(BaseType::String),
        ],
    },
];

/// Look up every instance for `class`. Returns an empty slice if the
/// class is unknown — callers (notably the blame prober) treat that as
/// "no probes available".
pub fn instances_of(class: ClassName) -> &'static [InstanceDecl] {
    match class {
        ClassName::Plus => PLUS_INSTANCES,
        ClassName::Indexable => INDEXABLE_INSTANCES,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plus_has_two_instances() {
        assert_eq!(PLUS_INSTANCES.len(), 2);
        for inst in PLUS_INSTANCES {
            assert_eq!(inst.class, ClassName::Plus);
            assert_eq!(inst.inputs.len(), 1);
        }
    }

    #[test]
    fn indexable_has_three_instances() {
        assert_eq!(INDEXABLE_INSTANCES.len(), 3);
        for inst in INDEXABLE_INSTANCES {
            assert_eq!(inst.class, ClassName::Indexable);
            assert_eq!(inst.inputs.len(), 3);
        }
    }

    #[test]
    fn instances_of_returns_matching_lists() {
        assert_eq!(instances_of(ClassName::Plus).len(), 2);
        assert_eq!(instances_of(ClassName::Indexable).len(), 3);
    }
}
