//! Per-language typeclass instance registry.
//!
//! A class predicate posted at a use site (e.g. `Div(left, right, result)`
//! for `a / b`) is resolved by looking up the active language's instance
//! list for that class and matching the operand's substituted shape
//! against an instance head. The frontend-specific decisions ("Python's
//! `/` honours `Path.__truediv__`; JS's `/` is numeric only") live in
//! this table, not in the operator typing rules.

use std::collections::HashMap;

use crate::ast::SourceLanguage;
use crate::types::{ClassName, Type, TypeId};

/// Registry keyed by (active language, class) → instance list. Looked
/// up by the constraint solver; populated by static built-in seeding
/// plus dynamic registration when a stub module is loaded (so a
/// language-specific class implementation lands as soon as the class's
/// brand id is allocated).
#[derive(Debug, Clone, Default)]
pub struct ClassEnv {
    instances: HashMap<(SourceLanguage, ClassName), Vec<Instance>>,
}

/// One instance: a head selecting which operand shapes it covers and a
/// body describing how the constraint's positions relate.
#[derive(Debug, Clone)]
pub struct Instance {
    pub head: InstanceHead,
    pub body: InstanceBody,
}

/// The operand shape this instance applies to. Matched against the
/// substituted form of the constraint's "dispatch" position (the left
/// operand for `Div`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceHead {
    /// A primitive base type: `Number`, `String`, `Boolean`.
    BaseType(BaseType),
    /// A specific branded nominal class — the brand id is the one
    /// allocated when the class was registered (e.g. `pathlib.Path`'s).
    Nominal(TypeId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseType {
    Number,
    String,
    Boolean,
}

/// How an instance constrains the predicate's positions.
#[derive(Debug, Clone)]
pub enum InstanceBody {
    /// All positions are independently-specified concrete types. Used by
    /// closed instances like numeric `Div = (Number, Number, Number)`.
    Direct {
        left: Type,
        right: Type,
        result: Type,
    },
    /// Method-style: left is already known to match `head`; the right
    /// operand subsumes `param`, the result equals `ret`. Used by
    /// class-instance dispatch like `pathlib.Path`'s `Div = (str, Path)`.
    Method { param: Type, ret: Type },
}

impl InstanceHead {
    /// True when this head matches the given (already-substituted) type.
    pub fn matches(&self, ty: &Type) -> bool {
        match (self, ty) {
            (InstanceHead::BaseType(BaseType::Number), Type::Number) => true,
            (InstanceHead::BaseType(BaseType::String), Type::String) => true,
            (InstanceHead::BaseType(BaseType::Boolean), Type::Boolean) => true,
            (InstanceHead::Nominal(id), Type::Named(other_id, _)) => id == other_id,
            _ => false,
        }
    }
}

impl ClassEnv {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an instance under `(lang, class)`. Later registrations
    /// stack onto the list; lookup returns them in insertion order, so
    /// language-specific seeding goes first and stub-loaded instances
    /// follow.
    pub fn register(&mut self, lang: SourceLanguage, class: ClassName, instance: Instance) {
        self.instances
            .entry((lang, class))
            .or_default()
            .push(instance);
    }

    /// All instances for `(lang, class)`, in registration order. Empty
    /// slice when nothing has been registered.
    pub fn lookup(&self, lang: SourceLanguage, class: ClassName) -> &[Instance] {
        self.instances
            .get(&(lang, class))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}
