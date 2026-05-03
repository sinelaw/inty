//! Type environment for name bindings.
//!
//! The type environment maps variable names to their type schemes,
//! supporting scoping through immutable extension.
//!
//! # Value-restriction note (phase 7e)
//!
//! The `Mutability` flag plus `crate::infer::features::bindings::is_syntactic_value`
//! is the canonical answer for the value restriction. Don't replace
//! it with a body-walker that traces aliasing — that approach
//!
//! 1. **misses aliasing.** A polymorphic binding aliased into a `var`
//!    is still polymorphic by the syntactic rule but a body-walker
//!    needs whole-program flow to detect that the alias is later
//!    mutated.
//! 2. **is O(n²).** Every assignment site re-walks every reachable
//!    binding's RHS expression to decide whether to demote.
//! 3. **looks more "principled" than it is.** The syntactic value
//!    rule is sound and small; resist the temptation.
//!
//! Adding policy here belongs in `crate::infer::InferConfig` (phase 6).

use std::collections::{HashMap, HashSet};

use crate::types::{Subst, Substitutable, TVarName, TypeScheme};

/// Whether a binding is mutable or immutable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mutability {
    /// Can be reassigned (regular `var` declarations)
    Mutable,
    /// Cannot be reassigned (`const` or declared without initializer)
    Immutable,
}

/// A binding in the type environment.
#[derive(Clone, Debug)]
pub struct Binding {
    /// The type scheme for this binding.
    pub scheme: TypeScheme,
    /// Whether this binding can be reassigned.
    pub mutability: Mutability,
}

impl Binding {
    /// Create a mutable binding.
    pub fn mutable(scheme: TypeScheme) -> Self {
        Binding {
            scheme,
            mutability: Mutability::Mutable,
        }
    }

    /// Create an immutable binding.
    pub fn immutable(scheme: TypeScheme) -> Self {
        Binding {
            scheme,
            mutability: Mutability::Immutable,
        }
    }
}

/// Type environment mapping names to type schemes.
#[derive(Clone, Debug, Default)]
pub struct TypeEnv {
    bindings: HashMap<String, Binding>,
}

impl TypeEnv {
    /// Create an empty environment.
    pub fn empty() -> Self {
        TypeEnv {
            bindings: HashMap::new(),
        }
    }

    /// Look up a name in the environment and return just the type scheme.
    /// For backwards compatibility with existing code.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.bindings.get(name).map(|b| &b.scheme)
    }

    /// Look up a name in the environment and return the full binding.
    pub fn lookup_binding(&self, name: &str) -> Option<&Binding> {
        self.bindings.get(name)
    }

    /// Extend the environment with a new mutable binding.
    /// Returns a new environment (immutable extension).
    pub fn extend(&self, name: String, scheme: TypeScheme) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, Binding::mutable(scheme));
        TypeEnv { bindings }
    }

    /// Extend the environment with a new immutable binding.
    /// Returns a new environment (immutable extension).
    pub fn extend_immutable(&self, name: String, scheme: TypeScheme) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, Binding::immutable(scheme));
        TypeEnv { bindings }
    }

    /// Extend the environment with a binding specifying mutability.
    pub fn extend_with_mutability(
        &self,
        name: String,
        scheme: TypeScheme,
        mutability: Mutability,
    ) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, Binding { scheme, mutability });
        TypeEnv { bindings }
    }

    /// Extend the environment with multiple mutable bindings.
    pub fn extend_many(&self, bindings: impl IntoIterator<Item = (String, TypeScheme)>) -> Self {
        let mut new_bindings = self.bindings.clone();
        for (name, scheme) in bindings {
            new_bindings.insert(name, Binding::mutable(scheme));
        }
        TypeEnv {
            bindings: new_bindings,
        }
    }

    /// Remove a binding from the environment.
    pub fn remove(&self, name: &str) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.remove(name);
        TypeEnv { bindings }
    }

    /// Check if a name is bound in the environment.
    pub fn contains(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    /// Get all free type variables in the environment.
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for binding in self.bindings.values() {
            vars.extend(binding.scheme.free_vars());
        }
        vars
    }

    /// Get all bound names.
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.bindings.keys()
    }

    /// Get the number of bindings.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Iterate over all bindings (returns type schemes for compatibility).
    pub fn iter(&self) -> impl Iterator<Item = (&String, &TypeScheme)> {
        self.bindings.iter().map(|(k, b)| (k, &b.scheme))
    }

    /// Iterate over all bindings with full binding info.
    pub fn iter_bindings(&self) -> impl Iterator<Item = (&String, &Binding)> {
        self.bindings.iter()
    }
}

impl Substitutable for TypeEnv {
    fn apply_subst(&self, subst: &Subst) -> Self {
        let bindings = self
            .bindings
            .iter()
            .map(|(k, b)| {
                (
                    k.clone(),
                    Binding {
                        scheme: b.scheme.apply_subst(subst),
                        mutability: b.mutability,
                    },
                )
            })
            .collect();
        TypeEnv { bindings }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        TypeEnv::free_vars(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;

    #[test]
    fn test_empty_env() {
        let env = TypeEnv::empty();
        assert!(env.is_empty());
        assert!(env.lookup("x").is_none());
    }

    #[test]
    fn test_extend() {
        let env = TypeEnv::empty();
        let scheme = TypeScheme::mono(Type::Number);
        let env2 = env.extend("x".to_string(), scheme.clone());

        assert!(env.lookup("x").is_none()); // Original unchanged
        assert!(env2.lookup("x").is_some()); // Extended has binding
    }

    #[test]
    fn test_shadowing() {
        let env = TypeEnv::empty().extend("x".to_string(), TypeScheme::mono(Type::Number));
        let env2 = env.extend("x".to_string(), TypeScheme::mono(Type::String));

        let scheme = env2.lookup("x").unwrap();
        assert_eq!(*scheme.ty(), Type::String);
    }

    #[test]
    fn test_free_vars() {
        let env = TypeEnv::empty()
            .extend("x".to_string(), TypeScheme::mono(Type::flex(0)))
            .extend("y".to_string(), TypeScheme::mono(Type::flex(1)));

        let vars = env.free_vars();
        assert!(vars.contains(&TVarName::Flex(0)));
        assert!(vars.contains(&TVarName::Flex(1)));
    }

    #[test]
    fn test_quantified_not_in_free_vars() {
        let env = TypeEnv::empty().extend(
            "id".to_string(),
            TypeScheme::poly(vec![TVarName::Flex(0)], Type::flex(0)),
        );

        let vars = env.free_vars();
        assert!(!vars.contains(&TVarName::Flex(0)));
    }

    #[test]
    fn test_mutability() {
        let env = TypeEnv::empty()
            .extend("x".to_string(), TypeScheme::mono(Type::Number))
            .extend_immutable("y".to_string(), TypeScheme::mono(Type::String));

        let x_binding = env.lookup_binding("x").unwrap();
        assert_eq!(x_binding.mutability, Mutability::Mutable);

        let y_binding = env.lookup_binding("y").unwrap();
        assert_eq!(y_binding.mutability, Mutability::Immutable);
    }
}
