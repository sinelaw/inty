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
    /// The binding's own scheme when `scheme` is a narrowing of it (see
    /// `narrow.rs`): what an assignment must fit, and what the binding
    /// goes back to once the narrowing stops holding.
    pub declared: Option<TypeScheme>,
}

impl Binding {
    /// Create a mutable binding.
    pub fn mutable(scheme: TypeScheme) -> Self {
        Binding {
            scheme,
            mutability: Mutability::Mutable,
            declared: None,
        }
    }

    /// Create an immutable binding.
    pub fn immutable(scheme: TypeScheme) -> Self {
        Binding {
            scheme,
            mutability: Mutability::Immutable,
            declared: None,
        }
    }
}

/// Type environment mapping names to type schemes.
#[derive(Clone, Debug, Default)]
pub struct TypeEnv {
    bindings: HashMap<String, Binding>,
    /// How many bindings are narrowed, so code with nothing narrowed can
    /// skip looking for assignments that would end a narrowing.
    narrowed: usize,
}

impl TypeEnv {
    /// Create an empty environment.
    pub fn empty() -> Self {
        TypeEnv {
            bindings: HashMap::new(),
            narrowed: 0,
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
        self.with_binding(name, Binding::mutable(scheme))
    }

    /// A copy with `name` bound to `binding`, replacing any binding it had.
    fn with_binding(&self, name: String, binding: Binding) -> Self {
        let mut out = self.clone();
        out.insert(name, binding);
        out
    }

    fn insert(&mut self, name: String, binding: Binding) {
        if binding.declared.is_some() {
            self.narrowed += 1;
        }
        if let Some(old) = self.bindings.insert(name, binding) {
            if old.declared.is_some() {
                self.narrowed -= 1;
            }
        }
    }

    /// Whether any binding is narrowed.
    pub fn has_narrowings(&self) -> bool {
        self.narrowed > 0
    }

    /// Whether `name`'s binding is narrowed.
    pub fn is_narrowed(&self, name: &str) -> bool {
        self.bindings
            .get(name)
            .is_some_and(|b| b.declared.is_some())
    }

    /// A copy with `name`'s type narrowed to `scheme`. The binding keeps
    /// its mutability and remembers its own scheme.
    pub fn narrow(&self, name: &str, scheme: TypeScheme) -> Self {
        let Some(b) = self.bindings.get(name) else {
            return self.clone();
        };
        let declared = b.declared.clone().unwrap_or_else(|| b.scheme.clone());
        self.with_binding(
            name.to_string(),
            Binding {
                scheme,
                mutability: b.mutability,
                declared: Some(declared),
            },
        )
    }

    /// A copy where the bindings of `names` that are narrowed have their
    /// own types back.
    pub fn unnarrow<'a>(&self, names: impl IntoIterator<Item = &'a String>) -> Self {
        if !self.has_narrowings() {
            return self.clone();
        }
        let mut out = self.clone();
        for name in names {
            if let Some(b) = out.bindings.get(name) {
                if let Some(declared) = b.declared.clone() {
                    let mutability = b.mutability;
                    out.insert(
                        name.clone(),
                        Binding {
                            scheme: declared,
                            mutability,
                            declared: None,
                        },
                    );
                }
            }
        }
        out
    }

    /// [`Self::unnarrow`] for the narrowed bindings `pred` picks.
    pub fn unnarrow_where(&self, mut pred: impl FnMut(&str, &Binding) -> bool) -> Self {
        if !self.has_narrowings() {
            return self.clone();
        }
        let names: Vec<String> = self
            .bindings
            .iter()
            .filter(|(k, b)| b.declared.is_some() && pred(k, b))
            .map(|(k, _)| k.clone())
            .collect();
        self.unnarrow(&names)
    }

    /// A copy with every narrowing dropped.
    pub fn without_narrowings(&self) -> Self {
        self.unnarrow_where(|_, _| true)
    }

    /// Extend the environment with a new immutable binding.
    /// Returns a new environment (immutable extension).
    pub fn extend_immutable(&self, name: String, scheme: TypeScheme) -> Self {
        self.with_binding(name, Binding::immutable(scheme))
    }

    /// Extend the environment with a binding specifying mutability.
    pub fn extend_with_mutability(
        &self,
        name: String,
        scheme: TypeScheme,
        mutability: Mutability,
    ) -> Self {
        self.with_binding(
            name,
            Binding {
                scheme,
                mutability,
                declared: None,
            },
        )
    }

    /// The environment with `f` applied to every binding's scheme.
    pub fn map_schemes(&self, mut f: impl FnMut(&TypeScheme) -> TypeScheme) -> Self {
        let bindings = self
            .bindings
            .iter()
            .map(|(k, b)| {
                (
                    k.clone(),
                    Binding {
                        scheme: f(&b.scheme),
                        mutability: b.mutability,
                        declared: b.declared.as_ref().map(&mut f),
                    },
                )
            })
            .collect();
        TypeEnv {
            bindings,
            narrowed: self.narrowed,
        }
    }

    /// Extend the environment with multiple mutable bindings.
    pub fn extend_many(&self, bindings: impl IntoIterator<Item = (String, TypeScheme)>) -> Self {
        let mut out = self.clone();
        for (name, scheme) in bindings {
            out.insert(name, Binding::mutable(scheme));
        }
        out
    }

    /// Remove a binding from the environment.
    pub fn remove(&self, name: &str) -> Self {
        let mut out = self.clone();
        if let Some(old) = out.bindings.remove(name) {
            if old.declared.is_some() {
                out.narrowed -= 1;
            }
        }
        out
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
            if let Some(declared) = &binding.declared {
                vars.extend(declared.free_vars());
            }
        }
        vars
    }

    /// Everything generalisation must know about the environment: its
    /// free type and presence variables and the named types it mentions
    /// (whose bodies can hide further variables). See
    /// `InferState::generalize`.
    pub fn free(&self) -> EnvFree {
        let mut free = EnvFree::default();
        for binding in self.bindings.values() {
            for scheme in std::iter::once(&binding.scheme).chain(binding.declared.as_ref()) {
                free.vars.extend(scheme.free_vars());
                free.pvars.extend(scheme.free_pvars());
                free.named.extend(scheme.body.ty.named_ids());
            }
        }
        free
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
                        declared: b.declared.as_ref().map(|d| d.apply_subst(subst)),
                    },
                )
            })
            .collect();
        TypeEnv {
            bindings,
            narrowed: self.narrowed,
        }
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

/// Free variables of an environment, as needed by generalisation (see
/// [`TypeEnv::free`]).
#[derive(Debug, Clone, Default)]
pub struct EnvFree {
    pub vars: HashSet<TVarName>,
    pub pvars: HashSet<crate::types::PVarName>,
    pub named: HashSet<crate::types::TypeId>,
}
