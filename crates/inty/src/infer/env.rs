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

use crate::ast::resolve::BindingId;
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
    /// `narrow.rs`). Only bindings that are never written are narrowed,
    /// so nothing is ever stored against a narrowed scheme; this is kept
    /// for what outlives the narrowing's scope, like a module's exports.
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

/// What a binding is keyed by: the declaration binding resolution found
/// (`ast::resolve`), or, for a global (the standard library, an import,
/// `this`), its name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Local(BindingId),
    Name(String),
}

/// Type environment: the bindings in scope and their type schemes.
///
/// Bindings are keyed by [`Key`]: inference reads and declares a
/// program's identifiers by the declaration they resolve to, so two
/// variables of the same name are never confused. The environment also
/// keeps, for each name, the key it was last bound under, for callers
/// outside inference (a module's exports, the CLI, tests) and for type
/// annotations, which refer to names.
#[derive(Clone, Debug, Default)]
pub struct TypeEnv {
    bindings: HashMap<Key, Binding>,
    names: HashMap<String, Key>,
}

impl TypeEnv {
    /// Create an empty environment.
    pub fn empty() -> Self {
        TypeEnv::default()
    }

    /// The scheme `name` is bound to, by the name view.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.lookup_binding(name).map(|b| &b.scheme)
    }

    /// The binding `name` refers to, by the name view.
    pub fn lookup_binding(&self, name: &str) -> Option<&Binding> {
        self.bindings.get(self.names.get(name)?)
    }

    /// The binding under `key`.
    pub fn lookup_key(&self, key: &Key) -> Option<&Binding> {
        self.bindings.get(key)
    }

    /// The key `name` was last bound under.
    pub fn key_of_name(&self, name: &str) -> Option<&Key> {
        self.names.get(name)
    }

    /// Bind `key` (named `name`) to `binding`.
    pub fn extend_key(&self, key: Key, name: &str, binding: Binding) -> Self {
        let mut out = self.clone();
        out.names.insert(name.to_string(), key.clone());
        out.bindings.insert(key, binding);
        out
    }

    /// Extend the environment with a new mutable global binding.
    /// Returns a new environment (immutable extension).
    pub fn extend(&self, name: String, scheme: TypeScheme) -> Self {
        self.extend_key(Key::Name(name.clone()), &name, Binding::mutable(scheme))
    }

    /// Extend the environment with a new immutable global binding.
    pub fn extend_immutable(&self, name: String, scheme: TypeScheme) -> Self {
        self.extend_key(Key::Name(name.clone()), &name, Binding::immutable(scheme))
    }

    /// Extend the environment with a global binding specifying mutability.
    pub fn extend_with_mutability(
        &self,
        name: String,
        scheme: TypeScheme,
        mutability: Mutability,
    ) -> Self {
        self.extend_key(
            Key::Name(name.clone()),
            &name,
            Binding {
                scheme,
                mutability,
                declared: None,
            },
        )
    }

    /// A copy with `key`'s type narrowed to `scheme`. The binding keeps
    /// its mutability and remembers its own scheme.
    pub fn narrow(&self, key: &Key, scheme: TypeScheme) -> Self {
        let Some(b) = self.bindings.get(key) else {
            return self.clone();
        };
        let declared = b.declared.clone().unwrap_or_else(|| b.scheme.clone());
        let mut out = self.clone();
        out.bindings.insert(
            key.clone(),
            Binding {
                scheme,
                mutability: b.mutability,
                declared: Some(declared),
            },
        );
        out
    }

    /// `name`'s own scheme, narrowed or not.
    pub fn lookup_declared(&self, name: &str) -> Option<&TypeScheme> {
        let b = self.lookup_binding(name)?;
        Some(b.declared.as_ref().unwrap_or(&b.scheme))
    }

    /// A copy whose narrowings are those of `base`: each narrowed binding
    /// takes `base`'s binding under the same key, or its own scheme when
    /// `base` has none. Other bindings (declared since `base`) are kept.
    pub fn with_narrowings_of(&self, base: &TypeEnv) -> Self {
        let mut out = self.clone();
        for (key, b) in &self.bindings {
            let Some(declared) = &b.declared else {
                continue;
            };
            let restored = match base.bindings.get(key) {
                Some(bb) => bb.clone(),
                None => Binding {
                    scheme: declared.clone(),
                    mutability: b.mutability,
                    declared: None,
                },
            };
            out.bindings.insert(key.clone(), restored);
        }
        out
    }

    /// A copy whose name view is `outer`'s: bindings this scope
    /// declared stay reachable by key only, as they are when it ends.
    pub fn with_names_of(&self, outer: &TypeEnv) -> Self {
        let mut out = self.clone();
        out.names = outer.names.clone();
        out
    }

    /// A copy with every binding's own scheme.
    pub fn without_narrowings(&self) -> Self {
        let mut out = self.clone();
        for b in out.bindings.values_mut() {
            if let Some(declared) = b.declared.take() {
                b.scheme = declared;
            }
        }
        out
    }

    /// What a program leaves for the next one (its importers, or the user
    /// program after the standard library): each name's binding as a
    /// global keyed by name. Other programs' declaration ids mean nothing
    /// here, so no `Local` key survives.
    pub fn globalized(&self) -> Self {
        let mut out = TypeEnv::default();
        for (key, b) in &self.bindings {
            if let Key::Name(n) = key {
                out.bindings.insert(key.clone(), b.clone());
                out.names.insert(n.clone(), key.clone());
            }
        }
        for (name, key) in &self.names {
            if let (Key::Local(_), Some(b)) = (key, self.bindings.get(key)) {
                let global = Key::Name(name.clone());
                out.bindings.insert(global.clone(), b.clone());
                out.names.insert(name.clone(), global);
            }
        }
        out
    }

    /// The environment with `f` applied to every binding's scheme.
    pub fn map_schemes(&self, mut f: impl FnMut(&TypeScheme) -> TypeScheme) -> Self {
        let mut out = self.clone();
        for b in out.bindings.values_mut() {
            b.scheme = f(&b.scheme);
            b.declared = b.declared.as_ref().map(&mut f);
        }
        out
    }

    /// Extend the environment with multiple mutable global bindings.
    pub fn extend_many(&self, bindings: impl IntoIterator<Item = (String, TypeScheme)>) -> Self {
        let mut out = self.clone();
        for (name, scheme) in bindings {
            out = out.extend(name, scheme);
        }
        out
    }

    /// Remove the binding `name` refers to.
    pub fn remove(&self, name: &str) -> Self {
        let mut out = self.clone();
        if let Some(key) = out.names.remove(name) {
            out.bindings.remove(&key);
        }
        out
    }

    /// Remove the binding under `key`.
    pub fn remove_key(&self, key: &Key) -> Self {
        let mut out = self.clone();
        out.bindings.remove(key);
        out.names.retain(|_, k| k != key);
        out
    }

    /// Check if a name is bound in the environment.
    pub fn contains(&self, name: &str) -> bool {
        self.lookup_binding(name).is_some()
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
        self.names.keys()
    }

    /// Get the number of bindings.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Iterate over the name view (name, scheme).
    pub fn iter(&self) -> impl Iterator<Item = (&String, &TypeScheme)> {
        self.iter_bindings().map(|(n, b)| (n, &b.scheme))
    }

    /// Iterate over the name view with full binding info.
    pub fn iter_bindings(&self) -> impl Iterator<Item = (&String, &Binding)> {
        self.names
            .iter()
            .filter_map(|(n, k)| self.bindings.get(k).map(|b| (n, b)))
    }
}

impl Substitutable for TypeEnv {
    fn apply_subst(&self, subst: &Subst) -> Self {
        let mut out = self.clone();
        for b in out.bindings.values_mut() {
            b.scheme = b.scheme.apply_subst(subst);
            b.declared = b.declared.as_ref().map(|d| d.apply_subst(subst));
        }
        out
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
