//! Substitution for type inference.
//!
//! Implements the substitution data structure and the Substitutable trait
//! for applying substitutions to types, type schemes, and other structures.

use std::collections::{HashMap, HashSet};

use super::ty::{PropName, QualType, RowTail, RowType, TVarName, Type, TypePred, TypeScheme};

/// A substitution mapping type variables to types.
#[derive(Clone, Debug, Default)]
pub struct Subst {
    map: HashMap<TVarName, Type>,
}

impl Subst {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Subst {
            map: HashMap::new(),
        }
    }

    /// Create a singleton substitution.
    pub fn singleton(var: TVarName, ty: Type) -> Self {
        let mut map = HashMap::new();
        map.insert(var, ty);
        Subst { map }
    }

    /// Check if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Get the type for a variable, if present.
    pub fn get(&self, var: &TVarName) -> Option<&Type> {
        self.map.get(var)
    }

    /// Check if a variable is in the domain.
    pub fn contains(&self, var: &TVarName) -> bool {
        self.map.contains_key(var)
    }

    /// Insert a mapping into the substitution.
    pub fn insert(&mut self, var: TVarName, ty: Type) {
        self.map.insert(var, ty);
    }

    /// Remove a variable from the substitution.
    pub fn remove(&mut self, var: &TVarName) {
        self.map.remove(var);
    }

    /// Get the domain (set of variables) of this substitution.
    pub fn domain(&self) -> HashSet<TVarName> {
        self.map.keys().cloned().collect()
    }

    /// Compose two substitutions: (self ∘ other)(x) = self(other(x))
    ///
    /// The result maps each variable to its fully substituted form.
    /// Variables in `other` are mapped through `self`, and variables
    /// only in `self` are kept.
    pub fn compose(&self, other: &Subst) -> Subst {
        let mut result = HashMap::new();

        // Apply self to all mappings in other
        for (var, ty) in &other.map {
            result.insert(var.clone(), self.apply(ty));
        }

        // Add mappings from self that aren't in other
        for (var, ty) in &self.map {
            if !result.contains_key(var) {
                result.insert(var.clone(), ty.clone());
            }
        }

        Subst { map: result }
    }

    /// Apply this substitution to a substitutable value.
    pub fn apply<T: Substitutable>(&self, t: &T) -> T {
        t.apply_subst(self)
    }

    /// Create a new substitution with certain variables removed.
    pub fn remove_vars(&self, vars: &[TVarName]) -> Subst {
        let mut map = self.map.clone();
        for var in vars {
            map.remove(var);
        }
        Subst { map }
    }

    /// Iterate over the mappings.
    pub fn iter(&self) -> impl Iterator<Item = (&TVarName, &Type)> {
        self.map.iter()
    }
}

impl IntoIterator for Subst {
    type Item = (TVarName, Type);
    type IntoIter = std::collections::hash_map::IntoIter<TVarName, Type>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl FromIterator<(TVarName, Type)> for Subst {
    fn from_iter<T: IntoIterator<Item = (TVarName, Type)>>(iter: T) -> Self {
        Subst {
            map: iter.into_iter().collect(),
        }
    }
}

/// Trait for types that can have substitutions applied.
pub trait Substitutable {
    /// Apply a substitution to this value.
    fn apply_subst(&self, subst: &Subst) -> Self;

    /// Collect all free type variables.
    fn free_vars(&self) -> HashSet<TVarName>;
}

impl Substitutable for Type {
    fn apply_subst(&self, subst: &Subst) -> Self {
        match self {
            // Primitives are unchanged
            Type::Number => Type::Number,
            Type::String => Type::String,
            Type::Boolean => Type::Boolean,
            Type::Undefined => Type::Undefined,
            Type::Null => Type::Null,
            Type::Regex => Type::Regex,

            // Variable substitution
            Type::Var(name) => {
                if let Some(ty) = subst.get(name) {
                    // Recursively apply to handle transitive substitutions
                    ty.apply_subst(subst)
                } else {
                    self.clone()
                }
            }

            // Function types
            Type::Func {
                this_type,
                params,
                ret,
            } => Type::Func {
                this_type: this_type.as_ref().map(|t| Box::new(t.apply_subst(subst))),
                params: params.iter().map(|p| p.apply_subst(subst)).collect(),
                ret: Box::new(ret.apply_subst(subst)),
            },

            // Row types
            Type::Row(row) => Type::Row(row.apply_subst(subst)),

            // Array types
            Type::Array(elem) => Type::Array(Box::new(elem.apply_subst(subst))),

            // Promise types
            Type::Promise(inner) => Type::Promise(Box::new(inner.apply_subst(subst))),

            // Map types
            Type::Map(value) => Type::Map(Box::new(value.apply_subst(subst))),

            // Named recursive types
            Type::Named(id, args) => {
                Type::Named(*id, args.iter().map(|a| a.apply_subst(subst)).collect())
            }

            // Literal types are unchanged by substitution
            Type::Literal(lit) => Type::Literal(lit.clone()),

            // Substitution can produce duplicates / nested unions, so
            // re-normalise via Type::union.
            Type::Union(members) => {
                Type::union(members.iter().map(|m| m.apply_subst(subst)))
            }

            // Modules: each export is a scheme; reuse TypeScheme's
            // substitution which already shadows quantified vars.
            Type::Module(m) => Type::Module(crate::types::ModuleType {
                source: m.source.clone(),
                exports: m
                    .exports
                    .iter()
                    .map(|(k, scheme)| (k.clone(), scheme.apply_subst(subst)))
                    .collect(),
            }),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        Type::free_vars(self)
    }
}

impl Substitutable for RowType {
    fn apply_subst(&self, subst: &Subst) -> Self {
        let props: std::collections::BTreeMap<PropName, Type> = self
            .props
            .iter()
            .map(|(k, v)| (k.clone(), v.apply_subst(subst)))
            .collect();

        let tail = match &self.tail {
            RowTail::Closed => RowTail::Closed,
            RowTail::Open(var) => {
                // If the row variable is substituted with a row type,
                // we need to merge the rows
                if let Some(ty) = subst.get(var) {
                    match ty {
                        Type::Row(_other_row) => {
                            // This case is handled during unification
                            // For now, just keep the open tail
                            RowTail::Open(var.clone())
                        }
                        Type::Var(new_var) => RowTail::Open(new_var.clone()),
                        _ => RowTail::Open(var.clone()),
                    }
                } else {
                    RowTail::Open(var.clone())
                }
            }
            RowTail::Recursive(id, args) => {
                RowTail::Recursive(*id, args.iter().map(|a| a.apply_subst(subst)).collect())
            }
        };

        RowType { props, tail }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for ty in self.props.values() {
            vars.extend(ty.free_vars());
        }
        match &self.tail {
            RowTail::Open(var) => {
                vars.insert(var.clone());
            }
            RowTail::Recursive(_, args) => {
                for arg in args {
                    vars.extend(arg.free_vars());
                }
            }
            RowTail::Closed => {}
        }
        vars
    }
}

impl Substitutable for TypePred {
    fn apply_subst(&self, subst: &Subst) -> Self {
        TypePred {
            class: self.class.clone(),
            types: self.types.iter().map(|t| t.apply_subst(subst)).collect(),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for ty in &self.types {
            vars.extend(ty.free_vars());
        }
        vars
    }
}

impl Substitutable for QualType {
    fn apply_subst(&self, subst: &Subst) -> Self {
        QualType {
            preds: self.preds.iter().map(|p| p.apply_subst(subst)).collect(),
            ty: self.ty.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.ty.free_vars();
        for pred in &self.preds {
            vars.extend(pred.free_vars());
        }
        vars
    }
}

impl Substitutable for TypeScheme {
    fn apply_subst(&self, subst: &Subst) -> Self {
        // Remove quantified variables from substitution
        let filtered_subst = subst.remove_vars(&self.vars);
        TypeScheme {
            vars: self.vars.clone(),
            body: self.body.apply_subst(&filtered_subst),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.body.free_vars();
        for v in &self.vars {
            vars.remove(v);
        }
        vars
    }
}

impl<T: Substitutable> Substitutable for Vec<T> {
    fn apply_subst(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply_subst(subst)).collect()
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for t in self {
            vars.extend(t.free_vars());
        }
        vars
    }
}

impl<T: Substitutable> Substitutable for Option<T> {
    fn apply_subst(&self, subst: &Subst) -> Self {
        self.as_ref().map(|t| t.apply_subst(subst))
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        self.as_ref().map(|t| t.free_vars()).unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_subst() {
        let subst = Subst::empty();
        assert!(subst.is_empty());

        let ty = Type::flex(0);
        assert_eq!(subst.apply(&ty), ty);
    }

    #[test]
    fn test_singleton_subst() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::flex(0);
        assert_eq!(subst.apply(&ty), Type::Number);
    }

    #[test]
    fn test_subst_preserves_other_vars() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::flex(1);
        assert_eq!(subst.apply(&ty), Type::flex(1));
    }

    #[test]
    fn test_subst_in_func() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::simple_func(vec![Type::flex(0)], Type::flex(0));
        let result = subst.apply(&ty);

        assert_eq!(result, Type::simple_func(vec![Type::Number], Type::Number));
    }

    #[test]
    fn test_compose() {
        // s1: a0 -> Number
        // s2: a1 -> a0
        // compose(s1, s2): a0 -> Number, a1 -> Number
        let s1 = Subst::singleton(TVarName::Flex(0), Type::Number);
        let s2 = Subst::singleton(TVarName::Flex(1), Type::flex(0));
        let composed = s1.compose(&s2);

        assert_eq!(composed.apply(&Type::flex(0)), Type::Number);
        assert_eq!(composed.apply(&Type::flex(1)), Type::Number);
    }

    #[test]
    fn test_free_vars() {
        let ty = Type::simple_func(vec![Type::flex(0), Type::flex(1)], Type::Number);
        let vars = ty.free_vars();

        assert!(vars.contains(&TVarName::Flex(0)));
        assert!(vars.contains(&TVarName::Flex(1)));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_scheme_subst_respects_quantifiers() {
        // forall a0. a0 -> a1
        // Substituting a0 -> Number should only affect a1
        let scheme = TypeScheme::poly(
            vec![TVarName::Flex(0)],
            Type::simple_func(vec![Type::flex(0)], Type::flex(1)),
        );

        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let result = subst.apply(&scheme);

        // The quantified a0 should be unchanged, a1 is not in domain
        assert_eq!(result.vars, vec![TVarName::Flex(0)]);
    }
}
