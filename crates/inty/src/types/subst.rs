//! Substitution for type inference.
//!
//! Implements the substitution data structure and the Substitutable trait
//! for applying substitutions to types, type schemes, and other structures.

use std::collections::{HashMap, HashSet};

use super::ty::{
    FieldEntry, PVarName, Presence, PropName, QualType, RowTail, RowType, TVarName, Type,
    TypePred, TypeScheme,
};

/// A substitution mapping type variables to types and presence
/// variables to presences (Remy '94 — two domains for one substitution).
#[derive(Clone, Debug, Default)]
pub struct Subst {
    map: HashMap<TVarName, Type>,
    presences: HashMap<PVarName, Presence>,
}

impl Subst {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Subst {
            map: HashMap::new(),
            presences: HashMap::new(),
        }
    }

    /// Create a singleton substitution.
    pub fn singleton(var: TVarName, ty: Type) -> Self {
        let mut map = HashMap::new();
        map.insert(var, ty);
        Subst {
            map,
            presences: HashMap::new(),
        }
    }

    /// Check if the substitution is empty in both domains.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty() && self.presences.is_empty()
    }

    /// Get the type for a variable, if present.
    pub fn get(&self, var: &TVarName) -> Option<&Type> {
        self.map.get(var)
    }

    /// Get the presence binding for a presence variable, if present.
    pub fn get_presence(&self, pvar: &PVarName) -> Option<&Presence> {
        self.presences.get(pvar)
    }

    /// Check if a type variable is in the domain.
    pub fn contains(&self, var: &TVarName) -> bool {
        self.map.contains_key(var)
    }

    /// Check if a presence variable is in the domain.
    pub fn contains_presence(&self, pvar: &PVarName) -> bool {
        self.presences.contains_key(pvar)
    }

    /// Insert a type mapping into the substitution.
    pub fn insert(&mut self, var: TVarName, ty: Type) {
        self.map.insert(var, ty);
    }

    /// Insert a presence mapping into the substitution.
    pub fn insert_presence(&mut self, pvar: PVarName, pres: Presence) {
        self.presences.insert(pvar, pres);
    }

    /// Remove a type variable from the substitution.
    pub fn remove(&mut self, var: &TVarName) {
        self.map.remove(var);
    }

    /// Get the domain (set of type variables) of this substitution.
    pub fn domain(&self) -> HashSet<TVarName> {
        self.map.keys().cloned().collect()
    }

    /// Get the presence-variable domain.
    pub fn presence_domain(&self) -> HashSet<PVarName> {
        self.presences.keys().cloned().collect()
    }

    /// Resolve a presence chain through the substitution. Returns the
    /// presence concrete or the first unbound variable.
    pub fn resolve_presence(&self, pres: &Presence) -> Presence {
        let mut current = pres.clone();
        let mut visited: HashSet<PVarName> = HashSet::new();
        loop {
            match &current {
                Presence::Pre | Presence::Abs => return current,
                Presence::Var(v) => {
                    if !visited.insert(v.clone()) {
                        return current;
                    }
                    match self.presences.get(v) {
                        Some(next) => current = next.clone(),
                        None => return current,
                    }
                }
            }
        }
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

        // Same composition rule on presences. Both maps live in
        // separate namespaces so we never need to thread a presence
        // through a type-map lookup or vice versa.
        let mut presences = HashMap::new();
        for (pvar, pres) in &other.presences {
            presences.insert(pvar.clone(), self.apply_presence(pres));
        }
        for (pvar, pres) in &self.presences {
            if !presences.contains_key(pvar) {
                presences.insert(pvar.clone(), pres.clone());
            }
        }

        Subst {
            map: result,
            presences,
        }
    }

    /// Apply this substitution to a presence (shallow — one step of
    /// presence-variable resolution).
    pub fn apply_presence(&self, pres: &Presence) -> Presence {
        match pres {
            Presence::Pre | Presence::Abs => pres.clone(),
            Presence::Var(v) => match self.presences.get(v) {
                Some(bound) => bound.clone(),
                None => pres.clone(),
            },
        }
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
        Subst {
            map,
            presences: self.presences.clone(),
        }
    }

    /// Iterate over the mappings.
    pub fn iter(&self) -> impl Iterator<Item = (&TVarName, &Type)> {
        self.map.iter()
    }

    /// Walk a type and merge every row tail variable that resolves
    /// to a row in this substitution into the row's own props.
    ///
    /// `apply_subst` is intentionally shallow on row tails — it's
    /// called by `Subst::compose` over every existing binding on
    /// every `extend_subst`, so a deep merge there explodes
    /// combinatorially on builder patterns and recursive
    /// `this`-typed rows. The rule it skips ("when `ρ` is bound to
    /// `Row(R)`, replace `RowTail::Open(ρ)` with `R`'s contents")
    /// is needed for two things: the printer's view of a type, and
    /// `generalize`'s computation of free variables. Both are
    /// boundary operations that run once per type, not inside the
    /// inference loop, so we do the merge lazily here.
    ///
    /// Cycles can exist on row tails because `unify_rows` extends
    /// the substitution directly without going through
    /// `var_bind`'s recursive-type wrapping. The local visited set
    /// caps each chain at one full traversal.
    pub fn flatten(&self, ty: &Type) -> Type {
        let mut visited: HashSet<TVarName> = HashSet::new();
        self.flatten_type(ty, &mut visited)
    }

    fn flatten_type(&self, ty: &Type, visited: &mut HashSet<TVarName>) -> Type {
        match ty {
            // Resolve variables here, not just at the top level —
            // `Subst::compose` only fully applies the substitution
            // to its own keys; deeply nested `Var(...)` inside
            // rows-bound-to-rows can still point at unsubstituted
            // variables.
            //
            // `visited` is insert-only across the whole flatten()
            // call: each variable is expanded at most once. The
            // structure produced is a DAG-collapse of the
            // substitution graph, which is what we want for the
            // boundary callers (printer, generalize). It also caps
            // the work: with `n` vars in the substitution,
            // flatten is O(n) instead of O(2^n) in the worst case
            // through wide-fan-out rows.
            Type::Var(name) => match self.get(name) {
                None => ty.clone(),
                Some(_) if !visited.insert(name.clone()) => ty.clone(),
                Some(bound) => {
                    let cloned = bound.clone();
                    self.flatten_type(&cloned, visited)
                }
            },
            Type::Row(row) => Type::Row(self.flatten_row(row, visited)),
            Type::Func {
                this_type,
                params,
                ret,
            } => Type::Func {
                this_type: this_type
                    .as_ref()
                    .map(|t| Box::new(self.flatten_type(t, visited))),
                params: params
                    .iter()
                    .map(|p| self.flatten_type(p, visited))
                    .collect(),
                ret: Box::new(self.flatten_type(ret, visited)),
            },
            Type::Array(elem) => Type::Array(Box::new(self.flatten_type(elem, visited))),
            Type::Promise(inner) => Type::Promise(Box::new(self.flatten_type(inner, visited))),
            Type::Map(value) => Type::Map(Box::new(self.flatten_type(value, visited))),
            Type::Union(members) => {
                Type::union(members.iter().map(|m| self.flatten_type(m, visited)))
            }
            Type::Named(id, args) => Type::Named(
                *id,
                args.iter().map(|a| self.flatten_type(a, visited)).collect(),
            ),
            // Module/Literal/primitives: nothing to flatten.
            _ => ty.clone(),
        }
    }

    fn flatten_row(&self, row: &RowType, visited: &mut HashSet<TVarName>) -> RowType {
        let mut props: std::collections::BTreeMap<PropName, FieldEntry> = row
            .props
            .iter()
            .map(|(k, e)| {
                (
                    k.clone(),
                    FieldEntry {
                        presence: self.resolve_presence(&e.presence),
                        ty: self.flatten_type(&e.ty, visited),
                    },
                )
            })
            .collect();

        let mut current_tail = row.tail.clone();
        let tail = loop {
            match current_tail {
                RowTail::Closed => break RowTail::Closed,
                RowTail::Recursive(id, args) => {
                    break RowTail::Recursive(
                        id,
                        args.iter().map(|a| self.flatten_type(a, visited)).collect(),
                    );
                }
                RowTail::Open(var) => {
                    if !visited.insert(var.clone()) {
                        break RowTail::Open(var);
                    }
                    match self.get(&var) {
                        None => break RowTail::Open(var),
                        Some(Type::Var(next_var)) => {
                            current_tail = RowTail::Open(next_var.clone());
                        }
                        Some(Type::Row(other_row)) => {
                            // Bindings in the substitution are kept
                            // idempotent by `Subst::compose` (every
                            // extend pushes the new singleton
                            // through every existing value), so
                            // `other_row`'s props don't need
                            // re-substitution beyond what the
                            // recursive `flatten_type` does for any
                            // `Var` we encounter.
                            for (k, e) in &other_row.props {
                                let v_flat = self.flatten_type(&e.ty, visited);
                                props.entry(k.clone()).or_insert(FieldEntry {
                                    presence: self.resolve_presence(&e.presence),
                                    ty: v_flat,
                                });
                            }
                            current_tail = other_row.tail.clone();
                        }
                        Some(_) => break RowTail::Open(var),
                    }
                }
            }
        };

        RowType { props, tail }
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
            presences: HashMap::new(),
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
            Type::Union(members) => Type::union(members.iter().map(|m| m.apply_subst(subst))),

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

            // Error sentinel: substitution is the identity. The
            // binding already failed; nothing here can change.
            Type::Error => Type::Error,
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        Type::free_vars(self)
    }
}

impl Substitutable for RowType {
    fn apply_subst(&self, subst: &Subst) -> Self {
        // `apply_subst` stays shallow on purpose: it's invoked
        // implicitly by `Subst::compose` on every existing binding
        // every time a new binding is added during inference, so
        // any deep work here amplifies into N² behaviour through
        // the chained-method / builder shape. The full row-tail
        // merge that Rémy unification's substitution semantics
        // require is implemented by `Subst::flatten` and called
        // only at the boundaries that need it (pretty-printing,
        // generalisation).
        let props: std::collections::BTreeMap<PropName, FieldEntry> = self
            .props
            .iter()
            .map(|(k, e)| (k.clone(), e.apply_subst(subst)))
            .collect();

        let tail = match &self.tail {
            RowTail::Closed => RowTail::Closed,
            RowTail::Open(var) => match subst.get(var) {
                Some(Type::Var(new_var)) => RowTail::Open(new_var.clone()),
                _ => RowTail::Open(var.clone()),
            },
            RowTail::Recursive(id, args) => {
                RowTail::Recursive(*id, args.iter().map(|a| a.apply_subst(subst)).collect())
            }
        };

        RowType { props, tail }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for entry in self.props.values() {
            vars.extend(entry.free_vars());
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

impl Substitutable for FieldEntry {
    fn apply_subst(&self, subst: &Subst) -> Self {
        FieldEntry {
            presence: subst.apply_presence(&self.presence),
            ty: self.ty.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        self.ty.free_vars()
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
        // Remove quantified type variables from substitution. We
        // don't need to filter presence variables similarly: a
        // generalized pvar in `self.pvars` couldn't be bound in the
        // outer substitution unless it had leaked, which the
        // env-difference rule in `generalize` prevents.
        let filtered_subst = subst.remove_vars(&self.vars);
        TypeScheme {
            vars: self.vars.clone(),
            pvars: self.pvars.clone(),
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
