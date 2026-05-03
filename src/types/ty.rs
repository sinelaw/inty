//! Core type definitions for minfern type inference.
//!
//! This module defines the type representation following the HMF (Hindley-Milner
//! with First-class Polymorphism) approach, with support for:
//! - Row polymorphism for structural typing of objects
//! - Equi-recursive types for self-referential structures
//! - Type classes for overloaded operators

use std::collections::{BTreeMap, HashSet};

/// Unique identifier for type variables.
pub type TVarId = u32;

/// Unique identifier for named recursive types.
pub type TypeId = u32;

/// Type variable names differentiate between flexible (unification) and
/// rigid (skolem) variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TVarName {
    /// Flexible variable that can be unified with other types.
    Flex(TVarId),
    /// Rigid variable (skolem) used during subsumption checking.
    Skolem(TVarId),
}

impl TVarName {
    pub fn id(&self) -> TVarId {
        match self {
            TVarName::Flex(id) | TVarName::Skolem(id) => *id,
        }
    }

    pub fn is_flex(&self) -> bool {
        matches!(self, TVarName::Flex(_))
    }

    pub fn is_skolem(&self) -> bool {
        matches!(self, TVarName::Skolem(_))
    }
}

/// Type class names for constraint-based polymorphism.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClassName {
    /// Plus class: types that support the + operator (Number, String).
    Plus,
    /// Indexable class: types that support indexed access.
    /// Indexable(container, index, element)
    Indexable,
}

/// Type class predicate: a constraint that a type must satisfy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypePred {
    pub class: ClassName,
    pub types: Vec<Type>,
}

impl TypePred {
    pub fn plus(ty: Type) -> Self {
        TypePred {
            class: ClassName::Plus,
            types: vec![ty],
        }
    }

    pub fn indexable(container: Type, index: Type, element: Type) -> Self {
        TypePred {
            class: ClassName::Indexable,
            types: vec![container, index, element],
        }
    }

    /// Get the free type variables in this predicate.
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for ty in &self.types {
            vars.extend(ty.free_vars());
        }
        vars
    }
}

/// Literal value for singleton-literal types.
///
/// `LitValue` represents a single concrete JavaScript value lifted into the
/// type lattice. Literal types are required for switch-exhaustiveness on
/// finite string sets (e.g. `"a" | "b" | "c"`) and for the discriminator
/// field of TypeScript-style discriminated unions.
#[derive(Clone, Debug)]
pub enum LitValue {
    /// String literal type, e.g. the type `"circle"`.
    String(String),
    /// Number literal type, e.g. the type `3.14`.
    Number(f64),
    /// Boolean literal type, e.g. the type `true`.
    Bool(bool),
}

impl LitValue {
    /// The base primitive type that this literal subsumes into.
    pub fn base_type(&self) -> Type {
        match self {
            LitValue::String(_) => Type::String,
            LitValue::Number(_) => Type::Number,
            LitValue::Bool(_) => Type::Boolean,
        }
    }

    /// Stable sort key used for normalising unions deterministically.
    fn sort_key(&self) -> (u8, String) {
        match self {
            LitValue::String(s) => (0, s.clone()),
            LitValue::Number(n) => (1, n.to_bits().to_string()),
            LitValue::Bool(b) => (2, b.to_string()),
        }
    }
}

impl PartialEq for LitValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LitValue::String(a), LitValue::String(b)) => a == b,
            (LitValue::Number(a), LitValue::Number(b)) => a.to_bits() == b.to_bits(),
            (LitValue::Bool(a), LitValue::Bool(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for LitValue {}

impl std::hash::Hash for LitValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            LitValue::String(s) => {
                0u8.hash(state);
                s.hash(state);
            }
            LitValue::Number(n) => {
                1u8.hash(state);
                n.to_bits().hash(state);
            }
            LitValue::Bool(b) => {
                2u8.hash(state);
                b.hash(state);
            }
        }
    }
}

/// Property name in object types.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PropName(pub String);

impl From<&str> for PropName {
    fn from(s: &str) -> Self {
        PropName(s.to_string())
    }
}

impl From<String> for PropName {
    fn from(s: String) -> Self {
        PropName(s)
    }
}

/// Row tail determines whether an object type is open (can have more properties)
/// or closed (exact set of properties).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowTail {
    /// Closed row: no additional properties allowed.
    Closed,
    /// Open row: can have additional properties via the row variable.
    Open(TVarName),
    /// Recursive reference to a named type.
    Recursive(TypeId, Vec<Type>),
}

/// Row type for structural typing of objects.
/// Represents a set of properties with an optional tail for extensibility.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RowType {
    /// Properties with their types.
    pub props: BTreeMap<PropName, Type>,
    /// Row tail for open/closed/recursive rows.
    pub tail: RowTail,
}

impl RowType {
    /// Create a closed row with the given properties.
    pub fn closed(props: BTreeMap<PropName, Type>) -> Self {
        RowType {
            props,
            tail: RowTail::Closed,
        }
    }

    /// Create an open row with the given properties and row variable.
    pub fn open(props: BTreeMap<PropName, Type>, var: TVarName) -> Self {
        RowType {
            props,
            tail: RowTail::Open(var),
        }
    }

    /// Create an empty open row.
    pub fn empty_open(var: TVarName) -> Self {
        RowType {
            props: BTreeMap::new(),
            tail: RowTail::Open(var),
        }
    }

    /// Create an empty closed row.
    pub fn empty_closed() -> Self {
        RowType {
            props: BTreeMap::new(),
            tail: RowTail::Closed,
        }
    }

    /// Get a property type by name.
    pub fn get_prop(&self, name: &PropName) -> Option<&Type> {
        self.props.get(name)
    }

    /// Check if this row has a specific property.
    pub fn has_prop(&self, name: &PropName) -> bool {
        self.props.contains_key(name)
    }

    /// Check if this row is open (has a row variable tail).
    pub fn is_open(&self) -> bool {
        matches!(self.tail, RowTail::Open(_))
    }

    /// Check if this row is closed.
    pub fn is_closed(&self) -> bool {
        matches!(self.tail, RowTail::Closed)
    }
}

/// Core type representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    // === Primitive types ===
    /// JavaScript number type (all numbers are f64).
    Number,
    /// JavaScript string type.
    String,
    /// JavaScript boolean type.
    Boolean,
    /// JavaScript undefined type.
    Undefined,
    /// JavaScript null type.
    Null,
    /// JavaScript regex type.
    Regex,

    // === Type variable ===
    /// Type variable (flexible or skolem).
    Var(TVarName),

    // === Compound types ===
    /// Function type: (this_type, param_types) -> return_type
    /// The this_type captures the type of `this` inside the function.
    /// - None: function doesn't reference `this` (static function)
    /// - Some(T): function references `this` with type T
    Func {
        this_type: Option<Box<Type>>,
        params: Vec<Type>,
        ret: Box<Type>,
    },

    /// Row type for objects: {prop1: T1, prop2: T2 | tail}
    Row(RowType),

    /// Array type: [T]
    Array(Box<Type>),

    /// Map type for string-keyed dictionaries: Map<T>
    Map(Box<Type>),

    /// Promise type: `Promise<T>`. Modelled as a parameterised nominal
    /// type analogous to `Array<T>`. The `await` expression extracts the
    /// inner `T`; an `async function` returning `T` has type `Promise<T>`.
    Promise(Box<Type>),

    /// Named recursive type reference: μα.T
    /// The TypeId refers to a type definition, and the Vec<Type> are type arguments.
    Named(TypeId, Vec<Type>),

    /// Singleton literal type, e.g. `"circle"` or `42` or `true`.
    Literal(LitValue),

    /// Untagged union type: `T1 | T2 | ...`. Always normalised so that
    /// members are deduplicated and sorted. A union is only constructed via
    /// [`Type::union`] which enforces the invariants.
    Union(Vec<Type>),
}

impl Type {
    // === Constructors ===

    /// Create a type variable.
    pub fn var(name: TVarName) -> Self {
        Type::Var(name)
    }

    /// Create a flexible type variable.
    pub fn flex(id: TVarId) -> Self {
        Type::Var(TVarName::Flex(id))
    }

    /// Create a skolem type variable.
    pub fn skolem(id: TVarId) -> Self {
        Type::Var(TVarName::Skolem(id))
    }

    /// Create a function type with a specific `this` type.
    pub fn func(this_type: Type, params: Vec<Type>, ret: Type) -> Self {
        Type::Func {
            this_type: Some(Box::new(this_type)),
            params,
            ret: Box::new(ret),
        }
    }

    /// Create a static function type (doesn't reference `this`).
    /// Use this for built-in functions like Math.min that ignore their receiver.
    pub fn static_func(params: Vec<Type>, ret: Type) -> Self {
        Type::Func {
            this_type: None,
            params,
            ret: Box::new(ret),
        }
    }

    /// Create a simple function type (doesn't reference `this`).
    /// Alias for static_func for backwards compatibility.
    pub fn simple_func(params: Vec<Type>, ret: Type) -> Self {
        Type::static_func(params, ret)
    }

    /// Create an array type.
    pub fn array(elem: Type) -> Self {
        Type::Array(Box::new(elem))
    }

    /// Create a promise type.
    pub fn promise(inner: Type) -> Self {
        Type::Promise(Box::new(inner))
    }

    /// Create a map type.
    pub fn map(value: Type) -> Self {
        Type::Map(Box::new(value))
    }

    /// Create a row type from an object.
    pub fn row(row: RowType) -> Self {
        Type::Row(row)
    }

    /// Create a string-literal type.
    pub fn lit_string(s: impl Into<String>) -> Self {
        Type::Literal(LitValue::String(s.into()))
    }

    /// Create a number-literal type.
    pub fn lit_number(n: f64) -> Self {
        Type::Literal(LitValue::Number(n))
    }

    /// Create a boolean-literal type.
    pub fn lit_bool(b: bool) -> Self {
        Type::Literal(LitValue::Bool(b))
    }

    /// The empty union, representing an unreachable / impossible value.
    pub fn never() -> Self {
        Type::Union(Vec::new())
    }

    /// Construct a union type, normalising the members.
    ///
    /// Normal form rules:
    /// - Nested unions are flattened: `(A | B) | A` ≡ `A | B`.
    /// - Members are deduplicated and sorted by a stable key.
    /// - A single-element union collapses to that element.
    /// - The empty union stays as `Type::Union(vec![])` (i.e. `never`).
    pub fn union(members: impl IntoIterator<Item = Type>) -> Self {
        let mut flat: Vec<Type> = Vec::new();
        for m in members {
            match m {
                Type::Union(inner) => {
                    for t in inner {
                        flat.push(t);
                    }
                }
                other => flat.push(other),
            }
        }

        // Deduplicate by structural equality. Quadratic in number of
        // members but unions in practice are small.
        let mut seen: Vec<Type> = Vec::new();
        for t in flat {
            if !seen.iter().any(|s| s == &t) {
                seen.push(t);
            }
        }

        seen.sort_by_key(union_member_sort_key);

        if seen.len() == 1 {
            seen.into_iter().next().unwrap()
        } else {
            Type::Union(seen)
        }
    }

    /// True if this type is the empty union (`never`).
    pub fn is_never(&self) -> bool {
        matches!(self, Type::Union(v) if v.is_empty())
    }

    /// Create a closed object type with the given properties.
    pub fn object(props: impl IntoIterator<Item = (impl Into<PropName>, Type)>) -> Self {
        let props: BTreeMap<PropName, Type> =
            props.into_iter().map(|(k, v)| (k.into(), v)).collect();
        Type::Row(RowType::closed(props))
    }

    /// Create an open object type with the given properties.
    pub fn object_open(
        props: impl IntoIterator<Item = (impl Into<PropName>, Type)>,
        tail: TVarName,
    ) -> Self {
        let props: BTreeMap<PropName, Type> =
            props.into_iter().map(|(k, v)| (k.into(), v)).collect();
        Type::Row(RowType::open(props, tail))
    }

    // === Predicates ===

    /// Check if this is a type variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Type::Var(_))
    }

    /// Check if this is a flexible type variable.
    pub fn is_flex_var(&self) -> bool {
        matches!(self, Type::Var(TVarName::Flex(_)))
    }

    /// Check if this is a function type.
    pub fn is_func(&self) -> bool {
        matches!(self, Type::Func { .. })
    }

    /// Check if this is a row/object type.
    pub fn is_row(&self) -> bool {
        matches!(self, Type::Row(_))
    }

    /// Check if this is a primitive type.
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::Number
                | Type::String
                | Type::Boolean
                | Type::Undefined
                | Type::Null
                | Type::Regex
        )
    }

    /// Check if this is a union type.
    pub fn is_union(&self) -> bool {
        matches!(self, Type::Union(_))
    }

    // === Accessors ===

    /// Get the type variable name if this is a Var.
    pub fn as_var(&self) -> Option<&TVarName> {
        match self {
            Type::Var(name) => Some(name),
            _ => None,
        }
    }

    /// Get the row type if this is a Row.
    pub fn as_row(&self) -> Option<&RowType> {
        match self {
            Type::Row(row) => Some(row),
            _ => None,
        }
    }

    /// Get the function components if this is a Func.
    /// Returns (this_type, params, ret) where this_type is None for static functions.
    pub fn as_func(&self) -> Option<(Option<&Type>, &[Type], &Type)> {
        match self {
            Type::Func {
                this_type,
                params,
                ret,
            } => Some((this_type.as_deref(), params, ret)),
            _ => None,
        }
    }

    /// Collect all free type variables in this type.
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    fn collect_free_vars(&self, vars: &mut HashSet<TVarName>) {
        match self {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex => {}

            Type::Var(name) => {
                vars.insert(name.clone());
            }

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                if let Some(this) = this_type {
                    this.collect_free_vars(vars);
                }
                for p in params {
                    p.collect_free_vars(vars);
                }
                ret.collect_free_vars(vars);
            }

            Type::Row(row) => {
                for ty in row.props.values() {
                    ty.collect_free_vars(vars);
                }
                match &row.tail {
                    RowTail::Open(v) => {
                        vars.insert(v.clone());
                    }
                    RowTail::Recursive(_, args) => {
                        for arg in args {
                            arg.collect_free_vars(vars);
                        }
                    }
                    RowTail::Closed => {}
                }
            }

            Type::Array(elem) => elem.collect_free_vars(vars),
            Type::Promise(inner) => inner.collect_free_vars(vars),
            Type::Map(value) => value.collect_free_vars(vars),

            Type::Named(_, args) => {
                for arg in args {
                    arg.collect_free_vars(vars);
                }
            }

            Type::Literal(_) => {}

            Type::Union(members) => {
                for m in members {
                    m.collect_free_vars(vars);
                }
            }
        }
    }
}

/// Qualified type: a type with type class constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QualType {
    /// Type class predicates that must be satisfied.
    pub preds: Vec<TypePred>,
    /// The underlying type.
    pub ty: Type,
}

impl QualType {
    /// Create a qualified type with no predicates.
    pub fn simple(ty: Type) -> Self {
        QualType { preds: vec![], ty }
    }

    /// Create a qualified type with predicates.
    pub fn with_preds(preds: Vec<TypePred>, ty: Type) -> Self {
        QualType { preds, ty }
    }

    /// Collect all free type variables.
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.ty.free_vars();
        for pred in &self.preds {
            for ty in &pred.types {
                vars.extend(ty.free_vars());
            }
        }
        vars
    }
}

/// Type scheme: a universally quantified type.
/// Represents ∀α₁...αₙ. Q => τ where Q is a set of predicates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme {
    /// Quantified type variables.
    pub vars: Vec<TVarName>,
    /// The qualified type body.
    pub body: QualType,
}

impl TypeScheme {
    /// Create a monomorphic type scheme (no quantification).
    pub fn mono(ty: Type) -> Self {
        TypeScheme {
            vars: vec![],
            body: QualType::simple(ty),
        }
    }

    /// Create a type scheme with the given quantified variables.
    pub fn poly(vars: Vec<TVarName>, ty: Type) -> Self {
        TypeScheme {
            vars,
            body: QualType::simple(ty),
        }
    }

    /// Create a type scheme with predicates.
    pub fn qualified(vars: Vec<TVarName>, preds: Vec<TypePred>, ty: Type) -> Self {
        TypeScheme {
            vars,
            body: QualType::with_preds(preds, ty),
        }
    }

    /// Get the underlying type (without looking at quantifiers).
    pub fn ty(&self) -> &Type {
        &self.body.ty
    }

    /// Check if this is a monomorphic type (no quantified variables).
    pub fn is_mono(&self) -> bool {
        self.vars.is_empty()
    }

    /// Collect all free type variables (not including quantified ones).
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.body.free_vars();
        for v in &self.vars {
            vars.remove(v);
        }
        vars
    }
}

/// Stable sort key for union members so the normal form is deterministic
/// across runs. Variants are first ordered by a small tag, then by a
/// content-derived string. The exact ordering is unspecified — we only
/// care that it's total and stable.
fn union_member_sort_key(t: &Type) -> (u8, String) {
    match t {
        Type::Number => (0, String::new()),
        Type::String => (1, String::new()),
        Type::Boolean => (2, String::new()),
        Type::Undefined => (3, String::new()),
        Type::Null => (4, String::new()),
        Type::Regex => (5, String::new()),
        Type::Literal(lit) => {
            let (sub, key) = lit.sort_key();
            (6, format!("{}|{}", sub, key))
        }
        Type::Var(TVarName::Flex(id)) => (7, format!("f{}", id)),
        Type::Var(TVarName::Skolem(id)) => (8, format!("s{}", id)),
        Type::Func { params, ret, .. } => (
            9,
            format!("{}->{}", params.len(), union_member_sort_key(ret).1),
        ),
        Type::Row(row) => {
            let mut keys: Vec<&str> = row.props.keys().map(|p| p.0.as_str()).collect();
            keys.sort();
            (10, keys.join(","))
        }
        Type::Array(elem) => (11, union_member_sort_key(elem).1),
        Type::Map(v) => (12, union_member_sort_key(v).1),
        Type::Promise(v) => (13, union_member_sort_key(v).1),
        Type::Named(id, _) => (14, format!("{}", id)),
        Type::Union(_) => (15, String::new()),
    }
}

/// A named type definition for recursive types.
/// Represents μα.T where α is the recursive variable.
#[derive(Clone, Debug)]
pub struct TypeDef {
    /// Unique identifier for this type definition.
    pub id: TypeId,
    /// Type parameters for the definition.
    pub params: Vec<TVarName>,
    /// The type body (may reference the type via Named(id, ...)).
    pub body: Type,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_construction() {
        let num = Type::Number;
        assert!(num.is_primitive());

        let var = Type::flex(0);
        assert!(var.is_var());
        assert!(var.is_flex_var());

        let func = Type::simple_func(vec![Type::Number], Type::String);
        assert!(func.is_func());
    }

    #[test]
    fn test_free_vars() {
        let var0 = Type::flex(0);
        let var1 = Type::flex(1);

        let func = Type::simple_func(vec![var0.clone()], var1.clone());
        let free = func.free_vars();

        assert!(free.contains(&TVarName::Flex(0)));
        assert!(free.contains(&TVarName::Flex(1)));
        assert_eq!(free.len(), 2);
    }

    #[test]
    fn test_row_type() {
        let row = RowType::closed(
            [("x".into(), Type::Number), ("y".into(), Type::Number)]
                .into_iter()
                .collect(),
        );

        assert!(row.is_closed());
        assert!(row.has_prop(&"x".into()));
        assert!(!row.has_prop(&"z".into()));

        let open_row = RowType::open(
            [("x".into(), Type::Number)].into_iter().collect(),
            TVarName::Flex(0),
        );

        assert!(open_row.is_open());
    }

    #[test]
    fn test_type_scheme() {
        let mono = TypeScheme::mono(Type::Number);
        assert!(mono.is_mono());

        let poly = TypeScheme::poly(vec![TVarName::Flex(0)], Type::flex(0));
        assert!(!poly.is_mono());
        assert!(poly.free_vars().is_empty());
    }
}
