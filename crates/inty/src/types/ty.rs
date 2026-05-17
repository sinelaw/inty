//! Core type definitions for inty type inference.
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

/// Unique identifier for presence variables.
///
/// Presence variables live in a namespace separate from type variables
/// (`TVarName`). A row field's *presence* — whether the field is
/// definitely present, definitely absent, or polymorphic — is tracked
/// independently of its type. See `Presence`, `FieldEntry`, and the
/// `Subst` presence map. The encoding follows Rémy, "Type Inference for
/// Records in a Natural Extension of ML" (1994).
pub type PVarId = u32;

/// Presence variable name. Flexible vs skolem mirrors `TVarName` so the
/// same generalization / subsumption discipline applies to presence.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PVarName {
    /// Flexible presence variable (unifiable).
    Flex(PVarId),
    /// Rigid presence variable (skolem).
    Skolem(PVarId),
}

impl PVarName {
    pub fn id(&self) -> PVarId {
        match self {
            PVarName::Flex(id) | PVarName::Skolem(id) => *id,
        }
    }

    pub fn is_flex(&self) -> bool {
        matches!(self, PVarName::Flex(_))
    }
}

/// A row field's presence: definitely present, definitely absent, or
/// polymorphic in presence. `Var(theta)` is what makes an "optional"
/// field expressible without lifting it into the value's type — the
/// caller may unify it with `Pre` (supplying the field) or `Abs`
/// (omitting it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Presence {
    Pre,
    Abs,
    Var(PVarName),
}

impl Presence {
    pub fn is_abs(&self) -> bool {
        matches!(self, Presence::Abs)
    }
    pub fn is_pre(&self) -> bool {
        matches!(self, Presence::Pre)
    }
}

/// One positional parameter of a `Type::Func`, carrying its presence
/// alongside its type.
///
/// `Presence::Pre` is required (the vast majority of params).
/// `Presence::Var(φ)` is polymorphic — the stdlib uses this to model
/// JavaScript's optional trailing args, e.g. `slice(start, end?)`. A
/// call site with N args unifies position-wise: surplus formal
/// params (formal.len() > N) must have a presence that unifies with
/// `Abs`. See `unify_impl`'s function arm for the rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncParam {
    pub presence: Presence,
    pub ty: Type,
}

impl FuncParam {
    /// Required parameter — the default. Equivalent to the
    /// pre-Shape-B representation where every parameter was just a
    /// `Type`.
    pub fn required(ty: Type) -> Self {
        FuncParam {
            presence: Presence::Pre,
            ty,
        }
    }

    /// Presence-polymorphic parameter. Used by the stdlib declarations
    /// for JavaScript built-ins that accept an optional trailing
    /// argument (`String.prototype.slice`, `padStart`, `replace`'s
    /// limit, etc.). Each declaration site allocates a fresh
    /// presence variable so per-call inference can bind it
    /// independently.
    pub fn optional(pvar: PVarName, ty: Type) -> Self {
        FuncParam {
            presence: Presence::Var(pvar),
            ty,
        }
    }
}

/// One entry in a `RowType`'s props map: presence + type.
///
/// A field written in source has `presence = Pre`. A field declared
/// optional in an annotation (`x?: T`) is assigned a fresh presence
/// variable. `Abs` only arises through unification when a closed row
/// constrains a polymorphic side's missing field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldEntry {
    pub presence: Presence,
    pub ty: Type,
}

impl FieldEntry {
    /// Field is definitely present with the given type. The common case
    /// for object literals and most stub declarations.
    pub fn pre(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Pre,
            ty,
        }
    }

    /// Field is presence-polymorphic — caller may omit or supply it.
    pub fn optional(pvar: PVarName, ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Var(pvar),
            ty,
        }
    }

    /// Field is definitely absent. Mostly produced by unification, not
    /// constructed directly.
    pub fn absent(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Abs,
            ty,
        }
    }
}

/// Type class names for constraint-based polymorphism.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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
/// Represents a set of properties (each with presence + type) and a
/// tail that controls extensibility.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RowType {
    /// Field name -> (presence, type). See `FieldEntry`.
    pub props: BTreeMap<PropName, FieldEntry>,
    /// Row tail for open/closed/recursive rows.
    pub tail: RowTail,
}

impl RowType {
    /// Create a closed row where every property is definitely present.
    /// Convenience for the common case (object literals, most stubs).
    pub fn closed(props: BTreeMap<PropName, Type>) -> Self {
        RowType {
            props: props.into_iter().map(|(k, v)| (k, FieldEntry::pre(v))).collect(),
            tail: RowTail::Closed,
        }
    }

    /// Create a closed row from a fully-specified entry map.
    pub fn closed_entries(props: BTreeMap<PropName, FieldEntry>) -> Self {
        RowType { props, tail: RowTail::Closed }
    }

    /// Create an open row where every listed property is definitely
    /// present. Tail variable carries the unmentioned fields.
    pub fn open(props: BTreeMap<PropName, Type>, var: TVarName) -> Self {
        RowType {
            props: props.into_iter().map(|(k, v)| (k, FieldEntry::pre(v))).collect(),
            tail: RowTail::Open(var),
        }
    }

    /// Create an open row from a fully-specified entry map.
    pub fn open_entries(props: BTreeMap<PropName, FieldEntry>, var: TVarName) -> Self {
        RowType { props, tail: RowTail::Open(var) }
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

    /// Get a property's type by name, regardless of presence. Returns
    /// `None` only when the field is not mentioned at all; an `Abs`
    /// field still returns `Some(&ty)` — callers that care about
    /// presence should use [`get_entry`].
    pub fn get_prop(&self, name: &PropName) -> Option<&Type> {
        self.props.get(name).map(|e| &e.ty)
    }

    /// Get the full field entry (presence + type).
    pub fn get_entry(&self, name: &PropName) -> Option<&FieldEntry> {
        self.props.get(name)
    }

    /// Check if this row has a specific property in any presence state.
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
    ///
    /// Each parameter carries a `Presence` alongside its type, modelling
    /// optional positional arguments à la Garrigue 1994 ("Labeled and
    /// optional arguments for OCaml"). `Presence::Pre` is the required
    /// case (the vast majority of inty functions); `Presence::Abs` is
    /// an unreachable annotation form; `Presence::Var(φ)` is the
    /// polymorphic case that lets a single stdlib decl like
    /// `slice(start, end?)` accept both 1-arg and 2-arg calls.
    Func {
        this_type: Option<Box<Type>>,
        params: Vec<FuncParam>,
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

    /// ES module namespace: the type of `ns` after `import * as ns from
    /// "./mod.js";`. Carries one type *scheme* per export so member access
    /// (`ns.foo`) instantiates polymorphism per use, and is identified by
    /// the canonicalised source path so two imports of the same file get
    /// the same type and two imports of different files don't unify even
    /// when their export shapes happen to coincide. See `modules.md` §2.
    Module(ModuleType),

    /// Error sentinel produced by best-effort recovery in the inference
    /// engine. When a binding fails to type-check we substitute
    /// `Type::Error` for its type so downstream uses don't cascade —
    /// `Error` unifies trivially with anything, every operation
    /// (member access, call, operator) on `Error` produces `Error`, and
    /// the type-class solver treats `Error` as satisfying every
    /// constraint. The user already saw one diagnostic for the original
    /// failure; subsequent references should stay quiet.
    ///
    /// `Type::Error` is never written by users (no surface syntax
    /// produces it). It only appears as a substitution applied by the
    /// recovery path; the pretty printer renders it as `<error>` so
    /// any leaked occurrence is obvious in test output and `--annotate`
    /// dumps.
    Error,
}

/// Body of `Type::Module`. A module is identified nominally (by source
/// path) and carries its export table as a map from exported name to
/// the scheme of the local binding it points to.
///
/// Identity is *nominal*, not structural: two modules unify iff their
/// `source` strings match. Width subtyping is intentionally not
/// implemented — a function expecting `module "./foo.js"` cannot be
/// passed a different module that happens to have a superset of the
/// same exports, and that's the right semantics for module identity.
/// If structural reuse across modules is ever needed, write the
/// parameter as a row type and pick out the field at the call site.
///
/// Future extension points (see `modules.rs` "Known limitations"):
/// - Type-class instances exported by a module would hang here
///   (`pub instances: Vec<InstanceDecl>`) so import-time merging can
///   detect conflicts.
/// - Module-field immutability is currently enforced ad-hoc in the
///   resolver; once the assignment-site check lands (see TODO in
///   `infer_assign`'s `Expr::Member` arm), no `ModuleType` field is
///   needed for it — the type variant alone is the discriminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleType {
    /// Canonicalised source path of the module — the identity of the type.
    /// Two `Type::Module` values unify iff their `source` strings match.
    pub source: String,
    /// Exported name → scheme of the underlying local binding. Stored as
    /// schemes (not types) so each `ns.foo` access can re-instantiate
    /// polymorphic exports independently.
    pub exports: BTreeMap<String, TypeScheme>,
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
    ///
    /// Under the unified callable-row design, function VALUES at top level
    /// are always rows with a `<CALL>` field. This constructor returns the
    /// wrapped form: `Row{<CALL>: Func{this, params, ret}, Closed}`. The
    /// raw `Type::Func` enum variant is reserved for the field value
    /// itself — never a top-level value type.
    ///
    /// Sub-component construction (the `Type::Func` that goes inside the
    /// `<CALL>` field) uses `Type::raw_func` / `Type::raw_static_func`
    /// instead.
    pub fn func(this_type: Type, params: Vec<Type>, ret: Type) -> Self {
        Self::wrap_callable(Type::raw_func(this_type, params, ret))
    }

    /// Create a static function type (doesn't reference `this`), wrapped
    /// in a callable row. Use this for built-in functions like Math.min
    /// that ignore their receiver.
    pub fn static_func(params: Vec<Type>, ret: Type) -> Self {
        Self::wrap_callable(Type::raw_static_func(params, ret))
    }

    /// Create a simple function type (doesn't reference `this`),
    /// wrapped in a callable row.
    pub fn simple_func(params: Vec<Type>, ret: Type) -> Self {
        Type::static_func(params, ret)
    }

    /// Raw function-type constructor with a `this`. Returns a bare
    /// `Type::Func` — only valid as the value of `<CALL>` inside a
    /// callable row, never as a top-level value type. Use `Type::func`
    /// for top-level callables.
    ///
    /// Every parameter is marked `Presence::Pre` (required). For
    /// declarations that need optional params, build the
    /// `Vec<FuncParam>` directly and use [`Type::raw_func_with_params`].
    pub fn raw_func(this_type: Type, params: Vec<Type>, ret: Type) -> Self {
        Type::Func {
            this_type: Some(Box::new(this_type)),
            params: params.into_iter().map(FuncParam::required).collect(),
            ret: Box::new(ret),
        }
    }

    /// Like [`Self::raw_func`] but takes a fully-specified parameter
    /// list, so optional parameters can be expressed. Used by the
    /// stdlib's optional-arg declarations and by the type parser's
    /// `name?: T` syntax.
    pub fn raw_func_with_params(
        this_type: Option<Type>,
        params: Vec<FuncParam>,
        ret: Type,
    ) -> Self {
        Type::Func {
            this_type: this_type.map(Box::new),
            params,
            ret: Box::new(ret),
        }
    }

    /// Raw static function-type constructor. Returns a bare
    /// `Type::Func` — only valid as the value of `<CALL>` inside a
    /// callable row, never as a top-level value type. Use
    /// `Type::static_func` for top-level callables.
    pub fn raw_static_func(params: Vec<Type>, ret: Type) -> Self {
        Type::Func {
            this_type: None,
            params: params.into_iter().map(FuncParam::required).collect(),
            ret: Box::new(ret),
        }
    }

    /// Wrap a `Type::Func` in a closed callable row.
    ///
    /// Function values at top level always carry their call signature
    /// inside the row's reserved `<CALL>` field. The row's tail is
    /// closed because a function value (from a JS function literal or a
    /// `.d.js` annotation) doesn't have implicit additional fields. Call
    /// sites that need to absorb a callable row's extras (e.g.,
    /// `arr.map(String)` where String has statics) build an *open*
    /// expected callable row via `InferState::callable_row_open`.
    pub fn wrap_callable(func: Type) -> Self {
        debug_assert!(
            matches!(func, Type::Func { .. }),
            "wrap_callable expects a raw Type::Func, got: {:?}",
            func
        );
        let mut props = BTreeMap::new();
        props.insert(PropName(super::CALLABLE_KEY.to_string()), func);
        Type::Row(RowType::closed(props))
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

    /// Create a module type with the given source identity and export
    /// schemes.
    pub fn module(source: impl Into<String>, exports: BTreeMap<String, TypeScheme>) -> Self {
        Type::Module(ModuleType {
            source: source.into(),
            exports,
        })
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

    /// Recursively widen singleton literal types to their base.
    ///
    /// Used at "fresh literal" widening points (mutable bindings without
    /// an annotation, function returns without a declared return type,
    /// joined array elements, etc.) to mirror TypeScript's notion of
    /// fresh literal widening. The transformation:
    ///
    /// * `Lit("circle")` → `String`, `Lit(42)` → `Number`,
    ///   `Lit(true)` → `Boolean`.
    /// * Recurses through `Row` (each property value), `Array`, `Map`,
    ///   `Promise`, `Union` (each member, then re-normalises so that
    ///   `"a" | "b"` widens to `String` rather than the awkward
    ///   `String | String`).
    /// * Recurses through `Func` covariantly into the return type and
    ///   contravariantly into parameters — a parameter typed `"a"`
    ///   really means "only the literal `"a"` is acceptable", and
    ///   widening it would change the function's contract, so we
    ///   leave parameters alone. (TS makes the same call.)
    /// * Type variables, named types, and modules are left alone.
    ///   Widening through a substitution is the substitution's job.
    pub fn widen_fresh_literals(&self) -> Self {
        match self {
            Type::Literal(lit) => lit.base_type(),
            Type::Row(row) => {
                let props = row
                    .props
                    .iter()
                    .map(|(k, e)| {
                        (
                            k.clone(),
                            FieldEntry {
                                presence: e.presence.clone(),
                                ty: e.ty.widen_fresh_literals(),
                            },
                        )
                    })
                    .collect();
                Type::Row(RowType {
                    props,
                    tail: row.tail.clone(),
                })
            }
            Type::Array(elem) => Type::Array(Box::new(elem.widen_fresh_literals())),
            Type::Map(v) => Type::Map(Box::new(v.widen_fresh_literals())),
            Type::Promise(inner) => Type::Promise(Box::new(inner.widen_fresh_literals())),
            Type::Union(members) => {
                let widened: Vec<Type> =
                    members.iter().map(|m| m.widen_fresh_literals()).collect();
                Type::union(widened)
            }
            Type::Func {
                this_type,
                params,
                ret,
            } => Type::Func {
                this_type: this_type.clone(),
                params: params.clone(),
                ret: Box::new(ret.widen_fresh_literals()),
            },
            // Primitives, vars, named refs, modules, error: nothing
            // to widen. `Error` is opaque — widening through it
            // would generate noise from a binding that already failed.
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::Var(_)
            | Type::Named(_, _)
            | Type::Module(_)
            | Type::Error => self.clone(),
        }
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

    /// Create a closed object type with the given properties. Every
    /// listed property is `Pre`. Use `object_entries` to mix presence
    /// states.
    pub fn object(props: impl IntoIterator<Item = (impl Into<PropName>, Type)>) -> Self {
        let props: BTreeMap<PropName, Type> =
            props.into_iter().map(|(k, v)| (k.into(), v)).collect();
        Type::Row(RowType::closed(props))
    }

    /// Create a closed object type from explicit `FieldEntry` props
    /// (i.e. presence + type per field).
    pub fn object_entries(
        props: impl IntoIterator<Item = (impl Into<PropName>, FieldEntry)>,
    ) -> Self {
        let props: BTreeMap<PropName, FieldEntry> =
            props.into_iter().map(|(k, v)| (k.into(), v)).collect();
        Type::Row(RowType::closed_entries(props))
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
    /// True if this type represents a callable function value.
    ///
    /// Under the unified callable-row design, function values at top
    /// level are rows carrying a `<CALL>` field. A bare `Type::Func` is
    /// only valid as the value of that field — it never represents a
    /// user-facing function value on its own. This predicate recognizes
    /// both forms so callers can ask "is this a function?" without
    /// caring about the encoding.
    pub fn is_func(&self) -> bool {
        match self {
            Type::Func { .. } => true,
            Type::Row(row) => row
                .props
                .contains_key(&PropName(super::CALLABLE_KEY.to_string())),
            _ => false,
        }
    }

    /// Get the function components if this represents a function value
    /// (either a bare `Type::Func` or a callable row carrying a
    /// `<CALL>` field). For callable rows, only the call signature is
    /// returned — extras on the row are ignored.
    pub fn as_callable(&self) -> Option<(Option<&Type>, &[FuncParam], &Type)> {
        match self {
            Type::Func {
                this_type,
                params,
                ret,
            } => Some((this_type.as_deref(), params, ret)),
            Type::Row(row) => {
                let key = PropName(super::CALLABLE_KEY.to_string());
                match &row.props.get(&key)?.ty {
                    Type::Func {
                        this_type,
                        params,
                        ret,
                    } => Some((this_type.as_deref(), params, ret)),
                    _ => None,
                }
            }
            _ => None,
        }
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

    /// True if this is a module type.
    pub fn is_module(&self) -> bool {
        matches!(self, Type::Module(_))
    }

    /// Get the module type if this is a Module.
    pub fn as_module(&self) -> Option<&ModuleType> {
        match self {
            Type::Module(m) => Some(m),
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
    pub fn as_func(&self) -> Option<(Option<&Type>, &[FuncParam], &Type)> {
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

    /// Collect the free *presence* variables in this type. Walks the
    /// same shape as `free_vars` but reports `PVarName`s carried by
    /// row field-entry presences.
    pub fn free_pvars(&self) -> HashSet<PVarName> {
        let mut pvars = HashSet::new();
        self.collect_free_pvars(&mut pvars);
        pvars
    }

    fn collect_free_pvars(&self, pvars: &mut HashSet<PVarName>) {
        match self {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::Var(_)
            | Type::Literal(_)
            | Type::Error => {}
            Type::Func {
                this_type,
                params,
                ret,
            } => {
                if let Some(t) = this_type {
                    t.collect_free_pvars(pvars);
                }
                for p in params {
                    if let Presence::Var(v) = &p.presence {
                        pvars.insert(v.clone());
                    }
                    p.ty.collect_free_pvars(pvars);
                }
                ret.collect_free_pvars(pvars);
            }
            Type::Row(row) => {
                for entry in row.props.values() {
                    if let Presence::Var(v) = &entry.presence {
                        pvars.insert(v.clone());
                    }
                    entry.ty.collect_free_pvars(pvars);
                }
                if let RowTail::Recursive(_, args) = &row.tail {
                    for a in args {
                        a.collect_free_pvars(pvars);
                    }
                }
            }
            Type::Array(elem) | Type::Promise(elem) | Type::Map(elem) => {
                elem.collect_free_pvars(pvars);
            }
            Type::Named(_, args) => {
                for a in args {
                    a.collect_free_pvars(pvars);
                }
            }
            Type::Union(members) => {
                for m in members {
                    m.collect_free_pvars(pvars);
                }
            }
            Type::Module(m) => {
                for scheme in m.exports.values() {
                    let mut inner = HashSet::new();
                    scheme.body.ty.collect_free_pvars(&mut inner);
                    for pred in &scheme.body.preds {
                        for ty in &pred.types {
                            ty.collect_free_pvars(&mut inner);
                        }
                    }
                    for v in &scheme.pvars {
                        inner.remove(v);
                    }
                    pvars.extend(inner);
                }
            }
        }
    }

    fn collect_free_vars(&self, vars: &mut HashSet<TVarName>) {
        match self {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::Error => {}

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
                    p.ty.collect_free_vars(vars);
                }
                ret.collect_free_vars(vars);
            }

            Type::Row(row) => {
                for entry in row.props.values() {
                    entry.ty.collect_free_vars(vars);
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

            Type::Module(m) => {
                // Each export is a scheme — its own quantified vars are
                // *not* free at the module level; only what survives in
                // the body after subtracting the scheme's binders is.
                for scheme in m.exports.values() {
                    let mut inner = HashSet::new();
                    scheme.body.ty.collect_free_vars(&mut inner);
                    for pred in &scheme.body.preds {
                        for ty in &pred.types {
                            ty.collect_free_vars(&mut inner);
                        }
                    }
                    for v in &scheme.vars {
                        inner.remove(v);
                    }
                    vars.extend(inner);
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
/// Represents ∀α₁...αₙ β₁...βₘ. Q => τ where α's are type variables,
/// β's are presence variables (Remy '94), and Q is a set of predicates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme {
    /// Quantified type variables.
    pub vars: Vec<TVarName>,
    /// Quantified presence variables.
    pub pvars: Vec<PVarName>,
    /// The qualified type body.
    pub body: QualType,
}

impl TypeScheme {
    /// Create a monomorphic type scheme (no quantification).
    pub fn mono(ty: Type) -> Self {
        TypeScheme {
            vars: vec![],
            pvars: vec![],
            body: QualType::simple(ty),
        }
    }

    /// Create a type scheme with the given quantified type variables
    /// (no presence variables).
    pub fn poly(vars: Vec<TVarName>, ty: Type) -> Self {
        TypeScheme {
            vars,
            pvars: vec![],
            body: QualType::simple(ty),
        }
    }

    /// Create a type scheme with both type and presence quantifiers.
    pub fn poly_with_presence(
        vars: Vec<TVarName>,
        pvars: Vec<PVarName>,
        ty: Type,
    ) -> Self {
        TypeScheme {
            vars,
            pvars,
            body: QualType::simple(ty),
        }
    }

    /// Create a type scheme with predicates.
    pub fn qualified(vars: Vec<TVarName>, preds: Vec<TypePred>, ty: Type) -> Self {
        TypeScheme {
            vars,
            pvars: vec![],
            body: QualType::with_preds(preds, ty),
        }
    }

    /// Create a type scheme with predicates and presence quantifiers.
    pub fn qualified_with_presence(
        vars: Vec<TVarName>,
        pvars: Vec<PVarName>,
        preds: Vec<TypePred>,
        ty: Type,
    ) -> Self {
        TypeScheme {
            vars,
            pvars,
            body: QualType::with_preds(preds, ty),
        }
    }

    /// Get the underlying type (without looking at quantifiers).
    pub fn ty(&self) -> &Type {
        &self.body.ty
    }

    /// Check if this is a monomorphic type (no quantified variables).
    pub fn is_mono(&self) -> bool {
        self.vars.is_empty() && self.pvars.is_empty()
    }

    /// Collect all free type variables (not including quantified ones).
    pub fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.body.free_vars();
        for v in &self.vars {
            vars.remove(v);
        }
        vars
    }

    /// Collect free presence variables (not including the scheme's
    /// own quantifiers).
    pub fn free_pvars(&self) -> HashSet<PVarName> {
        let mut pvars = self.body.ty.free_pvars();
        for pred in &self.body.preds {
            for ty in &pred.types {
                pvars.extend(ty.free_pvars());
            }
        }
        for v in &self.pvars {
            pvars.remove(v);
        }
        pvars
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
        Type::Module(m) => (16, m.source.clone()),
        Type::Error => (17, String::new()),
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
    fn test_module_free_vars_excludes_scheme_quantifiers() {
        // Module exports `id: ∀a. a → a`. The `a` is bound by the scheme
        // and must NOT show up as a free var of the enclosing module type.
        let var_a = TVarName::Flex(7);
        let id_scheme = TypeScheme::poly(
            vec![var_a.clone()],
            Type::simple_func(vec![Type::Var(var_a.clone())], Type::Var(var_a.clone())),
        );
        let mut exports = BTreeMap::new();
        exports.insert("id".to_string(), id_scheme);
        let module_ty = Type::module("./id.js", exports);

        let free = module_ty.free_vars();
        assert!(
            !free.contains(&var_a),
            "scheme-bound variable leaked into module's free_vars"
        );

        // A truly free variable inside an export's body should still count.
        let escaped = TVarName::Flex(99);
        let leaky_scheme = TypeScheme::mono(Type::Var(escaped.clone()));
        let mut exports2 = BTreeMap::new();
        exports2.insert("k".to_string(), leaky_scheme);
        let module_ty2 = Type::module("./k.js", exports2);
        assert!(module_ty2.free_vars().contains(&escaped));
    }

    #[test]
    fn test_module_equality_is_nominal_by_source() {
        let a = Type::module("./a.js", BTreeMap::new());
        let a2 = Type::module("./a.js", BTreeMap::new());
        let b = Type::module("./b.js", BTreeMap::new());
        assert_eq!(a, a2);
        assert_ne!(a, b);
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
