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
#[derive(Clone, Debug)]
pub struct FuncParam {
    pub presence: Presence,
    pub ty: Type,
    /// The parameter's name, when known (Python `def`/lambda, `.pyi`).
    /// Pure call-resolution metadata for keyword arguments — it is
    /// **deliberately excluded from `PartialEq`/`Eq` and from
    /// unification**, because a positional-or-keyword parameter's name
    /// never affects structural compatibility (`(x: A) => B` ≡ `(A) => B`,
    /// per PEP 484). It is the *label* half of the Garrigue 1994 model
    /// whose *optionality* half is `presence`.
    pub name: Option<String>,
}

impl PartialEq for FuncParam {
    fn eq(&self, other: &Self) -> bool {
        self.presence == other.presence && self.ty == other.ty
    }
}

impl Eq for FuncParam {}

impl FuncParam {
    /// Required parameter — the default. Equivalent to the
    /// pre-Shape-B representation where every parameter was just a
    /// `Type`.
    pub fn required(ty: Type) -> Self {
        FuncParam {
            presence: Presence::Pre,
            ty,
            name: None,
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
            name: None,
        }
    }

    /// Attach a parameter name (call-resolution metadata for keyword
    /// arguments). Chainable on the other constructors.
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
}

/// One entry in a `RowType`'s props map: presence, type, and how the
/// object holds the property.
///
/// A field written in source has `presence = Pre`. A field declared
/// optional in an annotation (`x?: T`) is assigned a fresh presence
/// variable. `Abs` only arises through unification when a closed row
/// constrains a polymorphic side's missing field.
///
/// Two more presences say how the object holds the property, each `Pre`,
/// `Abs` or a variable unified like a presence: `writable`, whether a
/// store to it is allowed (`Abs` for a getter, or a class's method), and
/// `own`, whether it is the object's own property, which a spread copies
/// (`Abs` for a class's method or getter, on its prototype). A read
/// leaves both as fresh variables, so it accepts any property; a store
/// needs `writable`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldEntry {
    pub presence: Presence,
    pub ty: Type,
    pub writable: Presence,
    pub own: Presence,
}

impl FieldEntry {
    /// Field is definitely present with the given type, an own property
    /// that holds a value. The common case for object literals and most
    /// stub declarations.
    pub fn pre(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Pre,
            ty,
            writable: Presence::Pre,
            own: Presence::Pre,
        }
    }

    /// Field is presence-polymorphic — caller may omit or supply it.
    pub fn optional(pvar: PVarName, ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Var(pvar),
            ty,
            writable: Presence::Pre,
            own: Presence::Pre,
        }
    }

    /// Field is definitely absent. Mostly produced by unification, not
    /// constructed directly.
    pub fn absent(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Abs,
            ty,
            writable: Presence::Pre,
            own: Presence::Pre,
        }
    }

    /// An own property with only a getter (`get x() {…}`): read, not
    /// stored to; a spread copies what it gives.
    pub fn getter(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Pre,
            ty,
            writable: Presence::Abs,
            own: Presence::Pre,
        }
    }

    /// A class's method or getter, on its prototype: read, not stored
    /// to, and not copied by a spread.
    pub fn proto(ty: Type) -> Self {
        FieldEntry {
            presence: Presence::Pre,
            ty,
            writable: Presence::Abs,
            own: Presence::Abs,
        }
    }

    /// The same flags, at another type.
    pub fn with_ty(&self, ty: Type) -> Self {
        FieldEntry {
            presence: self.presence.clone(),
            ty,
            writable: self.writable.clone(),
            own: self.own.clone(),
        }
    }

    /// Each presence mapped by `f`, the type by `g`.
    pub fn map(&self, f: &mut dyn FnMut(&Presence) -> Presence, ty: Type) -> Self {
        FieldEntry {
            presence: f(&self.presence),
            ty,
            writable: f(&self.writable),
            own: f(&self.own),
        }
    }

    /// The presences: whether it is there, then the two flags.
    pub fn presences(&self) -> [&Presence; 3] {
        [&self.presence, &self.writable, &self.own]
    }
}

/// Type class names for constraint-based polymorphism.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClassName {
    /// `Plus a`: `a + a` is an `a`, a `Number` or a `String`.
    Plus,
    /// Indexable class: types that support indexed access.
    /// Indexable(container, index, element)
    Indexable,
    /// `IndexWrite c`: an element of `c` can be stored (`c[i] = v`): an
    /// array, a typed array, a map or an object, not a string (whose
    /// characters are read-only: a store throws a `TypeError` in strict
    /// code).
    IndexWrite,
    /// `FieldWrite r "p"`: the property `p` of `r` can be stored (`r.p =
    /// v`): an object's property that takes stores (not a getter, nor a
    /// class's method), not an array's, a string's or a function's
    /// (whose properties are built in).
    FieldWrite,
    /// Property access on a value whose type isn't known yet:
    /// `HasProp(receiver, "name", result)` says reading `.name` from a
    /// `receiver` gives a `result`. The name is carried as a string
    /// literal type. Resolved once the receiver's type is known — a
    /// string or array (its built-in property), an object (its field) —
    /// and otherwise generalised with the function that made it, so
    /// `function f(s) { return s.length; }` accepts strings, arrays and
    /// `{length: …}` objects alike. The receiver determines the result
    /// (a functional dependency, like `Indexable`'s container).
    HasProp,
    /// `Inject τ T`: a `τ` is accepted where the sum `T` (a
    /// [`Type::Maybe`]) is expected — `τ` is `T` itself, its nothing,
    /// or something its value accepts. Posed when `τ` is still a
    /// variable, and resolved once it is known (the model's waiting
    /// constraint `Inject`).
    Inject,
    /// `Strip τ σ`: `σ` is what a `τ` holds besides nothing — the
    /// value of a sum `Maybe(_, σ)`, or `τ` itself when it is not a
    /// sum. Posed by `x ?? d` and `x != null` on an `x` whose type is
    /// still a variable, and resolved once it is known (the model's
    /// `Strip`). `τ` determines `σ`.
    Strip,
    /// `Spread operand so_far result`: an object literal spreading an
    /// `operand` over the row `so_far` of the fields before it is a
    /// `result`. Posed when the operand's type is still a variable, and
    /// decided once it is known, field by field as a spread of a known
    /// object is (the model's waiting `Merge`). The operand and `so_far`
    /// determine `result`.
    Spread,
}

/// Type class predicate: a constraint that a type must satisfy.
#[derive(Clone, Debug)]
pub struct TypePred {
    pub class: ClassName,
    pub types: Vec<Type>,
    /// Where the predicate was posed, once it is part of a scheme (the
    /// `o.name` read inside a generic function): an instance posed at a
    /// call that fails is reported there, and "required by" here.
    /// Not part of the predicate's identity.
    pub origin: Option<crate::span::Span>,
}

impl PartialEq for TypePred {
    fn eq(&self, other: &Self) -> bool {
        self.class == other.class && self.types == other.types
    }
}

impl Eq for TypePred {}

impl TypePred {
    /// `Plus t`: `+` on `t`.
    pub fn plus(ty: Type) -> Self {
        TypePred {
            class: ClassName::Plus,
            types: vec![ty],
            origin: None,
        }
    }

    pub fn indexable(container: Type, index: Type, element: Type) -> Self {
        TypePred {
            class: ClassName::Indexable,
            types: vec![container, index, element],
            origin: None,
        }
    }

    /// `FieldWrite r "p"`: the property `p` of an `r` can be stored.
    pub fn field_write(receiver: Type, name: &str) -> Self {
        TypePred {
            class: ClassName::FieldWrite,
            types: vec![receiver, Type::Literal(LitValue::String(name.to_string()))],
            origin: None,
        }
    }

    /// The receiver and the property of a [`Self::field_write`] predicate.
    pub fn as_field_write(&self) -> Option<(&Type, &str)> {
        match (self.class, self.types.as_slice()) {
            (ClassName::FieldWrite, [recv, Type::Literal(LitValue::String(name))]) => {
                Some((recv, name.as_str()))
            }
            _ => None,
        }
    }

    pub fn index_write(container: Type) -> Self {
        TypePred {
            class: ClassName::IndexWrite,
            types: vec![container],
            origin: None,
        }
    }

    pub fn has_prop(receiver: Type, name: &str, result: Type) -> Self {
        TypePred {
            class: ClassName::HasProp,
            types: vec![
                receiver,
                Type::Literal(LitValue::String(name.to_string())),
                result,
            ],
            origin: None,
        }
    }

    /// `Inject sub sup`: a `sub` is accepted where the sum `sup` is.
    pub fn inject(sub: Type, sup: Type) -> Self {
        TypePred {
            class: ClassName::Inject,
            types: vec![sub, sup],
            origin: None,
        }
    }

    /// `Strip ty sigma`: `sigma` is what a `ty` holds besides nothing.
    pub fn strip(ty: Type, sigma: Type) -> Self {
        TypePred {
            class: ClassName::Strip,
            types: vec![ty, sigma],
            origin: None,
        }
    }

    /// `Spread operand so_far result`: `{...so_far, ...operand}` is a
    /// `result`.
    pub fn spread(operand: Type, so_far: Type, result: Type) -> Self {
        TypePred {
            class: ClassName::Spread,
            types: vec![operand, so_far, result],
            origin: None,
        }
    }

    /// `HasProp` for a method call `receiver.name(…)`: also carries the
    /// call's `this`, which is bound to the receiver (unrolled, if it's
    /// a nominal type, as a call on a known receiver does) when the
    /// constraint is resolved.
    pub fn has_method(receiver: Type, name: &str, result: Type, this: Type) -> Self {
        let mut pred = Self::has_prop(receiver, name, result);
        pred.types.push(this);
        pred
    }

    /// `(receiver, name, result)` of a `HasProp` predicate.
    pub fn as_has_prop(&self) -> Option<(&Type, &str, &Type)> {
        match (self.class, self.types.as_slice()) {
            (ClassName::HasProp, [recv, Type::Literal(LitValue::String(name)), result, ..]) => {
                Some((recv, name.as_str(), result))
            }
            _ => None,
        }
    }

    /// The call's `this` of a [`Self::has_method`] predicate.
    pub fn method_this(&self) -> Option<&Type> {
        match (self.class, self.types.as_slice()) {
            (ClassName::HasProp, [_, _, _, this]) => Some(this),
            _ => None,
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

/// Whether a number is a *safe* integer — no fractional
/// part, `|n| ≤ 2^53` (every integer in that range is a distinct double),
/// and not `-0` (which prints, and divides, differently from `0`).
pub fn is_safe_int(n: f64) -> bool {
    n.is_finite()
        && n.fract() == 0.0
        && n.abs() <= 9007199254740992.0
        && !(n == 0.0 && n.is_sign_negative())
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
            props: props
                .into_iter()
                .map(|(k, v)| (k, FieldEntry::pre(v)))
                .collect(),
            tail: RowTail::Closed,
        }
    }

    /// Create a closed row from a fully-specified entry map.
    pub fn closed_entries(props: BTreeMap<PropName, FieldEntry>) -> Self {
        RowType {
            props,
            tail: RowTail::Closed,
        }
    }

    /// Create an open row where every listed property is definitely
    /// present. Tail variable carries the unmentioned fields.
    pub fn open(props: BTreeMap<PropName, Type>, var: TVarName) -> Self {
        RowType {
            props: props
                .into_iter()
                .map(|(k, v)| (k, FieldEntry::pre(v)))
                .collect(),
            tail: RowTail::Open(var),
        }
    }

    /// Create an open row from a fully-specified entry map.
    pub fn open_entries(props: BTreeMap<PropName, FieldEntry>, var: TVarName) -> Self {
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
    /// JavaScript number type (all numbers are f64). Whether a number is
    /// an integer is not a matter of types: a code generator works it out
    /// (the Go backend's integer analysis).
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
    /// What `new` gives a class's constructor as `this`, which nothing
    /// else gives: a class called without `new` is rejected, as
    /// JavaScript throws.
    NewTarget,
    /// An arrow function's `this`: it has none of its own (the enclosing
    /// function's is in scope), so a call on any receiver, or on none,
    /// gives it nothing; and an arrow function isn't a constructor, so
    /// it never meets `NewTarget` (`new` on one throws a `TypeError`).
    ArrowThis,

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

    /// Tuple (product) type: `(T0, T1, …)`. Fixed arity, heterogeneous.
    /// Unifies by structural congruence (same length, components unified
    /// pairwise); distinct arities are distinct types — there is no width
    /// subtyping. Element access is by *literal* index (resolved in
    /// inference), not via the homogeneous `Indexable` class. Note
    /// `tuple[T, ...]` (homogeneous, variadic) maps to `Array<T>`, not to
    /// this constructor.
    Tuple(Vec<Type>),

    /// Named recursive type reference: μα.T
    /// The TypeId refers to a type definition, and the Vec<Type> are type arguments.
    Named(TypeId, Vec<Type>),

    /// Singleton literal type, e.g. `"circle"` or `42` or `true`.
    Literal(LitValue),

    /// Untagged union type: `T1 | T2 | ...`. Always normalised so that
    /// members are deduplicated and sorted, and none is `Null` or
    /// `Undefined` (those make a [`Type::Maybe`]). A union is only
    /// constructed via [`Type::union`] which enforces the invariants.
    Union(Vec<Type>),

    /// A sum of nothing and a value: `Nullable T` (`T | Null`) holds `null`
    /// or a `T`, `Optional T` (`T | Undefined`) holds `undefined` or a
    /// `T`. It is tagged: it unifies only with a sum of the same nothing,
    /// so a `T` or a `null` is one only where it is checked against one
    /// (an annotation, a parameter's type: `subsume`), and it is taken
    /// apart by a test for nothing (`x != null`, `x ?? d`), which leaves
    /// the `T` (`ClassName::Strip`). Branches don't join into one: `c ? x
    /// : null` is an error unless an annotation says what it is. This is
    /// the Lean model's `Ty.maybe` (`lean/Inty/Types.lean`).
    Maybe(Nothing, Box<Type>),

    /// ES module namespace: the type of `ns` after `import * as ns from
    /// "./mod.js";`. Carries one type *scheme* per export so member access
    /// (`ns.foo`) instantiates polymorphism per use, and is identified by
    /// the canonicalised source path so two imports of the same file get
    /// the same type and two imports of different files don't unify even
    /// when their export shapes happen to coincide. See `modules.md` §2.
    Module(ModuleType),

    /// A JavaScript typed array (`Int32Array`, `Uint8Array`,
    /// `Float64Array`): a fixed-length array of one machine number type.
    /// Nominal and without parameters; its elements are
    /// [`TypedArrayKind::element`].
    TypedArray(TypedArrayKind),

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

/// What a [`Type::Maybe`] holds besides its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Nothing {
    Null,
    Undefined,
}

impl Nothing {
    /// The type whose only value is this nothing.
    pub fn ty(self) -> Type {
        match self {
            Nothing::Null => Type::Null,
            Nothing::Undefined => Type::Undefined,
        }
    }

    /// The nothing a type's only value is, if it is `Null` or `Undefined`.
    pub fn of(ty: &Type) -> Option<Nothing> {
        match ty {
            Type::Null => Some(Nothing::Null),
            Type::Undefined => Some(Nothing::Undefined),
            _ => None,
        }
    }
}

/// Which typed array a [`Type::TypedArray`] is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TypedArrayKind {
    Int32,
    Uint8,
    Float32,
    Float64,
}

impl TypedArrayKind {
    pub const ALL: [TypedArrayKind; 4] = [
        TypedArrayKind::Int32,
        TypedArrayKind::Uint8,
        TypedArrayKind::Float32,
        TypedArrayKind::Float64,
    ];

    /// The JavaScript constructor's name, which is also the type's.
    pub fn name(self) -> &'static str {
        match self {
            TypedArrayKind::Int32 => "Int32Array",
            TypedArrayKind::Uint8 => "Uint8Array",
            TypedArrayKind::Float32 => "Float32Array",
            TypedArrayKind::Float64 => "Float64Array",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|k| k.name() == name)
    }

    /// The type of an element as read, and as accepted by a store (an
    /// integer array converts what it stores, as JavaScript does: ToInt32
    /// or ToUint8, wrapping).
    pub fn element(self) -> Type {
        Type::Number
    }
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

impl ModuleType {
    /// Build a module namespace from `source` (its identity) and an
    /// iterator of `(export-name, scheme)` pairs. The single shared
    /// constructor used by every frontend's import resolution, so a module
    /// namespace has one representation across JavaScript / Python / Lua.
    pub fn from_exports(
        source: impl Into<String>,
        exports: impl IntoIterator<Item = (String, TypeScheme)>,
    ) -> Self {
        ModuleType {
            source: source.into(),
            exports: exports.into_iter().collect(),
        }
    }
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

    /// Create a static function type (no `this`) with a fully-
    /// specified parameter list, wrapped in a callable row. Used by
    /// stdlib declarations that mark trailing parameters optional
    /// via `FuncParam::optional(fresh_pvar, ty)`.
    pub fn simple_func_with_params(params: Vec<FuncParam>, ret: Type) -> Self {
        Self::wrap_callable(Type::raw_func_with_params(None, params, ret))
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

    /// Create a tuple (product) type from its component types.
    pub fn tuple(elems: Vec<Type>) -> Self {
        Type::Tuple(elems)
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
    /// * Recurses through what holds a value as it is: a sum (`Maybe`),
    ///   a tuple, and a `Union` of literals (each member, then
    ///   re-normalises so that `"a" | "b"` widens to `String` rather than
    ///   the awkward `String | String`). Any other union was declared and
    ///   is left alone.
    /// * Stops at what may be shared: a record, an array, a map, a promise
    ///   and a function are left alone. Their type is the one every alias
    ///   has, so widening a field of one (`let w = v` with `v: {k: "a"}`)
    ///   would let a write through the copy (`w.k = "z"`) break the
    ///   original's. A literal's own parts are widened where it is made
    ///   (an object literal's fields, an array literal's elements, a
    ///   function's returns), so a fresh one has nothing left to widen.
    /// * Type variables, named types, and modules are left alone.
    ///   Widening through a substitution is the substitution's job.
    pub fn widen_fresh_literals(&self) -> Self {
        self.widen_fresh_literals_with(&mut |lit| lit.base_type())
    }

    /// [`Self::widen_fresh_literals`] with the literal's widening given
    /// by `f` (inference widens an integral literal to a fresh variable).
    pub fn widen_fresh_literals_with(&self, f: &mut dyn FnMut(&LitValue) -> Type) -> Self {
        match self {
            Type::Literal(lit) => f(lit),
            Type::Row(_) | Type::Array(_) | Type::Map(_) | Type::Promise(_) | Type::Func { .. } => {
                self.clone()
            }
            Type::Maybe(z, elem) => Type::Maybe(*z, Box::new(elem.widen_fresh_literals_with(f))),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.widen_fresh_literals_with(f))
                    .collect(),
            ),
            // A union of literals (`"a" | "b"`) widens to its base type.
            // Any other union was declared, and stays as it is: widening a
            // discriminated union's tags would make its arms
            // indistinguishable.
            Type::Union(members) if members.iter().all(|m| matches!(m, Type::Literal(_))) => {
                let widened: Vec<Type> = members
                    .iter()
                    .map(|m| m.widen_fresh_literals_with(f))
                    .collect();
                Type::union(widened)
            }
            Type::Union(_) => self.clone(),
            // Primitives, vars, named refs, modules, error: nothing
            // to widen. `Error` is opaque — widening through it
            // would generate noise from a binding that already failed.
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::NewTarget
            | Type::ArrowThis
            | Type::TypedArray(_)
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
    /// - `Null` and `Undefined` members make a sum of the rest
    ///   ([`Type::Maybe`]): `T | Null` is `Nullable T`, and `T | Undefined
    ///   | Null` is `Nullable (Optional T)`.
    pub fn union(members: impl IntoIterator<Item = Type>) -> Self {
        let mut flat: Vec<Type> = Vec::new();
        let (mut null, mut undefined) = (false, false);
        let mut pending: Vec<Type> = members.into_iter().collect();
        while let Some(m) = pending.pop() {
            match m {
                Type::Union(inner) => pending.extend(inner),
                Type::Maybe(z, inner) => {
                    pending.push(z.ty());
                    pending.push(*inner);
                }
                Type::Null => null = true,
                Type::Undefined => undefined = true,
                other => flat.push(other),
            }
        }
        if null || undefined {
            let core = if flat.is_empty() {
                None
            } else {
                Some(Type::union(flat))
            };
            let with_undefined = match (core, undefined) {
                (Some(t), true) => Type::Maybe(Nothing::Undefined, Box::new(t)),
                (Some(t), false) => t,
                (None, true) => Type::Undefined,
                (None, false) => return Type::Null,
            };
            return if null {
                Type::Maybe(Nothing::Null, Box::new(with_undefined))
            } else {
                with_undefined
            };
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

    /// The alternatives a union or a sum holds: a union's members, a
    /// sum's nothing and its value's alternatives, or the type itself.
    /// [`Type::union`] of them is the type again.
    pub fn arms(&self) -> Vec<Type> {
        match self {
            Type::Union(members) => members.clone(),
            Type::Maybe(z, inner) => {
                let mut arms = vec![z.ty()];
                arms.extend(inner.arms());
                arms
            }
            other => vec![other.clone()],
        }
    }

    /// A sum as the union of its arms, sorted as a union's members are,
    /// for printing: `Nullable Number` is `Number | Null`, which reads
    /// back as the same sum.
    pub fn as_printed_union(&self) -> Type {
        let mut arms = self.arms();
        arms.sort_by_key(union_member_sort_key);
        Type::Union(arms)
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

    /// The `typeof` of every value of this type, if it has one (a type
    /// variable, a named type or a union has none).
    pub fn typeof_tag(&self) -> Option<&'static str> {
        match self {
            Type::Number | Type::Literal(LitValue::Number(_)) => Some("number"),
            Type::String | Type::Literal(LitValue::String(_)) => Some("string"),
            Type::Boolean | Type::Literal(LitValue::Bool(_)) => Some("boolean"),
            Type::Undefined => Some("undefined"),
            _ if self.is_func() => Some("function"),
            // (An open row's tail might add a call signature.)
            Type::Row(row) if matches!(row.tail, RowTail::Closed) => Some("object"),
            Type::Array(_) | Type::Tuple(_) | Type::Null => Some("object"),
            _ => None,
        }
    }

    /// Whether this is a sum told apart by `typeof`: a union whose members
    /// each have a `typeof`, no two the same (`Number | String`).
    pub fn is_typeof_sum(&self) -> bool {
        let Type::Union(members) = self else {
            return false;
        };
        let mut seen = Vec::with_capacity(members.len());
        for m in members {
            match m.typeof_tag() {
                Some(t) if !seen.contains(&t) => seen.push(t),
                _ => return false,
            }
        }
        members.len() > 1
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

    /// Ids of the recursive / nominal named types this type mentions
    /// (`Named(id, …)` and recursive row tails), not looking inside their
    /// bodies. Free-variable functions don't look inside named-type bodies
    /// either, so generalisation uses this to find the variables hidden
    /// there.
    pub fn named_ids(&self) -> HashSet<TypeId> {
        let mut ids = HashSet::new();
        self.collect_named_ids(&mut ids);
        ids
    }

    fn collect_named_ids(&self, ids: &mut HashSet<TypeId>) {
        match self {
            Type::Named(id, args) => {
                ids.insert(*id);
                for a in args {
                    a.collect_named_ids(ids);
                }
            }
            Type::Func {
                this_type,
                params,
                ret,
            } => {
                if let Some(t) = this_type {
                    t.collect_named_ids(ids);
                }
                for p in params {
                    p.ty.collect_named_ids(ids);
                }
                ret.collect_named_ids(ids);
            }
            Type::Row(row) => {
                for entry in row.props.values() {
                    entry.ty.collect_named_ids(ids);
                }
                if let RowTail::Recursive(id, args) = &row.tail {
                    ids.insert(*id);
                    for a in args {
                        a.collect_named_ids(ids);
                    }
                }
            }
            Type::Array(e) | Type::Promise(e) | Type::Map(e) | Type::Maybe(_, e) => {
                e.collect_named_ids(ids)
            }
            Type::Tuple(ts) | Type::Union(ts) => {
                for t in ts {
                    t.collect_named_ids(ids);
                }
            }
            _ => {}
        }
    }

    fn collect_free_pvars(&self, pvars: &mut HashSet<PVarName>) {
        match self {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::NewTarget
            | Type::ArrowThis
            | Type::TypedArray(_)
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
                    for p in entry.presences() {
                        if let Presence::Var(v) = p {
                            pvars.insert(v.clone());
                        }
                    }
                    entry.ty.collect_free_pvars(pvars);
                }
                if let RowTail::Recursive(_, args) = &row.tail {
                    for a in args {
                        a.collect_free_pvars(pvars);
                    }
                }
            }
            Type::Array(elem) | Type::Promise(elem) | Type::Map(elem) | Type::Maybe(_, elem) => {
                elem.collect_free_pvars(pvars);
            }
            Type::Named(_, args) => {
                for a in args {
                    a.collect_free_pvars(pvars);
                }
            }
            Type::Tuple(elems) => {
                for e in elems {
                    e.collect_free_pvars(pvars);
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
            | Type::NewTarget
            | Type::ArrowThis
            | Type::TypedArray(_)
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
            Type::Maybe(_, inner) => inner.collect_free_vars(vars),
            Type::Promise(inner) => inner.collect_free_vars(vars),
            Type::Map(value) => value.collect_free_vars(vars),

            Type::Tuple(elems) => {
                for e in elems {
                    e.collect_free_vars(vars);
                }
            }

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
    pub fn poly_with_presence(vars: Vec<TVarName>, pvars: Vec<PVarName>, ty: Type) -> Self {
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
        Type::NewTarget => (5, "new.target".to_string()),
        Type::ArrowThis => (5, "arrow.this".to_string()),
        Type::TypedArray(k) => (19, k.name().to_string()),
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
        // A sum is never a union's member (its arms are), but sort it by
        // its value's key all the same.
        Type::Maybe(_, inner) => (20, union_member_sort_key(inner).1),
        Type::Map(v) => (12, union_member_sort_key(v).1),
        Type::Promise(v) => (13, union_member_sort_key(v).1),
        Type::Named(id, _) => (14, format!("{}", id)),
        Type::Union(_) => (15, String::new()),
        Type::Module(m) => (16, m.source.clone()),
        Type::Error => (17, String::new()),
        Type::Tuple(elems) => (
            18,
            elems
                .iter()
                .map(|e| union_member_sort_key(e).1)
                .collect::<Vec<_>>()
                .join(","),
        ),
    }
}

/// A named type definition, used for two distinct purposes that share
/// the `Type::Named(id, args)` carrier:
///
/// 1. **Equi-recursive types** (`nominal == false`). Auto-generated by
///    unification when it detects a cycle (method chaining / `return
///    this`). These are *transparent*: unification unrolls them to
///    `body`, so a recursive named type unifies structurally with its
///    expansion. This is what makes builder chains type.
/// 2. **Nominal types** (`nominal == true`). Declared by the user (or by
///    a frontend lowering a `class`). These carry **brand identity**:
///    two nominal types unify iff their `id` matches (arguments
///    invariantly), and a nominal type never unrolls during unification —
///    so `UserId` (= `Number`) stays distinct from `Number` and from any
///    other nominal with the same representation. Field access and
///    operators still see *through* to `body` (transparent access); only
///    *identity* is opaque. See `docs/pyi-import-mapping.md` §8.
#[derive(Clone, Debug)]
pub struct TypeDef {
    /// Unique identifier for this type definition.
    pub id: TypeId,
    /// Type parameters for the definition.
    pub params: Vec<TVarName>,
    /// The type body. For a recursive def it may reference the type via
    /// `Named(id, ...)`; for a nominal def it is the representation
    /// (e.g. the instance row of a class, or a scalar for a newtype).
    pub body: Type,
    /// Whether this is a nominal (branded) type rather than an
    /// equi-recursive reference. Drives unification: nominal types do
    /// not unroll for identity.
    pub nominal: bool,
    /// User-facing name, when declared (used by diagnostics). Recursive
    /// defs are anonymous (`None`).
    pub name: Option<String>,
}

impl TypeDef {
    /// An equi-recursive type definition (anonymous, transparent).
    pub fn recursive(id: TypeId, params: Vec<TVarName>, body: Type) -> Self {
        TypeDef {
            id,
            params,
            body,
            nominal: false,
            name: None,
        }
    }

    /// A declared nominal (branded) type definition.
    pub fn nominal(id: TypeId, name: impl Into<String>, params: Vec<TVarName>, body: Type) -> Self {
        TypeDef {
            id,
            params,
            body,
            nominal: true,
            name: Some(name.into()),
        }
    }
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
