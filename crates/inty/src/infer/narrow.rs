//! Flow-sensitive narrowing.
//!
//! Narrowing refines the type of an identifier (or a property path off an
//! identifier) inside a control-flow branch where the predicate that
//! gates the branch tells us something about that value.
//!
//! The single most important pattern is the discriminated union dispatch:
//!
//! ```text
//! function area(shape) {                   // shape : {kind:"circle", r:Number}
//!                                          //       | {kind:"square", s:Number}
//!   if (shape.kind === "circle") {
//!     return Math.PI * shape.r * shape.r;  // shape narrowed to circle here
//!   }
//! }
//! ```
//!
//! Only *stable* bindings are narrowed: ones never written after their
//! initialiser (`ast::resolve`). A fact about a stable binding's value
//! holds for the rest of its scope, on every path and inside every
//! closure, because the value cannot change; nothing ever has to end a
//! narrowing.
//!
//! Narrowing is not a substitution. It only lives in the environment passed
//! down into a branch — a fact that holds *here*, not everywhere. Sharing
//! it with the unification substitution would over-narrow at sibling
//! branches.

use crate::span::Span;
use crate::types::{LitValue, PropName, RowTail, RowType, Type, TypeId, TypeScheme};

use super::env::TypeEnv;
use crate::ast::SourceLanguage as Language;
use crate::ast::{BinOp, Expr, Literal, UnaryOp};

/// A `Path` names something that can be narrowed: a local identifier, or
/// a (possibly nested) property access off one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Path {
    /// A bare identifier in the environment, and where it occurs (which
    /// is how its binding is found).
    Ident(String, Span),
    /// A property access: `<parent>.<prop>`.
    Member(Box<Path>, PropName),
}

impl Path {
    /// The root identifier of this path. All paths bottom out at an
    /// identifier; it's the one whose binding gets refined.
    pub fn root_ident(&self) -> &str {
        match self {
            Path::Ident(n, _) => n.as_str(),
            Path::Member(p, _) => p.root_ident(),
        }
    }
}

/// A predicate to apply to the value at a `Path`.
///
/// Comparisons are read by the *type* of the other operand, never its
/// name: `x === undefined` narrows because `undefined` has the singleton
/// type `Undefined`, and a local `const undefined = 0` doesn't.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Narrowing {
    /// `typeof <path> === "string-literal"`.
    IsTypeof(String),
    /// `typeof <path> !== "string-literal"`.
    IsNotTypeof(String),
    /// `<path> === e` where `e` has a singleton type (`Null`,
    /// `Undefined` or a literal): the value is that one value.
    Is(Type),
    /// `<path> !== e`, `e` of a singleton type.
    IsNot(Type),
    /// `<path> == e` in JavaScript with `e : Null` or `e : Undefined`:
    /// `null` or `undefined` (loose equality is exact here).
    Nullish,
    /// `<path> != e`, likewise.
    NotNullish,
    /// Python `<path> == e`, `e` of a singleton type. `==` calls
    /// `__eq__`, which an object may define to say anything, so an
    /// object member always stays; a primitive stays if it can be `e`.
    PyEq(Type),
    /// Python `<path> != e`: only the singleton itself is ruled out
    /// (built-in values compare as expected with `!=`).
    PyNotEq(Type),
    /// `isinstance(<path>, C)` — the value is an instance of the class
    /// whose nominal brand is `TypeId`. Filters a union of `Named` brands
    /// to the matching member.
    IsInstance(TypeId),
    /// Negation of [`Narrowing::IsInstance`] (the `else` branch).
    IsNotInstance(TypeId),
    /// `<path>` tested for truth, as in `if (x)`.
    Truthy,
    /// `!<path>`.
    Falsy,
}

impl Narrowing {
    /// Negate the predicate. Used when narrowing the *else* branch with
    /// the negation of the if-test's narrowing.
    pub fn negate(&self) -> Narrowing {
        match self {
            Narrowing::IsTypeof(s) => Narrowing::IsNotTypeof(s.clone()),
            Narrowing::IsNotTypeof(s) => Narrowing::IsTypeof(s.clone()),
            Narrowing::Is(t) => Narrowing::IsNot(t.clone()),
            Narrowing::IsNot(t) => Narrowing::Is(t.clone()),
            Narrowing::Nullish => Narrowing::NotNullish,
            Narrowing::NotNullish => Narrowing::Nullish,
            Narrowing::PyEq(t) => Narrowing::PyNotEq(t.clone()),
            Narrowing::PyNotEq(t) => Narrowing::PyEq(t.clone()),
            Narrowing::IsInstance(id) => Narrowing::IsNotInstance(*id),
            Narrowing::IsNotInstance(id) => Narrowing::IsInstance(*id),
            Narrowing::Truthy => Narrowing::Falsy,
            Narrowing::Falsy => Narrowing::Truthy,
        }
    }

    /// Whether a branch this narrowing makes dead is worth a warning.
    /// Defensive null checks and truth tests of values that can't be
    /// falsy are ordinary code, so those stay quiet.
    pub fn warns_when_dead(&self) -> bool {
        match self {
            Narrowing::IsTypeof(_)
            | Narrowing::IsNotTypeof(_)
            | Narrowing::IsInstance(_)
            | Narrowing::IsNotInstance(_) => true,
            Narrowing::Is(t) | Narrowing::IsNot(t) => matches!(t, Type::Literal(_)),
            _ => false,
        }
    }
}

/// Whether `ty` has exactly one value, so that `===` against a value of
/// it says which value, and `!==` rules it out. (`NaN` is its own
/// exception: it equals nothing.)
pub fn is_singleton(ty: &Type) -> bool {
    match ty {
        Type::Null | Type::Undefined => true,
        Type::Literal(LitValue::Number(n)) => !n.is_nan(),
        Type::Literal(_) => true,
        _ => false,
    }
}

/// What a test tells us: the narrowings that hold when it is true, and
/// those that hold when it is false.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Facts {
    pub when_true: Vec<(Path, Narrowing)>,
    pub when_false: Vec<(Path, Narrowing)>,
}

impl Facts {
    fn one(path: Path, narrowing: Narrowing) -> Facts {
        Facts {
            when_false: vec![(path.clone(), narrowing.negate())],
            when_true: vec![(path, narrowing)],
        }
    }

    fn swap(self) -> Facts {
        Facts {
            when_true: self.when_false,
            when_false: self.when_true,
        }
    }
}

/// The facts a test establishes. `atom` recognises the comparisons, which
/// need the checker (the other operand's type, `isinstance`'s class).
///
/// - a comparison `atom` understands;
/// - `<path>` alone: truthy when true, falsy when false;
/// - `!e`: the facts of `e`, swapped;
/// - `a && b`: when true, both sides' true facts (`b` only runs once
///   `a` held); when false, nothing we can pin to one side;
/// - `a || b`: when false, both sides' false facts; when true, nothing.
pub fn test_facts(test: &Expr, atom: &dyn Fn(&Expr) -> Option<(Path, Narrowing)>) -> Facts {
    if let Some((path, narrowing)) = atom(test) {
        return Facts::one(path, narrowing);
    }
    match test {
        Expr::Unary {
            op: UnaryOp::Not,
            argument,
            ..
        } => test_facts(argument, atom).swap(),
        Expr::Binary {
            op: BinOp::And,
            left,
            right,
            ..
        } => {
            let mut l = test_facts(left, atom);
            let r = test_facts(right, atom);
            l.when_true.extend(r.when_true);
            Facts {
                when_true: l.when_true,
                when_false: Vec::new(),
            }
        }
        Expr::Binary {
            op: BinOp::Or,
            left,
            right,
            ..
        } => {
            let mut l = test_facts(left, atom);
            let r = test_facts(right, atom);
            l.when_false.extend(r.when_false);
            Facts {
                when_true: Vec::new(),
                when_false: l.when_false,
            }
        }
        _ => match path_from_expr(test) {
            Some(path) => Facts::one(path, Narrowing::Truthy),
            None => Facts::default(),
        },
    }
}

/// Apply a narrowing predicate to an environment, returning a refined
/// copy. The binding for the root identifier is replaced with one whose
/// type reflects the predicate; other bindings are untouched.
///
/// Only a stable binding (see the module docs) is narrowed; for any other
/// the input env is returned unchanged, as it is when the root isn't
/// bound at all (the checker reports that use elsewhere).
///
/// The binding's type is normalised through the current substitution
/// before refinement — without this, a parameter bound to a fresh
/// variable that *happens* to be substituted to a union would never
/// narrow, because the env still holds the bare variable.
pub fn apply_narrowing(
    state: &super::state::InferState,
    env: &TypeEnv,
    path: &Path,
    narrowing: &Narrowing,
) -> TypeEnv {
    let Path::Ident(name, span) = root_of(path) else {
        unreachable!("a path is rooted at an identifier")
    };
    if !state.resolution.stable_at(*span, name) {
        return env.clone();
    }
    narrow_binding(state, env, path, narrowing)
}

/// Whether `narrowing` leaves the value at `path` no possible type: the
/// test can't come out this way, so the branch it guards is dead.
pub fn narrowing_is_dead(
    state: &super::state::InferState,
    env: &TypeEnv,
    path: &Path,
    narrowing: &Narrowing,
) -> bool {
    refinement(state, env, path, narrowing)
        .is_some_and(|(_, before, after)| after.is_never() && !before.is_never())
}

fn root_of(path: &Path) -> &Path {
    match path {
        Path::Member(p, _) => root_of(p),
        ident => ident,
    }
}

/// [`apply_narrowing`] without the stability check.
///
/// A narrowing that leaves no possible type (a branch the test rules
/// out) keeps the declared type instead: the branch is dead, and any type
/// is sound for it, but `never` would make an inexact predicate table
/// unsound rather than merely imprecise. (The checker warns about the
/// dead branch; see [`narrowing_is_dead`].)
fn narrow_binding(
    state: &super::state::InferState,
    env: &TypeEnv,
    path: &Path,
    narrowing: &Narrowing,
) -> TypeEnv {
    match refinement(state, env, path, narrowing) {
        Some((key, _, after)) if !after.is_never() => env.narrow(&key, TypeScheme::mono(after)),
        _ => env.clone(),
    }
}

/// The binding `path` is rooted at, its type, and its type refined by
/// `narrowing`; `None` when nothing is ruled out.
fn refinement(
    state: &super::state::InferState,
    env: &TypeEnv,
    path: &Path,
    narrowing: &Narrowing,
) -> Option<(super::env::Key, Type, Type)> {
    let Path::Ident(name, span) = root_of(path) else {
        unreachable!("a path is rooted at an identifier")
    };
    let key = state.key_of(*span, name);
    let scheme = env.lookup_key(&key)?.scheme.clone();

    // We only narrow monomorphic bindings. A polymorphic binding (a let
    // function) wouldn't typically be the target of a narrowing — the
    // refinements we model don't apply to type schemes — and trying to
    // refine inside a quantifier would be unsound.
    if !scheme.is_mono() {
        return None;
    }

    let original_ty = state.apply_subst(scheme.ty());
    let exposed = expose_named(state, &original_ty);
    let new_ty = refine_at_path(&exposed, &path_steps(path), narrowing, state.language);
    // Nothing ruled out: leave the binding (and a named type) alone.
    (new_ty != exposed).then_some((key, exposed, new_ty))
}

/// A named (recursive) type unrolled one step when it is a union, so
/// narrowing can pick its members; a union's named members likewise.
fn expose_named(state: &super::state::InferState, ty: &Type) -> Type {
    let unroll = |t: &Type| match t {
        Type::Named(id, args) if !state.is_nominal_type(*id) => match state.unroll_named(*id, args)
        {
            Some(u @ Type::Union(_)) => u,
            _ => t.clone(),
        },
        _ => t.clone(),
    };
    match ty {
        Type::Union(members) => Type::union(members.iter().map(unroll).collect::<Vec<_>>()),
        _ => unroll(ty),
    }
}

/// Decompose a path into a list of property steps below the root. The
/// first element of the returned vec is the property closest to the root.
fn path_steps(path: &Path) -> Vec<PropName> {
    let mut steps = Vec::new();
    let mut cur = path;
    loop {
        match cur {
            Path::Ident(..) => {
                steps.reverse();
                return steps;
            }
            Path::Member(parent, prop) => {
                steps.push(prop.clone());
                cur = parent;
            }
        }
    }
}

/// Refine `ty` so that the value at the property-access steps below the
/// root satisfies `narrowing`. Empty `steps` means refine the root value
/// directly; non-empty steps means filter union members at the root by
/// what the predicate says about the (possibly nested) sub-property.
fn refine_at_path(ty: &Type, steps: &[PropName], narrowing: &Narrowing, lang: Language) -> Type {
    if steps.is_empty() {
        return refine_type(ty, narrowing, lang);
    }

    // We have nested member accesses. The interesting cases are:
    //  - the root type is a union of rows with a discriminator field —
    //    keep only the members whose discriminator field is compatible
    //    with the narrowing;
    //  - the root type is a single row — refine the field in place;
    //  - the root type is something else — leave alone.
    match ty {
        Type::Union(members) => {
            let kept: Vec<Type> = members
                .iter()
                .filter(|m| member_property_compatible(m, steps, narrowing, lang))
                .cloned()
                .collect();
            // If we eliminated nothing, the result is the same union; if
            // we eliminated everything, the branch is unreachable and we
            // collapse to `never` (the empty union).
            Type::union(kept)
        }
        Type::Row(_) => {
            if member_property_compatible(ty, steps, narrowing, lang) {
                ty.clone()
            } else {
                Type::never()
            }
        }
        // For variables and other types, we don't yet know the shape;
        // the narrowing will become a no-op until the variable is solved.
        _ => ty.clone(),
    }
}

/// Refine a type with a top-level (non-property) narrowing.
fn refine_type(ty: &Type, narrowing: &Narrowing, lang: Language) -> Type {
    match ty {
        Type::Union(members) => {
            let kept: Vec<Type> = members
                .iter()
                .filter(|m| member_compatible(m, narrowing, lang))
                .map(|m| refine_type(m, narrowing, lang))
                .collect();
            Type::union(kept)
        }
        _ => {
            if !member_compatible(ty, narrowing, lang) {
                return Type::never();
            }
            // For positive narrowings, sharpen the type when possible
            // (e.g. a String narrowed by `=== "a"` becomes `Literal("a")`).
            match narrowing {
                Narrowing::Is(Type::Literal(lit))
                    if matches!(ty, Type::String | Type::Number | Type::Boolean)
                        || matches!(
                            (ty, lit),
                            (Type::Int, LitValue::Number(n)) if crate::types::is_safe_int(*n)
                        ) =>
                {
                    Type::Literal(lit.clone())
                }
                _ => ty.clone(),
            }
        }
    }
}

/// True if `ty` is consistent with `narrowing` — i.e. it's possible for
/// a value of type `ty` to satisfy the predicate.
fn member_compatible(ty: &Type, narrowing: &Narrowing, lang: Language) -> bool {
    match narrowing {
        Narrowing::IsTypeof(name) => typeof_matches(ty, name),
        Narrowing::IsNotTypeof(name) => !typeof_definitely_matches(ty, name),
        Narrowing::Is(single) => could_be_value(ty, single),
        Narrowing::IsNot(single) => ty != single,
        Narrowing::Nullish => could_be(ty, &Type::Null) || could_be(ty, &Type::Undefined),
        Narrowing::NotNullish => !matches!(ty, Type::Null | Type::Undefined),
        Narrowing::PyEq(single) => {
            could_be_value(ty, single) || !is_primitive(ty) || py_bool_int_equal(ty, single)
        }
        Narrowing::PyNotEq(single) => ty != single,
        Narrowing::IsInstance(id) => brand_could_match(ty, *id),
        Narrowing::IsNotInstance(id) => !brand_definitely_matches(ty, *id),
        Narrowing::Truthy => could_be_truthy(ty, lang),
        Narrowing::Falsy => could_be_falsy(ty, lang),
    }
}

/// True if a value of type `ty` could be the one value of the singleton
/// type `single`.
fn could_be_value(ty: &Type, single: &Type) -> bool {
    match single {
        Type::Literal(lit) => value_compatible_with_literal(ty, lit),
        unit => could_be(ty, unit),
    }
}

/// Whether Python's `==` can hold between a `ty` and the singleton
/// `single` across `bool` and the numbers: `bool` is an `int`, so
/// `True == 1` and `0 == False`.
fn py_bool_int_equal(ty: &Type, single: &Type) -> bool {
    let bool_like = |t: &Type| matches!(t, Type::Boolean | Type::Literal(LitValue::Bool(_)));
    let number_like = |t: &Type| {
        matches!(
            t,
            Type::Int | Type::Number | Type::Literal(LitValue::Number(_))
        )
    };
    match single {
        Type::Literal(LitValue::Number(n)) => bool_like(ty) && (*n == 0.0 || *n == 1.0),
        Type::Literal(LitValue::Bool(_)) => number_like(ty),
        _ => false,
    }
}

/// A value Python compares with built-in `==` (no user `__eq__`).
fn is_primitive(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Number
            | Type::Int
            | Type::String
            | Type::Boolean
            | Type::Null
            | Type::Undefined
            | Type::Literal(_)
    )
}

/// True if a value of type `ty` could be the unit value `unit` (`Null`
/// or `Undefined`): it is that type, or a type we don't know yet. (A
/// named type is a class instance or a recursive type that doesn't
/// unfold to a union — `expose_named` unfolds those — so it is neither.)
fn could_be(ty: &Type, unit: &Type) -> bool {
    ty == unit || matches!(ty, Type::Var(_) | Type::Union(_) | Type::Error)
}

/// True unless every value of `ty` is falsy. `null`/`nil`, `undefined`
/// and `false` are falsy everywhere; `0` and `""` only outside Lua.
fn could_be_truthy(ty: &Type, lang: Language) -> bool {
    match ty {
        Type::Null | Type::Undefined => false,
        Type::Literal(LitValue::Bool(b)) => *b,
        Type::Literal(LitValue::Number(n)) if lang != Language::Lua => *n != 0.0 && !n.is_nan(),
        Type::Literal(LitValue::String(s)) if lang != Language::Lua => !s.is_empty(),
        _ => true,
    }
}

/// True unless every value of `ty` is truthy. In JavaScript objects,
/// arrays and functions always are; in Lua everything but `nil` and
/// `false` is; in Python only functions are sure to be (an empty list
/// or an object with `__bool__` can be falsy).
fn could_be_falsy(ty: &Type, lang: Language) -> bool {
    if let Type::Literal(_) = ty {
        return !could_be_truthy(ty, lang);
    }
    let callable = ty.is_func();
    match lang {
        Language::JavaScript => {
            !(callable
                || matches!(
                    ty,
                    Type::Row(_)
                        | Type::Array(_)
                        | Type::Map(_)
                        | Type::Promise(_)
                        | Type::Tuple(_)
                        | Type::Module(_)
                        | Type::Regex
                ))
        }
        Language::Lua => matches!(
            ty,
            Type::Null
                | Type::Undefined
                | Type::Boolean
                | Type::Var(_)
                | Type::Named(_, _)
                | Type::Union(_)
                | Type::Error
        ),
        Language::Python => !callable,
    }
}

/// True if a value of type `ty` *could* be an instance of nominal brand
/// `id` — its `Named` brand matches, or its shape is still unknown.
fn brand_could_match(ty: &Type, id: TypeId) -> bool {
    match ty {
        Type::Named(mid, _) => *mid == id,
        // A variable or union member of unknown shape can't be ruled out.
        Type::Var(_) | Type::Union(_) => true,
        _ => false,
    }
}

/// True if a value of type `ty` *must* be an instance of nominal brand
/// `id` (used to drop members in the negated `else` branch).
fn brand_definitely_matches(ty: &Type, id: TypeId) -> bool {
    matches!(ty, Type::Named(mid, _) if *mid == id)
}

/// True if a value of type `ty` *could* have `typeof` equal to `name`.
fn typeof_matches(ty: &Type, name: &str) -> bool {
    match (ty, name) {
        (Type::Number | Type::Int, "number") => true,
        (Type::String, "string") => true,
        (Type::Boolean, "boolean") => true,
        (Type::Undefined, "undefined") => true,
        // Under the unified callable-row design, `typeof` "function"
        // matches any value with a `<CALL>` field. Rows without
        // `<CALL>` are plain objects.
        (_, "function") if ty.is_func() => true,
        (Type::Row(_), "object") if !ty.is_func() => true,
        (Type::Array(_) | Type::Tuple(_) | Type::Regex, "object") => true,
        (Type::Map(_), "object") | (Type::Promise(_), "object") => true,
        (Type::Module(_), "object") => true,
        (Type::Null, "object") => true,
        (Type::Literal(LitValue::String(_)), "string") => true,
        (Type::Literal(LitValue::Number(_)), "number") => true,
        (Type::Literal(LitValue::Bool(_)), "boolean") => true,
        // Variables / named / unions are accepted conservatively — we
        // don't yet know what they are, so we can't rule them out.
        (Type::Var(_) | Type::Named(_, _) | Type::Union(_) | Type::Error, _) => true,
        _ => false,
    }
}

/// True if a value of type `ty` *must* have `typeof` equal to `name`.
fn typeof_definitely_matches(ty: &Type, name: &str) -> bool {
    match (ty, name) {
        (Type::Number | Type::Int, "number") => true,
        (Type::String, "string") => true,
        (Type::Boolean, "boolean") => true,
        (Type::Undefined, "undefined") => true,
        (_, "function") if ty.is_func() => true,
        (Type::Literal(LitValue::String(_)), "string") => true,
        (Type::Literal(LitValue::Number(_)), "number") => true,
        (Type::Literal(LitValue::Bool(_)), "boolean") => true,
        _ => false,
    }
}

/// True if a value of type `ty` *could* equal the literal value `lit`.
fn value_compatible_with_literal(ty: &Type, lit: &LitValue) -> bool {
    match ty {
        Type::Literal(other) => other == lit,
        Type::String => matches!(lit, LitValue::String(_)),
        Type::Number => matches!(lit, LitValue::Number(_)),
        // An `Int` has no fractional part, but may be past 2^53 or not
        // finite (`Math.floor(1 / 0)`).
        Type::Int => {
            matches!(lit, LitValue::Number(n) if !(n.is_finite() && n.fract() != 0.0))
        }
        Type::Boolean => matches!(lit, LitValue::Bool(_)),
        // Unknown/abstract types are compatible — we can't rule them out.
        Type::Var(_) | Type::Named(_, _) | Type::Union(_) | Type::Error => true,
        // A row, function, etc. cannot equal a primitive literal value.
        _ => false,
    }
}

/// True if the property at `steps` inside `member_ty` is compatible with
/// `narrowing`. Used to keep/drop union members during refinement.
fn member_property_compatible(
    member_ty: &Type,
    steps: &[PropName],
    narrowing: &Narrowing,
    lang: Language,
) -> bool {
    if steps.is_empty() {
        return member_compatible(member_ty, narrowing, lang);
    }

    match member_ty {
        Type::Row(row) => {
            let head = &steps[0];
            if let Some(entry) = row.props.get(head) {
                member_property_compatible(&entry.ty, &steps[1..], narrowing, lang)
            } else {
                // Property is absent from this row's known fields.
                // - If the row is open, we don't know — be conservative
                //   (keep the member).
                // - If the row is closed, the property is genuinely
                //   missing; the narrowing rules it out.
                row.is_open()
            }
        }
        // Variables/named/etc.: don't know the shape, keep the member.
        _ => true,
    }
}

/// `typeof <path> === "lit"` (either order, `==` too: `typeof` yields a
/// string, so loose and strict equality agree), with its negations.
pub fn typeof_fact(test: &Expr) -> Option<(Path, Narrowing)> {
    let Expr::Binary {
        op, left, right, ..
    } = test
    else {
        return None;
    };
    let neg = match op {
        BinOp::EqEqEq | BinOp::EqEq => false,
        BinOp::NotEqEq | BinOp::NotEq => true,
        _ => return None,
    };
    let (path, name) = try_typeof_string_pair(left, right)?;
    Some((
        path,
        if neg {
            Narrowing::IsNotTypeof(name)
        } else {
            Narrowing::IsTypeof(name)
        },
    ))
}

/// Match `typeof <path>` on either operand and a string literal on the
/// other. Returns the path and the typeof string.
fn try_typeof_string_pair(a: &Expr, b: &Expr) -> Option<(Path, String)> {
    if let Some(path) = typeof_path(a) {
        if let Some(s) = string_literal(b) {
            return Some((path, s));
        }
    }
    if let Some(path) = typeof_path(b) {
        if let Some(s) = string_literal(a) {
            return Some((path, s));
        }
    }
    None
}

fn typeof_path(e: &Expr) -> Option<Path> {
    match e {
        Expr::Unary {
            op: UnaryOp::Typeof,
            argument,
            ..
        } => path_from_expr(argument),
        _ => None,
    }
}

fn string_literal(e: &Expr) -> Option<String> {
    match e {
        Expr::Lit {
            value: Literal::String(s),
            ..
        } => Some(s.clone()),
        _ => None,
    }
}

/// Public wrapper for switch's case-literal extraction.
pub fn literal_value_of(e: &Expr) -> Option<LitValue> {
    literal_value(e)
}

fn literal_value(e: &Expr) -> Option<LitValue> {
    match e {
        Expr::Lit {
            value: Literal::String(s),
            ..
        } => Some(LitValue::String(s.clone())),
        Expr::Lit {
            value: Literal::Number(n),
            ..
        } => Some(LitValue::Number(*n)),
        Expr::Lit {
            value: Literal::Boolean(b),
            ..
        } => Some(LitValue::Bool(*b)),
        _ => None,
    }
}

/// Build a `Path` from an `Expr`, if it's a pure identifier-or-member
/// chain. Anything else returns None — narrowing on derived expressions
/// (calls, arithmetic) isn't supported.
pub fn path_from_expr(e: &Expr) -> Option<Path> {
    match e {
        Expr::Ident { name, span } => Some(Path::Ident(name.clone(), *span)),
        Expr::Member {
            object, property, ..
        } => {
            let parent = path_from_expr(object)?;
            Some(Path::Member(Box::new(parent), PropName(property.clone())))
        }
        _ => None,
    }
}

/// Convenience: walk a `Type` looking for a row property at the given
/// path, returning its type if found.
#[allow(dead_code)]
pub fn lookup_path_type(ty: &Type, steps: &[PropName]) -> Option<Type> {
    if steps.is_empty() {
        return Some(ty.clone());
    }
    match ty {
        Type::Row(RowType { props, tail }) => {
            if let Some(entry) = props.get(&steps[0]) {
                lookup_path_type(&entry.ty, &steps[1..])
            } else {
                match tail {
                    RowTail::Open(_) | RowTail::Recursive(_, _) | RowTail::Closed => None,
                }
            }
        }
        Type::Union(members) => {
            // The path is well-typed across a union only if every member
            // has it; return a join of the per-member types.
            let mut acc: Option<Type> = None;
            for m in members {
                let t = lookup_path_type(m, steps)?;
                acc = Some(match acc {
                    None => t,
                    Some(prev) => {
                        if prev == t {
                            prev
                        } else {
                            Type::union(vec![prev, t])
                        }
                    }
                });
            }
            acc
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Type, TypeScheme};

    fn env_with(name: &str, ty: Type) -> TypeEnv {
        TypeEnv::empty().extend(name.to_string(), TypeScheme::mono(ty))
    }

    #[test]
    fn test_narrow_typeof_undefined_drops_undefined_member() {
        let ty = Type::union(vec![Type::String, Type::Undefined]);
        let env = env_with("x", ty);
        let state = crate::infer::InferState::new();
        let narrowed = narrow_binding(
            &state,
            &env,
            &Path::Ident("x".to_string(), Span::new(0, 0)),
            &Narrowing::IsNotTypeof("undefined".to_string()),
        );
        let new_ty = narrowed.lookup("x").unwrap().ty();
        assert_eq!(*new_ty, Type::String);
    }

    #[test]
    fn test_narrow_typeof_undefined_keeps_undefined_member() {
        let ty = Type::union(vec![Type::String, Type::Undefined]);
        let env = env_with("x", ty);
        let state = crate::infer::InferState::new();
        let narrowed = narrow_binding(
            &state,
            &env,
            &Path::Ident("x".to_string(), Span::new(0, 0)),
            &Narrowing::IsTypeof("undefined".to_string()),
        );
        let new_ty = narrowed.lookup("x").unwrap().ty();
        assert_eq!(*new_ty, Type::Undefined);
    }

    #[test]
    fn test_narrow_equals_literal_sharpens_string() {
        let env = env_with("s", Type::String);
        let state = crate::infer::InferState::new();
        let narrowed = narrow_binding(
            &state,
            &env,
            &Path::Ident("s".to_string(), Span::new(0, 0)),
            &Narrowing::Is(Type::lit_string("hi")),
        );
        let new_ty = narrowed.lookup("s").unwrap().ty();
        assert_eq!(*new_ty, Type::lit_string("hi"));
    }

    #[test]
    fn test_path_for_member_chain() {
        // shape.kind — the path the discriminant narrowing refines.
        let span = crate::span::Span::new(0, 5);
        let e = Expr::Member {
            object: Box::new(Expr::Ident {
                name: "shape".into(),
                span,
            }),
            property: "kind".into(),
            span,
        };
        assert_eq!(
            path_from_expr(&e),
            Some(Path::Member(
                Box::new(Path::Ident("shape".into(), span)),
                PropName("kind".into())
            ))
        );
    }

    #[test]
    fn test_narrow_member_kind_filters_union() {
        // shape : {kind: "circle", r: Number} | {kind: "square", s: Number}
        let circle = Type::object(vec![
            ("kind", Type::lit_string("circle")),
            ("r", Type::Number),
        ]);
        let square = Type::object(vec![
            ("kind", Type::lit_string("square")),
            ("s", Type::Number),
        ]);
        let union = Type::union(vec![circle.clone(), square.clone()]);
        let env = env_with("shape", union);

        let path = Path::Member(
            Box::new(Path::Ident("shape".to_string(), Span::new(0, 0))),
            PropName("kind".into()),
        );
        let narrowing = Narrowing::Is(Type::lit_string("circle"));
        let state = crate::infer::InferState::new();
        let narrowed = narrow_binding(&state, &env, &path, &narrowing);
        let new_ty = narrowed.lookup("shape").unwrap().ty();
        assert_eq!(*new_ty, circle);
    }

    #[test]
    fn test_narrow_member_negation_filters_other_member() {
        let circle = Type::object(vec![
            ("kind", Type::lit_string("circle")),
            ("r", Type::Number),
        ]);
        let square = Type::object(vec![
            ("kind", Type::lit_string("square")),
            ("s", Type::Number),
        ]);
        let union = Type::union(vec![circle.clone(), square.clone()]);
        let env = env_with("shape", union);

        let path = Path::Member(
            Box::new(Path::Ident("shape".to_string(), Span::new(0, 0))),
            PropName("kind".into()),
        );
        let narrowing = Narrowing::IsNot(Type::lit_string("circle"));
        let state = crate::infer::InferState::new();
        let narrowed = narrow_binding(&state, &env, &path, &narrowing);
        let new_ty = narrowed.lookup("shape").unwrap().ty();
        assert_eq!(*new_ty, square);
    }

    #[test]
    fn test_narrow_isinstance_filters_brand_union() {
        // x : Named(1) | Named(2). isinstance(x, brand 1) keeps Named(1);
        // the negation keeps Named(2).
        let dog = Type::Named(1, vec![]);
        let cat = Type::Named(2, vec![]);
        let env = env_with("x", Type::union(vec![dog.clone(), cat.clone()]));
        let state = crate::infer::InferState::new();

        let yes = narrow_binding(
            &state,
            &env,
            &Path::Ident("x".to_string(), Span::new(0, 0)),
            &Narrowing::IsInstance(1),
        );
        assert_eq!(*yes.lookup("x").unwrap().ty(), dog);

        let no = narrow_binding(
            &state,
            &env,
            &Path::Ident("x".to_string(), Span::new(0, 0)),
            &Narrowing::IsNotInstance(1),
        );
        assert_eq!(*no.lookup("x").unwrap().ty(), cat);
    }

    #[test]
    fn test_narrow_isinstance_unmatched_brand_is_dead() {
        // A value known to be one brand, tested against a different one:
        // the branch is dead, and the binding keeps its type there.
        let env = env_with("x", Type::Named(2, vec![]));
        let state = crate::infer::InferState::new();
        let path = Path::Ident("x".to_string(), Span::new(0, 0));
        assert!(narrowing_is_dead(
            &state,
            &env,
            &path,
            &Narrowing::IsInstance(1)
        ));
        let narrowed = narrow_binding(&state, &env, &path, &Narrowing::IsInstance(1));
        assert_eq!(*narrowed.lookup("x").unwrap().ty(), Type::Named(2, vec![]));
    }

    #[test]
    fn test_narrow_exhausted_keeps_the_declared_type() {
        // `s : "a"` tested `!== "a"`: the branch is dead. Its binding keeps
        // `"a"` rather than `never`, so an inexact predicate can only cost
        // precision.
        let env = env_with("s", Type::lit_string("a"));
        let state = crate::infer::InferState::new();
        let path = Path::Ident("s".to_string(), Span::new(0, 0));
        let n = Narrowing::IsNot(Type::lit_string("a"));
        assert!(narrowing_is_dead(&state, &env, &path, &n));
        let narrowed = narrow_binding(&state, &env, &path, &n);
        assert_eq!(*narrowed.lookup("s").unwrap().ty(), Type::lit_string("a"));
    }
}
