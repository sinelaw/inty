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
//! Narrowing is not a substitution. It only lives in the environment passed
//! down into a branch — a fact that holds *here*, not everywhere. Sharing
//! it with the unification substitution would over-narrow at sibling
//! branches.

use crate::types::{LitValue, PropName, RowTail, RowType, Type, TypeId, TypeScheme};

use super::env::TypeEnv;
use crate::ast::SourceLanguage as Language;
use crate::ast::{BinOp, Expr, Literal, UnaryOp};

/// A `Path` names something that can be narrowed: a local identifier, or
/// a (possibly nested) property access off one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Path {
    /// A bare identifier in the environment.
    Ident(String),
    /// A property access: `<parent>.<prop>`.
    Member(Box<Path>, PropName),
}

impl Path {
    /// The root identifier of this path. All paths bottom out at an
    /// identifier; it's the one whose binding gets refined.
    pub fn root_ident(&self) -> &str {
        match self {
            Path::Ident(n) => n.as_str(),
            Path::Member(p, _) => p.root_ident(),
        }
    }
}

/// A predicate to apply to the value at a `Path`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Narrowing {
    /// `typeof <path> === "string-literal"`.
    IsTypeof(String),
    /// `typeof <path> !== "string-literal"`.
    IsNotTypeof(String),
    /// `<path> === <literal>`.
    Equals(LitValue),
    /// `<path> !== <literal>`.
    NotEquals(LitValue),
    /// `isinstance(<path>, C)` — the value is an instance of the class
    /// whose nominal brand is `TypeId`. Filters a union of `Named` brands
    /// to the matching member.
    IsInstance(TypeId),
    /// Negation of [`Narrowing::IsInstance`] (the `else` branch).
    IsNotInstance(TypeId),
    /// `<path> === null`.
    IsNull,
    /// `<path> !== null`.
    NotNull,
    /// `<path> === undefined`.
    IsUndefined,
    /// `<path> !== undefined`.
    NotUndefined,
    /// `<path> == null` (or `== undefined`): null or undefined.
    IsNullish,
    /// `<path> != null` (or `!= undefined`).
    NotNullish,
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
            Narrowing::Equals(l) => Narrowing::NotEquals(l.clone()),
            Narrowing::NotEquals(l) => Narrowing::Equals(l.clone()),
            Narrowing::IsInstance(id) => Narrowing::IsNotInstance(*id),
            Narrowing::IsNotInstance(id) => Narrowing::IsInstance(*id),
            Narrowing::IsNull => Narrowing::NotNull,
            Narrowing::NotNull => Narrowing::IsNull,
            Narrowing::IsUndefined => Narrowing::NotUndefined,
            Narrowing::NotUndefined => Narrowing::IsUndefined,
            Narrowing::IsNullish => Narrowing::NotNullish,
            Narrowing::NotNullish => Narrowing::IsNullish,
            Narrowing::Truthy => Narrowing::Falsy,
            Narrowing::Falsy => Narrowing::Truthy,
        }
    }

    /// Whether a branch this narrowing makes dead is worth a warning.
    /// Defensive null checks and truth tests of values that can't be
    /// falsy are ordinary JavaScript, so those stay quiet.
    pub fn warns_when_dead(&self) -> bool {
        matches!(
            self,
            Narrowing::IsTypeof(_)
                | Narrowing::IsNotTypeof(_)
                | Narrowing::Equals(_)
                | Narrowing::NotEquals(_)
                | Narrowing::IsInstance(_)
                | Narrowing::IsNotInstance(_)
        )
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

    /// Drop every fact about a variable in `names` (ones the test itself
    /// assigns, whose value at the branch may not be the one tested).
    pub fn forget(&mut self, names: &std::collections::HashSet<String>) {
        self.when_true
            .retain(|(p, _)| !names.contains(p.root_ident()));
        self.when_false
            .retain(|(p, _)| !names.contains(p.root_ident()));
    }
}

/// The facts a test establishes. `extra` recognises tests that need the
/// checker's state (`isinstance`).
///
/// - a comparison [`try_extract_narrowing`] understands;
/// - `<path>` alone: truthy when true, falsy when false;
/// - `!e`: the facts of `e`, swapped;
/// - `a && b`: when true, both sides' true facts (`b` only runs once
///   `a` held); when false, nothing we can pin to one side;
/// - `a || b`: when false, both sides' false facts; when true, nothing.
pub fn test_facts(test: &Expr, extra: &dyn Fn(&Expr) -> Option<(Path, Narrowing)>) -> Facts {
    if let Some((path, narrowing)) = try_extract_narrowing(test).or_else(|| extra(test)) {
        return Facts::one(path, narrowing);
    }
    match test {
        Expr::Unary {
            op: UnaryOp::Not,
            argument,
            ..
        } => test_facts(argument, extra).swap(),
        Expr::Binary {
            op: BinOp::And,
            left,
            right,
            ..
        } => {
            let mut l = test_facts(left, extra);
            let r = test_facts(right, extra);
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
            let mut l = test_facts(left, extra);
            let r = test_facts(right, extra);
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
/// The binding's type is normalised through the current substitution
/// before refinement — without this, a parameter bound to a fresh
/// variable that *happens* to be substituted to a union would never
/// narrow, because the env still holds the bare variable.
///
/// If the path's root isn't bound, the input env is returned unchanged —
/// a missing binding is a non-narrowable expression and the type checker
/// will report the underlying use later.
pub fn apply_narrowing(
    state: &super::state::InferState,
    env: &TypeEnv,
    path: &Path,
    narrowing: &Narrowing,
) -> TypeEnv {
    let root = path.root_ident().to_string();
    let Some(scheme) = env.lookup(&root).cloned() else {
        return env.clone();
    };

    // We only narrow monomorphic bindings. A polymorphic binding (a let
    // function) wouldn't typically be the target of a narrowing — the
    // refinements we model don't apply to type schemes — and trying to
    // refine inside a quantifier would be unsound.
    if !scheme.is_mono() {
        return env.clone();
    }

    // A variable that a closure assigns can change during any call, so a
    // test of it may be stale by the time the branch reads it.
    let mutable = env
        .lookup_binding(&root)
        .is_some_and(|b| b.mutability == super::env::Mutability::Mutable);
    if mutable && state.closure_assigned.contains(&root) {
        return env.clone();
    }

    let original_ty = state.apply_subst(scheme.ty());
    let exposed = expose_named(state, &original_ty);
    let new_ty = refine_at_path(&exposed, &path_steps(path), narrowing, state.language);
    if new_ty == exposed {
        // Nothing ruled out: leave the binding (and a named type) alone.
        return env.clone();
    }

    env.narrow(&root, TypeScheme::mono(new_ty))
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
            Path::Ident(_) => {
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
                Narrowing::Equals(lit)
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
        Narrowing::Equals(lit) => value_compatible_with_literal(ty, lit),
        Narrowing::NotEquals(lit) => !value_definitely_equals_literal(ty, lit),
        Narrowing::IsInstance(id) => brand_could_match(ty, *id),
        Narrowing::IsNotInstance(id) => !brand_definitely_matches(ty, *id),
        Narrowing::IsNull => could_be(ty, &Type::Null),
        Narrowing::NotNull => *ty != Type::Null,
        Narrowing::IsUndefined => could_be(ty, &Type::Undefined),
        Narrowing::NotUndefined => *ty != Type::Undefined,
        Narrowing::IsNullish => could_be(ty, &Type::Null) || could_be(ty, &Type::Undefined),
        Narrowing::NotNullish => !matches!(ty, Type::Null | Type::Undefined),
        Narrowing::Truthy => could_be_truthy(ty, lang),
        Narrowing::Falsy => could_be_falsy(ty, lang),
    }
}

/// True if a value of type `ty` could be the unit value `unit` (`Null`
/// or `Undefined`): it is that type, or a type we don't know yet.
fn could_be(ty: &Type, unit: &Type) -> bool {
    ty == unit
        || matches!(
            ty,
            Type::Var(_) | Type::Named(_, _) | Type::Union(_) | Type::Error
        )
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
        (Type::Array(_), "object") => true,
        (Type::Map(_), "object") | (Type::Promise(_), "object") => true,
        (Type::Module(_), "object") => true,
        (Type::Null, "object") => true,
        (Type::Literal(LitValue::String(_)), "string") => true,
        (Type::Literal(LitValue::Number(_)), "number") => true,
        (Type::Literal(LitValue::Bool(_)), "boolean") => true,
        // Variables / named / unions are accepted conservatively — we
        // don't yet know what they are, so we can't rule them out.
        (Type::Var(_) | Type::Named(_, _) | Type::Union(_), _) => true,
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
        Type::Int => matches!(lit, LitValue::Number(n) if crate::types::is_safe_int(*n)),
        Type::Boolean => matches!(lit, LitValue::Bool(_)),
        // Unknown/abstract types are compatible — we can't rule them out.
        Type::Var(_) | Type::Named(_, _) | Type::Union(_) => true,
        // A row, function, etc. cannot equal a primitive literal value.
        _ => false,
    }
}

/// True if a value of type `ty` *must* equal the literal value `lit`.
fn value_definitely_equals_literal(ty: &Type, lit: &LitValue) -> bool {
    matches!(ty, Type::Literal(other) if other == lit)
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

/// Try to extract a `(Path, Narrowing)` from a test expression.
/// Returns `None` if the expression isn't a recognised narrowing pattern.
///
/// Recognised patterns:
///   - `typeof <path> === "lit"`     → `IsTypeof("lit")` on `<path>`
///   - `typeof <path> !== "lit"`     → `IsNotTypeof("lit")` on `<path>`
///   - `typeof <path> ==  "lit"`     → `IsTypeof("lit")` on `<path>`
///   - `typeof <path> !=  "lit"`     → `IsNotTypeof("lit")` on `<path>`
///   - `<path> === <literal>`        → `Equals(literal)` on `<path>`
///   - `<path> !== <literal>`        → `NotEquals(literal)` on `<path>`
///
/// Both operand orders are accepted for the comparison operators.
///
/// Loose equality (`==`/`!=`) is supported only for the typeof form: a
/// `typeof <expr>` always evaluates to a string, and the other operand
/// is a string literal, so JS's coercion rules cannot make `==` and
/// `===` differ. For `<value> == <literal>` in general, semantics
/// diverge from `===` (e.g. `0 == ""`), so loose equality is rejected.
pub fn try_extract_narrowing(test: &Expr) -> Option<(Path, Narrowing)> {
    let Expr::Binary {
        op, left, right, ..
    } = test
    else {
        return None;
    };

    let (strict, neg) = match op {
        BinOp::EqEqEq => (true, false),
        BinOp::NotEqEq => (true, true),
        BinOp::EqEq => (false, false),
        BinOp::NotEq => (false, true),
        _ => return None,
    };

    // `typeof <path> {==,===} "lit"` — sound for both strict and loose
    // equality (see doc comment).
    if let Some((path, name)) = try_typeof_string_pair(left, right) {
        let narrowing = if neg {
            Narrowing::IsNotTypeof(name)
        } else {
            Narrowing::IsTypeof(name)
        };
        return Some((path, narrowing));
    }

    // `<path> === null`, `<path> !== undefined`, … Loose equality is
    // exact here too: `x == null` holds for `null` and `undefined` and
    // nothing else.
    for (a, b) in [(left, right), (right, left)] {
        if let (Some(path), Some(unit)) = (path_from_expr(a), unit_literal(b)) {
            let narrowing = match (strict, unit) {
                (true, Type::Null) => Narrowing::IsNull,
                (true, _) => Narrowing::IsUndefined,
                (false, _) => Narrowing::IsNullish,
            };
            return Some((path, if neg { narrowing.negate() } else { narrowing }));
        }
    }

    // For `<path> === <literal>`, only strict equality is recognised.
    if !strict {
        return None;
    }

    if let (Some(path), Some(lit)) = (path_from_expr(left), literal_value(right)) {
        let narrowing = if neg {
            Narrowing::NotEquals(lit)
        } else {
            Narrowing::Equals(lit)
        };
        return Some((path, narrowing));
    }
    if let (Some(path), Some(lit)) = (path_from_expr(right), literal_value(left)) {
        let narrowing = if neg {
            Narrowing::NotEquals(lit)
        } else {
            Narrowing::Equals(lit)
        };
        return Some((path, narrowing));
    }

    None
}

/// True when applying a narrowing at `path` collapsed the binding's
/// type from a non-`never` type to `never`. That means the predicate
/// is statically unsatisfiable on this branch — the branch is dead.
///
/// Returns `false` if the binding wasn't found, isn't monomorphic, or
/// was already `never` before narrowing — in those cases there's
/// nothing useful to report.
pub fn narrowing_collapsed_to_never(
    state: &super::state::InferState,
    before: &TypeEnv,
    after: &TypeEnv,
    path: &Path,
) -> bool {
    let root = path.root_ident();
    let (Some(before_scheme), Some(after_scheme)) = (before.lookup(root), after.lookup(root))
    else {
        return false;
    };
    if !before_scheme.is_mono() || !after_scheme.is_mono() {
        return false;
    }
    let before_ty = state.apply_subst(before_scheme.ty());
    let after_ty = state.apply_subst(after_scheme.ty());
    !before_ty.is_never() && after_ty.is_never()
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

/// `null` or `undefined` as an operand: the type it is.
fn unit_literal(e: &Expr) -> Option<Type> {
    match e {
        Expr::Lit {
            value: Literal::Null,
            ..
        } => Some(Type::Null),
        Expr::Lit {
            value: Literal::Undefined,
            ..
        } => Some(Type::Undefined),
        Expr::Ident { name, .. } if name == "undefined" => Some(Type::Undefined),
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
        Expr::Ident { name, .. } => Some(Path::Ident(name.clone())),
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
    use crate::types::{LitValue, Type, TypeScheme};

    fn env_with(name: &str, ty: Type) -> TypeEnv {
        TypeEnv::empty().extend(name.to_string(), TypeScheme::mono(ty))
    }

    #[test]
    fn test_narrow_typeof_undefined_drops_undefined_member() {
        let ty = Type::union(vec![Type::String, Type::Undefined]);
        let env = env_with("x", ty);
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(
            &state,
            &env,
            &Path::Ident("x".to_string()),
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
        let narrowed = apply_narrowing(
            &state,
            &env,
            &Path::Ident("x".to_string()),
            &Narrowing::IsTypeof("undefined".to_string()),
        );
        let new_ty = narrowed.lookup("x").unwrap().ty();
        assert_eq!(*new_ty, Type::Undefined);
    }

    #[test]
    fn test_narrow_equals_literal_sharpens_string() {
        let env = env_with("s", Type::String);
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(
            &state,
            &env,
            &Path::Ident("s".to_string()),
            &Narrowing::Equals(LitValue::String("hi".into())),
        );
        let new_ty = narrowed.lookup("s").unwrap().ty();
        assert_eq!(*new_ty, Type::lit_string("hi"));
    }

    #[test]
    fn test_extract_narrowing_for_member_eq_literal() {
        // shape.kind === "circle" — does the predicate detector find it?
        let span = crate::span::Span::new(0, 0);
        let test = Expr::Binary {
            op: BinOp::EqEqEq,
            left: Box::new(Expr::Member {
                object: Box::new(Expr::Ident {
                    name: "shape".into(),
                    span,
                }),
                property: "kind".into(),
                span,
            }),
            right: Box::new(Expr::Lit {
                value: Literal::String("circle".into()),
                span,
            }),
            span,
        };
        let extracted = try_extract_narrowing(&test);
        assert!(extracted.is_some(), "should extract a narrowing");
        let (path, narrowing) = extracted.unwrap();
        assert_eq!(
            path,
            Path::Member(
                Box::new(Path::Ident("shape".into())),
                PropName("kind".into())
            )
        );
        assert_eq!(
            narrowing,
            Narrowing::Equals(LitValue::String("circle".into()))
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
            Box::new(Path::Ident("shape".to_string())),
            PropName("kind".into()),
        );
        let narrowing = Narrowing::Equals(LitValue::String("circle".into()));
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(&state, &env, &path, &narrowing);
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
            Box::new(Path::Ident("shape".to_string())),
            PropName("kind".into()),
        );
        let narrowing = Narrowing::NotEquals(LitValue::String("circle".into()));
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(&state, &env, &path, &narrowing);
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

        let yes = apply_narrowing(
            &state,
            &env,
            &Path::Ident("x".to_string()),
            &Narrowing::IsInstance(1),
        );
        assert_eq!(*yes.lookup("x").unwrap().ty(), dog);

        let no = apply_narrowing(
            &state,
            &env,
            &Path::Ident("x".to_string()),
            &Narrowing::IsNotInstance(1),
        );
        assert_eq!(*no.lookup("x").unwrap().ty(), cat);
    }

    #[test]
    fn test_narrow_isinstance_unmatched_brand_is_never() {
        // A value known to be one brand, tested against a different one,
        // collapses to never (a statically dead branch).
        let env = env_with("x", Type::Named(2, vec![]));
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(
            &state,
            &env,
            &Path::Ident("x".to_string()),
            &Narrowing::IsInstance(1),
        );
        assert!(narrowed.lookup("x").unwrap().ty().is_never());
    }

    #[test]
    fn test_narrow_exhausts_to_never() {
        // Narrow String to "a", then to NotEquals "a" — should be never.
        let env = env_with("s", Type::lit_string("a"));
        let state = crate::infer::InferState::new();
        let narrowed = apply_narrowing(
            &state,
            &env,
            &Path::Ident("s".to_string()),
            &Narrowing::NotEquals(LitValue::String("a".into())),
        );
        let new_ty = narrowed.lookup("s").unwrap().ty();
        assert!(new_ty.is_never(), "expected never, got {}", new_ty);
    }
}
