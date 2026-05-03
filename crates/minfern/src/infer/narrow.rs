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

use crate::types::{LitValue, PropName, RowTail, RowType, Type, TypeScheme};

use super::env::TypeEnv;
use crate::parser::ast::{BinOp, Expr, Literal, UnaryOp};

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
        }
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

    let original_ty = state.apply_subst(scheme.ty());
    let new_ty = refine_at_path(&original_ty, &path_steps(path), narrowing);

    let new_scheme = TypeScheme::mono(new_ty);
    env.extend(root, new_scheme)
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
fn refine_at_path(ty: &Type, steps: &[PropName], narrowing: &Narrowing) -> Type {
    if steps.is_empty() {
        return refine_type(ty, narrowing);
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
                .filter(|m| member_property_compatible(m, steps, narrowing))
                .cloned()
                .collect();
            // If we eliminated nothing, the result is the same union; if
            // we eliminated everything, the branch is unreachable and we
            // collapse to `never` (the empty union).
            Type::union(kept)
        }
        Type::Row(_) => {
            if member_property_compatible(ty, steps, narrowing) {
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
fn refine_type(ty: &Type, narrowing: &Narrowing) -> Type {
    match ty {
        Type::Union(members) => {
            let kept: Vec<Type> = members
                .iter()
                .filter(|m| member_compatible(m, narrowing))
                .map(|m| refine_type(m, narrowing))
                .collect();
            Type::union(kept)
        }
        _ => {
            if !member_compatible(ty, narrowing) {
                return Type::never();
            }
            // For positive narrowings, sharpen the type when possible
            // (e.g. a String narrowed by `=== "a"` becomes `Literal("a")`).
            match narrowing {
                Narrowing::Equals(lit) if matches!(ty, Type::String | Type::Number | Type::Boolean) => {
                    Type::Literal(lit.clone())
                }
                _ => ty.clone(),
            }
        }
    }
}

/// True if `ty` is consistent with `narrowing` — i.e. it's possible for
/// a value of type `ty` to satisfy the predicate.
fn member_compatible(ty: &Type, narrowing: &Narrowing) -> bool {
    match narrowing {
        Narrowing::IsTypeof(name) => typeof_matches(ty, name),
        Narrowing::IsNotTypeof(name) => !typeof_definitely_matches(ty, name),
        Narrowing::Equals(lit) => value_compatible_with_literal(ty, lit),
        Narrowing::NotEquals(lit) => !value_definitely_equals_literal(ty, lit),
    }
}

/// True if a value of type `ty` *could* have `typeof` equal to `name`.
fn typeof_matches(ty: &Type, name: &str) -> bool {
    match (ty, name) {
        (Type::Number, "number") => true,
        (Type::String, "string") => true,
        (Type::Boolean, "boolean") => true,
        (Type::Undefined, "undefined") => true,
        (Type::Func { .. }, "function") => true,
        (Type::Row(_), "object") | (Type::Array(_), "object") => true,
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
        (Type::Number, "number") => true,
        (Type::String, "string") => true,
        (Type::Boolean, "boolean") => true,
        (Type::Undefined, "undefined") => true,
        (Type::Func { .. }, "function") => true,
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
fn member_property_compatible(member_ty: &Type, steps: &[PropName], narrowing: &Narrowing) -> bool {
    if steps.is_empty() {
        return member_compatible(member_ty, narrowing);
    }

    match member_ty {
        Type::Row(row) => {
            let head = &steps[0];
            if let Some(prop_ty) = row.props.get(head) {
                member_property_compatible(prop_ty, &steps[1..], narrowing)
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
///   - `<path> === <literal>`        → `Equals(literal)` on `<path>`
///   - `<path> !== <literal>`        → `NotEquals(literal)` on `<path>`
///
/// Both operand orders are accepted for the comparison operators.
pub fn try_extract_narrowing(test: &Expr) -> Option<(Path, Narrowing)> {
    let Expr::Binary { op, left, right, .. } = test else {
        return None;
    };

    let (eq, neg) = match op {
        BinOp::EqEqEq => (true, false),
        BinOp::NotEqEq => (true, true),
        // Loose equality is intentionally excluded — its narrowing
        // semantics differ from === in JS (e.g. `0 == ""`), and we want
        // the predicate set to mirror what TypeScript's flow analysis
        // recognises.
        _ => return None,
    };
    if !eq {
        return None;
    }

    // Try `typeof <path> === "lit"` in either operand order.
    if let Some((path, name)) = try_typeof_string_pair(left, right) {
        let narrowing = if neg {
            Narrowing::IsNotTypeof(name)
        } else {
            Narrowing::IsTypeof(name)
        };
        return Some((path, narrowing));
    }

    // Try `<path> === <literal>` in either operand order.
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
        Expr::Unary { op: UnaryOp::Typeof, argument, .. } => path_from_expr(argument),
        _ => None,
    }
}

fn string_literal(e: &Expr) -> Option<String> {
    match e {
        Expr::Lit { value: Literal::String(s), .. } => Some(s.clone()),
        _ => None,
    }
}

/// Public wrapper for switch's case-literal extraction.
pub fn literal_value_of(e: &Expr) -> Option<LitValue> {
    literal_value(e)
}

fn literal_value(e: &Expr) -> Option<LitValue> {
    match e {
        Expr::Lit { value: Literal::String(s), .. } => Some(LitValue::String(s.clone())),
        Expr::Lit { value: Literal::Number(n), .. } => Some(LitValue::Number(*n)),
        Expr::Lit { value: Literal::Boolean(b), .. } => Some(LitValue::Bool(*b)),
        _ => None,
    }
}

/// Build a `Path` from an `Expr`, if it's a pure identifier-or-member
/// chain. Anything else returns None — narrowing on derived expressions
/// (calls, arithmetic) isn't supported.
pub fn path_from_expr(e: &Expr) -> Option<Path> {
    match e {
        Expr::Ident { name, .. } => Some(Path::Ident(name.clone())),
        Expr::Member { object, property, .. } => {
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
            if let Some(t) = props.get(&steps[0]) {
                lookup_path_type(t, &steps[1..])
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
        let span = crate::lexer::Span::new(0, 0);
        let test = Expr::Binary {
            op: BinOp::EqEqEq,
            left: Box::new(Expr::Member {
                object: Box::new(Expr::Ident { name: "shape".into(), span }),
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
        assert_eq!(narrowing, Narrowing::Equals(LitValue::String("circle".into())));
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
