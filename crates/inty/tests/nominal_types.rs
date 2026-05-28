//! End-to-end tests for declared nominal (branded) types via the
//! `/** nominal type Name = Repr */` surface syntax.
//!
//! A nominal type carries brand identity: the only way to introduce a
//! value is its injected constructor `Name(repr)`, two distinct brands
//! never interchange (even with identical representations), and a brand
//! never collapses into its representation — while field access still
//! sees through to the representation row. See
//! `docs/pyi-import-mapping.md` §8.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src`, returning the inferred top-level type string or the
/// formatted error.
fn check(src: &str) -> Result<String, String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    let (ty, _) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    let resolved = state.apply_subst(&ty);
    let mut ctx = inty::types::PrettyContext::new();
    Ok(ctx.format_type(&resolved))
}

#[test]
fn constructor_introduces_a_branded_value() {
    let src = "
        /** nominal type UserId = Number */
        const u = UserId(42);
    ";
    check(src).expect("UserId(42) should construct a branded value");
}

#[test]
fn constructor_rejects_wrong_representation() {
    let src = "
        /** nominal type UserId = Number */
        const u = UserId(\"oops\");
    ";
    assert!(
        check(src).is_err(),
        "constructing UserId from a String must fail"
    );
}

#[test]
fn brand_does_not_collapse_into_representation() {
    // A UserId is not a Number, even though it wraps one.
    let src = "
        /** nominal type UserId = Number */
        var n /*: Number */ = UserId(42);
    ";
    assert!(
        check(src).is_err(),
        "a UserId must not be usable where a Number is expected"
    );
}

/// Like [`check`], but renders nominal brands by their declared name
/// (rather than the `μ<id>` fallback), for asserting on branded output.
fn check_named(src: &str) -> Result<String, String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    let (ty, _) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    let resolved = state.apply_subst(&ty);
    let mut ctx = inty::types::PrettyContext::with_nominal_names(state.nominal_names());
    Ok(ctx.format_type(&resolved))
}

#[test]
fn js_class_instance_method_sees_through_brand() {
    // Branding a JS class must stay transparent for field/method access:
    // reading a field and calling a method through the brand still works.
    let src = "
        class Box {
            constructor(v) { this.v = v; }
            id() { return this.v; }
        }
        const b = new Box(7);
        const r = b.id();
        r
    ";
    assert!(
        check(src).is_ok(),
        "field/method access through a class brand must work: {:?}",
        check(src)
    );
}

#[test]
fn js_structurally_identical_classes_are_distinct_brands() {
    // JS classes are nominal by default: `A` and `B` have identical shape
    // but are distinct types, so a list holding both is the union `A | B`,
    // not the single structural row it would collapse to structurally.
    let src = "
        class A {}
        class B {}
        const xs = [new A(), new B()];
        xs
    ";
    assert_eq!(
        check_named(src).expect("distinct class brands"),
        "(A | B)[]"
    );
}

#[test]
fn js_distinct_classes_do_not_interchange() {
    // Reassigning a binding across two same-shape class brands must fail.
    let src = "
        class A { constructor(x) { this.x = x; } }
        class B { constructor(x) { this.x = x; } }
        var v = new A(1);
        v = new B(1);
    ";
    assert!(
        check(src).is_err(),
        "instances of distinct class brands must not unify"
    );
}

#[test]
fn same_brand_is_interchangeable() {
    let src = "
        /** nominal type UserId = Number */
        var a = UserId(1);
        var b /*: UserId */ = a;
    ";
    check(src).expect("two UserId values share the same brand");
}

#[test]
fn distinct_brands_do_not_interchange() {
    let src = "
        /** nominal type UserId = Number */
        /** nominal type OrderId = Number */
        var a = UserId(1);
        var b /*: OrderId */ = a;
    ";
    assert!(
        check(src).is_err(),
        "UserId and OrderId are distinct brands and must not interchange"
    );
}

#[test]
fn brand_mismatch_error_names_the_brands() {
    let src = "
        /** nominal type UserId = Number */
        /** nominal type OrderId = Number */
        var a = UserId(1);
        var b /*: OrderId */ = a;
    ";
    let err = check(src).expect_err("distinct brands must not interchange");
    assert!(
        err.contains("UserId") && err.contains("OrderId"),
        "mismatch should name both brands, got: {err}"
    );
}

#[test]
fn field_access_sees_through_to_representation() {
    // Reads see through the brand: `p.x` is a Number.
    let src = "
        /** nominal type Point = {x: Number, y: Number} */
        var p = Point({x: 1, y: 2});
        var n /*: Number */ = p.x;
    ";
    check(src).expect("p.x should read through the brand as Number");
}

#[test]
fn field_access_through_brand_is_typed() {
    // Negative: reading `p.x` as a String must fail — transparent
    // access still respects the representation's field types.
    let src = "
        /** nominal type Point = {x: Number, y: Number} */
        var p = Point({x: 1, y: 2});
        var s /*: String */ = p.x;
    ";
    assert!(check(src).is_err(), "p.x is a Number, not a String");
}

#[test]
fn generic_nominal_carries_its_type_argument() {
    let src = "
        /** nominal type Box<T> = {value: T} */
        var b = Box({value: 42});
        var n /*: Number */ = b.value;
    ";
    check(src).expect("Box's type argument should flow through to b.value");
}

// === Closed-row values do not collapse into a brand (#71) ===
//
// The new unify rule unfolds a nominal type against an *open-tailed*
// row constraint (synthesized by inference at member-access sites) so
// that module-level branded singletons can be read from inside function
// bodies. A *closed* row is a concrete user-introduced value, never an
// inferred constraint, and must still be rejected — otherwise nominal
// safety degrades into structural duck-typing.

#[test]
fn closed_object_literal_does_not_satisfy_brand_annotation() {
    // A bare object literal of the brand's representation shape is
    // *not* a brand value: only the brand's constructor produces one.
    let src = "
        /** nominal type Point = {x: Number, y: Number} */
        var p /*: Point */ = {x: 1, y: 2};
    ";
    assert!(
        check(src).is_err(),
        "an anonymous object literal must not satisfy a brand annotation"
    );
}

#[test]
fn closed_class_instance_literal_does_not_satisfy_class_brand() {
    // Same invariant for JS `class` brands: an object literal that
    // happens to match the instance shape is not an instance.
    let src = "
        class Box { constructor(v) { this.value = v; } }
        function takeBox(b) { return b.value + 1; }
        var b = new Box(1);
        takeBox(b);            // fine
        var v /*: Box */ = {value: 2};   // not fine
    ";
    assert!(
        check(src).is_err(),
        "an object literal must not satisfy a class brand annotation"
    );
}

// === Cycle-guard sanity: coinduction is bounded by structural mismatch ===
//
// The `UnfoldAssumption` stack only short-circuits when the *same*
// pair is re-entered. Two equirecursive types of genuinely different
// shape (different non-recursive field types) still fail. This guards
// against the cycle guard accepting too much.

use inty::infer::InferState;
use inty::span::Span;
use inty::types::{Type, TypeDef};

#[test]
fn cycle_guard_does_not_accept_distinct_recursive_shapes() {
    let mut state = InferState::new();
    let span = Span::new(0, 0);
    // Two equirecursive types with the same self-reference *shape* but
    // a disagreeing non-recursive field: A has `tag: Number`, B has
    // `tag: String`. Unrolling either side should still reach the
    // disagreeing field through a sub-unify and fail there.
    let id_a = state.fresh_type_id();
    let id_b = state.fresh_type_id();
    let body_a = Type::object([
        ("tag", Type::Number),
        ("self_ref", Type::Named(id_a, vec![])),
    ]);
    let body_b = Type::object([
        ("tag", Type::String),
        ("self_ref", Type::Named(id_b, vec![])),
    ]);
    state.register_named_type(TypeDef::recursive(id_a, vec![], body_a));
    state.register_named_type(TypeDef::recursive(id_b, vec![], body_b));
    let a = Type::Named(id_a, vec![]);
    let b = Type::Named(id_b, vec![]);
    assert!(
        state.unify(span, &a, &b).is_err(),
        "equirec types disagreeing on a non-recursive field must still fail"
    );
}

#[test]
fn cycle_guard_accepts_equal_recursive_shapes() {
    // Positive companion: two equirec types of the *same* shape (with
    // the loop closed through a self-reference) must unify under the
    // coinductive assumption. Otherwise the alternating unroll never
    // terminates.
    let mut state = InferState::new();
    let span = Span::new(0, 0);
    let id_a = state.fresh_type_id();
    let id_b = state.fresh_type_id();
    let body_a = Type::object([
        ("tag", Type::Number),
        ("self_ref", Type::Named(id_a, vec![])),
    ]);
    let body_b = Type::object([
        ("tag", Type::Number),
        ("self_ref", Type::Named(id_b, vec![])),
    ]);
    state.register_named_type(TypeDef::recursive(id_a, vec![], body_a));
    state.register_named_type(TypeDef::recursive(id_b, vec![], body_b));
    let a = Type::Named(id_a, vec![]);
    let b = Type::Named(id_b, vec![]);
    assert!(
        state.unify(span, &a, &b).is_ok(),
        "equirec types of the same shape must unify coinductively"
    );
}
