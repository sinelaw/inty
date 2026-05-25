//! Tests for member access (`obj.prop`) on built-in carriers.
//!
//! Regression coverage for two related bugs in the lookup path used by
//! plain member expressions (as opposed to method calls):
//!
//! 1. **Array methods on bare member access.** `arr.map(...)` worked
//!    because call-expression handling went through the
//!    builtin-method-aware lookup, but `arr.map` (no call) used a
//!    different path that only knew about `length` and otherwise fell
//!    through to unification, which then failed with "Property 'map'
//!    not found in type Number[]".
//!
//! 2. **Row-tail walking.** Static methods on callable rows like
//!    `String.fromCharCode` can land in a row's tail (a flex var bound
//!    to another row) after unification, not directly in `row.props`.
//!    The plain-member lookup path didn't follow tail bindings.
//!
//! These tests pin both behaviours via the public API. They check that
//! the program type-checks; the specific inferred type strings are not
//! asserted because they include fresh type-variable identifiers.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src` and return the inferred top-level type as a string,
/// or the formatted error message.
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

// ---------------------------------------------------------------------
// Array prototype methods on bare member access
// ---------------------------------------------------------------------

#[test]
fn array_map_as_value_typechecks() {
    // The reported bug: `const x = arr.map;` was rejected because the
    // plain-member path only knew about `length`. Calling
    // `arr.map(String)` worked because that goes through a different,
    // builtin-aware path.
    let src = "
        const arr = [1, 2, 3];
        const x = arr.map;
    ";
    check(src).expect("arr.map should be a valid value expression");
}

#[test]
fn array_filter_as_value_typechecks() {
    let src = "
        const arr = [1, 2, 3];
        const f = arr.filter;
    ";
    check(src).expect("arr.filter should be a valid value expression");
}

#[test]
fn array_reduce_as_value_typechecks() {
    let src = "
        const arr = [1, 2, 3];
        const r = arr.reduce;
    ";
    check(src).expect("arr.reduce should be a valid value expression");
}

#[test]
fn array_map_value_and_call_agree() {
    // Both forms should succeed. Sanity check that the value form
    // doesn't accidentally produce something that breaks downstream.
    let src = "
        const arr = [1, 2, 3];
        const m = arr.map;
        const stringified = arr.map(String);
    ";
    check(src).expect("both arr.map (value) and arr.map(...) should type-check");
}

#[test]
fn array_unknown_property_still_rejected() {
    // The fix should not paper over genuinely missing properties.
    let src = "
        const arr = [1, 2, 3];
        const bad = arr.thisDoesNotExist;
    ";
    let err = check(src).expect_err("unknown array property must be rejected");
    assert!(
        err.contains("thisDoesNotExist") || err.to_lowercase().contains("not found"),
        "error should mention the missing property; got: {err}"
    );
}

// ---------------------------------------------------------------------
// String prototype methods on bare member access
// ---------------------------------------------------------------------

#[test]
fn string_method_as_value_typechecks() {
    let src = "
        const s = \"hi\";
        const u = s.toUpperCase;
    ";
    check(src).expect("s.toUpperCase as a value should type-check");
}

#[test]
fn string_length_still_works() {
    let src = "
        const s = \"hi\";
        const n = s.length;
    ";
    check(src).expect("s.length should still type-check");
}

// ---------------------------------------------------------------------
// Callable-row static-method lookup: String.fromCharCode etc.
// (Covers the row-tail walking gap that motivated consolidating the
// two member-lookup functions.)
// ---------------------------------------------------------------------

#[test]
fn string_static_method_as_value_typechecks() {
    let src = "
        const f = String.fromCharCode;
    ";
    check(src).expect("String.fromCharCode as a value should type-check");
}

#[test]
fn string_static_method_call_and_value_agree() {
    let src = "
        const c = String.fromCharCode(65);
        const f = String.fromCharCode;
    ";
    check(src).expect("static method should resolve in both call and value position");
}

#[test]
fn number_static_method_as_value_typechecks() {
    let src = "
        const f = Number.isInteger;
    ";
    check(src).expect("Number.isInteger as a value should type-check");
}

// ---------------------------------------------------------------------
// Optional chaining goes through the same lookup path; make sure the
// builtin-method case still works there. (Caller: nullish.rs.)
// ---------------------------------------------------------------------

#[test]
fn array_method_via_optional_chain_typechecks() {
    let src = "
        const arr = [1, 2, 3];
        const m = arr?.map;
    ";
    check(src).expect("arr?.map should type-check via the optional-chain path");
}
