//! JSDoc `@type` annotations on object-literal fields.
//!
//! `/** @type {T} */` placed immediately before a property declaration
//! attaches `T` as the field's declared type, and the initialiser is
//! checked against it as a `const`'s is. A field that starts as `null`
//! and is filled in later (the htmx-style public-API pattern) says so:
//!
//! ```js
//! const htmx = {
//!   /** @type {(typeof onLoadHelper) | Null} */
//!   onLoad: null,
//! };
//! function onLoadHelper(cb) { /* … */ }
//! htmx.onLoad = onLoadHelper;        // fills it in
//! ```
//!
//! (An earlier rule let a `null` initialiser stand for the annotated
//! type, so a field declared `() => R` and still `null` could be called:
//! accepted, and a TypeError at run time.)
//!
//! Coverage:
//!   1. Bare `@type T` and braced `@type {T}` are both accepted.
//!   2. `typeof Helper` resolves to `Helper`'s inferred function type.
//!   3. An initialiser whose type doesn't subsume the annotated type is
//!      an error, `null` and `undefined` included.
//!   4. The forward-reference case (`@type {typeof Helper}` where
//!      `Helper` is declared later in the same scope) works because
//!      SCC inference hoists `Helper` before the annotated object
//!      literal is processed.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

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
fn jsdoc_at_type_braced_primitive() {
    // The `@type {Number}` annotation declares `count` as Number. The
    // later assignment of `42` type-checks against the declared type,
    // and the program's tail expression `o.count + 1` is a Number.
    let src = r#"
        var o = {
            /** @type {Number} */
            count: 0
        };
        o.count = 42;
        o.count + 1
    "#;
    let ty = check(src).expect("@type field + later assign should type-check");
    assert!(ty.contains("Number"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_bare_form() {
    // JSDoc-classic bare form `@type Number` (no braces) is accepted.
    let src = r#"
        var o = {
            /**
             * @type Number
             * @default 0
             */
            count: 0
        };
        o.count = 7;
        o.count
    "#;
    let ty = check(src).expect("bare @type form should type-check");
    assert!(ty.contains("Number"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_typeof_helper() {
    // The headline htmx pattern: `@type {typeof helper}` where helper
    // is a forward-referenced function declared later in the same
    // scope. SCC inference hoists helper, so it's in scope when the
    // object literal is processed.
    let src = r#"
        const api = {
            /** @type {(typeof helper) | Null} */
            run: null
        };
        function helper(n) { return n + 1; }
        api.run = helper;
        const run = api.run;
        run ? run(10) : 0
    "#;
    let ty = check(src).expect("typeof-helper pattern should type-check");
    assert!(ty.contains("Number"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_non_placeholder_value_still_checked() {
    // The placeholder relaxation only fires for literal `null` /
    // `undefined`. A non-placeholder initialiser whose type doesn't
    // match the annotation must still error.
    let src = r#"
        var o = {
            /** @type {Number} */
            count: "oops"
        };
    "#;
    let err = check(src).expect_err("annotated mismatch should still error");
    assert!(
        err.contains("mismatch") || err.contains("expected"),
        "got: {}",
        err
    );
}

#[test]
fn jsdoc_at_type_does_not_steal_inline_annotation() {
    // Inline `/*: T */` annotations win when both styles are present.
    // Use a type that wouldn't accept the placeholder so we know the
    // inline form was used.
    let src = r#"
        var o = {
            /** @type {String} */
            count /*: Number */: 5
        };
        o.count + 1
    "#;
    let ty = check(src).expect("inline annotation should win");
    assert!(ty.contains("Number"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_unknown_alias_degrades_to_warning() {
    // JSDoc annotations are best-effort hints (matches TypeScript's
    // handling of unrecognised JSDoc): an annotation referencing a
    // type alias inty doesn't model should NOT fail the whole field.
    // Inference still succeeds and the field takes its synthesised
    // type from the initialiser. This is the htmx case where
    // `@type HtmxSwapStyle` references a TypeScript-only alias.
    let src = r#"
        var o = {
            /** @type {HtmxSwapStyle} */
            kind: "innerHTML"
        };
        o.kind
    "#;
    let ty = check(src).expect("unknown alias in @type should not error");
    // The annotation was ignored, so we fall back to the literal's
    // widened type — String (singleton widened for object literal
    // synthesis, matching the existing widening rule).
    assert!(ty.contains("String"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_typeof_unknown_name_degrades() {
    // `typeof X` for an identifier not in scope: parse failure is
    // suppressed for JSDoc annotations (TypeScript ignores unrecognised
    // JSDoc), the field takes its synthesised type instead. A typo
    // becomes a no-op rather than a fatal error.
    let src = r#"
        var o = {
            /** @type {typeof doesNotExist} */
            x: 1
        };
        o.x + 0
    "#;
    // Should not error overall — annotation is silently ignored.
    let ty = check(src).expect("unknown typeof should degrade, not error");
    assert!(ty.contains("Number"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_fixture_htmx_iife_typechecks() {
    // Realistic-shape fixture: the htmx public-API pattern. The IIFE
    // declares a public-API object with null-initialised fields,
    // declares helper functions later, and assigns the helpers into
    // the fields. Without `@type {typeof helper}` parsing this would
    // fail with "expected Null, found Function" on every assignment.
    let src = include_str!("fixtures/jsdoc_at_type_iife.js");
    let _ = check(src).expect("htmx-shape fixture should type-check");
}

#[test]
fn jsdoc_at_type_multiline_braced_object() {
    // Multi-line braced form with `*` decoration — JSDoc convention
    // when the type spans several lines.
    let src = r#"
        var o = {
            /**
             * @type {{
             *   x: Number,
             *   y: String
             * }}
             */
            point: {x: 0, y: ""}
        };
        o.point = { x: 1, y: "a" };
        o.point.y
    "#;
    let ty = check(src).expect("multiline braced @type should type-check");
    assert!(ty.contains("String"), "got: {}", ty);
}

#[test]
fn jsdoc_at_type_null_initialiser_is_checked() {
    // A `@type` field's initialiser is checked as a `const`'s is: a field
    // declared a function that starts as `null` would throw when called
    // before it is filled in. Rosaclef's `hooks` and `inputSources`.
    for init in ["null", "undefined"] {
        let src = format!(
            r#"
            export const hooks = {{
                /** @type {{() => Undefined}} */
                mark: {init},
            }};
            /** function a() => Undefined */
            export function a() {{ hooks.mark(); }}
        "#
        );
        let err = check(&src).expect_err("a null-initialised function field should be rejected");
        assert!(
            err.contains("() => Undefined") && (err.contains("Null") || err.contains("Undefined")),
            "{init}: {err}"
        );
    }
    // Saying it may be nothing is accepted, and a call then needs a test.
    let ok = r#"
        export const hooks = {
            /** @type {(() => Undefined) | Null} */
            mark: null,
        };
        /** function a() => Undefined */
        export function a() { const m = hooks.mark; if (m) m(); }
    "#;
    check(ok).expect("`(() => Undefined) | Null` admits null");
    let called = r#"
        export const hooks = {
            /** @type {(() => Undefined) | Null} */
            mark: null,
        };
        /** function a() => Undefined */
        export function a() { hooks.mark(); }
    "#;
    check(called).expect_err("calling a field that may be null is rejected");
}

#[test]
fn inline_field_annotation_null_initialiser_is_checked() {
    // The inline form always checked its initialiser; pinned alongside.
    for init in ["null", "undefined", "3"] {
        let src = format!("export const o = {{ f /*: () => Undefined */: {init} }};");
        check(&src).expect_err(&format!("{init} is not a function"));
    }
}

#[test]
fn jsdoc_at_type_checked_against_an_expected_row() {
    // The checking path (an object literal where an annotated type is
    // expected) checks the initialiser too.
    let src = r#"
        /** type Hooks = {mark: (() => Undefined) | Null} */
        /** const h: Hooks */
        const h = {
            /** @type {() => Undefined} */
            mark: null,
        };
    "#;
    check(src).expect_err("null against `() => Undefined`");
}
