//! Reproductions for parser/inference gaps surfaced by attempting to
//! run inty against the htmx 2.x source (bigskysoftware/htmx,
//! `src/htmx.js`, ~5.3 kloc of plain JS — no TypeScript).
//!
//! Each test pins a minimal program that exercises one specific gap.
//! Tests for fixed gaps run by default and act as regression
//! coverage; tests for still-open gaps are marked `#[ignore]` with
//! a descriptive reason and can be exercised on demand with
//!
//!     cargo test -p inty --test htmx_gaps -- --ignored
//!
//! Gap status (see commits prefixed `parser:` / `infer:` / `tests:`
//! for history):
//!
//!   * Gap 1 — reserved word as member name: **fixed**
//!   * Gap 2 — `for (const x in/of y)`:       **fixed**
//!   * Gap 3 — `new Cls(...).member`:         **fixed**
//!   * Gap 4 — hoisting beyond adjacent decls: **fixed** via SCC
//!     dependency analysis (see `docs/scc-inference.md`)
//!   * Gap 5 — `delete o.k` aborted parsing: **fixed** via soft
//!     `Type::Error` diagnostic at the delete site (no row subtraction;
//!     the result is absorbed so downstream uses don't cascade)
//!   * Gap 6 — `async` arrow function: **fixed** by extending the
//!     arrow-head lookahead and reusing the same `Promise.resolve`
//!     wrap that `async function` declarations use

use inty::parser::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Parse-only check. Returns Ok(()) iff the parser accepts the input.
fn parses(src: &str) -> Result<(), String> {
    parse(src).map(|_| ()).map_err(|e| format!("{:?}", e))
}

/// Full parse + type-check pipeline with the embedded stdlib.
fn type_checks(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    state
        .infer_program_with_env(&env, &program)
        .map(|_| ())
        .map_err(|e| format!("type error: {:?}", e))
}

// ---------------------------------------------------------------------------
// Gap 1: reserved-word identifiers in member-access position.
//
// JavaScript permits reserved words as property names — both in object
// literal keys (which inty already accepts) and after a `.` in a
// member-access expression. inty's parser rejects the latter.
//
// htmx site:  newScript.async = false   // src/htmx.js:555
//
// Same shape would bite `.delete`, `.class`, `.case`, `.if`, `.for`,
// `.return`, etc. if any of them appeared as a property setter on the
// right-hand side of a `.`.
// ---------------------------------------------------------------------------

#[test]
fn reserved_word_as_member_async_assignment() {
    parses("var o = {}; o.async = 1;").expect("should accept `async` as a member name");
}

#[test]
fn reserved_word_as_member_async_read() {
    parses("var o = {async: 1}; var x = o.async;")
        .expect("should accept `async` as a member name on read");
}

// ---------------------------------------------------------------------------
// Gap 2: `for (const x in/of y)` is rejected.
//
// inty supports `for (let x of y)` and `for (var x in y)`, but the
// parser refuses to accept `const` as the binder for either loop form.
// Standard JS allows all three. htmx uses the `const` form 9 times
// because the loop variable is never reassigned.
//
// htmx sites:  for (const key in obj2)         // src/htmx.js:805
//              for (const preservedElt of …)   // src/htmx.js:1520
//              for (const child of …)          // src/htmx.js:2781
//              (and 6 more)
// ---------------------------------------------------------------------------

#[test]
fn for_const_in() {
    parses("for (const k in {}) {}")
        .expect("should accept `const` as binder in for-in");
}

#[test]
fn for_const_of() {
    parses("for (const k of []) {}")
        .expect("should accept `const` as binder in for-of");
}

// ---------------------------------------------------------------------------
// Gap 3: `new Cls(…)` followed by a member access fails to parse.
//
// `new Cls()` standalone is fine and is exercised in `examples/spa`,
// but the moment the constructed value is followed by `.member`,
// `[…]`, or `(…)`, the parser stops on the `.`. This holds whether
// the chain is on the same line or split across newlines.
//
// htmx sites:  new XPathEvaluator().createExpression(…)   // src/htmx.js:2764
//              new FormData(elt).forEach(…)               // src/htmx.js:3547
//
// Real-world JS chains constructor expressions all the time
// (`new URL(path, base).pathname`, `new Date().toISOString()`, etc.).
// The workaround is binding the constructed value to a temporary first.
// ---------------------------------------------------------------------------

#[test]
fn new_then_member_same_line() {
    let src = "
        function F() { return {y: 1}; }
        var v = new F().y;
    ";
    parses(src).expect("should accept member access on a `new` expression");
}

#[test]
fn new_then_member_next_line() {
    let src = "
        function F() { return {y: 1}; }
        var v = new F()
          .y;
    ";
    parses(src).expect("should accept member access on a `new` expression across newlines");
}

#[test]
fn new_with_args_then_method_call() {
    let src = "
        function F(a) { return {m: function() { return a; }}; }
        var v = new F(1).m();
    ";
    parses(src).expect("should accept a method call directly on a `new` expression");
}

// ---------------------------------------------------------------------------
// Gap 4: function-declaration hoisting only spans *adjacent* decls.
//
// inty hoists names within a "binding group" of contiguous function
// declarations, as documented in `examples/spa/gaps.md` (gap 1).
// Any other declaration — a `const`, `var`, expression statement,
// or object literal containing forward-referencing function
// expressions — breaks the group.
//
// In JS the entire function-scope of `function` declarations is
// hoisted regardless of intervening statements, so any pattern that
// declares a public-API object first and the helpers it references
// later (extremely common in single-file IIFE libraries) is rejected.
//
// htmx hits this immediately. The library is one IIFE that opens with
//
//     const htmx = {
//       values: function(elt, type) {
//         return getInputValues(elt, type || 'post').values
//       },
//       /* …30 more properties, mostly null placeholders… */
//     };
//     function getInputValues(elt, type) { /* … */ }
//     /* …~190 more function decls… */
//     return htmx;
//
// and `values`'s body references `getInputValues` before its
// declaration, which inty rejects as "Undefined variable".
//
// This is documented behaviour, not a parser bug — but lifting the
// adjacency restriction would let inty check a large class of
// real-world JS libraries without restructuring them.
// ---------------------------------------------------------------------------

#[test]
fn hoisting_through_intervening_const() {
    let src = "
        function a() { return b(); }
        const sep = 1;
        function b() { return 1; }
        var x = a();
    ";
    type_checks(src).expect("function `b` should hoist past the `const sep`");
}

#[test]
fn hoisting_into_object_literal_property() {
    // Mirrors htmx's `const htmx = { values: function(...) { getInputValues(...) }, … };
    // function getInputValues(...) {...}` pattern.
    let src = "
        const api = {
            values: function(elt) { return helper(elt); }
        };
        function helper(e) { return e; }
        var x = api.values(0);
    ";
    type_checks(src).expect("forward reference to `helper` should resolve via function hoisting");
}

#[test]
fn hoisting_iife_library_pattern() {
    let src = "
        var lib = (function() {
            const api = {
                run: function(x) { return helper(x); }
            };
            function helper(x) { return x; }
            return api;
        })();
        var y = lib.run(1);
    ";
    type_checks(src).expect("IIFE library pattern should type-check");
}

// ---------------------------------------------------------------------------
// Gap 5: `delete o.k` used to be a parse-time hard error, which aborted
// inference at the first `delete` in the file. In htmx 2.x this is line
// 1659: `delete internalData.onHandlers`. The fix accepts `delete` at
// parse time and emits a *soft* diagnostic during inference (the result
// is `Type::Error`, absorbed by downstream uses) so the rest of the file
// continues to type-check.
//
// We don't claim `delete` is sound — the row algebra doesn't model
// field subtraction. The diagnostic explicitly points at the safe
// workaround (`{ k: _drop, ...rest } = o`).
//
// htmx site:  delete internalData.onHandlers   // src/htmx.js:1659
// ---------------------------------------------------------------------------

#[test]
fn delete_parses() {
    parses("var o = {a: 1}; delete o.a;")
        .expect("delete should parse — diagnostic is moved to inference time");
}

// ---------------------------------------------------------------------------
// Gap 6: `async` arrow functions weren't recognised. The lookahead in
// `looks_like_arrow_function` only matched `ident =>` and `( ... ) =>`,
// so a leading `async` fell through to `parse_primary_expression`,
// which has no arm for `Token::Async` and produced
// `Unexpected token: found 'async', expected expression`.
//
// Real-world site:  acorn-loose `compiler/parse.js`:
//     const loadParser = async (fallbackParser = 'acorn', forceParser) => { ... }
//
// Fix: extend the lookahead to step past an optional `async`, and have
// `parse_arrow_function` consume that prefix, set the `next_fn_is_async`
// flag, and wrap the resulting body in `Promise.resolve(...)` with the
// same helper used for `async function` declarations.
// ---------------------------------------------------------------------------

#[test]
fn async_arrow_parens_with_defaults() {
    // The exact shape from acorn-loose.
    type_checks(
        "const loadParser = async (fallbackParser = 'acorn', forceParser) => {
            return fallbackParser;
        };
        var p = loadParser('acorn', 'x');",
    )
    .expect("async arrow with parenthesised params + default should type-check");
}

#[test]
fn async_arrow_single_ident_param() {
    // `async x => x` — single-identifier shorthand.
    type_checks(
        "const f = async x => x;
        var p = f(7);",
    )
    .expect("async single-ident arrow should type-check");
}

#[test]
fn async_arrow_block_body_with_await() {
    // `await` inside an async arrow's block body must be legal and must
    // produce the inner T of a `Promise<T>`.
    type_checks(
        "async function inner() { return 1; }
        const f = async () => {
            var x = await inner();
            return x + 1;
        };
        var p = f();",
    )
    .expect("async arrow block body should permit await");
}

#[test]
fn async_arrow_call_returns_promise() {
    // Calling an async arrow yields `Promise<T>`. We check via .then,
    // which is only defined on `Promise<T>` — if the call site's type
    // weren't a Promise this wouldn't type-check.
    type_checks(
        "const f = async () => 42;
        var p = f();
        var chained = p.then(function(n) { return Promise.resolve(n + 1); });",
    )
    .expect("async arrow result should be a Promise<T>");
}

#[test]
fn await_inside_non_async_arrow_still_rejected() {
    // The arrow's own async context — *not* an enclosing async
    // function — determines whether `await` is legal in its body.
    // The lookahead change must not loosen this.
    use inty::parser::parse;
    assert!(
        parse(
            "async function outer() {
                const f = () => {
                    var x = await Promise.resolve(1);
                    return x;
                };
                return f();
            }"
        )
        .is_err(),
        "await inside a non-async arrow nested in an async function should still be a parse error"
    );
}

#[test]
fn async_arrow_no_params() {
    parses("var f = async () => 1;")
        .expect("async arrow with zero parameters should parse");
}

#[test]
fn delete_in_middle_of_file_does_not_stop_inference() {
    // Inference should keep going past the `delete` so later
    // statements still get checked.
    use inty::parser::parse;
    use inty::stdlib::initial_env_with_stdlib;
    let src = "
        var o = {a: 1};
        delete o.a;
        var later = 1 + 2;
    ";
    let program = parse(src).expect("delete should parse");
    let (env, mut state) = initial_env_with_stdlib().expect("stdlib");
    let _ = state.infer_program_with_env(&env, &program);
    // The delete emits a diagnostic; that's expected.
    let errs = state.take_errors();
    assert_eq!(errs.len(), 1, "expected exactly one diagnostic (for delete), got: {:?}", errs);
}
