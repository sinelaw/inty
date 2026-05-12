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
//! Gap status (see commits prefixed `parser:` / `tests:` for history):
//!
//!   * Gap 1 — reserved word as member name: **fixed**
//!   * Gap 2 — `for (const x in/of y)`:       **fixed**
//!   * Gap 3 — `new Cls(...).member`:         **fixed**
//!   * Gap 4 — hoisting beyond adjacent decls: open (needs design)

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
#[ignore = "htmx gap 4: hoisting limited to adjacent function decls; `const` between two decls breaks the group"]
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
#[ignore = "htmx gap 4: function expression inside object literal can't see later function decl in same scope"]
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
#[ignore = "htmx gap 4: IIFE-wrapped library pattern (htmx, jQuery, lodash, …) not type-checkable"]
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
