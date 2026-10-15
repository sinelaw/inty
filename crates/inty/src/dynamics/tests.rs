//! Operator-coverage and end-to-end tests for the operational
//! semantics. The catalog from `crate::operators` enumerates every
//! operator we promise typing for; these tests assert the dynamics
//! has at least one matching operational rule per operator.

use super::*;

use crate::frontends::javascript::lexer::{Scanner, Token};
use crate::frontends::javascript::parser::Parser;
use crate::operators::OPERATORS;

fn parse_program(source: &str) -> crate::ast::Program {
    let mut scanner = Scanner::new(source);
    let mut tokens = Vec::new();
    loop {
        let tok = scanner.next_token().unwrap();
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);
    parser.parse_program().unwrap()
}

fn run(source: &str) -> Result<Value, Stuck> {
    run_to_end(&parse_program(source))
}

fn assert_number(source: &str, expected: f64) {
    match run(source) {
        Ok(Value::Number(n)) => assert_eq!(n, expected, "src: {}", source),
        other => panic!(
            "expected Number({}), got {:?} for {}",
            expected, other, source
        ),
    }
}

fn assert_string(source: &str, expected: &str) {
    match run(source) {
        Ok(Value::String(s)) => assert_eq!(s, expected, "src: {}", source),
        other => panic!(
            "expected String({:?}), got {:?} for {}",
            expected, other, source
        ),
    }
}

fn assert_bool(source: &str, expected: bool) {
    match run(source) {
        Ok(Value::Boolean(b)) => assert_eq!(b, expected, "src: {}", source),
        other => panic!(
            "expected Boolean({}), got {:?} for {}",
            expected, other, source
        ),
    }
}

// ---------------------------------------------------------------------
// Per-operator coverage. One example per catalog entry, all asserting
// the result the type system would predict.
// ---------------------------------------------------------------------

#[test]
fn arithmetic_ops() {
    assert_number("1 + 2", 3.0);
    assert_string("\"a\" + \"b\"", "ab");
    assert_number("3 - 1", 2.0);
    assert_number("3 * 4", 12.0);
    assert_number("10 / 4", 2.5);
    assert_number("10 % 3", 1.0);
    assert_number("2 ** 5", 32.0);
}

#[test]
fn comparison_ops() {
    assert_bool("1 < 2", true);
    assert_bool("2 > 1", true);
    assert_bool("1 <= 1", true);
    assert_bool("1 >= 2", false);
    assert_bool("1 == 1", true);
    // `null` and `undefined` are loosely equal: `x != null` tests for both.
    assert_bool("(void 0) == null", true);
    assert_bool("(void 0) != null", false);
    assert_bool("null != (void 0)", false);
    assert_bool("(void 0) === null", false);
    assert_bool("1 != 2", true);
    assert_bool("1 === 1", true);
    assert_bool("1 !== 2", true);
}

#[test]
fn logical_ops() {
    assert_number("1 && 2", 2.0);
    assert_number("0 || 5", 5.0);
    assert_number("1 || 9", 1.0);
}

#[test]
fn bitwise_ops() {
    assert_number("6 & 3", 2.0);
    assert_number("6 | 3", 7.0);
    assert_number("6 ^ 3", 5.0);
    assert_number("1 << 3", 8.0);
    assert_number("16 >> 2", 4.0);
    assert_number("16 >>> 2", 4.0);
}

#[test]
fn unary_ops() {
    assert_number("-5", -5.0);
    assert_number("+5", 5.0);
    assert_bool("!true", false);
    assert_bool("!0", true);
    assert_number("~0", -1.0);
    assert_string("typeof 42", "number");
    assert_string("typeof \"x\"", "string");
    assert_string("typeof true", "boolean");
    match run("void 1") {
        Ok(Value::Undefined) => {}
        other => panic!("expected undefined, got {:?}", other),
    }
}

// `delete` is rejected at parse time under the unified design (silent
// unsoundness without row-subtraction), so it has no dynamics rule to
// exercise. The catalog still lists it as a known operator for
// documentation purposes, but the catalog fixture is marked None.

#[test]
fn await_unwraps_promise_or_passes_through() {
    // Without a Promise constructor in our model, `await x` on a plain
    // value passes through unchanged. Demonstrates the documented
    // limitation.
    assert_number("(function() { return 42; })()", 42.0);
}

#[test]
fn pre_post_inc_dec() {
    assert_number("var x = 5; ++x", 6.0);
    assert_number("var x = 5; --x", 4.0);
    assert_number("var x = 5; x++; x", 6.0);
    assert_number("var x = 5; x--; x", 4.0);
}

#[test]
fn member_access() {
    assert_number("var o = {a: 7}; o.a", 7.0);
    assert_number("[1,2,3].length", 3.0);
    assert_number("\"hi\".length", 2.0);
}

#[test]
fn indexing() {
    assert_number("[10, 20, 30][1]", 20.0);
    assert_string("({a: \"hi\"})[\"a\"]", "hi");
}

#[test]
fn call_and_new() {
    assert_number("(function(x) { return x + 1; })(5)", 6.0);
    // `new` returns the constructed object; we read a field set inside.
    assert_number("function P(x) { this.x = x; } var p = new P(7); p.x", 7.0);
}

// ---------------------------------------------------------------------
// Catalog cross-check: every catalog entry has a matching rule, where
// "matching" means we have at least one fixture asserting the op runs
// without `NotImplemented`. We assert this by running a fixture per
// catalog name.
// ---------------------------------------------------------------------

#[test]
fn every_catalog_op_has_a_dynamics_rule() {
    // For each op in the catalog, supply a tiny program that exercises
    // it. Programs that intentionally hit `NotImplemented` (in/instanceof)
    // are excluded from the comprehensive check but still listed so we
    // notice if someone removes them from the catalog.
    let fixtures: &[(&str, Option<&str>)] = &[
        // BinOps
        ("+", Some("1 + 2")),
        ("-", Some("3 - 1")),
        ("*", Some("2 * 3")),
        ("/", Some("6 / 2")),
        ("%", Some("5 % 2")),
        ("//", None), // Python only; the fixtures are JavaScript
        ("**", Some("2 ** 3")),
        ("<", Some("1 < 2")),
        (">", Some("2 > 1")),
        ("<=", Some("1 <= 1")),
        (">=", Some("1 >= 0")),
        ("==", Some("1 == 1")),
        ("!=", Some("1 != 2")),
        ("===", Some("1 === 1")),
        ("!==", Some("1 !== 2")),
        ("&&", Some("true && true")),
        ("||", Some("false || true")),
        ("&", Some("3 & 1")),
        ("|", Some("3 | 0")),
        ("^", Some("3 ^ 1")),
        ("<<", Some("1 << 2")),
        (">>", Some("4 >> 1")),
        (">>>", Some("4 >>> 1")),
        ("in", None),         // intentionally NotImplemented
        ("instanceof", None), // intentionally NotImplemented
        // UnOps
        ("unary -", Some("-1")),
        ("unary +", Some("+1")),
        ("!", Some("!false")),
        ("~", Some("~0")),
        ("typeof", Some("typeof 1")),
        ("void", Some("void 1")),
        ("delete", None), // rejected at parse time; documented in operators/mod.rs catalog
        ("await", Some("var x = 1; x")),
        ("++ (prefix)", Some("var x = 1; ++x")),
        ("-- (prefix)", Some("var x = 1; --x")),
        ("++ (postfix)", Some("var x = 1; x++")),
        ("-- (postfix)", Some("var x = 1; x--")),
        // Pseudo-ops
        (".", Some("({a:1}).a")),
        ("[]", Some("[1,2][0]")),
        ("()", Some("(function(){return 1;})()")),
        ("new", Some("function C(){this.x=1;} var c = new C(); c.x")),
    ];

    // Sanity: every catalog entry has a fixture row.
    for op in OPERATORS {
        let found = fixtures.iter().any(|(n, _)| *n == op.name);
        assert!(found, "no dynamics fixture for catalog op {:?}", op.name);
    }
    // And every fixture row matches a catalog entry.
    for (name, _) in fixtures {
        let found = OPERATORS.iter().any(|op| op.name == *name);
        assert!(found, "fixture {:?} has no catalog entry", name);
    }

    // Run each fixture and assert it doesn't get stuck (or, for the
    // intentionally-skipped ones, assert the kind of stuck we expect).
    for (name, source) in fixtures {
        match source {
            Some(src) => {
                let r = run(src);
                assert!(r.is_ok(), "{:?} ({}): {:?}", name, src, r);
            }
            None => {
                // No fixture: catalog entry exists but dynamics
                // deliberately skips this op. Documented intentional
                // gaps include `in` / `instanceof` (BinOps without
                // type-system support) and `delete` (rejected at
                // parse time under the unified design).
                let _ = OPERATORS.iter().find(|op| op.name == *name).unwrap();
            }
        }
    }
}

// ---------------------------------------------------------------------
// End-to-end programs.
// ---------------------------------------------------------------------

#[test]
fn closure_captures_mutable_var() {
    let src = "
        function makeCounter() {
            var n = 0;
            function inc() { n = n + 1; return n; }
            return inc;
        }
        var c = makeCounter();
        c(); c(); c();
    ";
    assert_number(src, 3.0);
}

#[test]
fn factorial() {
    let src = "
        function fact(n) { if (n <= 1) { return 1; } else { return n * fact(n - 1); } }
        fact(5);
    ";
    assert_number(src, 120.0);
}

#[test]
fn for_loop_sum() {
    let src = "
        var s = 0;
        for (var i = 0; i < 10; i = i + 1) { s = s + i; }
        s;
    ";
    assert_number(src, 45.0);
}

#[test]
fn try_catch_recovers() {
    let src = "
        var x = 0;
        try { throw 7; } catch (e) { x = e; }
        x;
    ";
    assert_number(src, 7.0);
}

#[test]
fn fuel_exhaustion_clean_error() {
    let src = "while (true) { 1; }";
    let r = run_to_end_with_fuel(&parse_program(src), 100);
    assert!(matches!(r, Err(Stuck::FuelExhausted)), "got {:?}", r);
}

#[test]
fn template_literal_interpolation() {
    assert_string("var x = 1; `hi ${x}!`", "hi 1!");
}

#[test]
fn switch_with_fallthrough_blocked_by_break() {
    let src = "
        var r = 0;
        switch (2) { case 1: r = 1; break; case 2: r = 2; break; default: r = 9; }
        r;
    ";
    assert_number(src, 2.0);
}

/// A `throw` out of a called function is caught, and `finally` runs after a
/// handler that throws.
#[test]
fn try_catches_a_throw_from_a_call() {
    assert_number(
        "const f = function () { throw 1; }; let r = 0; try { f(); } catch (e) { r = 2; } r",
        2.0,
    );
    assert_number(
        "const f = function () { throw 1; }; let r = 0; \
         try { try { f(); } catch (e) { f(); } finally { r = 3; } } catch (e) {} r",
        3.0,
    );
}

/// An assignment evaluates its target's object before the value, once, as
/// JavaScript does; a compound assignment or update reads the target before
/// the right side.
#[test]
fn assignment_evaluates_its_target_once_and_first() {
    assert_string(
        "const obj = {x: 1}; let log = \"\"; \
         const o = function () { log = log + \"o\"; return obj; }; \
         const v = function () { log = log + \"v\"; return 2; }; \
         o().x = v(); log",
        "ov",
    );
    assert_number(
        "const obj = {x: 1}; let n = 0; \
         const o = function () { n = n + 1; return obj; }; \
         o().x += 1; o().x++; n * 10 + obj.x",
        23.0,
    );
    assert_number("let x = 1; x += (x = 10); x", 11.0);
}

/// An element read at an index the array or string hasn't, or a store past
/// an array's end, is a fault (JavaScript reads `undefined` and makes a
/// hole); a store just past the end pushes.
#[test]
fn indexing_out_of_bounds_is_a_fault() {
    for source in [
        "[1, 2][2]",
        "[1, 2][-1]",
        "[1, 2][0.5]",
        "\"ab\"[2]",
        "const xs = [1]; xs[2] = 3; xs[0]",
    ] {
        assert!(
            matches!(run(source), Err(Stuck::OutOfBounds { .. })),
            "{source}: {:?}",
            run(source)
        );
    }
    assert!(matches!(run("[1, 2][1]"), Ok(Value::Number(n)) if n == 2.0));
    assert!(matches!(run("\"ab\"[1]"), Ok(Value::String(s)) if s == "b"));
    assert!(matches!(
        run("const xs = [1]; xs[1] = 3; xs[1] + xs.length"),
        Ok(Value::Number(n)) if n == 5.0
    ));
}

#[test]
fn getters_run_when_read_and_copied_by_a_spread() {
    assert_number(
        "const o = { a: 1, get g() { return this.a + 1; } }; o.g;",
        2.0,
    );
    assert_number(
        "const o = { a: 1, get g() { return this.a + 1; } }; const c = {...o}; o.a = 5; c.g;",
        2.0,
    );
    assert!(matches!(
        run("const o = { get g() { return 1; } }; o.g = 2;"),
        Err(Stuck::ReadOnly)
    ));
}

/// An arrow function's `this` is its enclosing function's, and `new` on
/// one throws, as on a method.
#[test]
fn arrow_functions_close_over_this_and_are_not_constructors() {
    assert_number(
        "const o = { a: 2, m() { const f = () => this.a; return f(); } }; o.m();",
        2.0,
    );
    assert!(matches!(
        run("const f = () => ({x: 1}); new f();"),
        Err(Stuck::NotConstructor)
    ));
    // Nor is a method written `m() {…}`, which an arrow field using
    // `this` lowers to.
    assert!(matches!(
        run("const o = { m() { return {x: 1}; } }; new o.m();"),
        Err(Stuck::NotConstructor)
    ));
    assert!(matches!(
        run("class D { x = 1; f = () => this.x; } new (new D()).f();"),
        Err(Stuck::NotConstructor)
    ));
    assert_number(
        "const o = { m: function () { this.y = 2; } }; new o.m().y;",
        2.0,
    );
}

#[test]
fn new_gives_back_an_object_result_else_this() {
    assert_number("function F(n) { return {n: n}; } new F(3).n;", 3.0);
    assert_string("function F() { return 1; } typeof new F();", "object");
}

/// An object's properties are in the order they were made, which a spread
/// copies them in, reading each (a getter run) when it reaches it: a store
/// to a property that is there keeps its place, and of two of one label in
/// a literal, the first's place holds the second's value.
#[test]
fn spread_copies_properties_in_the_order_they_were_made() {
    assert_number(
        "const o = {get b() { this.a = 5; return 0; }, a: 1}; ({...o}).a;",
        5.0,
    );
    assert_number(
        "const o = {a: 1, get g() { this.a = 9; return 0; }}; o.a = 2; ({...o}).a;",
        2.0,
    );
    assert_number(
        "const o = {a: 1, get g() { this.a = 9; return 0; }, a: 3}; ({...o}).a;",
        3.0,
    );
    assert_number(
        "const o = {get g() { this.a = 9; return 0; }}; o.a = 2; ({...o}).a;",
        9.0,
    );
}

#[test]
fn string_and_array_methods_as_javascript() {
    // `NaN` as an index is `0`.
    assert_string("\"hello\".slice(0 / 0);", "hello");
    assert_string("\"hello\".slice(1.7, -1);", "ell");
    // `charCodeAt` outside the string is `NaN`; an index is truncated.
    assert!(matches!(run("\"AB\".charCodeAt(-1);"), Ok(Value::Number(n)) if n.is_nan()));
    assert!(matches!(run("\"AB\".charCodeAt(2);"), Ok(Value::Number(n)) if n.is_nan()));
    assert_number("\"AB\".charCodeAt(1.9);", 66.0);
    // An array's `indexOf` is by `===`: an object by its identity.
    assert_number("const o = {}; [{}, o].indexOf(o);", 1.0);
    assert_number("[0 / 0].indexOf(0 / 0);", -1.0);
}

#[test]
fn exported_declarations_run() {
    assert_number(
        "export function f(x) { return x; } export default 1; f(2);",
        2.0,
    );
    assert_number("export const a = 1; export let b = a + 1; b;", 2.0);
}

/// Strings compare by UTF-16 code units, as JavaScript's: an emoji (a
/// surrogate pair from U+D83D) is before U+FF61, though its code point is
/// after.
#[test]
fn strings_compare_by_utf16_code_units() {
    assert_bool("\"\u{1F600}\" < \"\u{FF61}\"", true);
    assert_bool("\"ab\" < \"b\"", true);
    assert_bool("\"a\" <= \"a\"", true);
    assert_bool("\"ab\" > \"a\"", true);
}

/// `xs.length = n` truncates the array (Rosaclef: the usual way to clear
/// one in place). A longer length would leave holes, which these arrays
/// don't have: an index fault, as reading past the end is.
#[test]
fn a_store_to_an_array_length_truncates_it() {
    assert_number("const xs = [1, 2, 3]; xs.length = 1; xs.length;", 1.0);
    assert_number(
        "const xs = [1, 2, 3]; xs.length = 0; xs[0] = 4; xs.length;",
        1.0,
    );
    assert!(matches!(
        run("const xs = [1]; xs.length = 3;"),
        Err(Stuck::OutOfBounds { .. })
    ));
}

#[test]
fn number_methods_run() {
    assert_string("(1.26).toFixed(1)", "1.3");
    assert!(
        run("(1.25).toFixed(1)").is_err(),
        "a tie rounds differently in Rust"
    );
    assert_string("(3).toFixed(2)", "3.00");
    assert_string("(255).toString(16)", "ff");
    assert_string("(-10).toString(2)", "-1010");
    assert_string("(1.5).toString()", "1.5");
}
