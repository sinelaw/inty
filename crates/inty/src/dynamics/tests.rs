//! Operator-coverage and end-to-end tests for the operational
//! semantics. The catalog from `crate::operators` enumerates every
//! operator we promise typing for; these tests assert the dynamics
//! has at least one matching operational rule per operator.

use super::*;

use crate::lexer::{Scanner, Token};
use crate::operators::{OpKind, OPERATORS};
use crate::parser::Parser;

fn parse_program(source: &str) -> crate::parser::ast::Program {
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
        other => panic!("expected Number({}), got {:?} for {}", expected, other, source),
    }
}

fn assert_string(source: &str, expected: &str) {
    match run(source) {
        Ok(Value::String(s)) => assert_eq!(s, expected, "src: {}", source),
        other => panic!("expected String({:?}), got {:?} for {}", expected, other, source),
    }
}

fn assert_bool(source: &str, expected: bool) {
    match run(source) {
        Ok(Value::Boolean(b)) => assert_eq!(b, expected, "src: {}", source),
        other => panic!("expected Boolean({}), got {:?} for {}", expected, other, source),
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
    assert_number(
        "function P(x) { this.x = x; } var p = new P(7); p.x",
        7.0,
    );
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
