//! Tests for the Lua frontend: AST lowerings and end-to-end inference.

use super::parse_source;
use crate::ast::{BinOp, Expr, Literal, Stmt, UnaryOp};
use crate::builtins::initial_env;
use crate::infer::InferState;

fn parse(src: &str) -> Vec<Stmt> {
    parse_source(src).expect("parse failed").statements
}

/// Type-check a Lua program; returns the collected errors (empty = ok).
fn check(src: &str) -> Vec<String> {
    let program = parse_source(src).expect("parse failed");
    let mut state = InferState::new();
    let mut env = initial_env();
    for stmt in &program.statements {
        match state.infer_stmt(&env, stmt) {
            Ok((_, new_env)) => env = new_env,
            Err(e) => return vec![format!("{:?}", e)],
        }
    }
    state.errors.iter().map(|e| format!("{:?}", e)).collect()
}

// ---- lowerings ----

#[test]
fn local_declaration() {
    match &parse("local x = 1")[0] {
        Stmt::Var { declarations, .. } => {
            assert_eq!(declarations[0].name, "x");
            assert!(matches!(
                declarations[0].init,
                Some(Expr::Lit { value: Literal::Number(n), .. }) if n == 1.0
            ));
        }
        other => panic!("expected var, got {:?}", other),
    }
}

#[test]
fn nil_is_null_literal() {
    match &parse("local y = nil")[0] {
        Stmt::Var { declarations, .. } => assert!(matches!(
            declarations[0].init,
            Some(Expr::Lit {
                value: Literal::Null,
                ..
            })
        )),
        _ => unreachable!(),
    }
}

#[test]
fn concat_lowers_to_plus() {
    // `..` maps to `+` (string concat via the Plus type class).
    assert!(matches!(
        first_expr_in("local s = \"a\" .. \"b\""),
        Expr::Binary { op: BinOp::Add, .. }
    ));
}

#[test]
fn length_lowers_to_member() {
    let e = match &parse("local n = #t")[0] {
        Stmt::Var { declarations, .. } => declarations[0].init.clone().unwrap(),
        _ => unreachable!(),
    };
    match e {
        Expr::Member { property, .. } => assert_eq!(property, "length"),
        other => panic!("expected member, got {:?}", other),
    }
}

#[test]
fn not_equal_is_strict() {
    let e = match &parse("local b = x ~= y")[0] {
        Stmt::Var { declarations, .. } => declarations[0].init.clone().unwrap(),
        _ => unreachable!(),
    };
    assert!(matches!(
        e,
        Expr::Binary {
            op: BinOp::NotEqEq,
            ..
        }
    ));
}

#[test]
fn repeat_is_dowhile_with_negation() {
    match &parse("repeat x = x + 1 until x > 10")[0] {
        Stmt::DoWhile { test, .. } => {
            assert!(matches!(
                test,
                Expr::Unary {
                    op: UnaryOp::Not,
                    ..
                }
            ));
        }
        other => panic!("expected do-while, got {:?}", other),
    }
}

#[test]
fn numeric_for_desugars() {
    match &parse("for i = 1, 10 do x = i end")[0] {
        Stmt::For {
            init: Some(_),
            test: Some(_),
            update: Some(_),
            ..
        } => {}
        other => panic!("expected C-style for, got {:?}", other),
    }
}

#[test]
fn elseif_nests() {
    match &parse("if a then x = 1 elseif b then x = 2 else x = 3 end")[0] {
        Stmt::If {
            alternate: Some(alt),
            ..
        } => {
            assert!(matches!(**alt, Stmt::If { .. }));
        }
        other => panic!("expected if with nested elseif, got {:?}", other),
    }
}

#[test]
fn method_def_injects_self() {
    // `function t:m(a) ... end` desugars to an assignment of a function
    // whose first parameter is `self`.
    match &parse("function t:m(a) return a end")[0] {
        Stmt::Expr {
            expression: Expr::Assign { right, .. },
            ..
        } => match &**right {
            Expr::Function { params, .. } => {
                assert_eq!(params[0].name, "self");
                assert_eq!(params[1].name, "a");
            }
            other => panic!("expected function, got {:?}", other),
        },
        other => panic!("expected assignment, got {:?}", other),
    }
}

#[test]
fn method_call_keeps_receiver() {
    let e = match &parse("local r = obj:greet(1)")[0] {
        Stmt::Var { declarations, .. } => declarations[0].init.clone().unwrap(),
        _ => unreachable!(),
    };
    match e {
        Expr::Call {
            callee, arguments, ..
        } => {
            assert!(matches!(*callee, Expr::Member { .. }));
            assert_eq!(arguments.len(), 1);
        }
        other => panic!("expected call, got {:?}", other),
    }
}

#[test]
fn array_vs_record_tables() {
    assert!(matches!(
        first_expr_in("local a = {1, 2, 3}"),
        Expr::Array { .. }
    ));
    assert!(matches!(
        first_expr_in("local r = {x = 1, y = 2}"),
        Expr::Object { .. }
    ));
}

fn first_expr_in(src: &str) -> Expr {
    match &parse(src)[0] {
        Stmt::Var { declarations, .. } => declarations[0].init.clone().unwrap(),
        _ => unreachable!(),
    }
}

#[test]
fn string_subscript_is_field_access() {
    // `t["name"]` lowers to a `.name` member read; `t[i]` stays dynamic.
    match first_expr_in("local v = t[\"name\"]") {
        Expr::Member { property, .. } => assert_eq!(property, "name"),
        other => panic!("expected member, got {:?}", other),
    }
    assert!(matches!(
        first_expr_in("local v = t[i]"),
        Expr::ComputedMember { .. }
    ));
}

// ---- rejections (limited subset) ----

#[test]
fn rejects_multiple_return() {
    assert!(parse_source("function f() return 1, 2 end").is_err());
}

#[test]
fn rejects_generic_for() {
    assert!(parse_source("for k, v in pairs(t) do end").is_err());
}

#[test]
fn rejects_mixed_table() {
    assert!(parse_source("local t = {1, x = 2}").is_err());
}

#[test]
fn rejects_varargs() {
    assert!(parse_source("function f(...) end").is_err());
}

// ---- end-to-end inference ----

#[test]
fn infers_arithmetic_function() {
    assert!(check("local function add(a, b) return a + b end\nlocal n = add(1, 2)").is_empty());
}

#[test]
fn infers_record_field_access() {
    let src = "local p = {name = \"alice\", age = 30}\nlocal nm = p.name";
    assert!(check(src).is_empty());
}

#[test]
fn string_concat_typechecks() {
    assert!(check("local s = \"a\" .. \"b\"").is_empty());
}

#[test]
fn numeric_for_typechecks() {
    let src = "local total = 0\nfor i = 1, 10 do total = total + i end";
    assert!(check(src).is_empty());
}

#[test]
fn mixed_plus_operands_rejected() {
    // `1 + "x"` must not type-check: inty's `+` requires matching operands.
    assert!(!check("local x = 1 + \"oops\"").is_empty());
}
