//! Tests for the Python frontend: AST lowerings and end-to-end inference.

use super::parse_source;
use crate::ast::{BinOp, Expr, Literal, Stmt, VarKind};
use crate::builtins::initial_env;
use crate::infer::InferState;

fn parse(src: &str) -> Vec<Stmt> {
    parse_source(src).expect("parse failed").statements
}

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

/// Like `check`, but runs the whole-program path so class factories get
/// branded nominally (the per-statement `check` skips brand setup).
fn check_program(src: &str) -> Vec<String> {
    let program = parse_source(src).expect("parse failed");
    let mut state = InferState::new();
    let env = initial_env();
    if let Err(e) = state.infer_program_with_env(&env, &program) {
        return vec![format!("{:?}", e)];
    }
    state.errors.iter().map(|e| format!("{:?}", e)).collect()
}

fn init_of(src: &str) -> Expr {
    match &parse(src)[0] {
        Stmt::Var { declarations, .. } => declarations[0].init.clone().unwrap(),
        other => panic!("expected var, got {:?}", other),
    }
}

// ---- lowerings ----

#[test]
fn first_assignment_is_hoisted_var() {
    match &parse("x = 1")[0] {
        Stmt::Var { kind, declarations, .. } => {
            assert_eq!(*kind, VarKind::Var);
            assert_eq!(declarations[0].name, "x");
        }
        other => panic!("expected var, got {:?}", other),
    }
}

#[test]
fn reassignment_is_plain_assign() {
    let stmts = parse("x = 1\nx = 2");
    assert!(matches!(stmts[0], Stmt::Var { .. }));
    assert!(matches!(
        stmts[1],
        Stmt::Expr {
            expression: Expr::Assign { .. },
            ..
        }
    ));
}

#[test]
fn none_true_false() {
    assert!(matches!(
        init_of("a = None"),
        Expr::Lit { value: Literal::Null, .. }
    ));
    assert!(matches!(
        init_of("a = True"),
        Expr::Lit { value: Literal::Boolean(true), .. }
    ));
}

#[test]
fn def_lowers_to_function_decl() {
    match &parse("def f(a, b):\n    return a + b")[0] {
        Stmt::FunctionDecl { name, params, .. } => {
            assert_eq!(name, "f");
            assert_eq!(params.len(), 2);
        }
        other => panic!("expected function decl, got {:?}", other),
    }
}

#[test]
fn annotations_are_discarded() {
    // `x: int = 5` declares x = 5 with the annotation dropped.
    match &parse("x: int = 5")[0] {
        Stmt::Var { declarations, .. } => {
            assert!(declarations[0].type_annotation.is_none());
            assert!(matches!(
                declarations[0].init,
                Some(Expr::Lit { value: Literal::Number(n), .. }) if n == 5.0
            ));
        }
        other => panic!("expected var, got {:?}", other),
    }
}

#[test]
fn elif_nests() {
    match &parse("if a:\n    x = 1\nelif b:\n    x = 2\nelse:\n    x = 3")[0] {
        Stmt::If { alternate: Some(alt), .. } => assert!(matches!(**alt, Stmt::If { .. })),
        other => panic!("expected if/elif, got {:?}", other),
    }
}

#[test]
fn ternary_is_conditional() {
    assert!(matches!(init_of("y = 1 if c else 2"), Expr::Conditional { .. }));
}

#[test]
fn for_in_is_for_of() {
    match &parse("for x in items:\n    pass")[0] {
        Stmt::ForOf { .. } => {}
        other => panic!("expected for-of, got {:?}", other),
    }
}

#[test]
fn lambda_is_function() {
    assert!(matches!(init_of("f = lambda a: a + 1"), Expr::Function { .. }));
}

#[test]
fn power_is_right_assoc() {
    // 2 ** 3 ** 2 == 2 ** (3 ** 2)
    match init_of("y = 2 ** 3 ** 2") {
        Expr::Binary { op: BinOp::Pow, right, .. } => {
            assert!(matches!(*right, Expr::Binary { op: BinOp::Pow, .. }));
        }
        other => panic!("expected pow, got {:?}", other),
    }
}

#[test]
fn list_and_dict() {
    assert!(matches!(init_of("a = [1, 2, 3]"), Expr::Array { .. }));
    assert!(matches!(init_of("d = {\"a\": 1, \"b\": 2}"), Expr::Object { .. }));
}

#[test]
fn string_subscript_is_field_access() {
    // `d["name"]` lowers to a `.name` member read; `d[i]` stays dynamic.
    match init_of("v = d[\"name\"]") {
        Expr::Member { property, .. } => assert_eq!(property, "name"),
        other => panic!("expected member, got {:?}", other),
    }
    assert!(matches!(init_of("v = d[i]"), Expr::ComputedMember { .. }));
}

#[test]
fn inline_suite() {
    match &parse("if a: x = 1")[0] {
        Stmt::If { consequent, .. } => assert!(matches!(**consequent, Stmt::Block { .. })),
        other => panic!("expected if, got {:?}", other),
    }
}

// ---- rejections (limited subset) ----

#[test]
fn rejects_tuple_return() {
    assert!(parse_source("def f():\n    return 1, 2").is_err());
}

#[test]
fn rejects_chained_comparison() {
    assert!(parse_source("y = a < b < c").is_err());
}

#[test]
fn class_lowers_to_factory_function() {
    // A class desugars to a factory `function` returning a structural
    // row of fields + methods.
    let stmts = parse("class Point:\n    def __init__(self, x, y):\n        self.x = x\n        self.y = y\n    def sum(self):\n        return self.x + self.y\n");
    match &stmts[0] {
        Stmt::FunctionDecl { name, params, .. } => {
            assert_eq!(name, "Point");
            // __init__ params (minus self) become the factory params.
            assert_eq!(params.len(), 2);
        }
        other => panic!("expected class to lower to FunctionDecl, got {:?}", other),
    }
}

#[test]
fn from_import_lowers_to_named_specifiers() {
    use crate::ast::ImportSpecifier;
    match &parse("from pkg.mod import a, b as c")[0] {
        Stmt::Import { specifiers, source, .. } => {
            assert_eq!(source, "pkg.mod");
            assert_eq!(specifiers.len(), 2);
            match &specifiers[0] {
                ImportSpecifier::Named { imported, local, .. } => {
                    assert_eq!(imported, "a");
                    assert_eq!(local, "a");
                }
                other => panic!("expected named import, got {:?}", other),
            }
            match &specifiers[1] {
                ImportSpecifier::Named { imported, local, .. } => {
                    assert_eq!(imported, "b");
                    assert_eq!(local, "c");
                }
                other => panic!("expected aliased named import, got {:?}", other),
            }
        }
        other => panic!("expected import, got {:?}", other),
    }
}

#[test]
fn import_binds_namespace() {
    use crate::ast::ImportSpecifier;
    match &parse("import os")[0] {
        Stmt::Import { specifiers, source, .. } => {
            assert_eq!(source, "os");
            assert!(matches!(
                specifiers[0],
                ImportSpecifier::Namespace { .. }
            ));
        }
        other => panic!("expected import, got {:?}", other),
    }
    // Dotted import binds the top segment unless aliased.
    match &parse("import a.b.c as abc")[0] {
        Stmt::Import { specifiers, source, .. } => {
            assert_eq!(source, "a.b.c");
            match &specifiers[0] {
                ImportSpecifier::Namespace { local, .. } => assert_eq!(local, "abc"),
                other => panic!("expected namespace, got {:?}", other),
            }
        }
        other => panic!("expected import, got {:?}", other),
    }
}

#[test]
fn import_comma_list_lowers_to_multiple_imports() {
    let stmts = parse("import os, sys");
    assert_eq!(stmts.len(), 2);
    assert!(stmts.iter().all(|s| matches!(s, Stmt::Import { .. })));
}

#[test]
fn from_import_star_is_side_effect_import() {
    match &parse("from pkg import *")[0] {
        Stmt::Import { specifiers, source, .. } => {
            assert_eq!(source, "pkg");
            assert!(specifiers.is_empty(), "star import has no specifiers");
        }
        other => panic!("expected import, got {:?}", other),
    }
}

#[test]
fn relative_from_import_keeps_leading_dots() {
    match &parse("from ..pkg.mod import x")[0] {
        Stmt::Import { source, .. } => assert_eq!(source, "..pkg.mod"),
        other => panic!("expected import, got {:?}", other),
    }
    match &parse("from . import sibling")[0] {
        Stmt::Import { source, specifiers, .. } => {
            assert_eq!(source, ".");
            assert_eq!(specifiers.len(), 1);
        }
        other => panic!("expected import, got {:?}", other),
    }
}

#[test]
fn rejects_class_inheritance() {
    assert!(parse_source("class Dog(Animal):\n    pass").is_err());
}

#[test]
fn class_instance_method_and_fields_typecheck() {
    let errs = check(
        "class Point:\n\
         \x20   def __init__(self, x, y):\n\
         \x20       self.x = x\n\
         \x20       self.y = y\n\
         \x20   def sum(self):\n\
         \x20       return self.x + self.y\n\
         p = Point(1, 2)\n\
         s = p.sum()\n",
    );
    assert!(errs.is_empty(), "expected no errors, got {:?}", errs);
}

#[test]
fn class_unknown_field_is_rejected() {
    let errs = check(
        "class Box:\n\
         \x20   def __init__(self, v):\n\
         \x20       self.value = v\n\
         b = Box(1)\n\
         z = b.missing\n",
    );
    assert!(
        !errs.is_empty(),
        "reading a field the class never defines should fail"
    );
}

#[test]
fn class_method_this_field_type_is_enforced() {
    // `self.name` is a String, so adding a Number to it must fail
    // (no coercion at `+`).
    let errs = check(
        "class Greeter:\n\
         \x20   def __init__(self, name):\n\
         \x20       self.name = name\n\
         \x20   def bad(self):\n\
         \x20       return self.name + 1\n\
         g = Greeter(\"hi\")\n\
         r = g.bad()\n",
    );
    assert!(
        !errs.is_empty(),
        "String field + Number should be a type error"
    );
}

#[test]
fn branded_class_instance_methods_still_typecheck() {
    // Branding must stay transparent for field/method access.
    let errs = check_program(
        "class Point:\n\
         \x20   def __init__(self, x, y):\n\
         \x20       self.x = x\n\
         \x20       self.y = y\n\
         \x20   def sum(self):\n\
         \x20       return self.x + self.y\n\
         p = Point(1, 2)\n\
         s = p.sum()\n",
    );
    assert!(errs.is_empty(), "expected no errors, got {:?}", errs);
}

#[test]
fn structurally_identical_classes_are_distinct_brands() {
    // `A` and `B` have identical shape but are different nominal types,
    // so unifying their instances (here, by reassigning one binding)
    // must fail.
    let errs = check_program(
        "class A:\n\
         \x20   def __init__(self, x):\n\
         \x20       self.x = x\n\
         class B:\n\
         \x20   def __init__(self, x):\n\
         \x20       self.x = x\n\
         v = A(1)\n\
         v = B(1)\n",
    );
    assert!(
        !errs.is_empty(),
        "two distinct class brands must not unify, got no errors"
    );
}

#[test]
fn same_class_reassignment_unifies() {
    let errs = check_program(
        "class A:\n\
         \x20   def __init__(self, x):\n\
         \x20       self.x = x\n\
         v = A(1)\n\
         v = A(2)\n",
    );
    assert!(errs.is_empty(), "same-brand reassignment should unify, got {:?}", errs);
}

#[test]
fn generic_class_brands_per_instantiation() {
    // `Box(1)` is `Box<Number>`, `Box("hi")` is `Box<String>` — the
    // brand is parameterised, and field access sees through to the
    // representation, so the String field + Number is a type error.
    let ok = check_program(
        "class Box:\n\
         \x20   def __init__(self, v):\n\
         \x20       self.value = v\n\
         b = Box(1)\n\
         n = b.value + 1\n",
    );
    assert!(ok.is_empty(), "Box<Number>.value + 1 should be fine, got {:?}", ok);

    let bad = check_program(
        "class Box:\n\
         \x20   def __init__(self, v):\n\
         \x20       self.value = v\n\
         b = Box(\"hi\")\n\
         n = b.value + 1\n",
    );
    assert!(
        !bad.is_empty(),
        "Box<String>.value + Number should be a type error"
    );
}

#[test]
fn rejects_kwargs() {
    assert!(parse_source("f(x=1)").is_err());
}

#[test]
fn rejects_comprehension() {
    assert!(parse_source("xs = [a for a in items]").is_err());
}

#[test]
fn rejects_tabs() {
    assert!(parse_source("if a:\n\tx = 1").is_err());
}

#[test]
fn trailing_newline_terminates() {
    // A file ending in a newline must not spin the lexer at EOF.
    assert_eq!(parse("x = 1\ny = 2\n").len(), 2);
    assert_eq!(parse("def f(a):\n    return a\n").len(), 1);
}

// ---- end-to-end inference ----

#[test]
fn infers_function_and_call() {
    let src = "def add(a, b):\n    return a + b\n\nn = add(1, 2)";
    assert!(check(src).is_empty());
}

#[test]
fn infers_record_field_access() {
    let src = "p = {\"name\": \"alice\", \"age\": 30}\nnm = p[\"name\"]";
    assert!(check(src).is_empty());
}

#[test]
fn while_loop_typechecks() {
    let src = "total = 0\ni = 0\nwhile i < 10:\n    total = total + i\n    i = i + 1";
    assert!(check(src).is_empty());
}

#[test]
fn ternary_typechecks() {
    assert!(check("x = 1 if True else 2").is_empty());
}

#[test]
fn mixed_plus_rejected() {
    assert!(!check("x = 1 + \"oops\"").is_empty());
}
