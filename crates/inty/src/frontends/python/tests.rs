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

#[test]
fn class_name_annotation_resolves_to_brand() {
    // An annotation naming a class resolves to that class's nominal brand,
    // not an opaque variable — so a mismatched argument is rejected.
    let bad = check_program(
        "class Point:\n\
         \x20   def __init__(self, x):\n\
         \x20       self.x = x\n\
         def use(p: Point):\n\
         \x20   return 1\n\
         q = use(\"nope\")\n",
    );
    assert!(!bad.is_empty(), "String where a Point is annotated should fail");

    let ok = check_program(
        "class Point:\n\
         \x20   def __init__(self, x):\n\
         \x20       self.x = x\n\
         def use(p: Point):\n\
         \x20   return 1\n\
         q = use(Point(1))\n",
    );
    assert!(ok.is_empty(), "passing a Point should check, got {:?}", ok);
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
fn return_annotation_does_not_eat_the_def_colon() {
    // `def f(...) -> T:` must parse: the return-annotation skip must stop
    // at the header's `:` rather than consuming it. Regression for
    // "Unexpected token: found 'newline', expected ':'".
    match &parse("def f(s):\n    return s")[0] {
        Stmt::FunctionDecl { name, .. } => assert_eq!(name, "f"),
        other => panic!("expected function decl, got {:?}", other),
    }
    match &parse("def f(s: str) -> str:\n    return s")[0] {
        Stmt::FunctionDecl { name, params, .. } => {
            assert_eq!(name, "f");
            assert_eq!(params.len(), 1);
        }
        other => panic!("expected function decl, got {:?}", other),
    }
    // A docstring as the first body statement (the shape that first
    // surfaced the bug) must also parse.
    assert!(matches!(
        &parse("def g(n: int) -> int:\n    \"\"\"doc\"\"\"\n    return n")[0],
        Stmt::FunctionDecl { .. }
    ));
    // And a method with a return annotation inside a class.
    assert!(matches!(
        &parse("class C:\n    def m(self) -> int:\n        return 1")[0],
        Stmt::FunctionDecl { .. }
    ));
}

#[test]
fn return_annotated_function_typechecks() {
    // The annotation is erased, but the function must infer normally.
    let errs = check("def inc(x: int) -> int:\n    return x + 1\nr = inc(41)\n");
    assert!(errs.is_empty(), "expected no errors, got {:?}", errs);
}

#[test]
fn default_param_is_marked_optional() {
    match &parse("def f(a, b=1):\n    return a")[0] {
        Stmt::FunctionDecl { params, .. } => {
            assert_eq!(params.len(), 2);
            assert!(!params[0].optional, "a is required");
            assert!(params[1].optional, "b has a default => optional");
        }
        other => panic!("expected function decl, got {:?}", other),
    }
}

#[test]
fn default_carries_type_constraint_except_none() {
    match &parse("def f(a, b=1, c=None):\n    return a")[0] {
        Stmt::FunctionDecl { params, .. } => {
            // a: required, no default constraint.
            assert!(!params[0].optional && params[0].default.is_none());
            // b=1: optional and constrains the type.
            assert!(params[1].optional && params[1].default.is_some());
            // c=None: optional but imposes no type constraint.
            assert!(params[2].optional && params[2].default.is_none());
        }
        other => panic!("expected function decl, got {:?}", other),
    }
}

#[test]
fn non_none_default_constrains_param_type() {
    // `y=1` makes y a Number: omitting it infers Number, and a
    // wrong-typed argument is rejected.
    assert!(
        check("def f(y=1):\n    return y\nx = f()\nr = x + 1\n").is_empty(),
        "omitted default should give y its Number type"
    );
    assert!(
        !check("def f(y=1):\n    return y\nf(\"hi\")\n").is_empty(),
        "a String argument must be rejected against a Number default"
    );
}

#[test]
fn none_default_imposes_no_constraint() {
    // `=None` is Python's idiomatic optional: it accepts any value.
    let errs = check(
        "def conn(timeout=None):\n    return 1\nconn()\nconn(30)\nconn(\"x\")\n",
    );
    assert!(errs.is_empty(), "=None should accept any argument, got {:?}", errs);
}

#[test]
fn default_param_may_be_omitted_or_supplied() {
    let errs = check("def f(a, b=1):\n    return a\nx = f(10)\ny = f(10, 20)\n");
    assert!(errs.is_empty(), "omitting/supplying a default should both check, got {:?}", errs);
}

#[test]
fn default_param_still_enforces_arity() {
    // The required parameter is still required, and surplus args fail.
    assert!(!check("def f(a, b=1):\n    return a\nf()\n").is_empty(), "missing required arg must fail");
    assert!(!check("def f(a, b=1):\n    return a\nf(1, 2, 3)\n").is_empty(), "too many args must fail");
}

#[test]
fn decorated_def_parses_ignoring_decorator() {
    // `@deco` lines are consumed; the decorated def still parses.
    match &parse("@staticmethod\ndef f(a):\n    return a")[0] {
        Stmt::FunctionDecl { name, params, .. } => {
            assert_eq!(name, "f");
            assert_eq!(params.len(), 1);
        }
        other => panic!("expected function decl, got {:?}", other),
    }
    // Stacked decorators with call args.
    assert!(matches!(
        &parse("@app.route(\"/\")\n@cached\ndef handler():\n    return 1")[0],
        Stmt::FunctionDecl { .. }
    ));
}

#[test]
fn rejects_class_inheritance() {
    assert!(parse_source("class Dog(Animal):\n    pass").is_err());
}

#[test]
fn param_annotation_is_captured() {
    use crate::types::TypeAst;
    match &parse("def f(a: int, b):\n    return a")[0] {
        Stmt::FunctionDecl { params, .. } => {
            assert!(matches!(params[0].type_ast, Some(TypeAst::Number)));
            assert!(params[1].type_ast.is_none());
        }
        other => panic!("expected function decl, got {:?}", other),
    }
}

#[test]
fn param_annotation_is_checked() {
    // An annotated parameter pins its type: a wrong-typed argument is
    // rejected, a matching one is accepted.
    assert!(
        !check("def f(x: int):\n    return x\nf(\"hi\")\n").is_empty(),
        "String argument against `int` parameter must fail"
    );
    assert!(
        check("def f(x: int):\n    return x\nr = f(5)\n").is_empty(),
        "matching argument should check"
    );
    // Container annotations are enforced too.
    assert!(
        !check("def f(xs: list[int]):\n    return xs\nf(\"nope\")\n").is_empty(),
        "String against `list[int]` parameter must fail"
    );
}

#[test]
fn unmodelled_param_annotation_imposes_no_constraint() {
    // An unknown/unmodelled annotation lowers to a fresh variable, so it
    // never produces a false positive.
    let errs = check("def f(x: SomeProtocol):\n    return 1\nf(\"anything\")\nf(5)\n");
    assert!(errs.is_empty(), "unmodelled annotation should not constrain, got {:?}", errs);
}

#[test]
fn return_annotation_is_captured() {
    use crate::types::TypeAst;
    match &parse("def f() -> int:\n    return 1")[0] {
        Stmt::FunctionDecl { return_type_ast, .. } => {
            assert!(matches!(return_type_ast, Some(TypeAst::Number)));
        }
        other => panic!("expected function decl, got {:?}", other),
    }
}

#[test]
fn return_annotation_is_checked() {
    // The body's result must conform to the declared return type.
    assert!(
        !check("def g() -> str:\n    return 123\n").is_empty(),
        "returning a Number from a `-> str` function must fail"
    );
    assert!(
        check("def g() -> int:\n    return 123\n").is_empty(),
        "a matching return should check"
    );
}

#[test]
fn unmodelled_return_annotation_imposes_no_constraint() {
    let errs = check("def g() -> SomeType:\n    return 123\nx = g()\n");
    assert!(errs.is_empty(), "unmodelled return annotation should not constrain, got {:?}", errs);
}

#[test]
fn variable_annotation_is_checked() {
    assert!(!check("x: int = \"s\"\n").is_empty(), "int annotation vs String init must fail");
    assert!(check("x: int = 5\n").is_empty(), "matching variable annotation should check");
    assert!(!check("xs: list[int] = \"nope\"\n").is_empty(), "container annotation enforced");
}

#[test]
fn unmodelled_variable_annotation_imposes_no_constraint() {
    let errs = check("x: SomeType = 5\ny: SomeType = \"s\"\n");
    assert!(errs.is_empty(), "unmodelled variable annotation should not constrain, got {:?}", errs);
}

#[test]
fn class_method_param_annotation_is_checked() {
    let errs = check(
        "class C:\n\
         \x20   def __init__(self):\n\
         \x20       self.v = 1\n\
         \x20   def m(self, x: int):\n\
         \x20       return x\n\
         c = C()\n\
         c.m(\"s\")\n",
    );
    assert!(!errs.is_empty(), "String arg against annotated `int` method param must fail");
}

#[test]
fn class_method_return_annotation_is_checked() {
    let errs = check(
        "class C:\n\
         \x20   def __init__(self):\n\
         \x20       self.v = 1\n\
         \x20   def m(self) -> str:\n\
         \x20       return 123\n",
    );
    assert!(!errs.is_empty(), "Number body against `-> str` method must fail");
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

/// The shared program for the `isinstance` narrowing tests: `x` is a
/// `Dog | Cat` union (via a conditional), where `bark` is Dog-only and
/// `meow` is Cat-only.
const DOG_CAT_UNION: &str = "class Dog:\n\
     \x20   def __init__(self):\n\
     \x20       self.legs = 4\n\
     \x20   def bark(self):\n\
     \x20       return 1\n\
     class Cat:\n\
     \x20   def __init__(self):\n\
     \x20       self.legs = 4\n\
     \x20   def meow(self):\n\
     \x20       return 2\n\
     x = Dog() if True else Cat()\n";

#[test]
fn union_without_narrowing_rejects_brand_specific_method() {
    // Control: on the bare `Dog | Cat` union, a Dog-only method is not a
    // common member, so the access must fail. This is what narrowing
    // rescues in the test below.
    let errs = check_program(&format!("{DOG_CAT_UNION}r = x.bark()\n"));
    assert!(
        !errs.is_empty(),
        "x.bark() on a Dog | Cat union should fail without narrowing"
    );
}

#[test]
fn isinstance_narrows_union_to_brand() {
    // `isinstance(x, Dog)` narrows `x` to the Dog brand in the true
    // branch, so the Dog-only method type-checks there.
    let errs = check_program(&format!(
        "{DOG_CAT_UNION}if isinstance(x, Dog):\n\
         \x20   r = x.bark()\n"
    ));
    assert!(
        errs.is_empty(),
        "isinstance(x, Dog) should narrow x to Dog, got {:?}",
        errs
    );
}

#[test]
fn isinstance_else_branch_narrows_to_other_brand() {
    // The negated predicate narrows the `else` branch to Cat, so the
    // Cat-only method type-checks there.
    let errs = check_program(&format!(
        "{DOG_CAT_UNION}if isinstance(x, Dog):\n\
         \x20   a = x.bark()\n\
         else:\n\
         \x20   b = x.meow()\n"
    ));
    assert!(
        errs.is_empty(),
        "else branch should narrow x to Cat, got {:?}",
        errs
    );
}

#[test]
fn isinstance_narrowing_still_rejects_wrong_brand_method() {
    // Proof the narrowing is real: inside the `isinstance(x, Dog)` branch,
    // x is Dog — the Cat-only method must still be rejected.
    let errs = check_program(&format!(
        "{DOG_CAT_UNION}if isinstance(x, Dog):\n\
         \x20   r = x.meow()\n"
    ));
    assert!(
        !errs.is_empty(),
        "x.meow() inside the Dog branch should be rejected"
    );
}

#[test]
fn keyword_arguments_resolve_by_name() {
    // Positional, mixed, all-keyword, and reordered keyword calls all
    // resolve against the callee's parameter names.
    let errs = check_program(
        "def f(x, y):\n    return x + y\n\
         def g(name, count):\n    return count\n\
         a = f(1, 2)\n\
         b = f(1, y=2)\n\
         c = f(x=1, y=2)\n\
         d = g(count=3, name=4)\n",
    );
    assert!(errs.is_empty(), "keyword calls should resolve, got {:?}", errs);
}

#[test]
fn keyword_argument_type_flows_to_parameter() {
    // A keyword arg is checked against the named parameter's type.
    let bad = check_program(
        "def f(x, y):\n    return x + y\n\
         r = f(x=1, y=\"s\")\n\
         z = r + 1\n",
    );
    assert!(!bad.is_empty(), "Number + String through a keyword arg should fail");
}

#[test]
fn keyword_argument_errors() {
    // Unknown keyword name.
    assert!(
        !check_program("def f(x, y):\n    return x\nr = f(1, z=2)\n").is_empty(),
        "unknown keyword should be rejected"
    );
    // Same parameter given positionally and by keyword.
    assert!(
        !check_program("def f(x, y):\n    return x\nr = f(1, x=2)\n").is_empty(),
        "duplicate positional+keyword should be rejected"
    );
    // Missing a required parameter.
    assert!(
        !check_program("def f(x, y):\n    return x\nr = f(x=1)\n").is_empty(),
        "missing required argument should be rejected"
    );
}

#[test]
fn keyword_with_default_may_be_omitted_or_supplied() {
    // A defaulted (optional) parameter can be filled by keyword or left
    // out; an omitted *required* one still errors (covered above).
    let errs = check_program(
        "def f(x, y=0):\n    return x + y\n\
         a = f(1)\n\
         b = f(1, y=5)\n\
         c = f(x=2, y=5)\n",
    );
    assert!(errs.is_empty(), "default + keyword should check, got {:?}", errs);
}

#[test]
fn type_alias_literal_parses_and_resolves() {
    // The bare `NAME = Literal[…]` form parses (comma subscript) and the
    // alias resolves in annotations, enforcing the literal union.
    let ok = check_program(
        "BumpType = Literal[\"patch\", \"minor\", \"major\"]\n\
         def bump(t: BumpType) -> BumpType:\n\
         \x20   return t\n\
         x = bump(\"patch\")\n",
    );
    assert!(ok.is_empty(), "valid literal arg should check, got {:?}", ok);

    let bad = check_program(
        "BumpType = Literal[\"patch\", \"minor\", \"major\"]\n\
         def bump(t: BumpType) -> BumpType:\n\
         \x20   return t\n\
         y = bump(\"nope\")\n",
    );
    assert!(
        !bad.is_empty(),
        "a literal outside the alias union must be rejected"
    );
}

#[test]
fn type_alias_explicit_forms() {
    // PEP 695 `type X = …`
    let pep695 = check_program(
        "type Id = Optional[int]\n\
         def f(v: Id) -> Id:\n\
         \x20   return v\n\
         a = f(3)\n\
         b = f(None)\n",
    );
    assert!(pep695.is_empty(), "`type X =` alias should work, got {:?}", pep695);

    // PEP 613 `X: TypeAlias = …`
    let pep613 = check_program(
        "Pair: TypeAlias = list[str]\n\
         def g(xs: Pair) -> Pair:\n\
         \x20   return xs\n",
    );
    assert!(pep613.is_empty(), "`X: TypeAlias =` alias should work, got {:?}", pep613);
}

#[test]
fn type_alias_used_as_value_is_not_bound() {
    // An alias is a type, not a runtime value; using it as a value is an
    // undefined reference (it must not silently type-check).
    let errs = check_program("Color = Literal[\"r\", \"g\"]\nx = Color\n");
    assert!(
        !errs.is_empty(),
        "using a type alias as a value should be undefined"
    );
}

#[test]
fn unknown_type_name_is_still_opaque() {
    // A non-alias unknown type name in an annotation imposes no
    // constraint (lowers opaque) — no false positive.
    let errs = check_program(
        "def f(x: SomeUnmodelledType) -> int:\n\
         \x20   return 1\n\
         r = f(\"anything\")\n\
         s = f(42)\n",
    );
    assert!(errs.is_empty(), "unknown annotation should be opaque, got {:?}", errs);
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
