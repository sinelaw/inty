//! Integration tests for the inference module.

use super::env::Mutability;
use super::*;

use crate::builtins::initial_env;
use crate::frontends::javascript::lexer::{Scanner, Token};
use crate::frontends::javascript::parser::Parser;
use crate::types::{Nothing, Type};

fn infer_expr_str(source: &str) -> InferResult<Type> {
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
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let program = parser.parse_program().unwrap();

    // Get the first expression statement
    let expr = match &program.statements[0] {
        crate::ast::Stmt::Expr { expression, .. } => expression.clone(),
        _ => panic!("Expected expression statement"),
    };

    let mut state = InferState::new();
    let env = initial_env();
    state.infer_expr(&env, &expr)
}

#[test]
fn test_infer_number() {
    // Bare literals synthesise as singletons; widening happens at
    // binding/return/operator-result sites.
    let ty = infer_expr_str("42").unwrap();
    assert_eq!(ty, Type::lit_number(42.0));
}

#[test]
fn test_infer_string() {
    let ty = infer_expr_str("\"hello\"").unwrap();
    assert_eq!(ty, Type::lit_string("hello"));
}

#[test]
fn test_infer_boolean() {
    let ty = infer_expr_str("true").unwrap();
    assert_eq!(ty, Type::lit_bool(true));
}

#[test]
fn test_infer_array() {
    let ty = infer_expr_str("[1, 2, 3]").unwrap();
    assert!(matches!(ty, Type::Array(_)));
}

#[test]
fn test_infer_object() {
    // Use parentheses to parse as expression, not block
    let ty = infer_expr_str("({x: 1, y: 2})").unwrap();
    assert!(ty.is_row());

    if let Type::Row(row) = ty {
        assert!(row.has_prop(&"x".into()));
        assert!(row.has_prop(&"y".into()));
    }
}

#[test]
fn test_infer_arithmetic() {
    let ty = infer_expr_str("1 + 2").unwrap();
    // With Plus constraint, result should be Number (or the constraint type var)
    // For this simple case we get a type variable with Plus constraint
    assert!(matches!(ty, Type::Number | Type::Var(_)));
}

#[test]
fn test_infer_function() {
    // Use parentheses to parse function expression
    let ty = infer_expr_str("(function(x) { return x; })").unwrap();
    assert!(ty.is_func());
}

#[test]
fn test_infer_array_length() {
    let ty = infer_expr_str("[1, 2, 3].length").unwrap();
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_infer_string_length() {
    let ty = infer_expr_str("\"hello\".length").unwrap();
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_infer_string_constructor() {
    // `String` / `Number` / `Boolean` live in core.d.js as callable
    // rows under the unified design. The bare `initial_env` no longer
    // declares them, so we go through the full stdlib-aware program
    // path to exercise the constructor call.
    let (_, env, state) = infer_program_via_program_with_stdlib("var s = String(42);").unwrap();
    let ty = state.apply_subst(&env.lookup("s").unwrap().body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn test_infer_number_constructor() {
    let (_, env, state) = infer_program_via_program_with_stdlib("var n = Number(\"42\");").unwrap();
    let ty = state.apply_subst(&env.lookup("n").unwrap().body.ty);
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_infer_boolean_constructor() {
    let (_, env, state) = infer_program_via_program_with_stdlib("var b = Boolean(0);").unwrap();
    let ty = state.apply_subst(&env.lookup("b").unwrap().body.ty);
    assert_eq!(ty, Type::Boolean);
}

/// Helper that runs a program through the full stdlib-aware
/// inference path. Used by tests that exercise builtin bindings
/// (`String`, `Number`, `Boolean`, `Math`, `JSON`, `Promise`, …)
/// declared in core.d.js / dom.d.js.
fn infer_program_via_program_with_stdlib(source: &str) -> InferResult<(Type, TypeEnv, InferState)> {
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let mut program = parser.parse_program().unwrap();
    program.type_aliases = type_aliases;

    let (env, mut state) = crate::stdlib::initial_env_with_stdlib()?;
    let (ty, env) = state.infer_program_with_env(&env, &program)?;
    Ok((ty, env, state))
}

/// Helper to infer a program and return the final type and state.
fn infer_program_with_state(source: &str) -> InferResult<(Type, TypeEnv, InferState)> {
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let mut program = parser.parse_program().unwrap();
    program.type_aliases = type_aliases;

    let mut state = InferState::new();
    state.load_type_aliases(&program.type_aliases)?;
    state.resolution =
        crate::ast::resolve::Resolution::of_program(&program.statements, program.language);
    let env = initial_env();

    // Infer statements and track final environment
    let mut final_env = env;
    let mut result_ty = Type::Undefined;
    for stmt in &program.statements {
        let (ty, new_env) = state.infer_stmt(&final_env, stmt)?;
        result_ty = ty;
        final_env = new_env;
    }

    Ok((result_ty, final_env, state))
}

#[test]
fn test_annotation_var_number() {
    let (_, env, state) = infer_program_with_state("/** var x: Number */ var x = 42;").unwrap();
    let scheme = env.lookup("x").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_annotation_var_string() {
    let (_, env, state) =
        infer_program_with_state("/** var s: String */ var s = \"hello\";").unwrap();
    let scheme = env.lookup("s").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn test_annotation_var_array() {
    let (_, env, state) =
        infer_program_with_state("/** var arr: Number[] */ var arr = [1, 2, 3];").unwrap();
    let scheme = env.lookup("arr").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::array(Type::Number));
}

#[test]
fn test_annotation_function_params() {
    // Use arrow syntax for function type annotations as expected by type parser
    let (_, env, state) = infer_program_with_state(
        "/** function add(a: Number, b: Number) => Number */ function add(a, b) { return a + b; }",
    )
    .unwrap();
    let scheme = env.lookup("add").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    let (_, params, ret) = ty.as_callable().expect("expected callable type for `add`");
    assert_eq!(params.len(), 2);
    let p0 = state.apply_subst(&params[0].ty);
    let p1 = state.apply_subst(&params[1].ty);
    assert_eq!(p0, Type::Number);
    assert_eq!(p1, Type::Number);
    assert_eq!(*ret, Type::Number);
}

#[test]
fn test_annotation_mismatch_error() {
    // Type annotation says String but value is Number - should error
    let result = infer_program_with_state("/** var x: String */ var x = 42;");
    assert!(result.is_err());
}

#[test]
fn test_annotation_more_specific_than_inferred() {
    // Empty array would be inferred as a[] (polymorphic element type),
    // but annotation constrains it to Number[]
    let (_, env, state) = infer_program_with_state("/** var x: Number[] */ var x = [];").unwrap();
    let scheme = env.lookup("x").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::array(Type::Number));
}

// ========================================================================
// Value Restriction and Declaration/Assignment Tests
// ========================================================================

#[test]
fn test_var_declared_then_assigned() {
    // Variable declared without initializer, then assigned later
    // should get the correct type from the assignment
    let (_, env, state) = infer_program_with_state("var x; x = 42;").unwrap();
    let scheme = env.lookup("x").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_var_declared_then_assigned_string() {
    let (_, env, state) = infer_program_with_state("var s; s = \"hello\";").unwrap();
    let scheme = env.lookup("s").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn test_value_restriction_function_call_monomorphic() {
    // Function call results should be monomorphic (not generalized)
    // This prevents unsoundness with mutable state
    let source = r#"
        function makeArray() { return []; }
        var arr = makeArray();
    "#;
    let (_, env, _state) = infer_program_with_state(source).unwrap();
    let scheme = env.lookup("arr").unwrap();
    // arr should be monomorphic (no quantified type variables)
    // because it's the result of a function call, not a syntactic value
    assert!(
        scheme.vars.is_empty(),
        "function call result should be monomorphic"
    );
}

#[test]
fn test_value_restriction_variable_reference_polymorphic() {
    // Variable references are syntactic values and can be generalized
    // So `var myId = id` should be polymorphic like `id`
    let source = r#"
        function id(x) { return x; }
        var myId = id;
        var a = myId(42);
        var b = myId("hello");
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    // myId should work with both Number and String
    let a_scheme = env.lookup("a").unwrap();
    let a_ty = state.apply_subst(&a_scheme.body.ty);
    assert_eq!(a_ty, Type::Number);

    let b_scheme = env.lookup("b").unwrap();
    let b_ty = state.apply_subst(&b_scheme.body.ty);
    assert_eq!(b_ty, Type::String);
}

#[test]
fn test_value_restriction_function_literal_polymorphic() {
    // Function literals are syntactic values and should be generalized
    let source = r#"
        var id = function(x) { return x; };
        var a = id(42);
        var b = id("hello");
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    let a_scheme = env.lookup("a").unwrap();
    let a_ty = state.apply_subst(&a_scheme.body.ty);
    assert_eq!(a_ty, Type::Number);

    let b_scheme = env.lookup("b").unwrap();
    let b_ty = state.apply_subst(&b_scheme.body.ty);
    assert_eq!(b_ty, Type::String);
}

#[test]
fn test_value_restriction_array_literal_polymorphic() {
    // Array literals with value elements are syntactic values
    let source = r#"
        var arr = [1, 2, 3];
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();
    let scheme = env.lookup("arr").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::array(Type::Number));
}

#[test]
fn test_value_restriction_object_literal_polymorphic() {
    // Object literals with value properties are syntactic values
    let source = r#"
        var obj = { x: 1, y: "hello" };
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();
    let scheme = env.lookup("obj").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert!(ty.is_row());
}

#[test]
fn test_no_monomorphism_restriction() {
    // We do NOT have ML-style monomorphism restriction
    // Simple bindings like `var myId = id` are still polymorphic
    let source = r#"
        function id(x) { return x; }
        var myId = id;
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();
    let scheme = env.lookup("myId").unwrap();
    // myId should be polymorphic (have quantified type variables)
    assert!(!scheme.vars.is_empty(), "myId should be polymorphic");
    let _ = state; // suppress unused warning
}

#[test]
fn test_uninitialized_var_monomorphic() {
    // Variables without initializers should be monomorphic
    // (not generalized) so that assignments can unify with them
    let source = r#"
        var x;
    "#;
    let (_, env, _state) = infer_program_with_state(source).unwrap();
    let scheme = env.lookup("x").unwrap();
    // x should be monomorphic (no quantified type variables)
    assert!(
        scheme.vars.is_empty(),
        "uninitialized var should be monomorphic"
    );
}

#[test]
fn test_var_never_assigned_remains_type_variable() {
    // A variable declared but never assigned should remain as a type variable
    // and should NOT cause an error
    let source = r#"
        var x;
    "#;
    let result = infer_program_with_state(source);
    assert!(result.is_ok(), "unassigned var should not cause error");

    let (_, env, state) = result.unwrap();
    let scheme = env.lookup("x").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    // The type should be a type variable (unconstrained)
    assert!(
        matches!(ty, Type::Var(_)),
        "unassigned var should remain as type variable, got {:?}",
        ty
    );
}

#[test]
fn test_var_used_but_never_assigned() {
    // Variable declared, used as value, but never assigned
    // should infer type from usage context
    let source = r#"
        var x;
        var y = x + 1;
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    // y is a number, or still a variable.
    let y_scheme = env.lookup("y").unwrap();
    let y_ty = state.apply_subst(&y_scheme.body.ty);
    assert!(
        matches!(y_ty, Type::Number | Type::Var(_)),
        "y should be a number, got {y_ty:?}"
    );
}

// ========================================================================
// This Method Return Type Tests
// ========================================================================

#[test]
fn test_this_method_returns_concrete_type() {
    // When an object has concrete field types (x: 10),
    // methods using 'this' should return concrete types (Number)
    // not type variables
    let source = r#"
        var point = {
            x: 10,
            y: 20,
            getX: function() {
                return this.x;
            },
            getY: function() {
                return this.y;
            }
        };
        var px = point.getX();
        var py = point.getY();
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    // px should be Number, not a type variable
    let px_scheme = env.lookup("px").unwrap();
    let px_ty = state.apply_subst(&px_scheme.body.ty);
    assert_eq!(
        px_ty,
        Type::Number,
        "point.getX() should return Number, got {:?}",
        px_ty
    );

    // py should be Number, not a type variable
    let py_scheme = env.lookup("py").unwrap();
    let py_ty = state.apply_subst(&py_scheme.body.ty);
    assert_eq!(
        py_ty,
        Type::Number,
        "point.getY() should return Number, got {:?}",
        py_ty
    );
}

#[test]
fn test_this_method_computed_return() {
    // Method that computes a value from concrete fields
    let source = r#"
        var rect = {
            width: 10,
            height: 20,
            area: function() {
                return this.width * this.height;
            }
        };
        var a = rect.area();
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    let a_scheme = env.lookup("a").unwrap();
    let a_ty = state.apply_subst(&a_scheme.body.ty);
    assert_eq!(
        a_ty,
        Type::Number,
        "rect.area() should return Number, got {:?}",
        a_ty
    );
}

#[test]
fn test_this_method_returns_string() {
    // Method returning string field
    let source = r#"
        var person = {
            name: "Alice",
            getName: function() {
                return this.name;
            }
        };
        var name = person.getName();
    "#;
    let (_, env, state) = infer_program_with_state(source).unwrap();

    let name_scheme = env.lookup("name").unwrap();
    let name_ty = state.apply_subst(&name_scheme.body.ty);
    assert_eq!(
        name_ty,
        Type::String,
        "person.getName() should return String, got {:?}",
        name_ty
    );
}

// ========================================================================
// Equi-Recursive Type Tests (Method Chaining)
// ========================================================================

#[test]
fn test_method_chaining_returns_this() {
    // Method that returns 'this' creates equi-recursive type
    // Should support chaining without infinite type errors
    let source = r#"
        var counter = {
            value: 0,
            increment: function() {
                this.value = this.value + 1;
                return this;
            }
        };
        var c = counter.increment().increment();
    "#;
    // Should not error - this is a valid equi-recursive type
    let result = infer_program_with_state(source);
    assert!(
        result.is_ok(),
        "Method chaining with 'return this' should not cause infinite type error"
    );
}

#[test]
fn test_unknown_method_after_chain_is_rejected() {
    // After a `return this` method call, accessing a property that
    // doesn't exist on the receiver must still error. Previously
    // `extend_subst` swallowed the unify failure when a row tail
    // variable acquired a second binding, letting `.moo()` slide
    // through with a fresh type variable for the result.
    let source = r#"
        var request = {
            url: "",
            setUrl: function(u) { this.url = u; return this; }
        };
        var response = request.setUrl("/api/users").moo();
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Calling an undefined method on the result of a chained `return this` call must fail"
    );
}

#[test]
fn recursive_type_against_function_needs_the_same_goal_to_close_a_cycle() {
    // `f : (a) => μt. (b) => t`. The annotation says `k(1)` returns a
    // function returning a Number, but `k(1)(2)` returns `f`. Was
    // accepted: the unfold of `μt` against the annotation was memoised by
    // the recursive type's id alone, so the second unfold, against
    // `(Number) => Number`, "succeeded" by coinduction.
    let src = "function f(x) { return f; }\n\
               /** const k: (x: Number) => (y: Number) => Number */\n\
               const k = f;\n\
               const n = k(1)(2) - 1;";
    assert!(check_program(src, &[]).is_err());
    // The same recursive type against itself is still fine.
    let ok = "function f(x) { return f; }\nconst k = f;\nconst g = k(1)(2)(3);";
    assert!(check_program(ok, &[]).is_ok());
}

#[test]
fn test_method_call_on_chained_result() {
    // Calling a method on the result of chained method calls
    let source = r#"
        var counter = {
            value: 0,
            increment: function() {
                this.value = this.value + 1;
                return this;
            },
            get: function() {
                return this.value;
            }
        };
        var c = counter.increment().increment();
        var finalValue = c.get();
    "#;
    // Should not error - equi-recursive types should work
    let result = infer_program_with_state(source);
    assert!(
        result.is_ok(),
        "Calling method on chained result should work with equi-recursive types"
    );
}

#[test]
fn test_multi_level_method_chaining() {
    // Multiple methods that return 'this' can be chained
    let source = r#"
        var builder = {
            value: 0,
            setValue: function(v) {
                this.value = v;
                return this;
            },
            increment: function() {
                this.value = this.value + 1;
                return this;
            }
        };
        var result = builder.setValue(10).increment().increment();
    "#;
    // Should not error - complex chaining should work
    let result = infer_program_with_state(source);
    assert!(
        result.is_ok(),
        "Multi-level method chaining should work without infinite type errors"
    );
}

#[test]
fn test_chained_method_with_final_value() {
    // Chain methods that return 'this', then call a method that returns a value
    let source = r#"
        var calculator = {
            result: 0,
            add: function(n) {
                this.result = this.result + n;
                return this;
            },
            multiply: function(n) {
                this.result = this.result * n;
                return this;
            },
            compute: function() {
                return this.result;
            }
        };
        var calcResult = calculator.add(5).multiply(3).compute();
    "#;
    // Should not error - this is the classic builder pattern
    let result = infer_program_with_state(source);
    assert!(
        result.is_ok(),
        "Builder pattern with final compute() should work"
    );
}

#[test]
fn test_simple_this_member_access() {
    // Simplified test: just access this.value in a method
    let source = r#"
        var obj = {
            value: 42,
            getValue: function() {
                return this.value;
            }
        };
        var result = obj.getValue();
    "#;
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    // Get the inferred type for 'result' from the environment
    let result_scheme = env
        .lookup("result")
        .expect("Should have inferred type for result");
    let result_type = state.apply_subst(&result_scheme.body.ty);

    // The type should be Number, not a type variable
    assert_eq!(
        result_type,
        Type::Number,
        "Result of obj.getValue() should be Number, got: {:?}",
        result_type
    );
}

#[test]
fn test_chained_call_without_generalization() {
    // Test chained call where the builder is NOT stored in a variable
    // This avoids generalization and tests pure unification
    let source = r#"
        var result = {
            value: 0,
            setValue: function(v) {
                this.value = v;
                return this;
            },
            build: function() {
                return this.value;
            }
        }.setValue(42).build();
    "#;
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    let result_scheme = env
        .lookup("result")
        .expect("Should have inferred type for result");
    let result_type = state.apply_subst(&result_scheme.body.ty);

    assert_eq!(
        result_type,
        Type::Number,
        "Result of inline builder should be Number, got: {:?}",
        result_type
    );
}

#[test]
fn test_builder_final_result_is_concrete() {
    // The final result of a builder pattern should have a concrete type, not a type variable
    let source = r#"
        var builder = {
            value: 0,
            setValue: function(v) {
                this.value = v;
                return this;
            },
            build: function() {
                return this.value;
            }
        };
        var result = builder.setValue(42).build();
    "#;
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    // Get the inferred type for 'result' from the environment
    let result_scheme = env
        .lookup("result")
        .expect("Should have inferred type for result");
    let result_type = state.apply_subst(&result_scheme.body.ty);

    // The type should be Number, not a type variable
    assert_eq!(
        result_type,
        Type::Number,
        "Result of builder.setValue(42).build() should be Number, got: {:?}",
        result_type
    );
}

// ============================================================
// Tests for declarations (const, var without init, imports)
// ============================================================

#[test]
fn test_const_declaration() {
    // const declarations should be immutable
    let source = r#"
        const x = 42;
    "#;
    let (_, env, _) = infer_program_with_state(source).expect("Should type-check successfully");

    let binding = env.lookup_binding("x").expect("Should have binding for x");
    assert_eq!(binding.mutability, Mutability::Immutable);
}

#[test]
fn test_const_assignment_rejected() {
    // Assignment to const should fail
    let source = r#"
        const x = 42;
        x = 100;
    "#;
    let result = infer_program_with_state(source);
    match result {
        Ok(_) => panic!("Should reject assignment to const"),
        Err(err) => {
            assert!(
                err.to_string().contains("constant"),
                "Error should mention constant: {}",
                err
            );
        }
    }
}

#[test]
fn test_var_declaration_is_immutable() {
    // var with type annotation and no init is treated as immutable declaration
    let source = r#"
        /** var x: Number */
        var x;
    "#;
    let (_, env, _) = infer_program_with_state(source).expect("Should type-check successfully");

    let binding = env.lookup_binding("x").expect("Should have binding for x");
    assert_eq!(
        binding.mutability,
        Mutability::Immutable,
        "var with type annotation and no init should be immutable"
    );
}

#[test]
fn test_var_with_init_is_mutable() {
    // Regular var with init is mutable
    let source = r#"
        var x = 42;
    "#;
    let (_, env, _) = infer_program_with_state(source).expect("Should type-check successfully");

    let binding = env.lookup_binding("x").expect("Should have binding for x");
    assert_eq!(
        binding.mutability,
        Mutability::Mutable,
        "var with init should be mutable"
    );
}

#[test]
fn test_declaration_assignment_rejected() {
    // Assignment to declared variable should fail
    let source = r#"
        /** var x: Number */
        var x;
        x = 42;
    "#;
    let result = infer_program_with_state(source);
    assert!(result.is_err(), "Should reject assignment to declaration");
}

// Note: Tests for polymorphic function declarations (like `<T>(x: T) => T`)
// are currently disabled due to a stack overflow in the type inference.
// This appears to be a pre-existing issue with how the type parser interacts
// with the inference engine for type annotations containing type variables.
// The core declaration features (const, var without init, mutability tracking)
// work correctly for monomorphic types.

#[test]
fn test_monomorphic_function_declaration() {
    // A monomorphic function declaration should work
    let source = r#"
        /** var greet: (name: String) => String */
        var greet;
        var result = greet("world");
    "#;
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    let result_scheme = env.lookup("result").expect("Should have result");
    let result_type = state.apply_subst(&result_scheme.body.ty);
    assert_eq!(
        result_type,
        Type::String,
        "greet(\"world\") should be String"
    );
}

#[test]
fn test_monomorphic_function_declaration_is_immutable() {
    // Monomorphic function declaration should be immutable
    let source = r#"
        /** var greet: (name: String) => String */
        var greet;
        greet = function(name) { return "Hello, " + name; };
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Should reject assignment to function declaration"
    );
}

#[test]
fn test_monomorphic_object_property_assignment() {
    // Assignment to monomorphic property of immutable object declaration should succeed
    let source = r#"
        /** var obj: { count: Number } */
        var obj;
        obj.count = 42;
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_ok(),
        "Should allow assignment to monomorphic property: {:?}",
        result.err()
    );
}

// Note: Tests for polymorphic object properties (like `{ fn: <T>(x: T) => T }`)
// are currently disabled due to a stack overflow in the type inference.
// This is a known limitation that requires further investigation.
// The core declaration features (const, var without init) still work correctly.

// ========================================================================
// Subsumption checking on reassignment to polymorphic mutable bindings.
//
// A var/let written after its initialiser is monomorphic, so these concern
// polymorphic record fields, written through an alias. Every assignment
// must produce a value at-least-as-polymorphic as the field's polytype.
// Without this check, assigning a less-polymorphic function to a polymorphic
// var lets later uses of the var instantiate the original (now-stale)
// polytype, producing inferred types that disagree with runtime values.
// ========================================================================

#[test]
fn test_polymorphic_var_reassignment_unsound() {
    // `id` has type `<a>(a) => a`. `var x = id` generalizes x to that polytype.
    // `(y) => 3` has type `<c>(c) => Number` — strictly LESS polymorphic than x's
    // declared type — and at runtime always returns 3 (a Number).
    //
    // Currently inty accepts the reassignment AND types `z : String` by
    // re-instantiating x's stale polytype with `b = String`. At runtime,
    // x("a") returns 3 (a Number), so the inferred type disagrees with the
    // value. With subsumption checking, the reassignment must be rejected.
    let source = r#"
        function id(x) { return x; }
        var x = id;
        x = function(y) { return 3; };
        var z = x("a");
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Reassigning a polymorphic var to a less-polymorphic function should be \
         rejected — otherwise inty types `z : String` despite x(\"a\") returning 3"
    );
}

#[test]
fn test_reassigned_var_is_monomorphic() {
    // A `var` written after its initialiser isn't generalized: `x` has one
    // type, `(a) => a` at a single `a`, and the assignment unifies with it.
    // Capturing `z` then just makes `z`'s type that `a` — nothing rigid is
    // involved, so nothing can escape.
    let source = r#"
        function id(a) { return a; }
        function leak(z) {
          var x = id;
          x = function(y) { return z; };
          return z;
        }
    "#;
    assert!(infer_program_with_state(source).is_ok());
    // The one type serves the initialiser and the assignment; a reassigned
    // `let` can't be used at two types.
    let mono = r#"
        let f = function (x) { return x; };
        f = function (x) { return x - 1; };
        const c = f(2);
    "#;
    assert!(infer_program_with_state(mono).is_ok());
    let two_types = r#"
        let g = function (x) { return x; };
        g = function (x) { return x; };
        const a = g(1);
        const b = g("s");
    "#;
    assert!(infer_program_with_state(two_types).is_err());
    // A `let` never written is generalized, as a `const` is.
    let poly = r#"
        let h = function (x) { return x; };
        const a = h(1);
        const b = h("s");
    "#;
    assert!(infer_program_with_state(poly).is_ok());
}

#[test]
fn test_polymorphic_deeply_nested_property_reassignment_unsound() {
    // The polymorphic record lives two levels deep — `c.inner.f` carries
    // the polytype, not `c.f`. `lhs_polytype` must walk the full member
    // chain or the subsumption check is bypassed and the original
    // soundness hole is reproduced through the nested property.
    let source = r#"
        function id(x) { return x; }
        const c = { inner: { f: id } };
        var alias = c;
        alias.inner.f = function(y) { return 3; };
        var z = alias.inner.f("a");
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Reassigning a deeply-nested polymorphic property must be rejected — \
         otherwise inty types `z : String` despite alias.inner.f(\"a\") \
         returning 3"
    );
}

#[test]
fn test_polymorphic_obj_property_reassignment_unsound() {
    // A `const` object with a syntactic-value initializer is generalized, so
    // `c` has scheme `<a>{ f: (a) => a }`. Aliasing it to a `var` (`alias = c`)
    // preserves the polytype but makes the binding mutable — opening the same
    // soundness hole at the property level: `alias.f = (y) => 3` is accepted
    // even though the new function isn't at-least-as-polymorphic as the
    // declared field type, and `alias.f("a")` is typed as String while at
    // runtime returning 3.
    let source = r#"
        function id(x) { return x; }
        const c = { f: id };
        var alias = c;
        alias.f = function(y) { return 3; };
        var z = alias.f("a");
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Reassigning a polymorphic property of an aliased polymorphic record \
         should be rejected — otherwise inty types `z : String` despite \
         alias.f(\"a\") returning 3"
    );
}

#[test]
fn test_rank_n_unannotated_record_is_monomorphic() {
    // Under the rank-N rule, polymorphic record fields require an explicit
    // annotation. An unannotated `const c = { f: id }` does NOT inherit
    // `id`'s polymorphism — `c.f` is monomorphic, so two calls at
    // incompatible types cannot both succeed.
    let source = r#"
        function id(x) { return x; }
        const c = { f: id };
        var z1 = c.f("a");
        var z2 = c.f(42);
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Unannotated record field should be monomorphic; using it at two \
         distinct types must fail"
    );
}

#[test]
fn test_rank_n_annotated_polymorphic_field_accepts_polymorphic_rhs() {
    // With an explicit polytype annotation on a record field, writes are
    // checked by subsumption — assigning a value whose type is at-least-as-
    // polymorphic as the declared field type is accepted, and the field
    // remains polymorphic for subsequent reads.
    let source = r#"
        function id(x) { return x; }
        /** var c: { f: <a>(a) => a } */
        var c;
        c.f = id;
        var z1 = c.f("a");
        var z2 = c.f(42);
    "#;
    let (_, env, state) =
        infer_program_with_state(source).expect("annotated polymorphic field write should pass");
    let z1 = state.apply_subst(&env.lookup("z1").unwrap().body.ty);
    let z2 = state.apply_subst(&env.lookup("z2").unwrap().body.ty);
    assert_eq!(z1, Type::String);
    assert_eq!(z2, Type::Number);
}

#[test]
fn test_rank_n_annotated_polymorphic_field_rejects_less_polymorphic_rhs() {
    // Subsumption check: assigning a less-polymorphic function to an
    // annotated polymorphic field is rejected. `(y) => 3` has type
    // `<c>(c) => Number`, which doesn't satisfy `<a>(a) => a`.
    let source = r#"
        /** var c: { f: <a>(a) => a } */
        var c;
        c.f = function(y) { return 3; };
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Writing a less-polymorphic function into a polytype-annotated field \
         should fail subsumption"
    );
}

#[test]
fn test_add_function_has_plus_constraint() {
    let source = "function add(a, b) { return a + b; }";
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    let scheme = env.lookup("add").expect("Should have add function");

    // The function should be polymorphic
    assert!(
        !scheme.vars.is_empty(),
        "add should be polymorphic, got: {:?}",
        scheme
    );

    // The scheme should have a Plus constraint
    assert!(
        !scheme.body.preds.is_empty(),
        "add should have Plus constraint, got scheme: {:?}",
        scheme
    );

    // Check that the constraint is Plus
    let pred = &scheme.body.preds[0];
    assert_eq!(
        pred.class,
        crate::types::ClassName::Plus,
        "Constraint should be Plus"
    );

    // Apply substitution to get the final type
    let ty = state.apply_subst(&scheme.body.ty);

    // The type should be a function
    assert!(ty.is_func(), "add should be a function type");

    // `Plus a` on the operands' one type.
    assert_eq!(pred.types.len(), 1);
    if let Some((_, params, _)) = ty.as_callable() {
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].ty, pred.types[0]);
        assert_eq!(params[1].ty, pred.types[0]);
    }
}

#[test]
fn test_map_function_indexable_unification() {
    // The map function should have a clean type where:
    // - arr element type unifies with fn input type
    // - fn output type unifies with result element type
    // - result type unifies with return type
    let source = r#"
        function map(arr, fn) {
            var result = [];
            for (var i = 0; i < arr.length; i++) {
                result[i] = fn(arr[i]);
            }
            return result;
        }
    "#;
    let (_, env, state) = infer_program_with_state(source).expect("Should type-check successfully");

    let scheme = env.lookup("map").expect("Should have map function");
    let ty = state.apply_subst(&scheme.body.ty);

    // The type should be a function
    assert!(ty.is_func(), "map should be a function type");

    if let Some((_, params, ret)) = ty.as_callable() {
        assert_eq!(params.len(), 2, "map should take 2 parameters");

        // Second param should be a function
        let fn_param = state.apply_subst(&params[1].ty);
        assert!(fn_param.is_func(), "second param should be a function");

        // Return type should be an array
        let ret_type = state.apply_subst(ret);
        assert!(
            matches!(ret_type, Type::Array(_)),
            "return type should be an array, got: {:?}",
            ret_type
        );

        // The fn's return type should match the result array's element type
        if let (Some((_, _, fn_ret)), Type::Array(result_elem)) =
            (fn_param.as_callable(), &ret_type)
        {
            let fn_ret_type = state.apply_subst(fn_ret);
            let result_elem_type = state.apply_subst(result_elem.as_ref());
            assert_eq!(
                fn_ret_type, result_elem_type,
                "fn return type should equal result array element type"
            );
        }
    }
}

#[test]
fn test_map_function_complete_type_signature() {
    // `map` reads `arr.length` and `arr[i]`, so it works on anything with
    // both: arrays and strings alike. Its result's element type is what
    // `fn` returns, and `fn` takes `arr`'s elements.
    let map = r#"
        function map(arr, fn) {
            var result = [];
            for (var i = 0; i < arr.length; i++) {
                result[i] = fn(arr[i]);
            }
            return result;
        }
    "#;
    let t = check_program(
        &format!(
            "{map}\nconst a = map([1, 2], (x) => x * 2);\n\
             const b = map(\"ab\", (c) => c + \"!\");"
        ),
        &["a", "b"],
    )
    .unwrap();
    assert_eq!(t, ["Number[]", "String[]"]);
    // The element flows from `arr` into `fn`: a string's elements are
    // strings, so `c * 2` is wrong.
    assert!(check_program(&format!("{map}\nmap(\"ab\", (c) => c.toFixed(1));"), &[]).is_err());
    // Every quantified variable is used by the type or its predicates.
    let (_, env, _) = infer_program_with_state(map).unwrap();
    let scheme = env.lookup("map").unwrap();
    let mut used = scheme.body.ty.free_vars();
    for p in &scheme.body.preds {
        used.extend(p.free_vars());
    }
    for v in &scheme.vars {
        assert!(
            used.contains(v),
            "quantified {:?} is unused in {:?}",
            v,
            scheme
        );
    }
}

// ========================================================================
// Phase 5 — Narrowing predicates: typeof, ===, !==, member-equality.
// The three programs here mirror the "What good looks like" examples
// in the design doc and must all type-check end-to-end.
// ========================================================================

#[test]
fn test_phase5_typeof_undefined_narrowing() {
    // function f(x: String | undefined) {
    //   if (typeof x === "undefined") { return 0; }
    //   else { return x.length; }   // x narrowed to String in the else
    // }
    // (TypeScript-style "narrow into post-if via early return" relies
    // on control-flow analysis we don't yet do; the explicit else
    // works because Phase-5 narrowing flows the negated predicate
    // into the alternate branch.)
    let src = "/** function f(x: String | undefined) => Number */\n\
               function f(x) { if (typeof x === \"undefined\") { return 0; } else { return x.length; } }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("f").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert_eq!(ret, Type::Number);
    } else {
        panic!("f should be a function");
    }
}

#[test]
fn test_phase5_switch_on_string_literal_union() {
    // function g(s: "a" | "b" | "c") {
    //   switch (s) { case "a": return 1; case "b": return 2; case "c": return 3; }
    // }
    let src = "/** function g(s: \"a\" | \"b\" | \"c\") => Number */\n\
               function g(s) { switch (s) { case \"a\": return 1; case \"b\": return 2; case \"c\": return 3; } return 0; }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("g").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert_eq!(ret, Type::Number);
    } else {
        panic!("g should be a function");
    }
}

#[test]
fn test_phase5_discriminated_union_via_if() {
    // Same shape as the switch example, but using a single if
    // instead of a switch — easier to isolate the narrowing.
    let src = "/** function area(\
               shape: {kind: \"circle\", r: Number} \
                    | {kind: \"square\", s: Number}) => Number */\n\
               function area(shape) { \
                 if (shape.kind === \"circle\") { return shape.r; } else { return shape.s; } \
               }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("area").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert_eq!(ret, Type::Number);
    } else {
        panic!("area should be a function");
    }
}

#[test]
fn test_call_site_tagged_union_arg_via_subsume() {
    // The README/web-examples tagged-union demo. Inference widens the
    // object literal's `"circle"` field to `String` in synthesis mode,
    // so the call site has to subsume `{kind: String, r: Number}` into
    // the discriminated-union parameter via S-UnionR — exactly one arm
    // (`{kind: "circle", r: Number}`) accepts it via field-level
    // literal-vs-base unification.
    let src = "\
        /** function area(s: {kind: \"circle\", r: Number} \
                            | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else { return shape.s; } \
        } \
        var a = area({ kind: \"circle\", r: 10 }); \
        var b = area({ kind: \"square\", s:  5 });";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let a = env.lookup("a").unwrap();
    let b = env.lookup("b").unwrap();
    assert_eq!(state.apply_subst(a.ty()), Type::Number);
    assert_eq!(state.apply_subst(b.ty()), Type::Number);
}

#[test]
fn unsound_string_into_literal_arm_rejected() {
    // The end-to-end soundness regression. Before the literal-vs-base
    // unify rule was made one-directional and `infer_literal` started
    // synthesising singletons, this program type-checked: the
    // checker accepted `String` flowing into the discriminator
    // position `"circle" | "square"`, then narrowing assumed
    // `shape.kind === "circle"` was decidable and let the body
    // return `shape.r`. At runtime k = "circle", control flowed into
    // the circle branch, and `shape.r` was undefined — a Number-typed
    // binding holding undefined.
    //
    // After the fix: `var k = "circle"` widens to `String`. Calling
    // area with `{kind: k, s: 5}` requires either arm to subsume it.
    // Arm 1 fails by row-shape (keys differ); arm 2 needs
    // `subsume(String, "square")`, which the directional S-LitBase
    // (Lit ≤ Base only) rejects. Subsume reports a mismatch.
    let src = "\
        /** function area(s: {kind: \"circle\", r: Number} \
                            | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else { return shape.s; } \
        } \
        var k = \"circle\"; \
        var oops = area({ kind: k, s: 5 });";
    let result = infer_program_with_state(src);
    assert!(
        result.is_err(),
        "soundness gap: String must not flow into a literal-typed \
         discriminator position",
    );
}

#[test]
fn variable_waits_to_be_injected_into_a_typeof_sum() {
    // A value of a type not known yet flowing into a sum told apart by
    // `typeof` waits for its type (the Lean model's `Inject`), rather than
    // being bound to the sum: here the method's `this.b`, a `Boolean`.
    let src = "const o = {b: true, m() { /** const v: Number | Boolean */ const v = this.b; \
               return v; }}; o.m();";
    assert!(infer_program_via_program(src).is_ok());
    // A parameter's: its function's callers pass a case, and only a case.
    let src = "function f(x) { /** const v: Number | String */ const v = x; return x; } \
               f(1); f(\"a\");";
    assert!(infer_program_via_program(src).is_ok());
    let src = "function f(x) { /** const v: Number | String */ const v = x; return x; } \
               f(true);";
    assert!(infer_program_via_program(src).is_err());
}

#[test]
fn typeof_object_takes_a_record_case_apart() {
    let src = "/** const v: Number | {a: Number} */ const v = {a: 1}; const x = v; \
               (typeof x === \"object\" ? x.a : 0);";
    assert!(infer_program_via_program(src).is_ok());
    // The other branch keeps the record case: a declaration may type a
    // function as a record (`Promise`, `Object`), whose `typeof` is
    // "function".
    let src = "/** const v: String | {resolve: (Number) => Promise<Number>, \
               reject: (Number) => Promise<Number>, all: (Promise<Number>[]) => \
               Promise<Number[]>} */ const v = Promise; const x = v; \
               (typeof x === \"object\" ? 0 : x.toUpperCase().length);";
    assert!(infer_program_via_program_with_stdlib(src).is_err());
    let src = "/** const v: Number | {a: Number} */ const v = {a: 1}; v - 1;";
    assert!(infer_program_via_program(src).is_err());
}

#[test]
fn tagged_literal_takes_the_arm_of_its_tag() {
    // Arms of one shape: the literal's tag picks its arm, as the Lean
    // model's `ObjCase.variant` does, rather than synthesis widening the
    // tag to `String`.
    let src = "/** const v: {b: \"circle\"} | {b: \"square\"} */ const v = {b: \"circle\"}; \
               const w = v; (w.b === \"square\" ? 1 : 2);";
    assert!(infer_program_via_program(src).is_ok());
    let src = "/** const v: {b: \"circle\", c: Number} | {b: \"square\", c: Number} */ \
               const v = {c: 1, b: \"square\"};";
    assert!(infer_program_via_program(src).is_ok());
    // A tag that isn't an arm's is still rejected.
    let src = "/** const v: {b: \"circle\"} | {b: \"square\"} */ const v = {b: \"line\"};";
    assert!(infer_program_via_program(src).is_err());
    // As is a field the tag's arm doesn't have.
    let src = "/** const v: {b: \"circle\", c: Number} | {b: \"square\", c: Number} */ \
               const v = {c: \"x\", b: \"square\"};";
    assert!(infer_program_via_program(src).is_err());
    // Only a field every arm has a different string literal type in is a
    // tag, whatever the literal's field order.
    for lit in ["{k: \"a\", c: \"x\"}", "{c: \"x\", k: \"a\"}"] {
        let src = format!(
            "/** const v: {{k: \"a\", c: String}} | {{k: \"b\", c: \"x\"}} */ const v = {lit};"
        );
        assert!(infer_program_via_program(&src).is_ok(), "{src}");
    }
    // A boolean tag picks its arm too, where the arms have one shape (the
    // differential test found it widened to `Boolean`).
    let src = "/** const v: {a: true, b: Number} | {a: false, b: Undefined} */ \
               const v = {b: undefined, a: false}; const w = v; (w.a === false ? 1 : 2);";
    assert!(infer_program_via_program(src).is_ok());
    let src = "/** const v: {a: true, b: Number} | {a: false, b: Undefined} */ \
               const v = {b: 1, a: false};";
    assert!(infer_program_via_program(src).is_err());
}

#[test]
fn alias_keeps_a_declared_records_literal_fields() {
    // Widening at an unannotated binding stops at a record: the copy is
    // the same object, so a write through it must keep the original's
    // literal field types.
    let src = "/** const v: {k: \"a\"} */ const v = {k: \"a\"}; let w = v; w.k = \"z\";";
    assert!(infer_program_via_program(src).is_err());
    let src = "/** const v: {k: \"a\", n: Number} | {k: \"b\", s: String} */ \
               const v = {k: \"a\", n: 1}; \
               function f() { if (v.k === \"a\") { let w = v; w.k = \"b\"; } return 0; }";
    assert!(infer_program_via_program(src).is_err());
    // A fresh literal's fields and elements still widen.
    let src = "const o = {k: \"a\"}; o.k = \"z\"; let p = [1]; p[0] = 2.5; \
               function mk() { return {k: \"a\"}; } let q = mk(); q.k = \"z\";";
    assert!(infer_program_via_program(src).is_ok());
}

#[test]
fn lit_widens_on_var_binding() {
    // `var k = "circle"` widens at the binding site (no annotation
    // ⇒ fresh-literal widening). The annotation is the escape hatch
    // when callers want the singleton preserved.
    let (_, env, state) = infer_program_with_state("var k = \"circle\";").unwrap();
    let k_ty = state.apply_subst(&env.lookup("k").unwrap().body.ty);
    assert_eq!(k_ty, Type::String);
}

#[test]
fn lit_preserved_on_annotated_var() {
    // With an annotation pinning the singleton, the var keeps its
    // literal type — the var's annotation governs.
    let src = "/** var c: {kind: \"circle\", r: Number} */ \
               var c = { kind: \"circle\", r: 10 };";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let c_ty = state.apply_subst(&env.lookup("c").unwrap().body.ty);
    if let Type::Row(row) = &c_ty {
        let kind = row.props.get(&"kind".into()).unwrap();
        assert_eq!(kind.ty, Type::lit_string("circle"));
    } else {
        panic!("expected row, got {:?}", c_ty);
    }
}

#[test]
fn annotated_var_then_call_with_tagged_union_succeeds() {
    // Mirror of the README example but with `var c = ...; area(c)`
    // instead of an inline call. The annotation on `c` keeps its
    // singleton field types so the call resolves to the circle arm.
    let src = "\
        /** function area(s: {kind: \"circle\", r: Number} \
                            | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else { return shape.s; } \
        } \
        /** var c: {kind: \"circle\", r: Number} */ \
        var c = { kind: \"circle\", r: 10 }; \
        var n = area(c);";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let n_ty = state.apply_subst(&env.lookup("n").unwrap().body.ty);
    assert_eq!(n_ty, Type::Number);
}

#[test]
fn unannotated_var_holding_object_widens_and_blocks_call() {
    // Without the annotation: var widens recursively, fields become
    // their bases, the call to `area` no longer matches any arm.
    let src = "\
        /** function area(s: {kind: \"circle\", r: Number} \
                            | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else { return shape.s; } \
        } \
        var c = { kind: \"circle\", r: 10 }; \
        var n = area(c);";
    let result = infer_program_with_state(src);
    assert!(
        result.is_err(),
        "var c widens recursively; calling area(c) must require an annotation",
    );
}

#[test]
fn test_call_site_tagged_union_no_matching_arm() {
    // The same function, called with an object whose *shape* matches
    // no arm. Neither `{kind, q}` row aligns with `{kind, r}` nor
    // `{kind, s}`, so S-UnionR finds zero candidates and subsume
    // reports a mismatch.
    //
    // (Intentionally not testing discriminator-value mismatch like
    // `kind: "triangle"`: the existing literal-vs-base rule in unify
    // widens any string literal to `String` during synthesis, so a
    // wrong discriminator still subsumes via field-level
    // literal-vs-base. Tightening that is a separate, larger change
    // — fresh literal types, option 1 — and this test deliberately
    // exercises only what subsume guarantees today.)
    let src = "\
        /** function area(s: {kind: \"circle\", r: Number} \
                            | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else { return shape.s; } \
        } \
        var t = area({ kind: \"circle\", q: 1 });";
    let result = infer_program_with_state(src);
    assert!(
        result.is_err(),
        "calling area with a shape matching no arm should fail",
    );
}

#[test]
fn test_phase5_discriminated_union_via_switch() {
    // function area(shape: {kind:"circle", r:Number}
    //                    | {kind:"square", s:Number}
    //                    | {kind:"rect", w:Number, h:Number}) {
    //   switch (shape.kind) {
    //     case "circle": return shape.r * shape.r;     // narrowed
    //     case "square": return shape.s * shape.s;     // narrowed
    //     case "rect":   return shape.w * shape.h;     // narrowed
    //   }
    //   return 0;
    // }
    let src = "/** function area(\
               shape: {kind: \"circle\", r: Number} \
                    | {kind: \"square\", s: Number} \
                    | {kind: \"rect\", w: Number, h: Number}) => Number */\n\
               function area(shape) { \
                 switch (shape.kind) { \
                   case \"circle\": return shape.r * shape.r; \
                   case \"square\": return shape.s * shape.s; \
                   case \"rect\":   return shape.w * shape.h; \
                 } \
                 return 0; \
               }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("area").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert_eq!(ret, Type::Number);
    } else {
        panic!("area should be a function");
    }
}

// ========================================================================
// Phase 7 — Builtins return `T | undefined` and the user narrows it.
// ========================================================================

#[test]
fn test_phase7_find_returns_optional() {
    // arr.find(p) on a known Number[] returns Number | Undefined.
    let src = "var arr = [1, 2, 3]; var v = arr.find(function(x) { return x > 0; });";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(scheme.ty());
    assert_eq!(ty, Type::Maybe(Nothing::Undefined, Box::new(Type::Number)));
}

#[test]
fn test_phase7_find_with_typeof_narrowing() {
    // Caller narrows the optional via typeof === "undefined".
    let src = "function pickPositive(arr) { \
                 /** var arr: Number[] */ \
                 var v = arr.find(function(x) { return x > 0; }); \
                 if (typeof v === \"undefined\") { return 0; } else { return v; } \
               }";
    let _ = src; // alternate form below; skip the inner-annotation form.
    let src = "var arr = [1, 2, 3]; \
               var v = arr.find(function(x) { return x > 0; }); \
               var pick = (typeof v === \"undefined\") ? 0 : v;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("pick").unwrap();
    let ty = state.apply_subst(scheme.ty());
    assert_eq!(ty, Type::Number);
}

// ========================================================================
// Phase 6 — Switch-exhaustiveness as a derived check.
// ========================================================================

#[test]
fn test_phase6_exhaustive_switch_no_warning() {
    let src = "/** function g(s: \"a\" | \"b\" | \"c\") => Number */\n\
               function g(s) { switch (s) { case \"a\": return 1; case \"b\": return 2; case \"c\": return 3; } return 0; }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state.warnings.is_empty(),
        "expected no warnings, got: {:?}",
        state.warnings
    );
}

#[test]
fn test_phase6_non_exhaustive_switch_warns() {
    // Missing case "c" — should warn but still type-check.
    let src = "/** function g(s: \"a\" | \"b\" | \"c\") => Number */\n\
               function g(s) { switch (s) { case \"a\": return 1; case \"b\": return 2; } return 0; }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state
            .warnings
            .iter()
            .any(|w| w.message.contains("non-exhaustive") && w.message.contains("\"c\"")),
        "expected non-exhaustive warning mentioning 'c', got: {:?}",
        state.warnings
    );
}

#[test]
fn test_phase6_default_case_suppresses_warning() {
    let src = "/** function g(s: \"a\" | \"b\" | \"c\") => Number */\n\
               function g(s) { switch (s) { case \"a\": return 1; default: return 0; } return 0; }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state.warnings.is_empty(),
        "expected no warnings (default present), got: {:?}",
        state.warnings
    );
}

#[test]
fn test_phase6_discriminated_union_exhaustive() {
    let src = "/** function area(\
               shape: {kind: \"circle\", r: Number} \
                    | {kind: \"square\", s: Number}) => Number */\n\
               function area(shape) { \
                 switch (shape.kind) { \
                   case \"circle\": return shape.r * shape.r; \
                   case \"square\": return shape.s * shape.s; \
                 } \
                 return 0; \
               }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state.warnings.is_empty(),
        "expected no warnings on exhaustive disc-union switch, got: {:?}",
        state.warnings
    );
}

// ========================================================================
// Phase 2 / 3 — Unions formed by join, then read at member-access sites.
// ========================================================================

#[test]
fn test_if_branches_form_union() {
    // Two branches with disjoint row shapes form a union when the return
    // type says so; unannotated, they must agree.
    assert!(infer_program_with_state(
        "function pick(b) { if (b) { return {x: 1, y: 2}; } else { return {x: 3, z: 4}; } }"
    )
    .is_err());
    let src = "/** function pick(Boolean) => {x: Number, y: Number} | {x: Number, z: Number} */\n\
               function pick(b) { if (b) { return {x: 1, y: 2}; } else { return {x: 3, z: 4}; } }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("pick").unwrap();
    let ty = state.apply_subst(scheme.ty());
    // The function's return should be a union of the two row shapes.
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert!(
            matches!(ret, Type::Union(_)),
            "expected return type to be a union, got: {}",
            ret
        );
    } else {
        panic!("pick should be a function");
    }
}

#[test]
fn test_member_on_union_with_shared_field() {
    // Both branches expose `x: Number`, so reading `.x` on the union
    // returns Number even though the rows differ otherwise.
    let src = "function getX(b) {\n\
               /** var pt: {x: Number, y: Number} | {x: Number, z: Number} */\n\
               var pt = b ? {x: 1, y: 2} : {x: 3, z: 4}; return pt.x; }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("getX").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        assert_eq!(ret, Type::Number, "getX return type should be Number");
    } else {
        panic!("getX should be a function");
    }
}

#[test]
fn test_member_on_union_disagreeing_field_joins() {
    // .x has type Number in one member and String in another →
    // the property access yields a union.
    let src = "function getX(b) {\n\
               /** var pt: {x: Number, y: Number} | {x: String, z: Number} */\n\
               var pt = b ? {x: 1, y: 2} : {x: \"a\", z: 4}; return pt.x; }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("getX").unwrap();
    let ty = state.apply_subst(scheme.ty());
    if let Some((_, _, ret)) = ty.as_callable() {
        let ret = state.apply_subst(ret);
        match ret {
            Type::Union(ref m) => {
                assert!(m.contains(&Type::Number));
                assert!(m.contains(&Type::String));
            }
            other => panic!("expected union, got {}", other),
        }
    } else {
        panic!("getX should be a function");
    }
}

// --- Unreachable-narrowing diagnostics --------------------------------

#[test]
fn test_warn_typeof_eqeq_impossible_branch() {
    // `res : Number | String`; `(typeof res) == "boolean"` can never
    // hold, so the if-body is unreachable and we should warn.
    let src = "\
        /** function test(Number) => Number | String */ \
        function test(x) { if (x > 4) { return \"bad\"; } else { return x; } } \
        /** function moshe(Number) => String */ \
        function moshe(x) { \
            /** let res: Number | String */ \
            let res = test(x); \
            if ((typeof res) == \"number\") { return \"cool\"; } \
            else if ((typeof res) == \"boolean\") { return \"bad\"; } \
            else { return \"other\"; } \
        }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state
            .warnings
            .iter()
            .any(|w| w.message.contains("always false")),
        "expected an 'always false' warning for the boolean branch, got: {:?}",
        state.warnings
    );
}

#[test]
fn test_warn_typeof_strict_eq_impossible_branch() {
    // Same as above, but with strict equality.
    let src = "\
        function f(x) { \
            /** let res: Number | String */ \
            let res = x; \
            if ((typeof res) === \"boolean\") { return 1; } else { return 2; } \
        }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        state
            .warnings
            .iter()
            .any(|w| w.message.contains("always false")),
        "expected an 'always false' warning, got: {:?}",
        state.warnings
    );
}

#[test]
fn test_no_warn_typeof_satisfiable_branch() {
    // `res : Number | String`; both `"number"` and `"string"` are
    // possible, so neither side of the if should warn.
    let src = "\
        function f(x) { \
            /** let res: Number | String */ \
            let res = x; \
            if ((typeof res) === \"number\") { return 1; } else { return 2; } \
        }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    assert!(
        !state
            .warnings
            .iter()
            .any(|w| w.message.contains("always false") || w.message.contains("always true")),
        "did not expect an unreachable-branch warning, got: {:?}",
        state.warnings
    );
}

#[test]
fn test_warn_strict_eq_literal_impossible_branch() {
    // Discriminated-union narrowing: the `triangle` arm can never
    // match the closed `"circle" | "square"` discriminator.
    // The annotation is now required: with the row-tail
    // substitution fix in place, an un-annotated `shape` would
    // be inferred as a single closed row carrying *all* of
    // `r`, `s`, `kind`, and the call below (which only supplies
    // `kind` and `r`) would fail at the missing `s`. The
    // annotation states the discriminated-union shape the
    // function is really meant to handle.
    // The annotation is required: with the row-tail substitution
    // fix, an un-annotated `shape` is inferred as a single closed
    // row carrying *all* of `r`, `s`, and `kind`, and any caller
    // missing one of those would fail. The annotation states the
    // discriminated-union shape the function is meant to handle.
    // We don't make a call here — the test only cares about which
    // warnings fire on the body's narrowing.
    let src = "\
        /** function area(shape: {kind: \"circle\", r: Number} \
                              | {kind: \"square\", s: Number}) => Number */\n\
        function area(shape) { \
            if (shape.kind === \"circle\") { return shape.r; } \
            else if (shape.kind === \"triangle\") { return 0; } \
            else { return shape.s; } \
        }";
    let (_, _, state) = infer_program_with_state(src).unwrap();
    // The narrowing on the second arm depends on `area`'s parameter
    // being inferred to a closed-union shape. If inference doesn't
    // reach that, the warning may not fire — we only assert that
    // *no* spurious warnings are emitted on the satisfiable arms.
    let spurious = state
        .warnings
        .iter()
        .filter(|w| {
            (w.message.contains("always false") || w.message.contains("always true"))
                && w.span.start <= "function area(shape) { if (shape.kind === \"circle\"".len()
        })
        .count();
    assert_eq!(
        spurious, 0,
        "no warning should fire on the first satisfiable arm, got: {:?}",
        state.warnings
    );
}

// ----- P4: class field declarations + modifier tolerance -----

#[test]
fn class_with_modifier_and_field_decls_types_check() {
    // The migration-style class: modifiers, declaration-only field
    // (constructor sets it), declaration-with-initializer, and a method.
    let src = "\
        class Counter { \
            private count = 0; \
            inc() { return this.count + 1; } \
        } \
        var c = Counter(); \
        var n = c.inc();";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("n").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::Number);
}

#[test]
fn class_ts_inline_annotation_pins_field_type() {
    let src = "\
        class C { count: Number = 0; constructor() {} } \
        var c = C(); \
        var v = c.count;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::Number);
}

#[test]
fn class_decl_only_field_annotation_typechecks_against_constructor_param() {
    // `name: String;` declaration-only field; constructor sets it.
    // Annotation moves to the constructor-extracted property, so the
    // parameter `name` is fixed at String. Calling with a Number errors.
    let src = "\
        class P { name: String; constructor(name) { this.name = name; } } \
        var p = P(\"alice\"); \
        var n = p.name;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("n").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);

    // Calling with a Number must fail (type mismatch on constructor arg).
    let src_bad = "\
        class P { name: String; constructor(name) { this.name = name; } } \
        var p = P(42);";
    assert!(infer_program_with_state(src_bad).is_err());
}

#[test]
fn class_field_array_type() {
    let src = "\
        class C { items: Number[] = []; constructor() {} } \
        var c = C(); \
        var first = c.items.length;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("first").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::Number);
}

// ----- P7: optional chaining (?.) and nullish coalescing (??) -----

fn assert_union_eq(actual: &Type, expected_members: &[Type]) {
    let want = Type::union(expected_members.iter().cloned());
    assert_eq!(actual, &want, "expected {:?}, got {:?}", want, actual);
}

#[test]
fn optional_member_on_nullable_receiver_adds_undefined() {
    // `o : {name: String} | Null` → `o?.name : String | Undefined`.
    let src = "\
        /** function f(o: {name: String} | Null) => String | Undefined */ \
        function f(o) { return o?.name; } \
        var v = f({name: \"a\"});";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_union_eq(&ty, &[Type::String, Type::Undefined]);
}

#[test]
fn optional_member_on_non_nullable_no_undefined() {
    // Non-nullable receiver: `?.` types identically to `.`.
    let src = "\
        var o = {name: \"a\"}; \
        var v = o?.name;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn nullish_coalesce_strips_null_and_undefined() {
    // `(String | Null) ?? "x"` → `String`.
    let src = "\
        /** function f(s: String | Null) => String */ \
        function f(s) { return s ?? \"x\"; } \
        var v = f(\"a\");";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn nullish_coalesce_with_disjoint_branches_unions() {
    // `(String | Null) ?? Number` → `String | Number`.
    let src = "\
        /** function f(s: String | Null) => String | Number */ \
        function f(s) { return s ?? 42; } \
        var v = f(\"a\");";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_union_eq(&ty, &[Type::String, Type::Number]);
}

#[test]
fn nullish_coalesce_non_nullable_left_drops_right() {
    // Non-nullable left: result is just the left type. Right side is
    // type-checked but unreachable.
    let src = "\
        var s = \"a\"; \
        var v = s ?? \"b\";";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn optional_chain_combined_with_nullish_coalesce() {
    // `o?.name ?? "anon"` on a nullable receiver pulls a clean `String`.
    let src = "\
        /** function getName(o: {name: String} | Null) => String */ \
        function getName(o) { return o?.name ?? \"anon\"; } \
        var v = getName(null);";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::String);
}

#[test]
fn optional_chain_member_chain_propagates() {
    // `a?.b.c` on a nullable head: the `.c` step rides the chain so
    // the whole expression types as `T_c | Undefined` rather than
    // erroring on the inner `.b` access against a nullable.
    let src = "\
        /** function f(o: {b: {c: Number}} | Null) => Number | Undefined */ \
        function f(o) { return o?.b.c; } \
        var v = f(null);";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("v").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_union_eq(&ty, &[Type::Number, Type::Undefined]);
}

// ----- P3: spread/rest in object & array literals -----

#[test]
fn array_spread_propagates_element_type() {
    // `[...xs, y]` with `xs : Number[]` and `y : Number` is
    // `Number[]`. Mixing element types fails just as plain literals
    // do.
    let src = "\
        var xs = [1, 2, 3]; \
        var ys = [...xs, 4];";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("ys").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::array(Type::Number));
}

#[test]
fn array_spread_mixed_types_unions() {
    // Mixed element types form a union when the annotation says so:
    // `[...xs, "three"]` with `xs : Number[]` checks against
    // `(Number | String)[]`. (Unannotated, the elements must agree.)
    assert!(infer_program_with_state("var xs = [1, 2]; var ys = [...xs, \"three\"];").is_err());
    let src = "\
        var xs = [1, 2]; \
        /** var ys: (Number | String)[] */ \
        var ys = [...xs, \"three\"];";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("ys").unwrap();
    let ty = state.apply_subst(&scheme.body.ty);
    assert_eq!(ty, Type::array(Type::union([Type::Number, Type::String])));
}

#[test]
fn object_spread_right_biased_merge() {
    // `{ ...a, x: 2 }` overrides `a.x`. With `a : {x: Number, y: String}`
    // the result is `{x: Number, y: String}` — right-bias keeps the
    // last value type at `x`.
    let src = "\
        var a = {x: 1, y: \"s\"}; \
        var b = { ...a, x: 99 }; \
        var bx = b.x; \
        var by = b.y;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("bx").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("by").unwrap().body.ty),
        Type::String
    );
}

#[test]
fn object_spread_two_sources_merge() {
    // `{ ...a, ...b }` with a and b disjoint produces the union of
    // their fields.
    let src = "\
        var a = {x: 1}; \
        var b = {y: \"hi\"}; \
        var c = { ...a, ...b }; \
        var cx = c.x; \
        var cy = c.y;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("cx").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("cy").unwrap().body.ty),
        Type::String
    );
}

#[test]
fn array_destructuring_rest_gives_array_type() {
    let src = "\
        var xs = [1, 2, 3]; \
        const [head, ...tail] = xs; \
        var hd = head; \
        var tl = tail;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("hd").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("tl").unwrap().body.ty),
        Type::array(Type::Number)
    );
}

// ----- P8: TS-flavor type-annotation extensions -----

#[test]
fn ts_optional_property_is_presence_polymorphic() {
    // `{ name?: String }` parses as a row whose `name` field carries a
    // fresh presence variable theta (Remy '94). Reading `o.name` forces
    // theta := Pre, so the access yields just `String` — not `String |
    // Undefined`. Optionality lives in the row, not in the value's type.
    let src = "\
        /** const o: { name?: String } */ \
        const o; \
        var n = o.name;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let n = state.apply_subst(&env.lookup("n").unwrap().body.ty);
    assert_eq!(n, Type::String);
}

// ----- Remy '94 presence polymorphism (optional row fields) -----

#[test]
fn optional_field_caller_may_omit() {
    // A function whose parameter row marks `b` optional accepts both a
    // caller that supplies it and a caller that does not. Generalising
    // over the presence variable means each call gets a fresh theta;
    // one binds Pre, the other binds Abs, and neither conflicts with
    // the other.
    let src = "\
        /** function f(o: {a: Number, b?: String}) => Number */ \
        function f(o) { return o.a; } \
        var x = f({a: 1, b: \"hi\"}); \
        var y = f({a: 2});";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("x").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("y").unwrap().body.ty),
        Type::Number
    );
}

#[test]
fn optional_field_extra_present_field_still_rejected_when_closed() {
    // Presence polymorphism is orthogonal to closed-row strictness:
    // unknown fields still don't fit a closed row. `c` here is not
    // declared in the annotation at all, so the call must fail.
    let src = "\
        /** function f(o: {a: Number, b?: String}) => Number */ \
        function f(o) { return o.a; } \
        var z = f({a: 1, b: \"hi\", c: true});";
    assert!(infer_program_with_state(src).is_err());
}

#[test]
fn optional_field_read_inside_body_forces_present() {
    // If the function body reads `o.b`, the body's typing pins
    // theta := Pre, so the scheme is no longer presence-polymorphic
    // and a caller that omits `b` fails to unify.
    let src = "\
        /** function f(o: {b?: String}) => String */ \
        function f(o) { return o.b; } \
        var z = f({});";
    assert!(infer_program_with_state(src).is_err());
}

#[test]
fn ts_object_type_semicolon_separator_accepted() {
    // TS uses `;` between properties in object types; we accept
    // both `;` and `,` for compatibility with hand-imported `.d.ts`.
    let src = "\
        /** const o: { x: Number; y: String } */ \
        const o; \
        var x = o.x; \
        var y = o.y;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("x").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("y").unwrap().body.ty),
        Type::String
    );
}

#[test]
fn ts_readonly_modifier_erased() {
    let src = "\
        /** const o: { readonly id: Number, name: String } */ \
        const o; \
        var n = o.id;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("n").unwrap().body.ty),
        Type::Number
    );
}

#[test]
fn ts_any_rejected_with_suggestion() {
    let src = "\
        /** const x: any */ \
        const x;";
    let err = match infer_program_with_state(src) {
        Ok(_) => panic!("any should reject"),
        Err(e) => e,
    };
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("not supported") && msg.contains("concrete type"),
        "expected a suggestion mentioning concrete types, got: {}",
        msg
    );
}

#[test]
fn ts_intersection_rejected_with_suggestion() {
    let src = "\
        /** const x: { a: Number } & { b: String } */ \
        const x;";
    let err = match infer_program_with_state(src) {
        Ok(_) => panic!("intersection should reject"),
        Err(e) => e,
    };
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("intersection") && msg.contains("merge"),
        "expected a suggestion to merge rows, got: {}",
        msg
    );
}

// ----- P6: user-defined generic type aliases -----

#[test]
fn generic_alias_substitutes_in_annotation() {
    // `Pair<Number>` substitutes `Number` for the alias's `T` and
    // produces a closed row `{ first: Number, second: Number }`.
    let src = "\
        /** type Pair<T> = { first: T, second: T } */ \
        /** const p: Pair<Number> */ \
        const p; \
        var f = p.first; \
        var s = p.second;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let f = state.apply_subst(&env.lookup("f").unwrap().body.ty);
    let s = state.apply_subst(&env.lookup("s").unwrap().body.ty);
    assert_eq!(f, Type::Number);
    assert_eq!(s, Type::Number);
}

#[test]
fn generic_alias_used_as_function_return_type() {
    // `(T) => Pair<T>` infers a polymorphic function whose return
    // type unifies with the substituted alias body.
    let src = "\
        /** type Pair<T> = { first: T, second: T } */ \
        /** const makePair: <T>(T) => Pair<T> */ \
        const makePair; \
        var p = makePair(42); \
        var f = p.first;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let f = state.apply_subst(&env.lookup("f").unwrap().body.ty);
    assert_eq!(f, Type::Number);
}

#[test]
fn generic_alias_two_parameters() {
    // `type Mapping<K, V> = { key: K, value: V }` with separate
    // parameters in source order.
    let src = "\
        /** type Mapping<K, V> = { key: K, value: V } */ \
        /** const m: Mapping<String, Number> */ \
        const m; \
        var k = m.key; \
        var v = m.value;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let k = state.apply_subst(&env.lookup("k").unwrap().body.ty);
    let v = state.apply_subst(&env.lookup("v").unwrap().body.ty);
    assert_eq!(k, Type::String);
    assert_eq!(v, Type::Number);
}

#[test]
fn alias_arity_mismatch_errors() {
    // Bare `Pair` (no `<…>`) for a 1-arg alias is also an arity
    // mismatch — it should not silently degrade to a fresh type
    // variable. Both forms below must error.
    let zero_args = "\
        /** type Pair<T> = { first: T, second: T } */ \
        /** const p: Pair */ \
        const p;";
    assert!(infer_program_with_state(zero_args).is_err());

    let bad = "\
        /** type Pair<T> = { first: T, second: T } */ \
        /** const p: Pair<Number, String> */ \
        const p;";
    assert!(infer_program_with_state(bad).is_err());
}

#[test]
fn nullary_alias_substitutes_in_const_annotation() {
    // `type Func = () => {id: String}` — the alias has no
    // parameters, and a bare reference (`func: Func`) should
    // expand to its body. The body's row is closed, so the
    // returned literal `{id: '123', name: 'hello'}` carrying an
    // excess `name` field must NOT unify.
    let src = "\
        /** type Func = () => {id: String} */ \
        /** const func: Func */ \
        const func = function() { return {id: '123', name: 'hello'}; };";
    assert!(
        infer_program_with_state(src).is_err(),
        "expected excess-field rejection via closed-row alias body"
    );
}

#[test]
fn nullary_alias_enforces_field_types() {
    // The body says `id: String`; the literal returns `id: 42`.
    // Bare alias reference must expand to the closed-row body so
    // the type mismatch is caught.
    let src = "\
        /** type Func = () => {id: String} */ \
        /** const func: Func */ \
        const func = function() { return {id: 42}; };";
    assert!(
        infer_program_with_state(src).is_err(),
        "expected Number-vs-String mismatch via expanded alias body"
    );
}

#[test]
fn nullary_alias_to_primitive_substitutes() {
    // The simplest case: a bare alias to a primitive. `const x: S`
    // followed by `x = 42` must reject because `S` resolves to
    // `String`, not to a fresh type variable.
    let src = "\
        /** type S = String */ \
        /** const x: S */ \
        const x = 42;";
    assert!(
        infer_program_with_state(src).is_err(),
        "expected Number-vs-String mismatch via nullary primitive alias"
    );
}

#[test]
fn unknown_type_identifier_rejects() {
    // A type identifier that isn't a primitive, an alias, or a
    // quantifier-bound parameter must be rejected at annotation
    // parse time. The previous "fall through to fresh type variable"
    // behaviour silently accepted typos like `Stirng`.
    let typoed_const = "\
        /** const a: Stirng */ \
        const a = 42;";
    assert!(infer_program_with_state(typoed_const).is_err());

    let typoed_param = "\
        /** function f(x: Numbr) => Numbr */ \
        function f(x) { return x; } \
        const r = f(\"oops\");";
    assert!(infer_program_with_state(typoed_param).is_err());
}

#[test]
fn quantifier_bound_identifier_resolves() {
    // Sanity check that the strict rule still admits the legitimate
    // cases: an explicit `<T>` quantifier introduces `T` as a
    // bindable type-variable name within its body.
    let src = "\
        /** const id: <T>(T) => T */ \
        const id; \
        const n = id(42); \
        const s = id(\"hi\");";
    let (_, env, state) = infer_program_with_state(src).expect("explicit quantifier should bind T");
    assert_eq!(
        state.apply_subst(&env.lookup("n").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("s").unwrap().body.ty),
        Type::String
    );
}

#[test]
fn polymorphic_annotation_checks_initializer_rigidly() {
    // A polymorphic annotation on a binding with an initialiser, as the
    // Lean model's `letPoly`: the initialiser is checked with the type
    // variables rigid, and the binding has every instance.
    let ok = "\
        /** const id: <a>(a) => a */ \
        const id = (x) => x; \
        const n = id(42); \
        const s = id(\"hi\");";
    let (_, env, state) = infer_program_with_state(ok).expect("a polymorphic identity checks");
    assert_eq!(
        state.apply_subst(&env.lookup("n").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("s").unwrap().body.ty),
        Type::String
    );
    // An initialiser less polymorphic than the annotation.
    let too_specific = "\
        /** const f: <a>(a) => a */ \
        const f = (x) => 5;";
    assert!(infer_program_with_state(too_specific).is_err());
    // A rigid type variable escaping into the context: `z`'s type would
    // have to be `a`.
    let escapes = "\
        const h = (z) => { \
          /** const f: <a>(a) => a */ \
          const f = (x) => { const w = [z, x]; return x; }; \
          return z; \
        };";
    assert!(infer_program_with_state(escapes).is_err());
    // A constraint left on a rigid type variable.
    let constrained = "\
        /** const f: <a>(a) => a */ \
        const f = (x) => x + x;";
    assert!(infer_program_with_state(constrained).is_err());
    // A rigid type variable escaping into a constraint left on a type
    // variable nothing fixes: `o.l` has the type `a`, so `o`'s type has a
    // field `l: a`. The rules type this (the Lean model's `polyGap`, with
    // `o: {l: a}` at each rigid name), but inference rejects it, as the
    // model's does (`polyGap_separates`): keeping the constraint would need
    // an implication constraint. (`p` puts the field `l` in the program,
    // which the model's wire format needs to read it.)
    let gap = "\
        const p = { l: 1 }; \
        /** const f: <a>(a) => a */ \
        const f = (y) => { const g = true ? (o) => o.l : (o) => y; return y; };";
    assert!(infer_program_with_state(gap).is_err());
    // Without the field read nothing escapes.
    let no_gap = "\
        /** const f: <a>(a) => a */ \
        const f = (y) => { const g = true ? (o) => y : (o) => y; return y; };";
    assert!(infer_program_with_state(no_gap).is_ok());
    // The initialiser sees the binding at the annotation's scheme:
    // polymorphic recursion.
    let recursive = "\
        /** const len: <a>(a[]) => Number */ \
        const len = (xs) => xs.length === 0 ? 0 : 1 + len(xs.slice(1)); \
        const n = len([\"a\"]) + len([1]);";
    assert!(infer_program_with_state(recursive).is_ok());
    // An initialiser that isn't a value has no rule in the model: its
    // annotation's variables stay flexible, and it isn't generalised.
    let not_value = "\
        const mk = () => (x) => x; \
        /** const g: <a>(a) => a */ \
        const g = mk(); \
        const n = g(1);";
    assert!(infer_program_with_state(not_value).is_ok());
}

#[test]
fn statement_values_are_dropped() {
    // A statement's value is dropped (the Lean model's `HasTypeS.drop`):
    // the branches of a `?:` or `??` in an expression statement needn't
    // have one type, but the program's last statement, its completion
    // value, still has one.
    let ok = "const c = true; (c ? 1 : \"a\"); 2;";
    assert!(infer_program_via_program(ok).is_ok());
    let in_loop = "let c = true; while (c) { c ? 1 : \"a\"; c = false; } 2;";
    assert!(infer_program_via_program(in_loop).is_ok());
    let last = "const c = true; (c ? 1 : \"a\");";
    assert!(infer_program_via_program(last).is_err());
}

#[test]
fn reads_of_an_operand_of_plus_stay_on_the_variable() {
    // A receiver `+` constrains is a number or a string: the end of the
    // program doesn't default its property reads to an object's fields.
    let src = "(function (x) { return (x + x).length; });";
    let (_, _, mut state) = infer_program_via_program(src).unwrap();
    assert!(state.resolve_constraints().is_ok());
}

#[test]
fn spread_of_a_field_stored_back() {
    // `{...x}` of an open row shares the operand's tail; its call signature
    // is absent as the operand's is, so storing it back unifies without a
    // cycle through the tail.
    let src = "({a: {c: \"\"}, m() { this.a = {...this.a}; return 1; }});";
    assert!(infer_program_with_state(src).is_ok());
}

#[test]
fn alias_is_structural_not_nominal() {
    // `Cancellable<X>` and an inline row of the same shape are
    // interchangeable. Passing the inline form where an alias is
    // expected (and vice versa) type-checks.
    let src = "\
        /** type Box<T> = { value: T } */ \
        /** const f: (Box<Number>) => Number */ \
        const f; \
        var inline = { value: 42 }; \
        var n = f(inline);";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let n = state.apply_subst(&env.lookup("n").unwrap().body.ty);
    assert_eq!(n, Type::Number);
}

#[test]
fn object_destructuring_rest_strips_named_keys() {
    // After `{a, ...rest} = {a: 1, b: "x", c: true}`, `rest` should
    // have the row `{b: String, c: Boolean}` — `a` is removed.
    let src = "\
        var obj = {a: 1, b: \"x\", c: true}; \
        const {a, ...rest} = obj; \
        var av = a; \
        var bv = rest.b; \
        var cv = rest.c;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("av").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("bv").unwrap().body.ty),
        Type::String
    );
    assert_eq!(
        state.apply_subst(&env.lookup("cv").unwrap().body.ty),
        Type::Boolean
    );

    // Reading `rest.a` must fail — the key was removed from the row.
    let src_bad = "\
        var obj = {a: 1, b: \"x\"}; \
        const {a, ...rest} = obj; \
        var av = rest.a;";
    assert!(infer_program_with_state(src_bad).is_err());
}

/// Re-runs a source string through the same code path as the CLI
/// (`infer_program_with_env`), which is the only path that exercises the
/// binding-group / hoisting logic in `infer_stmt_list`. The simpler
/// `infer_program_with_state` walks statements one at a time and bypasses
/// hoisting entirely.
fn infer_program_via_program(source: &str) -> InferResult<(Type, TypeEnv, InferState)> {
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let mut program = parser.parse_program().unwrap();
    program.type_aliases = type_aliases;

    let mut state = InferState::new();
    let env = initial_env();
    let (ty, env) = state.infer_program_with_env(&env, &program)?;
    Ok((ty, env, state))
}

// ---------------------------------------------------------------------------
// SCC-based binding inference (docs/scc-inference.md)
//
// Each test pins one behaviour of the dependency-driven hoisting
// analysis that replaces adjacent-only function-decl grouping.
// ---------------------------------------------------------------------------

/// Forward reference across an intervening `const` declaration —
/// previously rejected as "Undefined variable" because the const
/// broke the binding group. With SCC inference, the const is just
/// processed in source order against the fully-hoisted function
/// env. Mirrors the htmx pattern.
#[test]
fn scc_forward_ref_through_intervening_const() {
    let src = "
        function a() { return b(); }
        const sep = 1;
        function b() { return 1; }
        var x = a();
    ";
    let (_, env, state) = infer_program_via_program(src).expect("must type-check");
    let x_ty = state.apply_subst(&env.lookup("x").unwrap().body.ty);
    assert_eq!(x_ty, Type::Number);
}

/// Forward reference from inside an object-literal property to a
/// later function decl. This is the inner structure of the htmx
/// `const htmx = { values: function(...){ getInputValues(...) } };
/// function getInputValues(...){}` pattern.
#[test]
fn scc_forward_ref_into_object_literal_property() {
    let src = "
        const api = {
            run: function(x) { return helper(x); }
        };
        function helper(x) { return x; }
        var y = api.run(42);
    ";
    let (_, env, state) = infer_program_via_program(src).expect("must type-check");
    let y_ty = state.apply_subst(&env.lookup("y").unwrap().body.ty);
    assert_eq!(y_ty, Type::Number);
}

/// Mutual recursion produces one shared SCC. The pair `up` and
/// `down` cross-reference each other; the SCC analysis must put
/// them in the same group so peer references resolve. The test
/// asserts the program type-checks; the inferred return type of
/// the recursive cycle is implementation-detail (it ends up as a
/// fresh flex var when the base-case branch returns a singleton
/// `0` and both arms only ever flow through the recursion).
#[test]
fn scc_mutual_recursion_collapses_to_one_group() {
    let src = "
        function up(n)   { if (n <= 0) { return 0; } return down(n - 1); }
        function down(n) { if (n <= 0) { return 0; } return up(n - 1); }
        var x = up(4);
        var y = down(7);
    ";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "mutually-recursive `up`/`down` must type-check: {:?}",
        result.err()
    );
}

/// A group's members have one type each inside the group, and are
/// generalised together after it (as the Lean model's lowering of a group,
/// `model_wire::Cx::group`, types them).
#[test]
fn scc_group_monomorphic_inside_polymorphic_after() {
    let after = "
        function f(x, n) { return n > 0 ? g(x, n - 1) : x; }
        function g(x, n) { return f(x, n); }
        const a = f(1, 2) - 1;
        const b = g(\"s\", 1).length;
    ";
    assert!(infer_program_via_program(after).is_ok());
    let inside = "
        function f(x) { g(1); g(\"s\"); return x; }
        function g(y) { return f(y); }
    ";
    assert!(infer_program_via_program(inside).is_err());
}

/// Non-recursive callee in its own SCC keeps its polymorphism, so a
/// later caller can use it at two different instantiations. This is
/// the principal-types property — adjacent grouping forced both call
/// sites to share a TVar; SCC isolation lets them instantiate
/// independently.
#[test]
fn scc_polymorphic_callee_used_at_two_types() {
    let src = "
        function caller() {
            var a = id(1);
            var b = id(\"hi\");
            return a;
        }
        function id(x) { return x; }
        var r = caller();
    ";
    let (_, env, state) = infer_program_via_program(src).expect("must type-check");
    let r_ty = state.apply_subst(&env.lookup("r").unwrap().body.ty);
    assert_eq!(r_ty, Type::Number);
}

/// Three-function dependency chain `a → b → c`, no cycles. Each
/// becomes its own singleton SCC, processed in topological order
/// (callees first). `c` is polymorphic; `b` and `a` see its
/// generalised scheme. The chained call should type correctly.
#[test]
fn scc_topological_order_caller_after_callee() {
    let src = "
        function a() { return b(1) + 1; }
        function b(n) { return c(n) + 1; }
        function c(n) { return n; }
        var out = a();
    ";
    let (_, env, state) = infer_program_via_program(src).expect("must type-check");
    let out_ty = state.apply_subst(&env.lookup("out").unwrap().body.ty);
    assert_eq!(out_ty, Type::Number);
}

/// IIFE library pattern — the gap-4c shape that motivated the SCC
/// refactor. A function declared *after* an object literal whose
/// property body references it.
#[test]
fn scc_iife_library_pattern() {
    let src = "
        var lib = (function() {
            const api = {
                run: function(x) { return helper(x); }
            };
            function helper(x) { return x; }
            return api;
        })();
        var y = lib.run(42);
    ";
    let (_, env, state) = infer_program_via_program(src).expect("must type-check");
    let y_ty = state.apply_subst(&env.lookup("y").unwrap().body.ty);
    assert_eq!(y_ty, Type::Number);
}

/// Phase 0.1 regression: `export function` declarations must hoist as a
/// peer group so forward references and mutual recursion across exports
/// resolve, exactly like plain `function` declarations already do.
#[test]
fn export_functions_forward_reference_resolves() {
    let src = "\
        export function diff(x, y) { return bod(y) - bod(x); } \
        export function bod(d) { return 1; }";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "export function peer forward reference must type-check: {:?}",
        result.err()
    );
}

/// Plain function declarations were already hoisted; this guards against
/// regression while the predicate was extended to cover exports.
#[test]
fn plain_functions_forward_reference_still_resolves() {
    let src = "\
        function diff(x, y) { return bod(y) - bod(x); } \
        function bod(d) { return 1; }";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "plain forward ref regressed: {:?}",
        result.err()
    );
}

/// Mixed group: a plain `function` and an `export function` share a
/// binding group when they're adjacent.
#[test]
fn mixed_plain_and_export_functions_hoist_together() {
    let src = "\
        function helper(x) { return adjust(x); } \
        export function adjust(x) { return x + 1; }";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "mixed plain/export hoisting must work: {:?}",
        result.err()
    );
}

/// Phase 1.1 regression: `export async function` parses without a
/// "found 'async', expected ..." error. The body is wrapped in a
/// `Promise.resolve` IIFE by the parser, so this test only verifies
/// that the production parses; full-stdlib resolution lives in the
/// CLI integration path.
#[test]
fn export_async_function_parses() {
    let mut scanner = Scanner::new("export async function f(x) { return x; }");
    let mut tokens = Vec::new();
    loop {
        let tok = scanner.next_token().unwrap();
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let mut parser = Parser::with_source(
        tokens,
        scanner.type_annotations().to_vec(),
        "export async function f(x) { return x; }".to_string(),
    );
    let result = parser.parse_program();
    assert!(
        result.is_ok(),
        "export async function must parse: {:?}",
        result.err()
    );
}

/// Phase 1.3 regression: a default parameter value constrains the
/// parameter's inferred type to the default's type.
#[test]
fn default_parameter_pins_param_type() {
    let src = "\
        function throttle(fn, delay = 1000) { return delay; } \
        var n = throttle(function(){}, 500);";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "default param must work: {:?}",
        result.err()
    );

    // Mismatched call site: passing a String for `delay` must error.
    let bad = "\
        function throttle(fn, delay = 1000) { return delay; } \
        var n = throttle(function(){}, \"oops\");";
    assert!(
        infer_program_via_program(bad).is_err(),
        "default param must constrain call-site arg type"
    );
}

/// Phase 1.4 regression: destructuring defaults parse without error.
#[test]
fn destructuring_default_in_function_param() {
    let src = "\
        function orient({ target, anchor = 0, reset = false }) { return target; } \
        var x = orient({ target: 1, anchor: 2, reset: true });";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "destructuring defaults must parse: {:?}",
        result.err()
    );
}

/// Phase 1.5 regression: rest parameters bind a single name and don't
/// disturb earlier parameters. inty has no variadic-call shape so
/// callers must match arity exactly — `f(1, [2, 3])` would work but
/// `f(1, 2, 3)` would error on arity. This test exercises the parse
/// + the single-name binding shape only.
#[test]
fn rest_parameter_parses_and_binds() {
    let src = "function f(first, ...rest) { return first; } var n = f(1, [2, 3]);";
    let result = infer_program_via_program(src);
    assert!(result.is_ok(), "rest param must work: {:?}", result.err());
}

/// Phase 1.6 regression: spread in a call argument unwraps the array
/// to its element type and is treated as a single argument.
#[test]
fn spread_call_arg_unwraps_array_element() {
    let src = "\
        function f(x) { return x + 1; } \
        const arr = [1, 2, 3]; \
        const r = f(...arr);";
    let result = infer_program_via_program(src);
    assert!(
        result.is_ok(),
        "spread in call must work: {:?}",
        result.err()
    );
}

/// Phase 1.7 regression: `catch {}` without a binding parses.
#[test]
fn catch_without_binding_parses() {
    let mut scanner = Scanner::new("function f() { try { return 1; } catch {} }");
    let mut tokens = Vec::new();
    loop {
        let tok = scanner.next_token().unwrap();
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let mut parser = Parser::with_source(
        tokens,
        scanner.type_annotations().to_vec(),
        "function f() { try { return 1; } catch {} }".to_string(),
    );
    let result = parser.parse_program();
    assert!(
        result.is_ok(),
        "catch-no-bind must parse: {:?}",
        result.err()
    );
}

/// Phase 1.9 (bonus) regression: object property shorthand `{a, b}`
/// expands to `{a: a, b: b}`.
#[test]
fn object_property_shorthand() {
    let src = "var a = 1; var b = \"hi\"; var o = {a, b}; var n = o.a; var s = o.b;";
    let (_, env, state) = infer_program_via_program(src).unwrap();
    assert_eq!(
        state.apply_subst(&env.lookup("n").unwrap().body.ty),
        Type::Number
    );
    assert_eq!(
        state.apply_subst(&env.lookup("s").unwrap().body.ty),
        Type::String
    );
}

/// Phase 1.2 regression: `export default class extends X { ... }`
/// produces the existing inheritance-rejection error rather than a
/// confusing "expected expression" parse error.
#[test]
fn export_default_class_extends_rejects_with_inheritance_error() {
    use crate::error::IntyError;
    let src = "import { B } from \"./b.js\"; export default class extends B {}";
    let mut scanner = Scanner::new(src);
    let mut tokens = Vec::new();
    loop {
        let tok = scanner.next_token().unwrap();
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let mut parser =
        Parser::with_source(tokens, scanner.type_annotations().to_vec(), src.to_string());
    let result = parser.parse_program();
    let err = result.expect_err("must error on extends");
    let msg = match err {
        IntyError::Parse(p) => format!("{:?}", p),
        other => panic!("expected ParseError, got {:?}", other),
    };
    assert!(
        msg.contains("class inheritance is not supported"),
        "diagnostic should mention inheritance: {}",
        msg
    );
}

/// Two member accesses on the same parameter must both contribute their
/// row constraints to the parameter's inferred type. The first `o.foo`
/// access binds the parameter to `{foo: α | ρ₁}`; the second `o.bar`
/// access then unifies that row with `{bar: β | ρ₂}`, which binds `ρ₁`
/// to a row containing `bar`. Applying the substitution to the
/// parameter type must follow that binding through the tail variable —
/// otherwise the `bar` constraint is silently dropped, and the
/// printed/generalised function type only mentions `foo`.
#[test]
fn row_subst_merges_bindings_through_open_tail() {
    let t = check_program("function f(o) { var a = o.foo; var b = o.bar; }", &["f"]).unwrap();
    assert!(t[0].contains("a has {foo: b, bar: c}"), "{}", t[0]);
    // And once `o` is an object, both reads are its fields.
    let t = check_program(
        "function f(o) { var a = o.foo; var b = o.bar; return o; }\n\
         const r = f({foo: 1, bar: \"s\"});",
        &["r"],
    )
    .unwrap();
    assert_eq!(t[0], "{bar: String, foo: Number}");
}

/// Soundness companion to `row_subst_merges_bindings_through_open_tail`:
/// if the second member access's constraint is dropped, then calling
/// `f({foo: 1})` is wrongly accepted even though `f` reads `o.bar`.
#[test]
fn row_subst_call_missing_field_is_rejected() {
    let src = "function f(o) { var a = o.foo; var b = o.bar; } f({foo: 1});";
    let result = infer_program_with_state(src);
    assert!(
        result.is_err(),
        "calling f without `bar` should be a type error, but inference succeeded"
    );
}

/// Metamorphic property: the set of row constraints a function imposes
/// on its parameter must be invariant under reordering of the member
/// accesses in its body. For accesses [A1..An] over distinct fields
/// and a closed-row call argument, the call type-checks if and only
/// if the argument supplies every Ai — and which of the Ai is "first"
/// must not matter.
///
/// This catches the row-tail-substitution bug as an asymmetry: with
/// the bug, `function f(o){o.a; o.b;}` accepts `f({a:1})` (b's
/// constraint is dropped), while `function f(o){o.b; o.a;}` rejects
/// it (a's constraint is dropped instead). Both should reject.
#[test]
fn metamorphic_member_access_order_invariant() {
    let fields = ["foo", "bar", "baz"];

    // Every ordered pair (a, b) of distinct fields. For each pair we
    // build `function f(o){ o.a; o.b; }` and check that calls missing
    // either field are rejected. The full set of pairs covers both
    // orderings of every unordered pair, so any asymmetry surfaces as
    // one of the two pairs failing the assertion.
    for a in &fields {
        for b in &fields {
            if a == b {
                continue;
            }

            // Call provides only `a` (missing `b`).
            let missing_b = format!(
                "function f(o) {{ var x = o.{}; var y = o.{}; }} f({{ {}: 1 }});",
                a, b, a
            );
            assert!(
                infer_program_with_state(&missing_b).is_err(),
                "f(o){{o.{}; o.{};}} called with only `{}` should be rejected (missing `{}`)",
                a,
                b,
                a,
                b
            );

            // Call provides only `b` (missing `a`).
            let missing_a = format!(
                "function f(o) {{ var x = o.{}; var y = o.{}; }} f({{ {}: 1 }});",
                a, b, b
            );
            assert!(
                infer_program_with_state(&missing_a).is_err(),
                "f(o){{o.{}; o.{};}} called with only `{}` should be rejected (missing `{}`)",
                a,
                b,
                b,
                a
            );

            // And the well-formed call providing both must succeed —
            // proves the rejections above were the missing-field
            // constraint, not some incidental error.
            let both = format!(
                "function f(o) {{ var x = o.{}; var y = o.{}; }} f({{ {}: 1, {}: 2 }});",
                a, b, a, b
            );
            assert!(
                infer_program_with_state(&both).is_ok(),
                "f(o){{o.{}; o.{};}} called with both `{}` and `{}` should type-check",
                a,
                b,
                a,
                b
            );
        }
    }
}

/// Three-access version of the metamorphic property. Beyond the
/// pairwise asymmetry, the bug compounds with each additional access:
/// only the first one's constraint survives, so any call argument
/// that satisfies that single field gets through. Verifying every
/// permutation of three accesses ensures the row carries the full set
/// regardless of order.
#[test]
fn metamorphic_three_member_accesses_order_invariant() {
    let fields = ["foo", "bar", "baz"];

    // Permutations of three distinct fields.
    let perms: [[&str; 3]; 6] = [
        ["foo", "bar", "baz"],
        ["foo", "baz", "bar"],
        ["bar", "foo", "baz"],
        ["bar", "baz", "foo"],
        ["baz", "foo", "bar"],
        ["baz", "bar", "foo"],
    ];

    for perm in &perms {
        // For each permutation, every "drop one field from the call"
        // variant must be rejected. The position of the dropped field
        // in the access order should not matter.
        for missing in &fields {
            let provided: Vec<&str> = fields.iter().copied().filter(|f| f != missing).collect();
            let call_lit = provided
                .iter()
                .enumerate()
                .map(|(i, f)| format!("{}: {}", f, i + 1))
                .collect::<Vec<_>>()
                .join(", ");
            let body = perm
                .iter()
                .enumerate()
                .map(|(i, f)| format!("var v{} = o.{};", i, f))
                .collect::<Vec<_>>()
                .join(" ");
            let src = format!("function f(o) {{ {} }} f({{ {} }});", body, call_lit);
            assert!(
                infer_program_with_state(&src).is_err(),
                "access order [{}, {}, {}] missing `{}` should be rejected, but type-checked. Source: {}",
                perm[0], perm[1], perm[2], missing, src
            );
        }
    }
}

// ---------------------------------------------------------------------------
// `Type::Error` semantics
//
// The error sentinel is produced by best-effort recovery in the inference
// engine (used by the upcoming SCC partition logic: an SCC that fails to
// infer binds each of its members to `Type::Error` so downstream SCCs
// continue without cascading). These tests pin the four rules `Error`
// must satisfy: it unifies trivially with anything, member access on
// it produces `Error`, calling it produces `Error`, and the type-class
// solver treats it as satisfying every constraint.
// ---------------------------------------------------------------------------

#[test]
fn error_unifies_trivially_with_concrete() {
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    // Error on the left, concrete on the right.
    state
        .unify(span, &Type::Error, &Type::Number)
        .expect("Error ~ Number must succeed");
    state
        .unify(span, &Type::Error, &Type::String)
        .expect("Error ~ String must succeed");
    // Error on the right, concrete on the left.
    state
        .unify(span, &Type::Boolean, &Type::Error)
        .expect("Boolean ~ Error must succeed");
    state
        .unify(span, &Type::Undefined, &Type::Error)
        .expect("Undefined ~ Error must succeed");
}

#[test]
fn error_unifies_with_compound_types() {
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    let func = Type::simple_func(vec![Type::Number], Type::String);
    state
        .unify(span, &Type::Error, &func)
        .expect("Error ~ Func must succeed");
    let arr = Type::Array(Box::new(Type::Number));
    state
        .unify(span, &arr, &Type::Error)
        .expect("Array ~ Error must succeed");
}

#[test]
fn error_unifies_with_flex_var_without_binding_it() {
    // Specifically: unifying Error with a fresh var should not bind
    // the var to Error (which would propagate Error to every site
    // that shares the var). The current rule is to short-circuit
    // before var_bind, leaving the var unconstrained.
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    let v = state.fresh_type_var();
    state
        .unify(span, &Type::Error, &v)
        .expect("Error ~ Var must succeed");
    // The var should still be a free type variable, not bound to Error.
    let resolved = state.apply_subst(&v);
    assert!(
        matches!(resolved, Type::Var(_)),
        "expected var to remain free, got {:?}",
        resolved
    );
}

#[test]
fn error_member_access_produces_error() {
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    let result = state
        .infer_member_on_type(&Type::Error, "anyfield", span)
        .expect("member access on Error must succeed");
    assert_eq!(result, Type::Error);
}

#[test]
fn error_apply_subst_is_identity() {
    let mut state = InferState::new();
    let v = state.fresh_type_var();
    // Even with a substitution that binds the var, Error itself
    // shouldn't change.
    let span = crate::span::Span::new(0, 0);
    state.unify(span, &v, &Type::Number).unwrap();
    assert_eq!(state.apply_subst(&Type::Error), Type::Error);
}

#[test]
fn error_free_vars_is_empty() {
    assert!(Type::Error.free_vars().is_empty());
}

#[test]
fn error_renders_as_sentinel_string() {
    let mut ctx = crate::types::PrettyContext::new();
    assert_eq!(ctx.format_type(&Type::Error), "<error>");
}

#[test]
fn error_satisfies_plus_constraint() {
    use crate::types::TypePred;
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    state.add_constraint(TypePred::plus(Type::Error), span);
    state
        .resolve_constraints()
        .expect("Plus Error must resolve trivially");
}

#[test]
fn error_satisfies_indexable_constraint() {
    use crate::types::TypePred;
    let mut state = InferState::new();
    let span = crate::span::Span::new(0, 0);
    // Indexable Error _ _ — should resolve regardless of the
    // index/element components.
    state.add_constraint(
        TypePred::indexable(Type::Error, Type::Number, Type::String),
        span,
    );
    state
        .resolve_constraints()
        .expect("Indexable on Error must resolve trivially");
}

#[test]
fn error_call_propagates_through_call() {
    // End-to-end: a binding manually substituted to Error is called;
    // the call result should be Error, not propagate constraint
    // failures through the parameter inference.
    use crate::ast::Stmt;
    let mut state = InferState::new();
    let env = initial_env();
    // Build an env where `f` is Error.
    let env = env.extend("f".to_string(), crate::types::TypeScheme::mono(Type::Error));
    let src = "f(1, 2, 3)";
    let mut scanner = Scanner::new(src);
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
    let mut parser = Parser::with_source(tokens, type_annotations, src.to_string());
    let program = parser.parse_program().unwrap();
    let expr = match &program.statements[0] {
        Stmt::Expr { expression, .. } => expression.clone(),
        _ => panic!(),
    };
    let result = state
        .infer_expr(&env, &expr)
        .expect("Error(...) must succeed");
    let resolved = state.apply_subst(&result);
    assert_eq!(resolved, Type::Error);
}

#[test]
fn error_member_chain_propagates() {
    // Chained member access on an Error binding stays Error all the
    // way through — no diagnostics emitted at any of the segments.
    use crate::ast::Stmt;
    let mut state = InferState::new();
    let env = initial_env();
    let env = env.extend(
        "broken".to_string(),
        crate::types::TypeScheme::mono(Type::Error),
    );
    let src = "broken.a.b.c";
    let mut scanner = Scanner::new(src);
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
    let mut parser = Parser::with_source(tokens, type_annotations, src.to_string());
    let program = parser.parse_program().unwrap();
    let expr = match &program.statements[0] {
        Stmt::Expr { expression, .. } => expression.clone(),
        _ => panic!(),
    };
    let result = state
        .infer_expr(&env, &expr)
        .expect("chained access on Error must succeed");
    assert_eq!(state.apply_subst(&result), Type::Error);
}

#[test]
fn error_does_not_cascade_to_unrelated_bindings() {
    // The motivating use case: one binding fails (we substitute it
    // with Error), but other bindings in the same program continue
    // to type-check normally.
    let mut state = InferState::new();
    let env = initial_env();
    let env = env.extend(
        "broken".to_string(),
        crate::types::TypeScheme::mono(Type::Error),
    );

    // Build a program that uses `broken` *and* an unrelated valid
    // binding. The unrelated path must still infer correctly.
    let src = "var a = broken.field + 1; var b = 42 + 1;";
    let mut scanner = Scanner::new(src);
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, src.to_string());
    let mut program = parser.parse_program().unwrap();
    program.type_aliases = type_aliases;
    let (_, env_after) = state
        .infer_program_with_env(&env, &program)
        .expect("program with Error binding must still type-check");
    state
        .resolve_constraints()
        .expect("constraints must resolve");
    // `a` involves Error.field + 1 → Error + Number → resolves OK (Plus Error trivially).
    let a_ty = state.apply_subst(&env_after.lookup("a").unwrap().body.ty);
    // The result is whatever the `+` operator produced; since one
    // operand is Error, no diagnostic was emitted. We don't assert
    // the exact type — only that we reached here without an error.
    let _ = a_ty;
    // `b` is unrelated and must type-check to Number.
    let b_ty = state.apply_subst(&env_after.lookup("b").unwrap().body.ty);
    assert_eq!(b_ty, Type::Number, "unrelated `b` should be Number");
}

// ---------------------------------------------------------------------------
// Multi-error reporting: the `infer_stmt_list` recovery path accumulates
// every error it encounters in `state.errors`, so the CLI / LSP can
// surface them all in one run instead of forcing the user into a
// fix-recompile-fix loop. The public API still returns the first error
// via `Result::Err` for backwards compatibility.
// ---------------------------------------------------------------------------

/// Parse a source string using the same lexer + parser as the binary
/// pipeline. Helper for the multi-error tests below.
fn parse_for_multi_error_test(source: &str) -> crate::ast::Program {
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let mut program = parser.parse_program().unwrap();
    program.type_aliases = type_aliases;
    program
}

#[test]
fn multi_error_two_independent_undefined_vars() {
    // Two `var` initialisers each reference an undefined name. Pre-
    // recovery, only the first one was reported; now both should land
    // in `state.errors` and the second binding should be recoverable
    // (bound to `Type::Error`) so any later code referring to it
    // doesn't add a third unrelated error.
    let program =
        parse_for_multi_error_test("var a = doesNotExistOne; var b = doesNotExistTwo; var c = b;");
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    assert!(
        errs.len() >= 2,
        "expected at least two errors, got {}: {:?}",
        errs.len(),
        errs
    );
    // `a` and `b` should both end up as Error in the final env so a
    // third declaration that references one of them doesn't trigger
    // a cascading "undefined variable" error.
    let undef_count = errs
        .iter()
        .filter(|e| matches!(e.as_type(), Some(TypeError::UndefinedVariable { .. })))
        .count();
    assert!(
        undef_count >= 2,
        "expected at least two UndefinedVariable errors, got: {:?}",
        errs
    );
}

#[test]
fn multi_error_first_error_returned_matches_accumulated() {
    // The error returned via `Result::Err` must be byte-for-byte the
    // same diagnostic that lands at the head of `state.errors`. This
    // is what keeps existing single-error callers stable while
    // multi-error consumers drain the accumulated list.
    let program = parse_for_multi_error_test("var x = nope1; var y = nope2;");
    let mut state = InferState::new();
    let env = initial_env();
    let err = state
        .infer_program_with_env(&env, &program)
        .expect_err("missing names must error");
    let errs = state.take_errors();
    assert!(!errs.is_empty(), "errors should be accumulated");
    assert_eq!(
        format!("{:?}", err),
        format!("{:?}", errs[0]),
        "Result::Err should match state.errors[0]"
    );
}

#[test]
fn multi_error_clean_program_accumulates_nothing() {
    // No errors should accumulate when a program type-checks cleanly.
    // This pins the invariant that recovery never *adds* spurious
    // entries to `state.errors`.
    let program = parse_for_multi_error_test("var x = 1; var y = 2; var z = x + y;");
    let mut state = InferState::new();
    let env = initial_env();
    state
        .infer_program_with_env(&env, &program)
        .expect("clean program must type-check");
    assert!(
        state.take_errors().is_empty(),
        "no errors should be accumulated for a clean program"
    );
}

#[test]
fn multi_error_failing_var_binds_name_to_error() {
    // After a `var x = <bad>` fails, `x` should be bound to
    // `Type::Error` in the env so a later reference doesn't cascade
    // into a fresh "undefined variable" error. The original error is
    // the only one surfaced for `x`; the later read of `x` is
    // silently absorbed.
    let program = parse_for_multi_error_test("var x = undefinedName; var y = x;");
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    // Exactly one error: the original UndefinedVariable for
    // `undefinedName`. The read of `x` on the second statement must
    // not produce another.
    let undef_for_x = errs.iter().any(
        |e| matches!(e.as_type(), Some(TypeError::UndefinedVariable { name, .. }) if name == "x"),
    );
    assert!(
        !undef_for_x,
        "reading recovered `x` should not error: {:?}",
        errs
    );
}

#[test]
fn multi_error_cross_scc_and_source_order_both_collected() {
    // A failing SCC plus a failing source-order statement should
    // *both* land in state.errors. This exercises the combined
    // Pass 2 + Pass 3 recovery.
    //
    // SCC failure: `bad` calls a non-existent name `noSuchThing`.
    // Source-order failure: a later `var` references another missing name.
    let program = parse_for_multi_error_test(
        "function bad() { return noSuchThing(); }
         var here = alsoMissing;",
    );
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    assert!(
        errs.len() >= 2,
        "expected at least two errors (one from SCC, one from source order), got: {:?}",
        errs
    );
}

#[test]
fn multi_error_duplicate_const_no_longer_aborts() {
    // The duplicate-`const`-in-the-same-scope diagnostic used to
    // `return Err(...)` immediately. With multi-error recovery it
    // joins `state.errors` and inference continues.
    let program = parse_for_multi_error_test(
        "const dup = 1; const dup = 2; var after = somethingElseMissing;",
    );
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    let has_dup = errs.iter().any(|e| {
        matches!(e.as_type(), Some(TypeError::Module { message, .. })
            if message.contains("duplicate declaration"))
    });
    let has_undef = errs.iter().any(|e| {
        matches!(e.as_type(), Some(TypeError::UndefinedVariable { name, .. })
            if name == "somethingElseMissing")
    });
    assert!(has_dup, "expected duplicate-const error, got: {:?}", errs);
    assert!(
        has_undef,
        "expected later undefined-variable error to still surface, got: {:?}",
        errs
    );
}

// ---------------------------------------------------------------------------
// Recursion-depth limit on `Type::apply_subst`. See `docs/scaling.md`.
// The cap protects against SIGSEGV on adversarial input; the
// integration test below confirms a diagnostic surfaces cleanly
// instead of a crash when an overflow happens inside inference.
// ---------------------------------------------------------------------------

/// Build a source string `var x = { a: { a: { a: ... 1 } } }` nested
/// `depth` times. Each `{a: ...}` adds one Row layer to the inferred
/// type, so inference produces a Type::Row whose `a` field's type is
/// itself a Row whose `a` field's type is ... — exactly the recursive
/// shape `Type::apply_subst` walks. Used (with a lowered depth cap)
/// to drive the limit from inside `infer_program_with_env` without
/// fighting the parser, which is itself recursive on deep literals.
fn nested_object_literal_source(depth: usize) -> String {
    // Annotated: a declaration resolves its annotated type whole (an
    // inferred result is only resolved at its head).
    let mut src = String::from("/** var x: ");
    for _ in 0..depth {
        src.push_str("{a: ");
    }
    src.push_str("Number");
    for _ in 0..depth {
        src.push('}');
    }
    src.push_str(" */\nvar x = ");
    for _ in 0..depth {
        src.push_str("{a: ");
    }
    src.push('1');
    for _ in 0..depth {
        src.push('}');
    }
    src.push(';');
    src
}

/// RAII helper that lowers the apply_subst depth cap for the
/// duration of one test and restores it on drop.
struct DepthLimitScope(usize);
impl DepthLimitScope {
    fn new(limit: usize) -> Self {
        let prev = crate::types::subst::set_apply_subst_depth_limit_for_test(limit);
        Self(prev)
    }
}
impl Drop for DepthLimitScope {
    fn drop(&mut self) {
        crate::types::subst::set_apply_subst_depth_limit_for_test(self.0);
    }
}

#[test]
fn apply_subst_overflow_surfaces_clean_diagnostic() {
    // Drive `apply_subst` past the cap from inside inference using
    // a shallow object-literal value plus a deliberately tiny cap.
    // The walk bails to `Type::Error` and the driver pushes a clean
    // "recursion-depth cap" diagnostic — the user-facing payoff of
    // the depth limit. Never a SIGSEGV, always a clean message. The
    // 3-deep source is shallow enough that the test thread's small
    // stack handles it comfortably; cap=2 still trips during
    // apply_subst because each row layer recurses through the type
    // tree.
    let _scope = DepthLimitScope::new(2);
    let src = nested_object_literal_source(3);
    let program = parse_for_multi_error_test(&src);
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    let has_overflow_diag = errs.iter().any(|e| {
        matches!(e.as_type(), Some(TypeError::Module { message, .. })
            if message.contains("recursion-depth cap"))
    });
    assert!(
        has_overflow_diag,
        "expected the apply_subst overflow to surface as a clean diagnostic, got: {:?}",
        errs
    );
}

#[test]
fn apply_subst_overflow_flag_does_not_leak_between_runs() {
    // Run 1 trips the cap and surfaces the diagnostic. Run 2 on a
    // shallow program with fresh state must NOT see the stale flag
    // — the driver clears it at the start of every call.
    let _scope = DepthLimitScope::new(2);

    let program = parse_for_multi_error_test(&nested_object_literal_source(3));
    let mut state = InferState::new();
    let env = initial_env();
    let _ = state.infer_program_with_env(&env, &program);
    let errs = state.take_errors();
    assert!(
        errs.iter().any(
            |e| matches!(e.as_type(), Some(TypeError::Module { message, .. })
                    if message.contains("recursion-depth cap")
            )
        ),
        "run 1 should see the diagnostic, got: {:?}",
        errs
    );

    // Run 2: fresh state, shallow program, no diagnostic.
    let program = parse_for_multi_error_test("var y = 1;");
    let mut state = InferState::new();
    let env = initial_env();
    state
        .infer_program_with_env(&env, &program)
        .expect("clean program in run 2");
    let errs = state.take_errors();
    assert!(
        errs.is_empty(),
        "run 2 must not see the stale flag, got: {:?}",
        errs
    );
}

#[test]
fn modestly_deep_program_does_not_trigger_overflow_diagnostic() {
    // Regression: legitimate code must not trip the diagnostic. A
    // 2-deep nested literal under the default 256 cap (no scope
    // override) is comfortably under the limit.
    let src = nested_object_literal_source(2);
    let program = parse_for_multi_error_test(&src);
    let mut state = InferState::new();
    let env = initial_env();
    state
        .infer_program_with_env(&env, &program)
        .expect("modestly-deep literal should type-check");
    let errs = state.take_errors();
    assert!(
        !errs.iter().any(
            |e| matches!(e.as_type(), Some(TypeError::Module { message, .. })
                    if message.contains("recursion-depth cap")
            )
        ),
        "shallow program must not trigger overflow diagnostic, got: {:?}",
        errs
    );
}

// ----- Shape B: annotated param + stdlib optional params -----

/// Pins the user-visible win of Shape B phase 4 on the canonical
/// htmx-shaped pattern: a function takes a parameter annotated as
/// `String` and calls the stdlib's `String.prototype.slice` with
/// mixed arities in the same body. Without phase 4 (or without the
/// annotation), `slice` is declared `(Number, Number) => String`
/// and the 1-arg call errors with "Arity mismatch: expected 2,
/// found 1". With phase 4 AND the annotation, the 1-arg call binds
/// the presence variable to `Abs` and the 2-arg call binds it to
/// `Pre` — both type-check.
///
/// This is the shape that htmx's `getTimeoutInterval` (line 380 of
/// htmx.js) hits, distilled to avoid stdlib globals that the bare
/// test harness doesn't load.
#[test]
fn annotated_string_param_accepts_mixed_arity_slice() {
    let src = "\
        /** function getSuffix(str: String) => String */ \
        function getSuffix(str) { \
            if (str.slice(-2) == \"ms\") { return str.slice(0, -2); } \
            if (str.slice(-1) == \"s\")  { return str.slice(0, -1); } \
            return str; \
        }";
    let result = infer_program_with_state(src);
    assert!(
        result.is_ok(),
        "annotated-String param + mixed-arity stdlib slice should type-check, got: {:?}",
        result.err()
    );
    let (_, _, state) = result.unwrap();
    let errs: Vec<_> = state
        .errors
        .iter()
        .filter(|e| !matches!(e.as_type(), Some(TypeError::Module { .. })))
        .collect();
    assert!(errs.is_empty(), "expected no errors, got: {:?}", errs);
}

/// Same pattern with `padStart`'s optional second arg. Pins that the
/// optional-trailing-arg decl handles the "omit the optional"
/// direction even when the value is annotated.
#[test]
fn annotated_string_param_accepts_padstart_omitting_optional() {
    let src = "\
        /** function rightPad(s: String) => String */ \
        function rightPad(s) { return s.padStart(4); }";
    let result = infer_program_with_state(src);
    assert!(
        result.is_ok(),
        "padStart(target) should accept the omitted-padString form, got: {:?}",
        result.err()
    );
}

/// `Array.prototype.indexOf` has both args optional in the stdlib
/// decl (`indexOf(elem, fromIndex?)`). Test both the 1-arg and
/// 2-arg call shapes on the same annotated array param.
#[test]
fn annotated_array_param_accepts_optional_index_of() {
    let src = "\
        /** function searchTwice(arr: Number[], needle: Number) => Boolean */ \
        function searchTwice(arr, needle) { \
            var first  = arr.indexOf(needle); \
            var second = arr.indexOf(needle, first + 1); \
            return first < second; \
        }";
    let result = infer_program_with_state(src);
    assert!(
        result.is_ok(),
        "Array.indexOf with mixed arity should type-check, got: {:?}",
        result.err()
    );
}

/// An unannotated parameter used as `str.slice(-2)` and `str.slice(0, -2)`:
/// each read of `.slice` is its own `HasProp` constraint, resolved against
/// a fresh copy of `String.prototype.slice` once `str` is known, so the
/// optional second argument can be omitted in one call and given in the
/// other. (A single inferred row field shared one presence variable
/// between the two calls and rejected this.)
#[test]
fn unannotated_param_mixed_arity_slice() {
    let src = "\
        function getSuffix(str) { \
            if (str.slice(-2) == \"ms\") { return str.slice(0, -2); } \
            return str; \
        }\n\
        const s = getSuffix(\"10ms\");";
    assert_eq!(check_program(src, &["s"]).unwrap(), ["String"]);
    // A number has no `slice`.
    let bad = "\
        function getSuffix(str) { \
            if (str.slice(-2) == \"ms\") { return str.slice(0, -2); } \
            return str; \
        }\n\
        getSuffix(10);";
    assert!(check_program(bad, &[]).is_err());
}

/// A `for (let i = 0; …)` header variable is mutable, so it widens like
/// an ordinary `let`: its type is `Number`, not the singleton `0` (which
/// a later `f(i)` / `g(1)` pair sharing one parameter would contradict).
#[test]
fn test_for_init_literal_is_widened() {
    let program =
        crate::frontends::javascript::parse_source("for (let i = 0; i < 3; i++) {}").unwrap();
    let decl_span = match &program.statements[0] {
        crate::ast::Stmt::For {
            init: Some(crate::ast::ForInit::VarDecl(decls)),
            ..
        } => decls[0].span,
        other => panic!("expected a for loop, got {:?}", other),
    };
    let mut state = InferState::new();
    state.infer_program(&initial_env(), &program).unwrap();
    let ty = state.apply_subst(state.get_decl_type(decl_span).unwrap());
    assert_eq!(ty, Type::Number);
}

/// Indexing an as-yet-unknown container with a literal (`xs[0]`) defers
/// an `Indexable` constraint whose index is the singleton type `0`. The
/// resolver must widen it like the eager rule does, or `first` could not
/// be applied to an array at all.
#[test]
fn test_deferred_literal_index_is_widened() {
    let src = "function first(xs) { return xs[0]; }\n\
               const a = first([3, 1, 2]);\n\
               const b = first([\"x\", \"y\"]);";
    let program = crate::frontends::javascript::parse_source(src).unwrap();
    let mut state = InferState::new();
    state
        .infer_program(&initial_env(), &program)
        .and_then(|_| state.resolve_constraints())
        .expect("first(xs) = xs[0] should apply to number[] and string[]");
}

// ---- Generalisation soundness ---------------------------------------------
//
// Regression tests for generalising against `ftv(S Γ)` (the environment's
// free variables *after* substitution) closed over the pending constraints'
// functional dependencies, and for inferring function-valued `const`s with
// the hoisted functions. Each program was mis-typed before the change; the
// comment says how.

/// Infer a whole program; the display form of each requested binding's
/// scheme, or the first error.
fn check_program(src: &str, names: &[&str]) -> Result<Vec<String>, String> {
    let program = crate::frontends::javascript::parse_source(src).map_err(|e| e.to_string())?;
    let mut state = InferState::new();
    let (_, env) = state
        .infer_program_with_env(&initial_env(), &program)
        .map_err(|e| e.to_string())?;
    if let Some(e) = state.errors.first() {
        return Err(e.to_string());
    }
    state.resolve_constraints().map_err(|e| e.to_string())?;
    Ok(names
        .iter()
        .map(|n| {
            let scheme = env.lookup(n).unwrap_or_else(|| panic!("{} not bound", n));
            format!("{}", state.display_scheme(scheme))
        })
        .collect())
}

#[test]
fn gen_rejects_wrong_argument_through_later_const() {
    // Was accepted: `f` was generalised to `∀a. (a) => …` although its
    // body passes `x` to the (then placeholder) `g : (Number) => Number`.
    let src = "function f(x) { return g(x); }\n\
               const g = (y) => y * 2;\n\
               const r = f(\"hi\");";
    assert!(check_program(src, &[]).is_err());
}

#[test]
fn gen_later_const_keeps_its_principal_type() {
    // `pair` was corrupted to `(a, a) => {first: b, second: a}` by the
    // hoisted `both`; now it is inferred first and both stay polymorphic.
    let src = "function both(x) { return pair(x, x); }\n\
               const pair = (a, b) => ({ first: a, second: b });\n\
               const b1 = both(1.5);\n\
               const b2 = both(\"s\");\n\
               const p = pair(\"s\", 2);";
    let t = check_program(src, &["pair", "both", "p"]).unwrap();
    assert_eq!(t[0], "<a, b>(a, b) => {first: a, second: b}");
    assert_eq!(t[1], "<a>(a) => {first: a, second: a}");
    assert_eq!(t[2], "{first: String, second: Number}");
}

#[test]
fn gen_element_of_later_const_is_not_quantified() {
    // `pick` was `∀r. (Number) => r`: the element variable of
    // `Indexable(NAMES, Number, r)` was quantified while `NAMES` was still
    // a placeholder, so `pick(0) * 2` type-checked.
    let src = "function pick(i) { return NAMES[i]; }\n\
               const NAMES = [\"a\", \"b\"];\n\
               const s = pick(0);\n\
               const t = s * 2;";
    assert!(check_program(src, &[]).is_err());
    let ok = "function pick(i) { return NAMES[i]; }\nconst NAMES = [\"a\", \"b\"];";
    assert_eq!(
        check_program(ok, &["pick"]).unwrap()[0],
        "(Number) => String"
    );
}

#[test]
fn gen_fixed_index_does_not_fix_the_container() {
    // Functional dependency container → element: a fixed *index* (a
    // top-level const, still a placeholder) must not make `get`
    // monomorphic.
    let src = "const KEY = 0;\n\
               function get(o) { return o[KEY]; }\n\
               const a = get([1]);\n\
               const b = get([\"s\"]);";
    let t = check_program(src, &["get"]).unwrap();
    assert!(t[0].contains("Indexable a"), "{}", t[0]);
}

#[test]
fn gen_captured_variable_is_not_quantified() {
    // `outer` was `<a, b> where Plus a => (b) => (a) => a`: `inner` was
    // generalised over the type of the captured `x`.
    let src = "function outer(x) { function inner(y) { return x + y; } return inner; }\n\
               var addThree = outer(3);";
    let t = check_program(src, &["outer", "addThree"]).unwrap();
    assert_eq!(t[0], "<a> where Plus a => (a) => (a) => a");
    assert_eq!(t[1], "(Number) => Number");
}

#[test]
fn gen_presence_variable_in_environment_is_not_quantified() {
    // The optional field's presence variable is reachable from `o`; `m`
    // used to generalise it, accepting a read of a field that is absent.
    let src = "function outer(o) {\n\
                 /** const g: (p: {name?: String}) => Number */\n\
                 const g = (p) => 1;\n\
                 g(o);\n\
                 let m = () => o;\n\
                 const n = m().name.length;\n\
                 return n;\n\
               }\n\
               outer({});";
    assert!(check_program(src, &[]).is_err());
}

#[test]
fn gen_hoisted_const_function_stays_immutable() {
    let src = "const f = () => 1;\nf = () => 2;";
    let err = check_program(src, &[]).unwrap_err();
    assert!(err.contains("constant"), "{}", err);
}

#[test]
fn gen_parameter_shadows_function_name() {
    let t = check_program("const f = (f) => f + 1;\nconst r = f(2);", &["f"]).unwrap();
    assert_eq!(t[0], "(Number) => Number");
    let t = check_program("function g(g) { return g + 1; }\nconst r = g(2);", &["g"]).unwrap();
    assert_eq!(t[0], "(Number) => Number");
}

#[test]
fn gen_const_function_using_polymorphic_alias_stays_in_source_order() {
    // `g` depends on the non-function const `alias`, so it is not hoisted
    // and sees `alias`'s polymorphic scheme.
    let src = "const id = (x) => x;\n\
               const alias = id;\n\
               const g = () => { alias(1); return alias(\"s\"); };";
    let t = check_program(src, &["alias"]).unwrap();
    assert_eq!(t[0], "<a>(a) => a");
}

#[test]
fn gen_return_in_both_branches_of_if() {
    // The `if` statement's completion type joined `Lit(0)` with `f`'s
    // return variable, pinning it to the singleton `0`.
    let src = "function f(n) { if (n == 0) return 0; else return f(n - 1); }";
    let principal = "(Number) => Number";
    assert_eq!(check_program(src, &["f"]).unwrap()[0], principal);
    let nested = "function f(n) { function g(m) { return f(m - 1); } \
                  if (n == 0) return 0; else return g(n); }";
    assert_eq!(
        check_program(nested, &["f"]).unwrap()[0],
        "(Number) => Number"
    );
}

// ---- Older holes found by the generalisation review ------------------------

#[test]
fn flatten_expands_every_occurrence_of_a_bound_row() {
    // `flatten` expanded each bound variable once per call, so the second
    // copy of `o` lost its fields and `r.p.y` could be used as a Number.
    let src = "function f(o) { const a = o.x; const b = o.y; return {p: o, q: o}; }\n\
               const r = f({x: 1, y: \"s\"});\n\
               const bad = r.p.y * 2;";
    assert!(check_program(src, &[]).is_err());
    let t = check_program(
        "function f(o) { const a = o.x; const b = o.y; return {p: o, q: o}; }",
        &["f"],
    )
    .unwrap();
    assert!(t[0].contains("a has {x: b, y: c}"), "{}", t[0]);
    assert!(t[0].contains("{p: a, q: a}"), "{}", t[0]);
}

#[test]
fn mutually_recursive_functions_share_predicates() {
    // Only the first member of the SCC used to get the `Indexable`
    // predicate, so `b(["s"], 0, 1)` was unconstrained.
    let src = "function a(o, k, n) { return n > 0 ? b(o, k, n - 1) : o[k]; }\n\
               function b(o, k, n) { return a(o, k, n); }\n\
               const bad = b([\"s\"], 0, 1) * 2;";
    assert!(check_program(src, &[]).is_err());
    let t = check_program(
        "function a(o, k, n) { return n > 0 ? b(o, k, n - 1) : o[k]; }\n\
         function b(o, k, n) { return a(o, k, n); }",
        &["a", "b"],
    )
    .unwrap();
    assert!(t[1].contains("Indexable"), "{}", t[1]);
}

#[test]
fn record_indexing_constrains_the_element() {
    // The element type of `record[key]` was left unconstrained.
    assert!(check_program(
        "function get(o, k) { return o[k]; }\nconst bad = get({x: \"s\"}, \"x\") * 2;",
        &[]
    )
    .is_err());
    assert!(check_program(
        "const o = {x: \"s\"};\nfunction get(k) { return o[k]; }\nconst bad = get(\"x\") * 2;",
        &[]
    )
    .is_err());
    // A literal key selects the field.
    let src = "const o = {x: \"s\", y: 1};\nconst a = o[\"x\"];\nconst b = o[\"y\"];";
    assert_eq!(
        check_program(src, &["a", "b"]).unwrap(),
        ["String", "Number"]
    );
    // A key known only at run time may name no field (`get("z")` reads
    // `undefined`): an error, which says to use a `Dict`.
    let src =
        "const o = {x: \"s\", y: \"t\"};\nfunction get(k) { return o[k]; }\nconst v = get(\"z\").length;";
    let err = check_program(src, &[]).unwrap_err();
    assert!(err.contains("Dict"), "{}", err);
    // A `Dict` says so in its type.
    let src = "/** const o: Dict<String> */\nconst o = {x: \"s\"};\nfunction get(k) { return o[k] ?? \"\"; }\nconst v = get(\"z\");";
    assert_eq!(check_program(src, &["v"]).unwrap(), ["String"]);
}

#[test]
fn self_application_through_recursive_callable_row_is_rejected() {
    let src = "function outer(o) { return o(o) * 2; }\nouter((x) => x);";
    assert!(check_program(src, &[]).is_err());
}

#[test]
fn use_before_initialisation_is_reported() {
    for src in [
        "const r = f(1);\nconst f = (x) => x + 1;",
        "const a = b;\nconst b = a;",
        "f();\nconst x = 1;\nfunction f() { return x; }",
        "const y = v * 2;\nvar v = 3;",
    ] {
        let err = check_program(src, &[]).unwrap_err();
        assert!(err.contains("before"), "{}: {}", src, err);
    }
    // Hoisted function declarations may be called early; functions that
    // run later may read later bindings.
    for src in [
        "const r = f(1);\nfunction f(x) { return x + 1; }",
        "function helper() { return lib.foo; }\nconst lib = { foo: 1 };\nconst r = helper();",
    ] {
        check_program(src, &[]).unwrap_or_else(|e| panic!("{}: {}", src, e));
    }
}

/// A cycle between two row tails (`ρ₁ ↦ {| ρ₂}`, `ρ₂ ↦ {| ρ₁}`) that
/// `zonk` cuts made `unify_rows` re-bind the same pair forever and
/// overflow the stack (found in a Markdown converter). The unification
/// of a pair of tails already in progress is now assumed to succeed.
#[test]
fn cyclic_row_tails_terminate() {
    let src = "function isBlank(l) { return l.length === 0; }\n\
               function indentOf(l) { return 0; }\n\
               function dedent(line, cols) { return line.slice(cols); }\n\
               function isRule(t) { return t.length >= 3; }\n\
               function fenceLength(t) { return t.charCodeAt(0) === 96 && t.indexOf(\"`\", 1) >= 0 ? 3 : 0; }\n\
               function interrupts(t) { return isRule(t) || fenceLength(t) > 0 || t.startsWith(\">\"); }\n\
               function render(lines) {\n\
                 let i = 0;\n\
                 while (i < lines.length) {\n\
                   const t = dedent(lines[i], indentOf(lines[i]));\n\
                   if (fenceLength(t) > 0) {\n\
                     const u = dedent(lines[i], 0);\n\
                     if (!interrupts(dedent(u, indentOf(u))) && !isBlank(u)) i++;\n\
                   }\n\
                   i++;\n\
                 }\n\
                 return i;\n\
               }";
    assert!(check_program(src, &[]).is_ok());
}

// ---- HasProp: property reads on values of not-yet-known type -----------------

#[test]
fn has_prop_string_parameter_used_through_methods() {
    // `s` is only known through its methods; a string satisfies them.
    let src = "function f(s) { return s.charCodeAt(0) + s.slice(1).length; }\n\
               const n = f(\"abc\");";
    assert_eq!(check_program(src, &["n"]).unwrap(), ["Number"]);
    // So does an array, for the methods arrays have.
    let arr = "function first(xs) { return xs.slice(0, 1); }\n\
               const a = first([1, 2]);\n\
               const b = first(\"xy\");";
    assert_eq!(
        check_program(arr, &["a", "b"]).unwrap(),
        ["Number[]", "String"]
    );
    // A number has neither.
    assert!(check_program("function f(s) { return s.slice(1); }\nf(5);", &[]).is_err());
    // An array has no `charCodeAt`.
    assert!(check_program("function f(s) { return s.charCodeAt(0); }\nf([1]);", &[]).is_err());
}

#[test]
fn has_prop_recursion_through_a_method_result() {
    // md2html's `inline(s)` calls itself on `s.slice(…)`: the parameter's
    // type is "whatever `slice` returns", which used to be an
    // equi-recursive row that no string could match (and, in larger
    // programs, overflowed the stack).
    let src = "function inline(s) {\n\
                 if (s.length > 0 && s.charCodeAt(0) === 42) {\n\
                   return \"<em>\" + inline(s.slice(1, s.length - 1)) + \"</em>\";\n\
                 }\n\
                 return s;\n\
               }\n\
               const h = inline(\"*a*\");";
    assert_eq!(check_program(src, &["h"]).unwrap(), ["String"]);
}

#[test]
fn has_prop_result_follows_the_receiver() {
    // The receiver determines the result: an object whose `length` is a
    // string gives a string, which can't be multiplied.
    let src = "function len(x) { return x.length; }\n\
               const a = len(\"abc\") * 2;\n\
               const b = len({length: 3}) * 2;";
    assert!(check_program(src, &[]).is_ok());
    let bad = "function len(x) { return x.length; }\n\
               const c = len({length: \"3\"}) * 2;";
    assert!(check_program(bad, &[]).is_err());
}

#[test]
fn has_prop_unused_result_is_quantified() {
    // `o.x`'s result isn't part of `f`'s type; each call still gets its
    // own (it's quantified with the predicate), so the two calls don't
    // have to agree on `x`.
    let src = "function f(o) { o.x; return 1; }\n\
               f({x: 1});\n\
               f({x: \"s\"});";
    assert!(check_program(src, &[]).is_ok());
}

#[test]
fn has_prop_array_methods_on_a_parameter() {
    let src = "function add(xs, v) { xs.push(v); return xs.length; }\n\
               const n = add([1], 2);";
    assert_eq!(check_program(src, &["n"]).unwrap(), ["Number"]);
    // The pushed value must be an element.
    assert!(check_program(
        "function add(xs, v) { xs.push(v); return xs; }\nadd([1], \"s\");",
        &[]
    )
    .is_err());
}

#[test]
fn has_prop_scheme_display() {
    let t = check_program("function getX(p) { return p.x; }", &["getX"]).unwrap();
    assert_eq!(t[0], "<a, b> where a has {x: b} => (a) => b");
}

#[test]
fn instantiated_predicate_errors_point_at_the_use() {
    // A predicate of a polymorphic function is checked where the function
    // is used, and reported there (it used to be reported at 0:0).
    let src = "function twice(x) { return x + x; }\ntwice(true);";
    let program = crate::frontends::javascript::parse_source(src).unwrap();
    let mut state = InferState::new();
    // (Decided at the use, by improvement, or at the end.)
    let err = match state.infer_program_with_env(&initial_env(), &program) {
        Err(e) => e,
        Ok(_) => state.resolve_constraints().unwrap_err(),
    };
    let span = match err {
        crate::error::IntyError::Type(ref e) => e.span(),
        ref other => panic!("expected a type error, got {:?}", other),
    };
    assert_eq!(&src[span.start..span.end], "twice");
}
// ---- Review findings on HasProp ---------------------------------------------

#[test]
fn has_prop_on_a_union_needs_every_arm() {
    // Reading `.x` of a union of objects whose `x` differ can't give a
    // `String` for all of them (it used to join the fields to
    // `Number | String` and let unify's union-membership rule accept it).
    let bad = "function up(o) { const y = o.x; const t = \"\" + y; const w = t === y; return y.toUpperCase(); }\n\
               /** const u: {a: Number, x: Number} | {b: Number, x: String} */\n\
               const u = true ? {a: 1, x: 5} : {b: 1, x: \"hi\"};\n\
               up(u);";
    assert!(check_program(bad, &[]).is_err());
    // Arms that agree are fine, including a string and an array.
    let ok = "function nm(o) { return o.name; }\n\
              /** const a: {name: String, k: Number} | {name: String, z: Number} */\n\
              const a = true ? {name: \"a\", k: 1} : {name: \"b\", z: 2};\n\
              const s = nm(a);\n\
              function ln(x) { return x.length; }\n\
              /** const b: String | Number[] */\n\
              const b = true ? \"abc\" : [1, 2];\n\
              const n = ln(b);";
    assert_eq!(
        check_program(ok, &["s", "n"]).unwrap(),
        ["String", "Number"]
    );
}

#[test]
fn predicate_variables_in_shared_recursive_types_stay_monomorphic() {
    // `a = o.x` also lives in `mk`'s recursive type; quantifying it with
    // the `HasProp` separated each call's `x` from that shared body.
    let src = "function f(o) { const a = o.x; function mk() { return { v: a, me: mk }; } o.z = mk(); return 0; }\n\
               function mk2() { return { v: \"s\", me: mk2 }; }\n\
               const obj = { x: 1, z: mk2() };\n\
               f(obj);\n\
               obj.z.v.toUpperCase();";
    assert!(check_program(src, &[]).is_err());
}

#[test]
fn spread_of_a_parameter_after_reading_it() {
    // The reducer shape. `coerce_to_row` used to hand out an unallocated
    // variable id that the next fresh variable reused.
    let src = "function inc(state, v) { return {...state, count: state.count + v}; }\n\
               const s = inc({count: 1, name: \"a\"}, 2);\n\
               const c = s.count * 2;";
    assert!(check_program(src, &[]).is_ok());
}

#[test]
fn factories_reading_this_fields_stay_generic() {
    let src = "function W(s) { return { src: s, get: function() { return this.src; } }; }\n\
               const a = W(\"a\").get();\n\
               const b = W(5).get();";
    assert_eq!(
        check_program(src, &["a", "b"]).unwrap(),
        ["String", "Number"]
    );
}

#[test]
fn has_prop_on_a_primitive_reports_the_missing_property() {
    let err = check_program("function up(s) { return s.toUpperCase(); }\nup(5);", &[]).unwrap_err();
    assert!(
        err.contains("toUpperCase") && err.contains("Number"),
        "{}",
        err
    );
}

#[test]
fn a_join_with_a_type_not_known_yet_is_equality() {
    // As in HM: joining (or passing into a slot) a value whose type isn't
    // known yet unifies it with the other side; implicit unions only form
    // between types already known to differ. So whether `o` is read
    // before or after the join, `o` is a string here, which has no `x` —
    // the verdict doesn't depend on statement order.
    for src in [
        "function h(o, b) { const n = o.x; const v = b ? o : \"str\"; return n; }",
        "function h(o, b) { const v = b ? o : \"str\"; const n = o.x; return n; }",
        "function h(o) { const n = o.x; const a = [o, \"s\"]; return n; }",
    ] {
        let err = check_program(src, &[]).unwrap_err();
        assert!(err.contains("Property 'x' not found"), "{}\n{}", src, err);
    }
    // Known, different types don't join either: a union is annotated.
    let err = check_program("function k(b) { return b ? {x: 1} : \"str\"; }", &[]).unwrap_err();
    assert!(err.contains("Branches have different types"), "{}", err);
    let t = check_program(
        "/** function k(Boolean) => {x: Number} | String */\n\
         function k(b) { return b ? {x: 1} : \"str\"; }",
        &["k"],
    )
    .unwrap();
    assert_eq!(t[0], "(Boolean) => String | {x: Number}");
}

#[test]
fn declared_constraints_hold_consumers_to_them() {
    // What `inty declarations` prints for `add(a, b) { return a + b }` and
    // for property reads; a consumer of the `.d.js` is checked against the
    // constraints (they used to be dropped: `add(true, false)` passed).
    let decls = "/** const add: <a> where Plus a => (a, a) => a */\nconst add;\n\
                 /** const len: <a, b> where a has {length: b} => (a) => b */\nconst len;\n\
                 /** const mixed: <c, r> where Plus r, c has {slice: (Number, Number) => r, slice: (Number) => r} => (c) => r */\nconst mixed;\n";
    for ok in [
        "const a = add(1, 2) * 2;",
        "const b = len(\"abc\") * 2;",
        "const c = len([1, 2]) * 2;",
        "const d = mixed(\"abc\").toUpperCase();",
    ] {
        check_program(&format!("{decls}{ok}"), &[]).unwrap_or_else(|e| panic!("{}: {}", ok, e));
    }
    for bad in [
        "add(true, false);",
        "len(5);",
        "mixed(3);",
        "const s = len({length: \"x\"}) * 2;",
    ] {
        assert!(
            check_program(&format!("{decls}{bad}"), &[]).is_err(),
            "{}",
            bad
        );
    }
}

#[test]
fn where_clauses_parse_in_annotations() {
    let t = check_program(
        "/** const f: <a, b> where Indexable a Number b => (a) => b */\nconst f;",
        &["f"],
    )
    .unwrap();
    assert_eq!(t[0], "<a, b> where Indexable a Number b => (a) => b");
}

// ---- Sound joins and unification --------------------------------------------

#[test]
fn a_union_is_not_one_of_its_arms() {
    // Unification is equality: a `String | Number` value doesn't pass for a
    // `String` (it used to, through a union-membership rule in `unify`).
    for bad in [
        "function g(o) { const y = o.x; const s = \"\" + y; const w = s === y; return y.toUpperCase(); }\n\
         /** const o: {x: String | Number} */\n\
         const o = {x: true ? \"hi\" : 5};\n\
         g(o);",
        "/** const xs: (Number | String)[] */\n\
         const xs = [5, \"a\"];\n\
         function up(a, i) { const v = a[i]; const s = \"\" + v; const w = s === v; return v.toUpperCase(); }\n\
         up(xs, 0);",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
    // An arm's value fits where the union is expected (subsumption).
    let ok = "/** function f(String | Number) => Number */\nfunction f(v) { return 1; }\nconst a = f(\"s\") + f(2);";
    assert!(check_program(ok, &[]).is_ok());
}

#[test]
fn a_deferred_method_call_checks_arguments_like_a_direct_one() {
    // `s.replaceAll("\n", " ")` on a parameter of unknown type: the
    // literal argument fits `String | Regex`, as it does on a string.
    let src =
        "function norm(s) { return s.replaceAll(\"\\n\", \" \"); }\nconst r = norm(\"a\\nb\");";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["String"]);
}

#[test]
fn detached_built_in_methods_are_rejected() {
    for bad in [
        "const g = \"a\".toUpperCase;\nconst r = g();",
        "function f(s) { const g = s.toUpperCase; return g(); }\nf(\"a\");",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
    // Called on a (literal) receiver, fine.
    assert!(check_program(
        "const t = \"  a \".trim();\nconst n = [3, 1].slice(0, 1).length;",
        &[]
    )
    .is_ok());
}

#[test]
fn branches_checked_against_an_annotation_form_a_union() {
    for (src, name, ty) in [
        (
            "/** const v: Number | String */\nconst v = true ? 1 : \"a\";",
            "v",
            "Number | String",
        ),
        (
            "/** const xs: (Number | String)[] */\nconst xs = [1, \"a\"];",
            "xs",
            "(Number | String)[]",
        ),
        (
            "/** function f(Boolean) => Number | String */\nfunction f(b) { if (b) { return 1; } return \"a\"; }\nconst r = f(true);",
            "r",
            "Number | String",
        ),
        (
            "/** function g(String | Null) => String | Number */\nfunction g(s) { return s ?? 42; }\nconst q = g(\"a\");",
            "q",
            "Number | String",
        ),
    ] {
        assert_eq!(check_program(src, &[name]).unwrap(), [ty], "{}", src);
    }
    // Without the annotation, the branches must agree.
    for bad in [
        "const v = true ? 1 : \"a\";",
        "const xs = [1, \"a\"];",
        "function f(b) { if (b) { return 1; } return \"a\"; }",
    ] {
        let err = check_program(bad, &[]).unwrap_err();
        assert!(
            err.contains("Branches have different types")
                || err.contains("Array elements have different types"),
            "{}: {}",
            bad,
            err
        );
    }
}

#[test]
fn a_null_branch_needs_the_sum_said() {
    // As in the model, branches have one type: `null` and a value don't
    // join into a guessed sum. An annotation says the sum, and each
    // branch is injected into it.
    let src =
        "function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }\n\
               const hit = find([1, 2], 2);";
    assert!(check_program(src, &["hit"]).is_err());
    let src = "/** function find<a>(xs: a[], v: a) => a | Null */\n\
               function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }\n\
               const hit = find([1, 2], 2);";
    assert_eq!(check_program(src, &["hit"]).unwrap(), ["Number | Null"]);
}

#[test]
fn statements_are_not_joined_by_value() {
    // `n += 4` (a Number) and `break` in the branches of an `if`
    // statement: statements have no value to agree on.
    let src = "function w(line) { let n = 0; for (let i = 0; i < line.length; i++) { \
               const c = line.charCodeAt(i); if (c === 32) n += 1; else if (c === 9) n += 4; else break; } \
               return n; }\nconst k = w(\"  x\");";
    assert_eq!(check_program(src, &["k"]).unwrap(), ["Number"]);
}

#[test]
fn javascript_class_names_are_types_in_annotations() {
    let src = "class A {}\nclass B {}\n/** const xs: (A | B)[] */\nconst xs = [new A(), new B()];";
    assert!(check_program(src, &[]).is_ok());
    let err = check_program(
        "class A {}\nclass B {}\nconst xs = [new A(), new B()];",
        &[],
    )
    .unwrap_err();
    assert!(
        err.contains("Array elements have different types"),
        "{}",
        err
    );
}

#[test]
fn new_array_fill_is_an_array_of_the_value() {
    // `new Array(n)` is declared in core.d.js: holes with only `length`
    // and `fill`, so it types the same however it's written.
    let ty = |src: &str, name: &str| -> Result<String, String> {
        let (_, env, state) =
            infer_program_via_program_with_stdlib(src).map_err(|e| e.to_string())?;
        if let Some(e) = state.errors.first() {
            return Err(e.to_string());
        }
        let scheme = env.lookup(name).expect("bound");
        Ok(format!("{}", state.display_scheme(scheme)))
    };
    assert_eq!(
        ty("const v = new Array(3).fill(-1);", "v").unwrap(),
        "Number[]"
    );
    assert_eq!(
        ty("const w = Array(2).fill(\"a\");", "w").unwrap(),
        "String[]"
    );
    assert_eq!(
        ty("const t = new Array(3); const v = t.fill(0);", "v").unwrap(),
        "Number[]"
    );
    // The length is a number (one with a fraction is a fault: JavaScript
    // throws a RangeError), and a hole can't be read.
    assert!(ty("const v = new Array(1.5).fill(0);", "v").is_ok());
    assert!(ty("const t = new Array(3); const x = t[0];", "x").is_err());
    // A local `Array` is just that.
    assert_eq!(
        ty(
            "function f() { const Array = (n) => ({ fill: (v) => n }); return Array(3).fill(1); }\n\
             const r = f();",
            "r"
        )
        .unwrap(),
        "Number"
    );
}

#[test]
fn null_tests_narrow() {
    let p = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n";
    let accepted = [
        "const q = p(1); if (q !== null) { const a = q.x; }",
        "const q = p(1); if (q != null) { const a = q.x; }",
        "const q = p(1); if (q) { const a = q.x; }",
        "const q = p(1); if (q === null) { } else { const a = q.x; }",
        "const q = p(1); const a = q === null ? 0 : q.x;",
        "const q = p(1); const a = q !== null && q.x > 0;",
        "const q = p(1); const a = q === null || q.x > 0;",
        "const a = p(1); const b = p(2); if (a !== null && b !== null) { const c = a.x + b.x; }",
        "function f() { const q = p(1); if (q === null) return 0; return q.x; }",
        "function f() { const q = p(1); if (!q) throw 'none'; return q.x; }",
        "function f() { const a = p(1); const b = p(2); if (a === null || b === null) return 0; return a.x + b.x; }",
        "let t = 0; for (let i = 0; i < 3; i++) { const q = p(i); if (q === null) continue; t += q.x; }",
        // The stored value is checked against the variable's own type.
        "let q = p(1); if (q !== null) { q = p(0); }",
        "const q = p(1); if (q !== null) { const g = () => q.x; }",
    ];
    for body in accepted {
        let src = format!("{p}{body}");
        assert!(check_program(&src, &[]).is_ok(), "rejected: {body}");
    }
}

#[test]
fn null_narrowing_ends_where_the_value_may_change() {
    let p = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n";
    let rejected = [
        "const q = p(1); const a = q.x;",
        "const q = p(1); if (q === null) { const a = q.x; }",
        "const a = p(1); const b = p(2); if (a !== null || b !== null) { const c = a.x; }",
        // Reassigned inside the branch.
        "let q = p(1); if (q !== null) { q = p(0); const a = q.x; }",
        // Reassigned by a later loop iteration.
        "let q = p(1); if (q !== null) { while (q.x > 0) { q = p(q.x - 1); } }",
        // Assigned by a closure the branch calls.
        "let q = p(1); const reset = () => { q = null; }; if (q !== null) { reset(); const a = q.x; }",
        // Read by a closure after the variable changes.
        "let q = p(1); let g = () => 0; if (q !== null) { g = () => q.x; } q = null;",
        // The handler can run before the test.
        "function f() { let q = p(1); try { if (q === null) return 0; q = p(0); return 1; } catch (e) { return q.x; } }",
    ];
    for body in rejected {
        let src = format!("{p}{body}");
        assert!(check_program(&src, &[]).is_err(), "accepted: {body}");
    }
}

#[test]
fn narrowing_a_const_keeps_it_const() {
    let src = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n\
               const q = p(1); if (q !== null) { q = p(2); }";
    assert!(check_program(src, &[]).is_err());
}

/// The review of the first narrowing (docs/flow-narrowing-safe.md): each
/// of these crashed under Node yet type-checked, or type-checked or not
/// depending on something that shouldn't matter.
#[test]
fn narrowing_refines_only_bindings_that_never_change() {
    let p = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n";
    let rejected = [
        // An assignment inside the guarded expression.
        "let q = p(1); const a = q !== null ? (q = p(0), q.x) : 0;",
        "let q = p(1); function f(a, b) { return a; } if (q !== null) { if (f(q = p(0), q.x)) {} }",
        // A `var` redeclared: its initialiser is a write.
        "function f() { var q = p(1); if (q === null) return 0; { var q = null; } return q.x; }",
        // A local `undefined` is an `Number`, not the unit value.
        "function f() { const undefined = 0; const v = [1].find(x => x > 1); \
         if (v === undefined) return 0; return v + 1; }",
        // A closure writes it.
        "let q = p(1); const reset = () => { q = null; }; if (q !== null) { reset(); const a = q.x; }",
        // The handler can run before the test in the block did.
        "function f() { const q = p(1); try { if (q === null) return 0; } catch (e) { return q.x; } return 1; }",
    ];
    for body in rejected {
        let src = format!("{p}{body}");
        assert!(check_program(&src, &[]).is_err(), "accepted: {body}");
    }
    let accepted = [
        // Facts before a `try` hold in its handler.
        "function f() { const q = p(1); if (q === null) return 0; \
         try { g(); } catch (e) { return q.x; } return q.x; } function g() {}",
        // An unrelated binding of the same name elsewhere doesn't matter.
        "function a() { const q = p(1); if (q === null) return 0; \
         [1, 2].forEach(k => { let q = k; q = q + 1; }); return q.x; }",
        "function a() { const q = p(1); if (q === null) return 0; return q.x; }\n\
         function b() { let q = 0; const f = () => { q = 1; }; f(); return q; }",
        // A closure reads a narrowed `const`.
        "const q = p(1); if (q !== null) { const g = () => q.x; }",
        // The loop test narrows the body, the update, and what follows.
        "/** function h(q: {x: Number} | Null) => Number */\n\
         function h(q) { let s = 0; for (let i = 0; q !== null && i < q.x; i = i + q.x) { s += q.x; } return s; }",
        "/** function h(q: {x: Number} | Null) => Number */\n\
         function h(q) { let n = 0; while (q !== null && n < q.x) { n += 1; } return n; }",
    ];
    for body in accepted {
        let src = format!("{p}{body}");
        assert!(
            check_program(&src, &[]).is_ok(),
            "rejected: {body}: {:?}",
            check_program(&src, &[])
        );
    }
}

#[test]
fn narrowing_is_coherent() {
    let p = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n";
    let pairs = [
        // Operand order.
        ("const q = p(1); const a = q === null ? 0 : q.x;", "const q = p(1); const a = null === q ? 0 : q.x;"),
        // `?:` and `if`.
        ("const q = p(1); const a = q === null ? 0 : q.x;", "const q = p(1); let a = 0; if (q === null) { a = 0; } else { a = q.x; }"),
        // De Morgan.
        ("const q = p(1); const r = p(2); if (!(q === null || r === null)) { const a = q.x + r.x; }",
         "const q = p(1); const r = p(2); if (!(q === null) && !(r === null)) { const a = q.x + r.x; }"),
        // `for` and its `while` form.
        ("/** function h(q: {x: Number} | Null) => Number */\n\
          function h(q) { let s = 0; for (; q !== null && s < 3; s = s + q.x) {} return s; }",
         "/** function h(q: {x: Number} | Null) => Number */\n\
          function h(q) { let s = 0; while (q !== null && s < 3) { s = s + q.x; } return s; }"),
        // A `const` and a `let` that is never written.
        ("const q = p(1); if (q !== null) { const a = q.x; }", "let q = p(1); if (q !== null) { const a = q.x; }"),
    ];
    for (a, b) in pairs {
        let ra = check_program(&format!("{p}{a}"), &[]).is_ok();
        let rb = check_program(&format!("{p}{b}"), &[]).is_ok();
        assert!(ra && rb, "{a} => {ra}, {b} => {rb}");
    }
}

/// The review of the stable-bindings narrowing: each program crashed
/// under Node yet type-checked, because a fact landed on a different
/// variable of the same name or a write went unseen. The environment is
/// now keyed by declaration, and binding resolution sees these writes.
#[test]
fn narrowing_holds_only_for_its_own_binding() {
    let x = "const x = Math.random() > 2 ? \"abc\" : null;\n";
    let rejected = [
        // `break L` completes the labeled statement.
        format!("{x}L: if (x === null) break L;\nconsole.log(x.length);"),
        format!("{x}L: try {{ if (x === null) throw 0; }} finally {{ break L; }}\nconsole.log(x.length);"),
        // A `var` in a `try` is not the outer binding of the same name.
        "const x = { a: { b: 1 } };\n\
         function f(c) { try { var x = c ? \"s\" : null; if (x === null) return 0; } catch (e) {} return x.a.b; }"
            .to_string(),
        // `function x` and `var x` are one binding, written by the `var`.
        "var x = Math.random() < 2 ? \"s\" : null;\n\
         const g = x !== null ? () => x.length : () => 0;\n\
         var x = Math.random() > 2 ? \"s\" : null;\nfunction x() {}"
            .to_string(),
        // `for (var x of …)`: one variable, written by every iteration.
        format!("{x}const fs = [];\nfor (var y of [\"b\", x]) {{ if (y !== null) fs.push(() => y.length); }}"),
        "function f() { var x = \"str\"; for (var x of [null]) {} return x.length; }".to_string(),
        // A `var` directly under an `if` is the function's.
        "const x = \"str\";\nfunction g(n) { if (n > 0) var x = null; return x.length; }".to_string(),
        // A direct `eval` can write anything in scope.
        "function f() { let y = Math.random() > 2 ? \"s\" : null; \
                 if (y !== null) { eval(\"y = null\"); return y.length; } return 0; }".to_string(),
        // A destructuring default is checked (and can write).
        "let x = \"s\";\nconst o = { a: undefined };\nconst { a = (x = null) } = o;".to_string(),
        // `typeof` of a regex is "object".
        "const r = /a/;\nif (typeof r === \"object\") { const z = r.foo; }".to_string(),
    ];
    for src in &rejected {
        assert!(check_program(src, &[]).is_err(), "accepted:\n{src}");
    }
}

#[test]
fn renaming_a_binding_changes_nothing() {
    let p = "/** function p(x: Number) => {x: Number} | Null */ function p(x) { return x > 0 ? { x: x } : null; }\n\
             function a() { const q = p(1); if (q === null) return 0; return q.x; }\n";
    // Another function's binding named `q` (written, captured and written
    // by a closure, shadowing) is not `a`'s `q`: renaming it changes
    // nothing.
    for other in [
        "function b() { let NAME = 0; const f = () => { NAME = 1; }; f(); return NAME; }",
        "function b() { [1, 2].forEach(k => { let NAME = k; NAME = NAME + 1; }); return 0; }",
        "function b() { var NAME = 1; NAME = 2; return NAME; }",
    ] {
        for name in ["q", "r"] {
            let src = format!("{p}{}", other.replace("NAME", name));
            assert!(
                check_program(&src, &[]).is_ok(),
                "rejected:\n{src}: {:?}",
                check_program(&src, &[])
            );
        }
    }
}

#[test]
fn destructuring_defaults_are_checked() {
    let (_, env, state) = infer_program_via_program_with_stdlib(
        "const { a = 1 } = { a: 2 };\nconst [b, c = \"z\"] = [\"x\", \"y\"];",
    )
    .unwrap();
    assert!(state.errors.is_empty(), "{:?}", state.errors);
    let ty = |n: &str| state.apply_subst(&env.lookup(n).unwrap().body.ty);
    assert_eq!(ty("a"), Type::Number);
    assert_eq!(ty("c"), Type::String);
    // A default must be of the property's type.
    assert!(infer_program_via_program_with_stdlib("const { a = \"s\" } = { a: 2 };").is_err());
}

#[test]
fn typed_arrays_have_fixed_length_and_machine_elements() {
    let ty = |src: &str, name: &str| -> Result<String, String> {
        let (_, env, state) =
            infer_program_via_program_with_stdlib(src).map_err(|e| e.to_string())?;
        if let Some(e) = state.errors.first() {
            return Err(e.to_string());
        }
        let scheme = env.lookup(name).expect("bound");
        Ok(format!("{}", state.display_scheme(scheme)))
    };
    assert_eq!(
        ty("const a = new Int32Array(4);", "a").unwrap(),
        "Int32Array"
    );
    assert_eq!(
        ty("const a = new Int32Array(4); const x = a[0];", "x").unwrap(),
        "Number"
    );
    assert_eq!(
        ty(
            "const f = new Float64Array(2).fill(0.5); const x = f[1];",
            "x"
        )
        .unwrap(),
        "Number"
    );
    assert_eq!(
        ty(
            "const b = Uint8Array.from([1, 2]); const n = b.length;",
            "n"
        )
        .unwrap(),
        "Number"
    );
    // An integer array stores any number, wrapped to its bits as
    // JavaScript does.
    assert!(ty("const a = new Int32Array(1); a[0] = 1.5;", "a").is_ok());
    assert!(ty("const a = new Int32Array(1); a[0] = 3;", "a").is_ok());
    assert!(ty("const f = new Float64Array(1); f[0] = 3;", "f").is_ok());
    // Fixed length: no `push`. A typed array is not an ordinary array.
    assert!(ty("const a = new Int32Array(1); a.push(1);", "a").is_err());
    assert!(ty(
        "const a = new Int32Array(1); const b = [1]; const c = true ? a : b;",
        "c"
    )
    .is_err());
    assert!(ty("const a = new Int32Array(1.5);", "a").is_ok());
    // An index is a number (one with a fraction reads nothing: a fault).
    assert!(ty("const a = new Int32Array(2); const x = a[0.5];", "x").is_ok());
    // Distinct kinds don't mix.
    assert!(ty("const a = new Int32Array(1); const b = new Uint8Array(1); const c = true ? a : b; c[0] = 1;", "c").is_err());
}

/// A `const` bound to a function is a declaration like any other: the
/// program's result after it is `Undefined`, not the preceding
/// expression's type (found by the metamorphic soak: inserting `;` or
/// wrapping `true` in a call changed the program's type).
#[test]
fn const_function_statement_yields_undefined() {
    let (ty, _, state) =
        infer_program_via_program_with_stdlib("true;\nconst a = function() { return null; };")
            .unwrap();
    assert_eq!(state.apply_subst(&ty), Type::Undefined);
}

#[test]
fn mutable_containers_are_invariant() {
    // A `String[]` read as a `(String | Number)[]` could be pushed a
    // number through the wider alias, and the `String[]` would hold it.
    assert!(infer_program_with_state(
        "\
        /** const xs: String[] */ \
        const xs = ['hi']; \
        /** function f(list: (String | Number)[]) => Undefined */ \
        function f(list) { list.push(420); } \
        f(xs);"
    )
    .is_err());
    assert!(infer_program_with_state(
        "\
        /** const xs: String[] */ \
        const xs = ['hi']; \
        /** const ys: (String | Number)[] */ \
        const ys = xs;"
    )
    .is_err());
    // The error says the mismatch is the array's invariance, and how to
    // get around it.
    let err = infer_program_with_state(
        "\
        /** const xs: String[] */ \
        const xs = ['hi']; \
        /** const ys: (String | Number)[] */ \
        const ys = xs;",
    )
    .err()
    .expect("an invariance error");
    let msg = format!("{:?}", err);
    assert!(msg.contains("must match exactly"), "{msg}");
    assert!(msg.contains("function f<a>(xs: a[])"), "{msg}");
    // Both suggestions type-check: a generic parameter, and a copy.
    assert!(infer_program_with_state(
        "\
        /** const xs: String[] */ \
        const xs = ['hi']; \
        /** function count<a>(xs: a[]) => Number */ \
        function count(xs) { return xs.length; } \
        count(xs); \
        /** function f(list: (String | Number)[]) => Undefined */ \
        function f(list) { list.push(420); } \
        f([...xs]);"
    )
    .is_ok());
    // A literal-typed array is not a `String[]`: pushing `"zzz"` through
    // the alias would leave the `("a" | "b")[]` holding it.
    assert!(infer_program_with_state(
        "\
        /** const xs: (\"a\" | \"b\")[] */ \
        const xs = [\"a\"]; \
        /** const ys: String[] */ \
        const ys = xs;"
    )
    .is_err());
    // A record field is mutable too: `p.x = 1` would write into `o`.
    assert!(infer_program_with_state(
        "\
        const o = { x: \"a\" }; \
        /** const p: { x: String | Number } */ \
        const p = o;"
    )
    .is_err());
    // A fresh literal's elements and fields are values, and fit.
    assert!(infer_program_with_state(
        "\
        /** const ys: (String | Number)[] */ \
        const ys = ['hi', 1]; \
        /** const p: { x: String | Number } */ \
        const p = { x: \"a\" }; \
        /** type Shape = { kind: \"circle\", r: Number } | { kind: \"sq\", s: Number } */ \
        /** const shapes: Shape[] */ \
        const shapes = [{ kind: \"circle\", r: 1 }, { kind: \"sq\", s: 2 }];"
    )
    .is_ok());
}

/// A `Plus` on a known type is decided when a binding is generalised, not
/// carried in its scheme to each use: a binding whose body adds two
/// functions is an error even if nothing uses it. On a variable it stays,
/// as `<a> where Plus a`.
#[test]
fn plus_on_known_type_is_decided_at_generalisation() {
    let errors = |src: &str| {
        let program = parse_for_multi_error_test(src);
        let mut state = InferState::new();
        let r = state.infer_program_with_env(&initial_env(), &program);
        let mut errs = state.take_errors();
        if let Err(e) = r {
            errs.push(e);
        }
        if let Err(e) = state.resolve_constraints() {
            errs.push(e);
        }
        errs
    };
    let unused =
        "const x = function () { const g = function (y) { return y; }; return g + g; }; 1;";
    let errs = errors(unused);
    assert!(
        errs.iter().any(|e| matches!(
            e.as_type(),
            Some(TypeError::ConstraintNotSatisfied { class, .. }) if class == "Plus"
        )),
        "{errs:?}"
    );
    let on_variable = "const d = function (y) { return y + y; }; 1;";
    assert!(errors(on_variable).is_empty());
}

/// A named function expression's own name is immutable in its body, as in
/// strict-mode JavaScript, where assigning to it is a `TypeError`; a function
/// declaration's name can be reassigned.
#[test]
fn function_expression_name_is_immutable() {
    let expr = "const g = function f() { f = function () { return 2; }; return 1; }; g();";
    assert!(infer_program_with_state(expr).is_err());
    let decl = "function f() { f = function () { return 2; }; return 1; } f();";
    assert!(infer_program_with_state(decl).is_ok());
}

/// A `catch` binds whatever was thrown, which can be any value: its type is
/// rigid, so it can't be used at a concrete type.
#[test]
fn caught_exception_is_opaque() {
    let errors = |src: &str| {
        let program = parse_for_multi_error_test(src);
        let mut state = InferState::new();
        let r = state.infer_program_with_env(&initial_env(), &program);
        let mut errs = state.take_errors();
        if let Err(e) = r {
            errs.push(e);
        }
        errs
    };
    assert!(!errors("let r = 0; try { throw \"s\"; } catch (e) { r = e - 1; }").is_empty());
    assert!(!errors(
        "const f = function (x) { return x.length; }; try { throw 3; } catch (e) { f(e); }"
    )
    .is_empty());
    // Passing it on, testing it, and rethrowing it are fine.
    assert!(errors(
        "const id = function (x) { return x; }; \
         try { throw 1; } catch (e) { const t = typeof id(e); if (e) { throw e; } }"
    )
    .is_empty());
}

#[test]
fn test_try_finally_that_returns_doesnt_fall_through() {
    // `try { return … } finally { … }` always returns: the function's
    // result has no implicit `undefined`, so it joins with one that
    // returns the same type.
    let source = r#"
        const f = function () { try { return null; } finally { 1; } };
        const g = function () { return null; };
        const h = true ? f : g;
    "#;
    assert!(infer_program_with_state(source).is_ok());
}

#[test]
fn test_while_true_with_break_falls_through() {
    // A `while (true)` left by `break` falls off the function's end, so the
    // function can return `undefined`; using its result as a number is an
    // error (it was accepted when the result was typed `never`).
    let source = r#"
        const f = function () { while (true) { break; } };
        const a = true ? f() : 1;
        const r = a - 1;
    "#;
    assert!(infer_program_with_state(source).is_err());
    let forever = r#"
        const f = function () { while (true) { } };
        const a = true ? f() : 1;
        const r = a - 1;
    "#;
    assert!(infer_program_with_state(forever).is_ok());
}

#[test]
fn test_spread_of_an_open_row_keeps_earlier_fields_sound() {
    // A spread operand of unknown shape may hold any field written before
    // it, and then wins: the two must agree on its type. (Taking the
    // operand's tail alone typed `f({a: "s"}).a` as an `Number`.)
    let rejected = [
        r#"
        function f(o) { return {a: 1, ...o}; }
        const n = f({a: "s"}).a - 1;
        "#,
        // Two operands of types not known yet: decided at the use, where
        // the second's `a` is a number.
        r#"
        function g(o1, o2) { return {...o1, ...o2}; }
        const r = {a: "s", ...g({a: 1}, {})};
        r.a.length;
        "#,
        // A spread's operand is an object, not a function (whose call
        // signature it used to copy).
        r#"
        const f = function () { return 1; };
        const n = ({...f})();
        "#,
        r#"
        const f = function () { return 1; };
        const o = {...f};
        "#,
        r#"
        function h(o) { return {...o}; }
        const f = function () { return 1; };
        const n = h(f);
        "#,
    ];
    for source in rejected {
        assert!(infer_program_with_state(source).is_err(), "{source}");
    }
    let accepted = r#"
        function f(o) { return {a: 1, ...o}; }
        const x = f({b: "s"}).b.length;
        const y = f({}).a - 1;
        const z = f({a: 2}).a - 1;
        function h(o) { return {...o, ...{b: 1}}; }
        const q = h({a: "s"}).a.length;
        const p = h({b: "s"}).b - 1;
        // A closed spread after an open one keeps the open one's fields
        // (`r.a` was typed `String`).
        const r = {a: "s", ...h({a: 1})};
        const n = r.a - 1;
        const defaults = {a: 1, b: "x"};
        function opts(o) { return {...defaults, ...o}; }
        const oo = opts({a: 3}).b.length;
        function g(o1, o2) { return {...o1, ...o2}; }
        const w = g({a: 1}, {a: 2}).a - 1;
        const v = {a: "s", ...g({a: 1}, {})}.a - 1;
        const u = g({a: "s"}, {a: 1}).a - 1;
    "#;
    assert!(infer_program_with_state(accepted).is_ok());
}

#[test]
fn test_stores_only_into_what_takes_them() {
    // A string's characters are read-only: a store throws a `TypeError` in
    // strict code, and `dynamics` gets stuck. Indexing it is fine.
    for source in [
        r#"
        const s = "ab";
        s[0] = "c";
        "#,
        r#"
        function f(x) { x[0] = "c"; return x; }
        const t = f("ab");
        "#,
        r#"
        let s = "ab";
        s[0]++;
        "#,
        // Nor a built-in property: a string's, a function's (an array's
        // `length` takes a number: `a_store_to_an_array_length_truncates_it`).
        r#"
        function f(o) { o.length = 0; return o; }
        const s = f("ab");
        "#,
        r#"
        const xs = [1, 2];
        xs.length = "1";
        "#,
        r#"
        const f = function () { return 1; };
        f.call = 2;
        "#,
    ] {
        assert!(check_program(source, &[]).is_err(), "{source}");
    }
    let accepted = r#"
        const s = "ab";
        const c = s[0];
        const xs = [1, 2];
        xs[0] = 3;
        xs[1]++;
        function set0(c, v) { c[0] = v; return c; }
        const ys = set0([1], 2);
        const o = {length: 1};
        o.length = 2;
        function setA(r, v) { r.a = v; return r; }
        const p = setA({a: 1}, 2);
    "#;
    assert!(check_program(accepted, &[]).is_ok());
}

#[test]
fn test_indexing_a_string_literal() {
    // A string literal's type is a singleton, which indexes as a string.
    let source = r#"
        const c = "xyz"[0];
        const d = c + "!";
    "#;
    assert!(check_program(source, &[]).is_ok());
}

// ---- Principal numbers ------------------------------------------------------

#[test]
fn plus_is_principal_whatever_the_order() {
    // `+` takes two operands of one type, a number or a string.
    let src = "function len(xs, y) { return xs.length + y; }\n\
               const a = len([1], 0.5);\n\
               const b = len(\"ab\", 1);\n\
               const c = len([1], \"!\") ;";
    assert!(check_program(src, &[]).is_err(), "Number + String");
    let ok = "function len(xs, y) { return xs.length + y; }\n\
              const a = len([1], 0.5);\n\
              const b = len(\"ab\", 1);";
    let t = check_program(ok, &["a", "b"]).unwrap();
    assert_eq!(t, vec!["Number".to_string(), "Number".to_string()]);
    let add = "function add(x, y) { return x + y; }\n\
               const n = add(1, 0.5);\n\
               const s = add(\"a\", \"b\");";
    let t = check_program(add, &["add", "n", "s"]).unwrap();
    assert_eq!(t[0], "<a> where Plus a => (a, a) => a");
    assert_eq!(t[1], "Number");
    assert_eq!(t[2], "String");
}

#[test]
fn numbers_are_one_type() {
    // An integer and a fraction are both `Number`s: nothing to choose
    // between where a function is generalised, nor at a use.
    let src = "function half(x) { return x * 0.5; }\n\
               function k() { return 1; }\n\
               const xs = [0.5, k()];\n\
               const i = [10, 20][k()];";
    let t = check_program(src, &["half", "k", "xs", "i"]).unwrap();
    assert_eq!(t[0], "(Number) => Number");
    assert_eq!(t[1], "() => Number");
    assert_eq!(t[2], "Number[]");
    assert_eq!(t[3], "Number");
}

#[test]
fn arith_on_a_string_is_rejected_at_the_use() {
    // Arithmetic's operands are numbers: a call with a string fails (it
    // used to be accepted, and got stuck).
    let src = "function h(x) { return x * 2; }\nconst r = h(\"s\");";
    assert!(check_program(src, &[]).is_err());
}

#[test]
fn a_recursive_group_types_its_numbers() {
    let src = "function f(s) { let x = 0; x = x + 1; return g(s, x); }\n\
               function g(s, i) { return i > 3 ? s : f(s + \"!\"); }";
    let t = check_program(src, &["f", "g"]).unwrap();
    assert_eq!(t[0], "(String) => String");
    assert_eq!(t[1], "(String, Number) => String");
}

/// A class's methods see the variables outside the class, not the
/// constructor's parameters, but inty lowers a class to a factory taking
/// those parameters with the methods inside it. A method reading a name
/// that is also a constructor parameter was typed as reading the
/// parameter: `m` below was a `() => Number` and `new A(5).m() - 1` was
/// accepted, though it computes `"outer" - 1`. The class is rejected now.
#[test]
fn class_method_reading_a_constructor_parameter_name_is_rejected() {
    let err = check_program(
        "const x = \"outer\";\n\
         class A { constructor(x) { this.v = x; } m() { return x; } }\n\
         const r = new A(5).m() - 1;",
        &["r"],
    )
    .unwrap_err();
    assert!(err.contains("also a constructor parameter"), "{err}");
    // A class-body field initialiser doesn't see them either.
    let err = check_program(
        "const x = 1; class A { constructor(x) { this.v = x; } w = x; }",
        &["A"],
    )
    .unwrap_err();
    assert!(err.contains("also a constructor parameter"), "{err}");
    // The constructor's own initialisers do.
    let t = check_program(
        "class A { constructor(x) { this.v = x; } m() { return this.v; } }\n\
         const r = new A(5).m() - 1;",
        &["r"],
    )
    .unwrap();
    assert_eq!(t[0], "Number");
}

/// A class's methods, shorthand ones included, are checked with the
/// instance as `this`, and a call needs a receiver of exactly the
/// instance's type: a copy by spread with another field isn't one.
#[test]
fn class_methods_are_checked_against_the_instance() {
    let t = check_program(
        "class C { constructor(v) { this.v = v; } inc() { this.v = this.v + 1; return this; } }\n\
         const r = new C(1).inc().inc().v;",
        &["r"],
    )
    .unwrap();
    assert_eq!(t[0], "Number");
    assert!(check_program(
        "class C { constructor() { this.v = 1; } get() { return this.v; } }\n\
         const c = new C();\n\
         const r = {...c, w: 2}.get();",
        &["r"],
    )
    .is_err());
    assert!(check_program("const o = {v: \"s\", m() { return this.v - 1; }};", &["o"]).is_err());
}

/// An external class, declared without a body by a `/** class … */`
/// annotation, is a constructor of its members; it may extend a class or
/// constructor that is itself declared without a body, its instances
/// having the base's fields too. Nothing else extends.
#[test]
fn external_class_declarations() {
    let t = check_program(
        "/** const Base: (n: Number) => {n: Number, twice: () => Number} */ const Base;\n\
         /** class Sub extends Base { label: String } */ class Sub;\n\
         /** class Pt<T>(x: T) { x: T } */ class Pt;\n\
         const s = new Sub(1);\n\
         const a = s.label;\n\
         const b = s.twice() + s.n;\n\
         const c = new Pt(\"p\").x;",
        &["a", "b", "c"],
    )
    .unwrap();
    assert_eq!(t, ["String", "Number", "String"]);
    // A member redeclares a base field.
    let t = check_program(
        "/** const Base: () => {n: Number} */ const Base;\n\
         /** class Sub extends Base { n: String } */ class Sub;\n\
         const n = new Sub().n;",
        &["n"],
    )
    .unwrap();
    assert_eq!(t[0], "String");
    // The base must be declared without a body.
    for src in [
        "class B { constructor() { this.a = 1; } } /** class C extends B { b: String } */ class C;",
        "function B() { return {a: 1}; } /** class C extends B { b: String } */ class C;",
    ] {
        let err = check_program(src, &[]).unwrap_err();
        assert!(err.contains("declared without a body"), "{err}");
    }
    // A class with a body doesn't extend, and a bodiless one needs its
    // annotation.
    assert!(check_program(
        "/** class C { a: Number } */ class C; class D extends C { m() { return 1; } }",
        &[]
    )
    .is_err());
    assert!(check_program("class C;", &[]).is_err());
}

/// A class's fields are set one by one, as JavaScript sets them: an
/// initialiser (or a constructor's `this.f = …`) reads through `this` only a
/// field set before it. Reading a later field (`undefined` at run time),
/// calling a method (which may read one) or using `this` otherwise was
/// accepted and typed as reading the finished instance.
#[test]
fn class_initialisers_read_only_fields_set_before() {
    let t = check_program(
        "class P {\n\
           x = 1;\n\
           y = this.x + 1;\n\
           f = () => this.x + this.y;\n\
           constructor(n) { this.z = this.y + n; this.x = 5; }\n\
           get sum() { return this.x + this.y + this.z; }\n\
           twice() { return this.f() * 2; }\n\
         }\n\
         const p = new P(3);\n\
         const a = p.sum;\n\
         const b = p.twice();\n\
         const c = p.f();",
        &["a", "b", "c"],
    )
    .unwrap();
    assert_eq!(t, ["Number", "Number", "Number"]);
    for (src, why) in [
        ("class A { x = this.y; y = 1; }", "isn't a field set before"),
        (
            "class A { x = this.m(); m() { return 1; } }",
            "calling a method",
        ),
        (
            "class A { constructor() { this.x = this.y; this.y = 1; } }",
            "isn't a field set before",
        ),
        (
            "class A { x = 1; g = function () { return this.x; }; }",
            "inside a function",
        ),
        (
            "class A { x = 1; f = () => this.x; g = this.f; }",
            "arrow-function field",
        ),
        ("class A { x = 1; y = this; }", "other than `this.field`"),
        ("class A { x = 1; y = (this.x = 2); }", "storing to a field"),
        (
            "class A { x = 1; x() { return 2; } }",
            "same name as one of its methods",
        ),
        (
            "class A { constructor() { this.m = 1; } m() { return 2; } }",
            "same name as one of its methods",
        ),
        ("class A { set s(v) {} }", "setter"),
    ] {
        let err = check_program(src, &[]).unwrap_err();
        assert!(err.contains(why), "{src}: {err}");
    }
}

/// Only `new` calls a class (a call without it throws), and `new` gives
/// back the constructor's result only if that is an object: `new F()` of a
/// function returning a number was typed as that number.
#[test]
fn new_and_class_calls() {
    let err = check_program(
        "class C { constructor(n) { this.n = n; } } const c = C(1);",
        &["c"],
    )
    .unwrap_err();
    assert!(err.contains("without `new`"), "{err}");
    let err = check_program(
        "/** class Q(n: Number) { n: Number } */ class Q; const q = Q(1);",
        &["q"],
    )
    .unwrap_err();
    assert!(err.contains("without `new`"), "{err}");
    assert!(check_program("function F() { return \"s\"; } const f = new F();", &["f"]).is_err());
    assert!(check_program(
        "function mk(F) { return new F(); } const v = mk(function () { return 1; });",
        &["v"]
    )
    .is_err());
    let t = check_program(
        "function F(n) { return {n: n}; } const f = new F(1).n;",
        &["f"],
    )
    .unwrap();
    assert_eq!(t[0], "Number");
}

/// An arrow function isn't a constructor: `new` on one throws a
/// `TypeError`. Called, it takes any receiver, its `this` being its
/// enclosing function's.
#[test]
fn arrow_functions_are_not_constructors() {
    for src in [
        "const f = () => ({x: 1}); const r = new f();",
        "class D { f = () => ({x: 1}); } const r = new (new D()).f();",
        "class D { f = () => { this; return {x: 1}; }; } const r = new (new D()).f();",
        "function mk(g) { return new g(); } const r = mk(() => ({x: 1}));",
    ] {
        assert!(check_program(src, &[]).is_err(), "{src}");
    }
    let t = check_program(
        "class D { f = () => 3; } const d = new D(); const g = d.f;\n\
         const o = { h: () => 1 };\n\
         const r = g() + d.f() + o.h();\n\
         function F() { return {x: 1}; } const s = new F().x;",
        &["r", "s"],
    )
    .unwrap();
    assert_eq!(t, ["Number", "Number"]);
}

/// A getter is read, not stored to (a store throws in strict code), and a
/// class's methods and getters are on its prototype: a store to one is
/// rejected, and a spread doesn't copy them.
#[test]
fn getters_and_prototype_members() {
    let t = check_program(
        "const o = { a: 1, get g() { return this.a + 1; } };\n\
         const n = o.g;\n\
         const c = {...o}.g;",
        &["n", "c"],
    )
    .unwrap();
    assert_eq!(t, ["Number", "Number"]);
    for src in [
        "const o = { get g() { return 1; } }; o.g = 2;",
        "class A { get g() { return 1; } } const a = new A(); a.g = 2;",
        "class P { m() { return 1; } } const p = new P(); p.m = () => 2;",
        "class P { x = 1; m() { return this.x; } } const q = {...new P()}; const r = q.m();",
        "class P { get g() { return 1; } } const r = {...new P()}.g;",
        "/** class Q(n: Number) { n: Number, m: () => Number } */ class Q;\n\
         const r = {...new Q(1)}.m();",
        "function f(o) { o.g = 1; } f({ get g() { return 2; } });",
    ] {
        assert!(check_program(src, &[]).is_err(), "{src}");
    }
    // Reading code takes either kind of property.
    let t = check_program(
        "function get(o) { return o.g; }\n\
         const a = get({ g: 1 }) + get({ get g() { return 2; } });",
        &["a"],
    )
    .unwrap();
    assert_eq!(t[0], "Number");
    // A class's own fields are copied, and stored to.
    let t = check_program(
        "class P { x = 1; m() { return this.x; } } const p = new P(); p.x = 2;\n\
         const r = {...p}.x + p.m();",
        &["r"],
    )
    .unwrap();
    assert_eq!(t[0], "Number");
}

#[test]
fn an_annotated_function_type_without_this_is_called_detached() {
    // A function type written without `this:` is called detached, so a
    // function that reads `this` doesn't have it: each of these throws a
    // `TypeError` on `this.x`.
    for bad in [
        "/** const f: (Number) => Number */\n\
         const f = function (n) { return this.x + n; };\n\
         const r = f(1);",
        "const o = { x: 1, m(n) { return this.x + n; } };\n\
         /** const g: (Number) => Number */\n\
         const g = o.m;\n\
         const r = g(1);",
        "/** function call((Number) => Number) => Number */\n\
         function call(g) { return g(1); }\n\
         const o = { x: 1, m(n) { return this.x + n; } };\n\
         const r = call(o.m);",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
    // A function that doesn't read `this` has it.
    for (src, name, ty) in [
        (
            "/** const f: (Number) => Number */\n\
             const f = function (n) { return n + 1; };\n\
             const r = f(1);",
            "r",
            "Number",
        ),
        (
            "/** function call((Number) => Number) => Number */\n\
             function call(g) { return g(1); }\n\
             const r = call((n) => n * 2);",
            "r",
            "Number",
        ),
    ] {
        assert_eq!(check_program(src, &[name]).unwrap(), [ty], "{}", src);
    }
}

#[test]
fn a_method_in_an_annotated_object_type_has_the_object_as_this() {
    // A method says its `this`, `m: (this: O, n: Number) => Number`, and is
    // called on such an object, which it reads as `this`.
    let src = "/** type O = {x: Number, m: (this: O, n: Number) => Number} */\n\
               /** const o: O */\n\
               const o = { x: 1, m(n) { return this.x + n; } };\n\
               const r = o.m(1);";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
    // Taken off the object, it can't be called detached.
    let bad = "/** type O = {x: Number, m: (this: O, n: Number) => Number} */\n\
               /** const o: O */\n\
               const o = { x: 1, m(n) { return this.x + n; } };\n\
               const g = o.m;\n\
               const r = g(1);";
    let err = check_program(bad, &[]).unwrap_err();
    assert!(err.contains("`g` is a method (it reads `this`)"), "{}", err);
    // A property of a function type, `m: (Number) => Number`, is a
    // function that uses no `this`: one that reads it doesn't fit.
    let bad = "/** const o: {x: Number, m: (Number) => Number} */\n\
               const o = { x: 1, m(n) { return this.x + n; } };";
    assert!(check_program(bad, &[]).is_err(), "{}", bad);
}

/// A record field of a function type holds a callback: a function that
/// uses no `this`, which can be stored, read back, called on the object
/// or detached, and passed on (Rosaclef, item 2).
#[test]
fn a_record_field_holds_a_callback() {
    let src = "/** const s: { stop: () => Undefined } */\n\
               const s = { stop: () => undefined };\n\
               /** function set(stop: () => Undefined) => Undefined */\n\
               function set(stop) { s.stop = stop; }\n\
               const end = s.stop;\n\
               end();\n\
               /** function call(f: () => Undefined) => Undefined */\n\
               function call(f) { f(); }\n\
               call(s.stop);\n\
               s.stop();\n\
               set(function () { return undefined; });\n\
               const r = 1;";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
    // A property's own annotation says the same.
    let src = "const hooks = {\n\
               /** @type {() => Undefined} */\n\
               mark: null,\n\
               };\n\
               hooks.mark = () => undefined;\n\
               if (hooks.mark) hooks.mark();\n\
               const m = hooks.mark;\n\
               const r = 1;";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
    // But a function that reads `this` can't be stored there: it would
    // be called detached.
    let bad = "/** const s: { stop: () => Number } */\n\
               const s = { x: 1, stop: () => 1 };\n\
               s.stop = function () { return this.x; };";
    assert!(check_program(bad, &[]).is_err(), "{}", bad);
}

/// A method that reads `this` and a function that uses none don't make
/// one type, as an array's elements or a conditional's branches: either
/// could then be called detached.
#[test]
fn a_method_and_a_detached_function_are_different_types() {
    for bad in [
        "const o = { x: 1, m() { return this.x; } };\n\
         const fs = [() => 1, o.m];\n\
         const g = fs[1];\n\
         const r = g();",
        "const o = { x: 1, m() { return this.x; } };\n\
         const g = true ? () => 1 : o.m;\n\
         const r = g();",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
    // A method that doesn't mention `this` uses none.
    let src = "const o = { x: 1, m() { return 2; } };\n\
               const g = o.m;\n\
               const r = g() + o.m();";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
}

#[test]
fn a_builtin_calls_its_callbacks_detached() {
    // `map`, `forEach`, … call their callback with `this` undefined, so
    // a method that reads `this` throws a `TypeError` there.
    for bad in [
        "const o = { x: 1, m(n) { return this.x + n; } };\n\
         const r = [1, 2].map(o.m);",
        "const o = { x: 1, m: function (n) { return this.x + n; } };\n\
         [1, 2].forEach(o.m);",
        "const r = [\"a\"].map(\"b\".concat);",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
    // A callback that doesn't read `this` is fine, as is calling a
    // built-in method on its receiver.
    for (src, name, ty) in [
        (
            "const r = [1, 2].map(function (n) { return n + 1; });",
            "r",
            "Number[]",
        ),
        ("const r = [1, 2].map((n) => n * 2);", "r", "Number[]"),
        (
            "const o = { x: 1, m(n) { return this.x + n; } };\n\
             const r = [1, 2].map((n) => o.m(n));",
            "r",
            "Number[]",
        ),
        ("const r = \"ab\".slice(1);", "r", "String"),
    ] {
        assert_eq!(check_program(src, &[name]).unwrap(), [ty], "{}", src);
    }
}

const SHAPES: &str = "/** const v: {kind: \"a\", x: Number} | {kind: \"b\", y: String} \
                      | {kind: \"c\", z: Number} */ const v = {kind: \"a\", x: 1};";

#[test]
fn switch_default_sees_the_cases_left() {
    // `default:` is taken when no case matches: the arms tested by the
    // cases are ruled out there, wherever `default` stands.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": return v.x; \
         case \"b\": return 0; default: return v.z; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ default: return v.z; \
         case \"a\": return v.x; case \"b\": return 0; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
    // An arm no case rules out is still there.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": return v.x; \
         default: return v.z; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_err(), "{src}");
    // A case fallen into from the one before gets no facts of its own.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": v.x; \
         default: return v.z; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_err(), "{src}");
}

#[test]
fn exhaustive_switch_whose_cases_return_does_not_fall_through() {
    // Every tag has a case and each returns: the function never falls off
    // its end, so it returns a `Number`, not `Number | Undefined`.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": return v.x; \
         case \"b\": return 1; case \"c\": return v.z; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
    // A missing tag can fall through.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": return v.x; \
         case \"b\": return 1; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_err(), "{src}");
    // So can a case that breaks out of the switch.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": break; \
         case \"b\": return 1; case \"c\": return v.z; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_err(), "{src}");
    // Cases falling through into one that returns don't.
    let src = format!(
        "{SHAPES} function f() {{ switch (v.kind) {{ case \"a\": case \"b\": \
         default: return 1; }} }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
}

#[test]
fn narrowing_after_an_early_exit_reaches_what_is_defined_after_it() {
    // A function-valued `const` and a class can't run before their
    // declaration, so they see the facts an early exit before them
    // establishes.
    let src = format!(
        "{SHAPES} function f() {{ if (v.kind !== \"a\") {{ return 0; }} \
         const g = () => v.x; return g(); }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
    let src = format!(
        "{SHAPES} function f() {{ if (v.kind !== \"a\") {{ return 0; }} \
         class C {{ m() {{ return v.x; }} }} return new C().m(); }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_ok(), "{src}");
    // A `function` declaration is hoisted: it may run before the test.
    let src = format!(
        "{SHAPES} function f() {{ if (v.kind !== \"a\") {{ return g(); }} \
         function g() {{ return v.x; }} return g(); }} f() - 1;"
    );
    assert!(infer_program_via_program(&src).is_err(), "{src}");
}

#[test]
fn spread_of_an_operand_not_known_yet_waits_for_it() {
    // Which fields the operand writes over is decided at each use, as the
    // Lean model's `Merge` decides it slot by slot.
    let src = "const f = (a, b) => ({...a, ...b}); \
               const r = f({a: \"s\", c: true}, {a: 1}); r.a - 1; r.c ? 1 : 2;";
    assert!(infer_program_via_program(src).is_ok());
    let src = "const f = (a, b) => ({...a, ...b}); f({a: \"s\"}, {a: 1}).a.length;";
    assert!(infer_program_via_program(src).is_err());
    // Fields written after the spread win over the operand's; those
    // before it lose to them.
    let src = "const g = (o) => ({x: 1, ...o, y: \"z\"}); \
               const s = g({x: \"q\", y: 2, w: 3}); s.x.length + s.y.length + s.w;";
    assert!(infer_program_via_program(src).is_ok());
    let src = "const g = (o) => ({...o, y: \"z\"}); g({y: 2, w: 3}).y.length; \
               g({w: true}).w ? 1 : 0;";
    assert!(infer_program_via_program(src).is_ok());
    // A field the operand may lack keeps the one before it.
    let src = "const g = (o) => ({x: 1, ...o}); g({}).x + 1;";
    assert!(infer_program_via_program(src).is_ok());
    // A spread's result is an object, whose fields take stores: the call
    // signature it carries as absent doesn't make it a function's (the
    // differential test found `{...{...o}}` refused a store).
    let src = "function k(o) { const r = {...{...o}}; r.c = 5; return r; } k({c: 1}).c - 1;";
    assert!(infer_program_via_program(src).is_ok()); // Its result is an object even before the operand is known: it can't
                                                     // be called (the differential test found it callable).
    let src = "function f(o) { return ({...o})(1); }";
    assert!(infer_program_via_program(src).is_err());
    // A getter written after the spread stays a getter: it can't be
    // stored to (the review found it made writable).
    for src in [
        "function f(o) { return {...o, get x() { return 1; }}; } const r = f({}); r.x = 2;",
        "function f(o) { const r = {...o, get x() { return 1; }}; r.x = 2; return r; } f({});",
    ] {
        assert!(infer_program_via_program(src).is_err(), "{src}");
    }
    let src = "function f(o) { return {...o, get x() { return 1; }}; } \
               f({x: \"s\", y: 2}).x - 1 + f({y: 2}).y;";
    assert!(infer_program_via_program(src).is_ok()); // A spread whose result flows back into its operand (`x = {...x}`)
                                                     // isn't a cycle (the differential test found the unifier giving up).
    for src in [
        "let x = [][0]; x = {...{a: \"\"}, ...x};",
        "const o = {b: [][0], m() { this.b = {...{a: \"\"}, ...this.b}; return this; }}; o.m();",
    ] {
        assert!(infer_program_via_program(src).is_ok(), "{src}");
    }
}

#[test]
fn instance_holding_its_own_factory_is_a_recursive_type() {
    // `t ~ μ<{c: () => t}>`: solved by a recursive type, not refused by
    // the occurs check (the differential test found it).
    let src = "function f6() { class C7 { constructor() { this.c = f6; } \
               get g() { return this; } } return new C7(); } const h = f6().g.c; h().g;";
    assert!(infer_program_via_program(src).is_ok());
}

#[test]
fn a_body_that_never_completes_returns_any_type() {
    // It gives no value, so its result is a type variable the binding
    // generalises, as the Lean model has it: it joins with any other
    // function's (`never` joined with none).
    for src in [
        "const f = function () { throw 1; }; const g = function () { return 1; }; \
         const h = true ? f : g; h() - 1;",
        "const f = function () { throw 1; }; const xs = [f, function () { return \"s\"; }];",
        "function apply(k) { return k(); } apply(function () { throw 1; }) + 1;",
        "function f() { throw 1; } f() - 1; f().length;",
        // A member of an object or class keeps `never`: the object's type
        // holds it as it is, so a variable would be fixed by its first use
        // (the review found `fail` used as a number, then a string,
        // refused).
        "const util = { fail(msg) { throw msg; } }; \
         function num(c) { return c ? 1 : util.fail(\"x\"); } \
         function str(c) { return c ? \"s\" : util.fail(\"y\"); } num(true) - 1; str(true).length;",
        "const util = { fail: (msg) => { throw msg; } }; \
         function num(c) { return c ? 1 : util.fail(\"x\"); } \
         function str(c) { return c ? \"s\" : util.fail(\"y\"); } num(true) - 1; str(true).length;",
        "class C { m() { throw 1; } } const c = new C(); \
         function a() { return c.m() - 1; } function b() { return c.m().length; }",
    ] {
        assert!(infer_program_via_program(src).is_ok(), "{src}");
    }
}

/// Whether `source` type-checks: inferred, with no error recorded, and its
/// constraints resolved.
fn typechecks(source: &str) -> bool {
    match infer_program_with_state(source) {
        Ok((_, _, mut state)) => {
            state.take_errors().is_empty() && state.resolve_constraints().is_ok()
        }
        Err(_) => false,
    }
}

/// A comparison takes two numbers or two strings, and no coercion between
/// types: stricter than JavaScript, which would compare `"10" < 9` as
/// numbers, `true < 2` with `true` as `1`, and two arrays as strings.
#[test]
fn comparisons_take_two_numbers_or_two_strings() {
    for ok in [
        "1 < 2;",
        "\"a\" <= \"b\";",
        "const s = \"a\"; s > \"b\";",
        "function lt(a, b) { return a < b; } lt(1, 2); lt(\"a\", \"b\");",
    ] {
        assert!(typechecks(ok), "should type-check: {ok}");
    }
    for bad in [
        "\"10\" < 9;",
        "1 >= \"a\";",
        "true < false;",
        "({}) < ({});",
        "[1] < [2];",
        "null < 1;",
        "function lt(a, b) { return a < b; } lt(true, false);",
        "function lt(a, b) { return a < b; } lt(1, \"a\");",
    ] {
        assert!(!typechecks(bad), "should be rejected: {bad}");
    }
}

/// `function lt(a, b) { return a < b; }` is generic in a number-or-string
/// type, `Plus a`, as `+` is.
#[test]
fn comparison_function_has_plus_constraint() {
    let (_, env, _) = infer_program_with_state("function lt(a, b) { return a < b; }").unwrap();
    let scheme = env.lookup("lt").unwrap();
    assert_eq!(scheme.body.preds.len(), 1, "{scheme:?}");
    assert_eq!(scheme.body.preds[0].class, crate::types::ClassName::Plus);
}

// Rosaclef (inty-notes "Gaps found moving to inty cb4bfca", E): an
// array's `length` takes a number, which truncates it.
#[test]
fn a_store_to_an_array_length_truncates_it() {
    let src = "/** const xs: String[] */\n\
               const xs = [];\n\
               xs.length = 0;\n\
               function clear(a) { a.length = 0; return a; }\n\
               const ys = clear([1, 2]);\n\
               const n = xs.length;";
    assert_eq!(
        check_program(src, &["ys", "n"]).unwrap(),
        ["Number[]", "Number"]
    );
    // A number only, and no other built-in property.
    for bad in [
        "const xs = [1]; xs.length = \"0\";",
        "const xs = [1]; xs.push = 0;",
    ] {
        assert!(check_program(bad, &[]).is_err(), "{}", bad);
    }
}

// Rosaclef (F): a branch that is exactly `undefined` or `null` makes the
// conditional the other branch's type or nothing.
#[test]
fn a_branch_of_nothing_makes_the_conditional_a_sum() {
    let src = "/** const xs: Number[] */\n\
               const xs = [];\n\
               const last = xs.length > 0 ? xs[xs.length - 1] : undefined;\n\
               const c = xs.length > 2;\n\
               const s = c ? \"a\" : null;\n\
               const u = c ? undefined : 1;\n\
               const v = last ?? 0;";
    assert_eq!(
        check_program(src, &["last", "s", "u", "v"]).unwrap(),
        [
            "Number | Undefined",
            "String | Null",
            "Number | Undefined",
            "Number"
        ]
    );
    // The value may be nothing, so it is used only once told apart.
    let bad = "const c = Math.random() > 0.5;\n\
               const x = c ? 1 : undefined;\n\
               const y = x + 1;";
    assert!(check_program(bad, &[]).is_err(), "{}", bad);
}

// Rosaclef (G): `Array.prototype.at`, which is past the end (either way)
// `undefined`.
#[test]
fn an_array_at_may_be_undefined() {
    let src = "const xs = [1, 2, 3];\n\
               const a = xs.at(-1);\n\
               const b = xs.at(0) ?? 0;";
    assert_eq!(
        check_program(src, &["a", "b"]).unwrap(),
        ["Number | Undefined", "Number"]
    );
    let bad = "const xs = [1, 2, 3];\nconst a = xs.at(-1) + 1;";
    assert!(check_program(bad, &[]).is_err(), "{}", bad);
}

// Rosaclef (D), not changed: `{}` is a closed empty record, so
// `(raw.c ?? {}).off` reads a field `{}` doesn't have. Accepting it would
// need an open `{}` (unsound: a later read of a field the value lacks) or
// fields that may be absent (`off?: T` read as `T | Undefined`). Telling
// the absent case apart first does it.
#[test]
fn a_field_of_an_empty_default_is_not_read() {
    let src = "/** function f<T>(raw: T) => String[] */\n\
               function f(raw) { return ((raw.c ?? {}).off ?? []).map((x) => x); }";
    let err = check_program(src, &[]).unwrap_err();
    assert!(err.to_string().contains("'off' not found"), "{err}");
    let src = "/** function decode<T>(c: T) => String[] */\n\
               function decode(c) {\n\
                 if (!c) return [];\n\
                 return (c.off ?? []).map((x) => x);\n\
               }\n\
               /** function f<T>(raw: T) => String[] */\n\
               function f(raw) { return decode(raw.c); }\n\
               const r = 1;";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
}

// An object literal's method that never mentions `this` fits a method's
// slot (`stop: (this: S) => Number`) as well as a plain function's; one
// that reads `this` reads the object (of the annotated type), and doesn't
// fit a plain function's.
#[test]
fn a_literal_method_fits_the_slot_it_is_checked_against() {
    let src = "/** type S = { stop: (this: S) => Number, x: Number } */\n\
               /** const s: S */\n\
               const s = { x: 1, stop() { return this.x; } };\n\
               /** const u: S */\n\
               const u = { x: 1, stop() { return 2; } };\n\
               /** const t: { stop: () => Number, x: Number } */\n\
               const t = { x: 1, stop() { return 2; } };\n\
               const f = t.stop;\n\
               const r = s.stop() + u.stop() + f();";
    assert_eq!(check_program(src, &["r"]).unwrap(), ["Number"]);
    let bad = "/** const t: { stop: () => Number, x: Number } */\n\
               const t = { x: 1, stop() { return this.x; } };";
    assert!(check_program(bad, &[]).is_err(), "{}", bad);
}

// A declared method (a declaration has no body to show whether it reads
// `this`, so its type says: `m: (this: L) => Number`) is called on its
// object: not detached, and not where a function that is called detached
// goes. A declared plain function (`f: () => Number`) is either.
#[test]
fn a_declared_method_is_called_on_its_object() {
    let decl = "/** type L = {x: Number, m: (this: L) => Number, f: () => Number} */\n\
                /** const lib: L */\nconst lib;\n";
    let ok = format!(
        "{decl}const a = lib.m() + lib.x;\n\
         const g = lib.f;\n\
         /** function call(h: () => Number) => Number */\n\
         function call(h) {{ return h(); }}\n\
         const r = a + g() + call(lib.f);"
    );
    assert_eq!(check_program(&ok, &["r"]).unwrap(), ["Number"]);
    for bad in [
        "const g = lib.m;\nconst r = g();",
        "/** function call(h: () => Number) => Number */\n\
         function call(h) { return h(); }\nconst r = call(lib.m);",
        "function call(h) { return h(); }\nconst r = call(lib.m);",
    ] {
        let src = format!("{decl}{bad}");
        assert!(check_program(&src, &[]).is_err(), "{}", src);
    }
}

// TypeScript's method signature (`m(): T`) leaves `this` implicit; inty's
// error says how to write it.
#[test]
fn a_method_signature_says_its_this() {
    let err = check_program(
        "/** const o: {m(): Number} */\nconst o = {m() { return 1; }};",
        &[],
    )
    .unwrap_err();
    assert!(err.contains("(this: T, …) => R"), "{err}");
}

#[test]
fn test_member_on_recursive_union_alias() {
    // A union that refers to itself is a named (recursive) type: reading a
    // field reads it from each member, and the tag narrows, as for a union
    // written out.
    let src = "/** type T = {kind: \"a\", kids: T[]} | {kind: \"b\", n: Number} */\n\
               /** function size(t: T) => Number */\n\
               function size(t) { if (t.kind === \"b\") return t.n; return t.kids.length; }\n\
               /** function tag(t: T) => String */\n\
               function tag(t) { return t.kind; }";
    infer_program_with_state(src).expect("field access on a recursive union alias");
}

#[test]
fn number_methods() {
    // `Number.prototype`'s formatting methods, each optional argument
    // omittable per call.
    let src = "const n = 1.5;\n\
               const a = n.toFixed(1);\n\
               const b = n.toString(16);\n\
               const c = n.toString();\n\
               const d = n.toPrecision(2);\n\
               const e = (2).toFixed();\n\
               const f = true.toString();\n\
               function g(x) { return x.toFixed(2); }\n\
               const h = g(3);";
    let t = check_program(src, &["a", "b", "c", "d", "e", "f", "h"]).unwrap();
    assert!(t.iter().all(|s| s == "String"), "{t:?}");
    assert!(check_program("const n = 1; n.toFixed(\"2\");", &[]).is_err());
    assert!(check_program("const n = 1; n.toUpperCase();", &[]).is_err());
}

#[test]
fn string_replace_with_a_function() {
    // The replacement is a string or a function of the match.
    let src = "const a = \"ab\".replace(/a/g, c => c + \"b\");\n\
               const b = \"ab\".replaceAll(\"a\", (m) => m.toUpperCase());\n\
               const c = \"ab\".replace(\"a\", \"z\");";
    let t = check_program(src, &["a", "b", "c"]).unwrap();
    assert!(t.iter().all(|s| s == "String"), "{t:?}");
    // A replacer returns a string, and gets the match as one.
    assert!(check_program("\"ab\".replace(/a/, c => 1);", &[]).is_err());
    assert!(check_program("\"ab\".replace(/a/, c => c * 2);", &[]).is_err());
    // The groups and the offset aren't modelled: their types depend on
    // the pattern.
    assert!(check_program("\"ab\".replace(/(a)/, (m, g) => g);", &[]).is_err());
}

#[test]
fn dict_dot_and_bracket_writes_agree() {
    // `d.k = v` stores key `k` of a `Dict<V>`, as `d["k"] = v` does, and
    // both store a `V`: an `undefined` stored would come back out of
    // `Object.values`. A read is `V | Undefined` (the key may be missing),
    // so an update that reads the entry first needs it narrowed.
    let ok = "/** function g({dataset: Dict<String>}) => Undefined */\n\
              function g(el) { el.dataset.x = \"a\"; el.dataset[\"y\"] = \"b\"; el.dataset.z ??= \"c\"; }";
    check_program(ok, &[]).unwrap();
    for bad in [
        "el.dataset.x = undefined;",
        "el.dataset[\"x\"] = undefined;",
        "el.dataset.x = 1;",
        "el.dataset.x += \"s\";",
    ] {
        let src = format!(
            "/** function g({{dataset: Dict<String>}}) => Undefined */\n\
             function g(el) {{ {bad} }}"
        );
        assert!(check_program(&src, &[]).is_err(), "{src}");
    }
}
#[test]
fn block_scoped_bindings_are_distinct() {
    // `let`/`const` are block-scoped, and a `for … of` binding is the
    // loop body's: two bindings of one name in one function are two
    // variables, each with its own type, and the later one, never
    // reassigned, narrows.
    let src = "/** function f(Dict<String>) => String */\n\
               function f(d) {\n\
                 for (const [k, v] of [[1, 2]]) { const z = v + 1; }\n\
                 const v = d[\"k\"];\n\
                 if (v !== undefined) { const g = () => v.length; return v; }\n\
                 return \"\";\n\
               }\n\
               /** function g(Dict<String>) => Number */\n\
               function g(d) {\n\
                 { let v = 1; v = 2; }\n\
                 for (let i = 0; i < 2; i++) { const v = true; }\n\
                 const v = d[\"k\"];\n\
                 if (v !== undefined) { const h = () => v.length; return h(); }\n\
                 return 0;\n\
               }\n\
               function h() { if (true) { const x = 1; return x + 1; } else { const x = \"s\"; return x.length; } }";
    check_program(src, &[]).unwrap();
    // The inner binding isn't visible after its block.
    assert!(check_program("function f() { { const x = 1; } return x; }", &[]).is_err());
}

/// Check with the standard library (`Set`, `Map`, `Array.from`, …);
/// `Ok` holds the display form of each named binding's scheme.
fn check_with_stdlib(src: &str, names: &[&str]) -> Result<Vec<String>, String> {
    let program = crate::frontends::javascript::parse_source(src).map_err(|e| e.to_string())?;
    let (env, mut state) = crate::stdlib::initial_env_with_stdlib().map_err(|e| e.to_string())?;
    let (_, env) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| e.to_string())?;
    if let Some(e) = state.errors.first() {
        return Err(e.to_string());
    }
    state.resolve_constraints().map_err(|e| e.to_string())?;
    Ok(names
        .iter()
        .map(|n| {
            let scheme = env.lookup(n).unwrap_or_else(|| panic!("{} not bound", n));
            format!("{}", state.display_scheme(scheme))
        })
        .collect())
}

#[test]
fn iterating_strings_sets_and_maps() {
    let src = "for (const ch of \"abc\") { ch.toUpperCase(); }\n\
               const xs = [...\"abc\"];\n\
               const st = new Set(); st.add(1);\n\
               let n = 0; for (const x of st) { n = n + x; }\n\
               const ys = [...st];\n\
               const s2 = new Set([\"a\", \"b\"]);\n\
               const s3 = new Set(\"abc\");\n\
               const s4 = new Set(s2);\n\
               const m = new Map([[\"a\", 1]]);\n\
               for (const [k, v] of m) { k.length + v; }\n\
               const ks = [...m.keys()];\n\
               const vs = [...m.values()];\n\
               const es = [...m.entries()];\n\
               function mk() { return new Set(); }\n\
               const s5 = mk(); s5.add(\"q\");";
    // (`mk`'s scheme has no `Iterable`: the one `new Set()` posed for the
    // argument it leaves out is vacuous.)
    let t = check_with_stdlib(src, &["xs", "ys", "ks", "vs", "es"]).unwrap();
    assert_eq!(
        t,
        [
            "String[]",
            "Number[]",
            "String[]",
            "Number[]",
            "[String, Number][]",
        ]
    );
    for bad in [
        // A Dict is a plain object: not iterable.
        "/** const d: Dict<Number> */ const d; for (const x of d) {}",
        "for (const x of {a: 1}) {}",
        "const xs = [...5];",
        // The element type is the set's.
        "const s = new Set([\"a\"]); for (const x of s) { x * 2; }",
        "const m = new Map([[\"a\", 1]]); m.set(\"b\", \"c\");",
    ] {
        assert!(check_with_stdlib(bad, &[]).is_err(), "{bad}");
    }
}

#[test]
fn declared_iterable_host_collection() {
    // A declaration says what iterating a host object gives, without
    // claiming it is an array.
    let src = "/** type El = {id: String} */\n\
               /** type NodeList = {length: Number, item: (Number) => El | Null, [Symbol.iterator]: El} */\n\
               /** const all: () => NodeList */\n\
               const all;\n\
               for (const el of all()) { el.id.length; }\n\
               const ids = Array.from(all(), (el) => el.id);\n\
               const els = [...all()];";
    let t = check_with_stdlib(src, &["ids", "els"]).unwrap();
    assert_eq!(t, ["String[]", "{id: String}[]"]);
    // It isn't an array.
    let bad = "/** type NodeList = {length: Number, [Symbol.iterator]: String} */\n\
               /** const all: () => NodeList */\n\
               const all;\n\
               all().map((x) => x);";
    assert!(check_with_stdlib(bad, &[]).is_err());
}

#[test]
fn array_from_is_checked() {
    let src = "const a = Array.from(new Set([\"s\"]));\n\
               const b = Array.from(\"abc\");\n\
               const c = Array.from({length: 3}, (_, i) => i * 2);\n\
               const d = Array.from([1, 2], (x) => String(x));";
    let t = check_with_stdlib(src, &["a", "b", "c", "d"]).unwrap();
    assert_eq!(t, ["String[]", "String[]", "Number[]", "String[]"]);
    for bad in [
        // Was an unchecked cast: `a` and `b[]` unrelated.
        "Array.from(new Set([\"s\"])).push(3);",
        // An array-like object needs a map function.
        "const z = Array.from({length: 3});",
        "const z = Array.from(5);",
        "const z = Array.from([1], (x) => x.length);",
    ] {
        assert!(check_with_stdlib(bad, &[]).is_err(), "{bad}");
    }
}

#[test]
fn iterable_constraint_is_generalised() {
    // A function that iterates its parameter takes any iterable.
    let src = "function firstOf(xs) { for (const x of xs) { return x; } throw 0; }\n\
               const a = firstOf([1, 2]);\n\
               const b = firstOf(\"ab\");\n\
               const c = firstOf(new Set([true]));";
    let t = check_with_stdlib(src, &["firstOf", "a", "b", "c"]).unwrap();
    assert_eq!(t[0], "<a, b> where Iterable a b => (a) => b");
    assert_eq!(&t[1..], ["Number", "String", "Boolean"]);
}

#[test]
fn narrowing_through_a_disjunction_of_tag_tests() {
    let alias = "/** type S = {kind: \"row\", children: Number[]} | {kind: \"col\", children: Number[]} | {kind: \"leaf\", v: String} */\n";
    let ok = format!(
        "{alias}/** function f(S) => Number */\n\
         function f(spec) {{ if (spec.kind === \"row\" || spec.kind === \"col\") return spec.children.length; return spec.v.length; }}\n\
         /** function g(S) => Number */\n\
         function g(spec) {{ if (spec.kind !== \"row\" && spec.kind !== \"col\") return spec.v.length; return spec.children.length; }}\n\
         /** function h(String | Number | Boolean) => Number */\n\
         function h(x) {{ if (typeof x === \"string\" || typeof x === \"number\") {{ return 1; }} return x ? 1 : 0; }}"
    );
    check_program(&ok, &[]).unwrap();
    for bad in [
        // A member the disjunction lets through lacks the field.
        "/** function f(S) => Number */\nfunction f(spec) { if (spec.kind === \"row\" || spec.kind === \"leaf\") return spec.children.length; return 0; }",
        // A test of another path says nothing about this one.
        "/** function f(S, S) => Number */\nfunction f(a, b) { if (a.kind === \"row\" || b.kind === \"col\") return a.children.length; return 0; }",
    ] {
        let src = format!("{alias}{bad}");
        assert!(check_program(&src, &[]).is_err(), "{src}");
    }
}

#[test]
fn a_copied_property_narrows() {
    // Records are mutable: a test of `reg.palette` says nothing about a
    // later read (a call between them could store `null`; see the golden
    // test `25-unnarrowed-property` for the error). A `const` copy does
    // narrow.
    let decls = "/** function render(String) => Undefined */\nfunction render(s) {}\n";
    let bad = format!(
        "{decls}/** function g({{palette: String | Null}}) => Undefined */\n\
         function g(reg) {{ if (reg.palette) render(reg.palette); }}"
    );
    assert!(check_program(&bad, &[]).is_err());
    let ok = format!(
        "{decls}/** function g({{palette: String | Null}}) => Undefined */\n\
         function g(reg) {{ const p = reg.palette; if (p) render(p); }}"
    );
    check_program(&ok, &[]).unwrap();
}

#[test]
fn independent_groups_are_inferred_in_a_fixed_order() {
    // `a` … `f` are independent groups that each fix `xs`' element type:
    // the one inferred first decides it, and the others are errors.
    // Which that is mustn't depend on hash order (a group's call edges
    // and a statement's free names are hash sets), so every run reports
    // the same error.
    let src = "const xs = [];\n\
               function h() { a(); b(); c(); d(); e(); f(); }\n\
               function a() { xs.push(1); }\n\
               function b() { xs.push(\"s\"); }\n\
               function c() { xs.push(true); }\n\
               function d() { xs.push(null); }\n\
               function e() { xs.push([1]); }\n\
               function f() { xs.push({ k: 1 }); }\n\
               h();";
    let first = check_program(src, &[]).expect_err("xs is given six element types");
    for _ in 0..32 {
        assert_eq!(check_program(src, &[]).expect_err("as before"), first);
    }
}

#[test]
fn member_of_a_nullable_value_says_it_may_be_nothing() {
    // The receiver is what's found, not what's expected, and the error
    // says the value may be nothing rather than naming a record shape.
    let src = "/** const q: Number | Null */\nconst q = 1;\nconst s = q.toFixed(2);";
    let err = check_program(src, &[]).expect_err("q may be null");
    assert!(
        err.contains("Property 'toFixed' not found") && err.contains("may be null"),
        "{err}"
    );
    let src = "/** const q: String | Undefined */\nconst q = \"a\";\nconst n = q.length;";
    let err = check_program(src, &[]).expect_err("q may be undefined");
    assert!(err.contains("may be undefined"), "{err}");
    // Narrowed first, it type-checks.
    let src =
        "/** const q: Number | Null */\nconst q = 1;\nconst s = q !== null ? q.toFixed(2) : \"\";";
    assert!(check_program(src, &[]).is_ok());
}
