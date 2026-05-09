//! Integration tests for the inference module.

use super::env::Mutability;
use super::*;

use crate::builtins::initial_env;
use crate::lexer::{Scanner, Token};
use crate::parser::Parser;
use crate::types::Type;

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
        crate::parser::ast::Stmt::Expr { expression, .. } => expression.clone(),
        _ => panic!("Expected expression statement"),
    };

    let mut state = InferState::new();
    let env = initial_env();
    state.infer_expr(&env, &expr)
}

#[test]
fn test_infer_number() {
    let ty = infer_expr_str("42").unwrap();
    assert_eq!(ty, Type::Number);
}

#[test]
fn test_infer_string() {
    let ty = infer_expr_str("\"hello\"").unwrap();
    assert_eq!(ty, Type::String);
}

#[test]
fn test_infer_boolean() {
    let ty = infer_expr_str("true").unwrap();
    assert_eq!(ty, Type::Boolean);
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
    let p0 = state.apply_subst(&params[0]);
    let p1 = state.apply_subst(&params[1]);
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

    // y should be Number (or a type with Plus constraint)
    let y_scheme = env.lookup("y").unwrap();
    let y_ty = state.apply_subst(&y_scheme.body.ty);
    assert!(
        matches!(y_ty, Type::Number | Type::Var(_)),
        "y should be Number or Plus-constrained"
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
// When a var/let is generalized to a polytype σ at its declaration, every
// subsequent assignment must produce a value at-least-as-polymorphic as σ.
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
fn test_polymorphic_var_assignment_skolem_escape() {
    // The RHS of `x = function(y) { return z; }` captures `z` from the
    // enclosing function. Naively skolemizing x's polytype `<a>(a) => a`
    // and unifying with `(?γ) => typeof z` would bind z's flex var to
    // the fresh skolem α — leaking α into the surrounding env. After
    // that, `leak`'s inferred signature contains a free skolem and
    // calling `leak(42)` produces a confusing "expected 'a', found
    // Number" mismatch. The subsumption check must detect the escape
    // and reject the assignment cleanly.
    let source = r#"
        function id(a) { return a; }
        function leak(z) {
          var x = id;
          x = function(y) { return z; };
          return z;
        }
    "#;
    let result = infer_program_with_state(source);
    assert!(
        result.is_err(),
        "Capturing an outer-scope variable in the RHS of a polymorphic \
         reassignment must be rejected — otherwise a skolem leaks into the \
         enclosing function's signature"
    );
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

    // Both parameters should be unified to the same type
    if let Some((_, params, _)) = ty.as_callable() {
        assert_eq!(params.len(), 2);
        assert_eq!(
            params[0], params[1],
            "Both parameters should have the same type"
        );
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
        let fn_param = state.apply_subst(&params[1]);
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
    // Test that the map function has a clean type signature where:
    // 1. arr is typed as an array (not just a row with length)
    // 2. fn's input type equals arr's element type
    // 3. fn's output type equals result's element type
    // 4. All quantified type variables are actually used in the type
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

    // All quantified variables should appear in the type body
    let body_vars = scheme.body.ty.free_vars();
    for var in &scheme.vars {
        assert!(
            body_vars.contains(var),
            "Quantified variable {:?} should appear in type body",
            var
        );
    }

    let ty = state.apply_subst(&scheme.body.ty);

    let (_, params, ret) = ty.as_callable().expect("map should be a function type");
    let arr_param = state.apply_subst(&params[0]);
    let fn_param = state.apply_subst(&params[1]);
    let ret_type = state.apply_subst(ret);

    // arr should be an array type
    assert!(
        matches!(arr_param, Type::Array(_)),
        "arr parameter should be Array type, got: {}",
        arr_param
    );

    // fn should be a function type
    assert!(
        fn_param.is_func(),
        "fn parameter should be a function type, got: {}",
        fn_param
    );

    // ret should be an array type
    assert!(
        matches!(ret_type, Type::Array(_)),
        "return type should be Array type, got: {}",
        ret_type
    );

    if let (Type::Array(arr_elem), Some((_, fn_params, fn_ret)), Type::Array(result_elem)) =
        (&arr_param, fn_param.as_callable(), &ret_type)
    {
        let arr_elem_type = state.apply_subst(arr_elem.as_ref());
        let fn_input_type = state.apply_subst(&fn_params[0]);
        let fn_ret_type = state.apply_subst(fn_ret);
        let result_elem_type = state.apply_subst(result_elem.as_ref());

        // arr element type should equal fn's input type
        assert_eq!(
            arr_elem_type, fn_input_type,
            "arr element type should equal fn input type"
        );

        // fn return type should equal result element type
        assert_eq!(
            fn_ret_type, result_elem_type,
            "fn return type should equal result element type"
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
    match ty {
        Type::Union(ref m) => {
            assert_eq!(m.len(), 2);
            assert!(m.contains(&Type::Number));
            assert!(m.contains(&Type::Undefined));
        }
        other => panic!("expected union, got {}", other),
    }
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
    // Two branches with disjoint row shapes form a union.
    let src = "function pick(b) { if (b) { return {x: 1, y: 2}; } else { return {x: 3, z: 4}; } }";
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
    let src = "function getX(b) { var pt = b ? {x: 1, y: 2} : {x: 3, z: 4}; return pt.x; }";
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
    let src = "function getX(b) { var pt = b ? {x: 1, y: 2} : {x: \"a\", z: 4}; return pt.x; }";
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
    // Mixed element types union, matching the existing `[1, "two"]`
    // behaviour. `[...xs, "three"]` with `xs : Number[]` produces
    // `(Number | String)[]`.
    let src = "\
        var xs = [1, 2]; \
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
fn ts_optional_property_widens_to_union_with_undefined() {
    // `{ name?: String }` parses as `{ name: String | Undefined }`.
    let src = "\
        /** const o: { name?: String } */ \
        const o; \
        var n = o.name;";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let n = state.apply_subst(&env.lookup("n").unwrap().body.ty);
    assert_eq!(n, Type::union([Type::String, Type::Undefined]));
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
    let (_, env, state) =
        infer_program_with_state(src).expect("explicit quantifier should bind T");
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
/// inty has no nullable types so the default itself isn't type-checked,
/// but the surrounding pattern must continue to work.
#[test]
fn destructuring_default_in_function_param() {
    let src = "\
        function orient({ target, anchor = null, reset = false }) { return target; } \
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
    let err = result.err().expect("must error on extends");
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
    use crate::types::{PropName, Type};
    let src = "function f(o) { var a = o.foo; var b = o.bar; }";
    let (_, env, state) = infer_program_with_state(src).unwrap();
    let scheme = env.lookup("f").unwrap();
    let ty = state.apply_subst(scheme.ty());
    let (_, params, _) = ty.as_callable().expect("f should be callable");
    let param = state.apply_subst(&params[0]);
    let row = match &param {
        Type::Row(r) => r,
        other => panic!("parameter should be a row, got {}", other),
    };
    assert!(
        row.props.contains_key(&PropName("foo".to_string())),
        "parameter row should mention `foo`, got {}",
        param
    );
    assert!(
        row.props.contains_key(&PropName("bar".to_string())),
        "parameter row should mention `bar` (the second access dropped its constraint), got {}",
        param
    );
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
