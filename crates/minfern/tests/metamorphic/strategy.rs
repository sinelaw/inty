//! Proptest strategies for generating programs the type checker might
//! actually have something interesting to say about.
//!
//! The original strategy was deliberately minimal (literals + idents +
//! a couple of binary ops). That covered the easiest metamorphic edges
//! but bypassed most of the type checker — no objects, no functions,
//! no member access, no structural typing, no polymorphism. This
//! version grows the grammar in those directions while keeping recursion
//! bounded so proptest shrinking stays fast.
//!
//! Generated programs will often *not* type-check, and that's fine: the
//! metamorphic properties are invariants that hold in both directions
//! (ok→ok or err→err), so err cases are just as useful — as long as
//! they reach the inference stage, which all of these do because the
//! strategy emits only parseable forms.

use proptest::prelude::*;

use minfern::parser::ast::*;

use super::ast::span;

// -------------------------------------------------------------------------
// Identifier pool — small enough that random references often land on
// something previously declared, which raises the rate of type-correct
// programs without biasing against err cases (still plenty of mis-typed
// combinations happen).
// -------------------------------------------------------------------------

pub fn ident_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("a".to_string()),
        Just("b".to_string()),
        Just("c".to_string()),
        Just("x".to_string()),
        Just("y".to_string()),
        Just("foo".to_string()),
        Just("bar".to_string()),
    ]
}

/// Property keys for object literals. Kept separate from the variable
/// pool to minimise incidental overlap (renaming a variable shouldn't
/// ever touch a label, but it's still nice to see that visually).
pub fn prop_key_strategy() -> impl Strategy<Value = PropKey> {
    prop_oneof![
        Just(PropKey::Ident("k".to_string())),
        Just(PropKey::Ident("value".to_string())),
        Just(PropKey::Ident("label".to_string())),
        Just(PropKey::Ident("count".to_string())),
    ]
}

pub fn literal_strategy() -> impl Strategy<Value = Literal> {
    prop_oneof![
        Just(Literal::Null),
        Just(Literal::Undefined),
        Just(Literal::Boolean(true)),
        Just(Literal::Boolean(false)),
        (-100i32..100).prop_map(|n| Literal::Number(n as f64)),
        prop::string::string_regex("[a-zA-Z0-9 ]{0,8}")
            .unwrap()
            .prop_map(Literal::String),
    ]
}

pub fn binop_strategy() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::Add),
        Just(BinOp::Sub),
        Just(BinOp::Mul),
        Just(BinOp::Lt),
        Just(BinOp::EqEqEq),
    ]
}

// -------------------------------------------------------------------------
// Expression strategy — recursive, with a depth cap of 2 and a leaf
// budget of 12. Bigger trees produce more flakey shrinkers without
// adding much coverage at this grammar size.
// -------------------------------------------------------------------------

pub fn expr_strategy() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        literal_strategy().prop_map(|v| Expr::Lit {
            value: v,
            span: span(),
        }),
        ident_strategy().prop_map(|n| Expr::Ident {
            name: n,
            span: span(),
        }),
    ];

    leaf.prop_recursive(2, 12, 4, |inner| {
        prop_oneof![
            // Array literal
            prop::collection::vec(inner.clone(), 0..3).prop_map(|elements| Expr::Array {
                elements: elements.into_iter().map(Some).collect(),
                span: span(),
            }),

            // Object literal with regular props
            prop::collection::vec((prop_key_strategy(), inner.clone()), 1..3).prop_map(|pairs| {
                // Deduplicate by key so we don't emit `{k: 1, k: 2}` which
                // the parser rejects as a duplicate-property error.
                let mut seen = std::collections::HashSet::new();
                let properties = pairs
                    .into_iter()
                    .filter_map(|(key, value)| {
                        let name = match &key {
                            PropKey::Ident(s) | PropKey::String(s) => s.clone(),
                            PropKey::Number(n) => n.to_string(),
                        };
                        if !seen.insert(name) {
                            return None;
                        }
                        Some(PropDef::Property {
                            key,
                            value,
                            type_annotation: None,
                            span: span(),
                        })
                    })
                    .collect::<Vec<_>>();
                Expr::Object {
                    properties,
                    span: span(),
                }
            }),

            // Member access: obj.prop
            (inner.clone(), prop_key_strategy()).prop_map(|(obj, key)| {
                let property = match key {
                    PropKey::Ident(s) | PropKey::String(s) => s,
                    PropKey::Number(n) => n.to_string(),
                };
                Expr::Member {
                    object: Box::new(obj),
                    property,
                    span: span(),
                }
            }),

            // Binary expression
            (binop_strategy(), inner.clone(), inner.clone()).prop_map(|(op, l, r)| {
                Expr::Binary {
                    op,
                    left: Box::new(l),
                    right: Box::new(r),
                    span: span(),
                }
            }),

            // Unary expression
            inner.clone().prop_map(|arg| Expr::Unary {
                op: UnaryOp::Not,
                argument: Box::new(arg),
                span: span(),
            }),

            // Conditional: a ? b : c
            (inner.clone(), inner.clone(), inner.clone()).prop_map(|(t, c, a)| {
                Expr::Conditional {
                    test: Box::new(t),
                    consequent: Box::new(c),
                    alternate: Box::new(a),
                    span: span(),
                }
            }),

            // Function call. Callee is a bare ident so the pretty-
            // printer doesn't have to parenthesise it — avoids a whole
            // class of round-trip ambiguity issues without losing
            // anything interesting about the inference behaviour.
            (ident_strategy(), prop::collection::vec(inner.clone(), 0..2)).prop_map(
                |(name, args)| Expr::Call {
                    callee: Box::new(Expr::Ident {
                        name,
                        span: span(),
                    }),
                    arguments: args,
                    span: span(),
                }
            ),

            // Function expression with 0-2 parameters and a single
            // return body. Keeping the body trivial (just `return e`)
            // dramatically raises the round-trip success rate — nested
            // control flow inside a function body is its own minefield
            // for pretty-printing and better tested separately.
            (
                prop::collection::vec(ident_strategy(), 0..2),
                inner.clone()
            )
                .prop_map(|(params, body_expr)| {
                    let body = Stmt::Block {
                        body: vec![Stmt::Return {
                            argument: Some(body_expr),
                            span: span(),
                        }],
                        span: span(),
                    };
                    Expr::Function {
                        name: None,
                        params,
                        body: Box::new(body),
                        type_annotation: None,
                        span: span(),
                    }
                }),
        ]
    })
}

// -------------------------------------------------------------------------
// Statement strategy — covers var/const declarations, bare expressions,
// function declarations (with and without `this` use via method-shaped
// bodies), empty statements, and a simple if.
// -------------------------------------------------------------------------

/// True if the first token emitted for this expression would be `{`
/// (object literal) or `function` (function expression). The printer
/// walks the left spine to render, so any binary/conditional/member/
/// call/... rooted at an object or function expression will start with
/// that token too — and at statement position, both parse as something
/// completely different from what we intended. This predicate tells the
/// strategy filter to reject those shapes up front.
fn starts_with_object_or_function(e: &Expr) -> bool {
    match e {
        Expr::Object { .. } | Expr::Function { .. } => true,
        Expr::Binary { left, .. } | Expr::Assign { left, .. } => {
            starts_with_object_or_function(left)
        }
        Expr::Conditional { test, .. } => starts_with_object_or_function(test),
        Expr::Member { object, .. } | Expr::ComputedMember { object, .. } => {
            starts_with_object_or_function(object)
        }
        Expr::Call { callee, .. } => starts_with_object_or_function(callee),
        Expr::Sequence { expressions, .. } => expressions
            .first()
            .map(starts_with_object_or_function)
            .unwrap_or(false),
        Expr::Unary { op, argument, .. } => {
            // Postfix unary operators keep the operand on the left,
            // prefix operators don't.
            use UnaryOp::*;
            matches!(op, PostInc | PostDec) && starts_with_object_or_function(argument)
        }
        _ => false,
    }
}

/// Expressions safe to emit at statement position (see the predicate
/// above for why). Applied wherever a `Stmt::Expr` is synthesised.
fn safe_stmt_expr_strategy() -> impl Strategy<Value = Expr> {
    expr_strategy().prop_filter(
        "expression at statement position must not start with `function` or `{`",
        |e| !starts_with_object_or_function(e),
    )
}

pub fn stmt_strategy() -> impl Strategy<Value = Stmt> {
    prop_oneof![
        // var / const declaration with initialiser
        (
            prop_oneof![Just(VarKind::Var), Just(VarKind::Const)],
            ident_strategy(),
            expr_strategy()
        )
            .prop_map(|(kind, name, init)| {
                Stmt::Var {
                    kind,
                    declarations: vec![VarDeclarator {
                        name,
                        init: Some(init),
                        type_annotation: None,
                        kind,
                        span: span(),
                    }],
                    span: span(),
                }
            }),

        // Bare expression statement (ambiguity-free forms only)
        safe_stmt_expr_strategy().prop_map(|e| Stmt::Expr {
            expression: e,
            span: span(),
        }),

        // Empty statement (`;`)
        Just(Stmt::Empty { span: span() }),

        // Top-level function declaration
        (
            ident_strategy(),
            prop::collection::vec(ident_strategy(), 0..2),
            expr_strategy()
        )
            .prop_map(|(name, params, ret_expr)| {
                Stmt::FunctionDecl {
                    name,
                    params,
                    body: Box::new(Stmt::Block {
                        body: vec![Stmt::Return {
                            argument: Some(ret_expr),
                            span: span(),
                        }],
                        span: span(),
                    }),
                    type_annotation: None,
                    span: span(),
                }
            }),

        // if with only a consequent (same stmt-position restriction)
        (expr_strategy(), safe_stmt_expr_strategy()).prop_map(|(test, body_expr)| {
            Stmt::If {
                test,
                consequent: Box::new(Stmt::Expr {
                    expression: body_expr,
                    span: span(),
                }),
                alternate: None,
                span: span(),
            }
        }),
    ]
}

// -------------------------------------------------------------------------
// Program strategy — 1..6 statements gives the swap test enough material
// to find an independent pair most of the time without bloating the
// shrinking search space.
// -------------------------------------------------------------------------

pub fn program_strategy() -> impl Strategy<Value = Program> {
    prop::collection::vec(stmt_strategy(), 1..6).prop_map(|statements| Program {
        statements,
        span: span(),
    })
}
