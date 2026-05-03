//! Property-based tests for parser round-trip.

use proptest::prelude::*;

use super::ast::*;
use super::pretty::print_program;
use super::Parser;
use crate::lexer::{Scanner, Span};

fn span() -> Span {
    Span::new(0, 0)
}

// Strategy for valid JavaScript identifiers
fn ident_strategy() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z_][a-zA-Z0-9_]{0,5}")
        .unwrap()
        .prop_filter("not a keyword", |s| {
            !matches!(
                s.as_str(),
                "var"
                    | "function"
                    | "if"
                    | "else"
                    | "while"
                    | "do"
                    | "for"
                    | "in"
                    | "of"
                    | "return"
                    | "break"
                    | "continue"
                    | "throw"
                    | "try"
                    | "catch"
                    | "finally"
                    | "switch"
                    | "case"
                    | "default"
                    | "new"
                    | "this"
                    | "typeof"
                    | "void"
                    | "delete"
                    | "instanceof"
                    | "null"
                    | "undefined"
                    | "true"
                    | "false"
                    | "NaN"
                    | "Infinity"
            )
        })
}

// Strategy for simple string content (no escapes needed for round-trip)
fn simple_string_strategy() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z0-9 ]{0,10}").unwrap()
}

// Strategy for numbers that round-trip cleanly
fn number_strategy() -> impl Strategy<Value = f64> {
    prop_oneof![
        // Integers (including negative)
        (-1000i32..1000).prop_map(|n| n as f64),
        // Simple decimals
        (-100i32..100).prop_map(|n| n as f64 / 10.0),
    ]
}

// Strategy for literals
fn literal_strategy() -> impl Strategy<Value = Literal> {
    prop_oneof![
        Just(Literal::Null),
        Just(Literal::Undefined),
        prop::bool::ANY.prop_map(Literal::Boolean),
        number_strategy().prop_map(Literal::Number),
        simple_string_strategy().prop_map(Literal::String),
    ]
}

// Strategy for binary operators
fn binop_strategy() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::Add),
        Just(BinOp::Sub),
        Just(BinOp::Mul),
        Just(BinOp::Div),
        Just(BinOp::Mod),
        Just(BinOp::Lt),
        Just(BinOp::Gt),
        Just(BinOp::LtEq),
        Just(BinOp::GtEq),
        Just(BinOp::EqEq),
        Just(BinOp::NotEq),
        Just(BinOp::EqEqEq),
        Just(BinOp::NotEqEq),
        Just(BinOp::And),
        Just(BinOp::Or),
        Just(BinOp::BitAnd),
        Just(BinOp::BitOr),
        Just(BinOp::BitXor),
        Just(BinOp::LShift),
        Just(BinOp::RShift),
        Just(BinOp::URShift),
    ]
}

// Strategy for unary operators (only simple ones for round-trip)
fn unaryop_strategy() -> impl Strategy<Value = UnaryOp> {
    prop_oneof![
        Just(UnaryOp::Neg),
        Just(UnaryOp::Pos),
        Just(UnaryOp::Not),
        Just(UnaryOp::BitNot),
        Just(UnaryOp::Typeof),
    ]
}

// Recursive expression strategy
fn expr_strategy() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        literal_strategy().prop_map(|lit| Expr::Lit {
            value: lit,
            span: span()
        }),
        ident_strategy().prop_map(|name| Expr::Ident { name, span: span() }),
    ];

    leaf.prop_recursive(3, 16, 4, |inner| {
        prop_oneof![
            // Array literal
            prop::collection::vec(inner.clone(), 0..3).prop_map(|elements| {
                Expr::Array {
                    elements: elements.into_iter().map(Some).collect(),
                    span: span(),
                }
            }),
            // Binary expression
            (binop_strategy(), inner.clone(), inner.clone()).prop_map(|(op, left, right)| {
                Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                    span: span(),
                }
            }),
            // Unary expression
            (unaryop_strategy(), inner.clone()).prop_map(|(op, arg)| {
                Expr::Unary {
                    op,
                    argument: Box::new(arg),
                    span: span(),
                }
            }),
            // Member access
            (inner.clone(), ident_strategy()).prop_map(|(obj, prop)| {
                Expr::Member {
                    object: Box::new(obj),
                    property: prop,
                    span: span(),
                }
            }),
            // Function call (use ident as callee to avoid ambiguity)
            (ident_strategy(), prop::collection::vec(inner.clone(), 0..2)).prop_map(
                |(name, args)| {
                    Expr::Call {
                        callee: Box::new(Expr::Ident { name, span: span() }),
                        arguments: args,
                        span: span(),
                    }
                }
            ),
            // Conditional
            (inner.clone(), inner.clone(), inner.clone()).prop_map(|(test, cons, alt)| {
                Expr::Conditional {
                    test: Box::new(test),
                    consequent: Box::new(cons),
                    alternate: Box::new(alt),
                    span: span(),
                }
            }),
        ]
    })
}

// Strategy for simple statements
fn stmt_strategy() -> impl Strategy<Value = Stmt> {
    let expr_stmt = expr_strategy().prop_map(|e| Stmt::Expr {
        expression: e,
        span: span(),
    });

    let var_stmt =
        (ident_strategy(), prop::option::of(expr_strategy())).prop_map(|(name, init)| Stmt::Var {
            kind: VarKind::Var,
            declarations: vec![VarDeclarator {
                name,
                init,
                type_annotation: None,
                kind: VarKind::Var,
                span: span(),
            }],
            span: span(),
        });

    let return_stmt = prop::option::of(expr_strategy()).prop_map(|arg| Stmt::Return {
        argument: arg,
        span: span(),
    });

    prop_oneof![expr_stmt, var_stmt, return_stmt,]
}

// Strategy for programs
fn program_strategy() -> impl Strategy<Value = Program> {
    prop::collection::vec(stmt_strategy(), 1..4).prop_map(|statements| Program {
        statements,
        span: span(),
    })
}

// Compare expressions structurally (ignoring spans)
fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Lit { value: v1, .. }, Expr::Lit { value: v2, .. }) => literals_equal(v1, v2),

        (Expr::Ident { name: n1, .. }, Expr::Ident { name: n2, .. }) => n1 == n2,

        // undefined literal prints as "undefined" which parses as an identifier
        (
            Expr::Lit {
                value: Literal::Undefined,
                ..
            },
            Expr::Ident { name, .. },
        ) if name == "undefined" => true,
        (
            Expr::Ident { name, .. },
            Expr::Lit {
                value: Literal::Undefined,
                ..
            },
        ) if name == "undefined" => true,

        // Negative number literals parse as Unary(Neg, positive_lit)
        (
            Expr::Lit {
                value: Literal::Number(n),
                ..
            },
            Expr::Unary {
                op: UnaryOp::Neg,
                argument,
                ..
            },
        ) if *n < 0.0 => {
            if let Expr::Lit {
                value: Literal::Number(m),
                ..
            } = argument.as_ref()
            {
                (*n).abs() == *m
            } else {
                false
            }
        }
        (
            Expr::Unary {
                op: UnaryOp::Neg,
                argument,
                ..
            },
            Expr::Lit {
                value: Literal::Number(n),
                ..
            },
        ) if *n < 0.0 => {
            if let Expr::Lit {
                value: Literal::Number(m),
                ..
            } = argument.as_ref()
            {
                (*n).abs() == *m
            } else {
                false
            }
        }

        (Expr::This { .. }, Expr::This { .. }) => true,

        (Expr::Array { elements: e1, .. }, Expr::Array { elements: e2, .. }) => {
            e1.len() == e2.len()
                && e1.iter().zip(e2.iter()).all(|(a, b)| match (a, b) {
                    (Some(x), Some(y)) => exprs_equal(x, y),
                    (None, None) => true,
                    _ => false,
                })
        }

        (
            Expr::Binary {
                op: op1,
                left: l1,
                right: r1,
                ..
            },
            Expr::Binary {
                op: op2,
                left: l2,
                right: r2,
                ..
            },
        ) => op1 == op2 && exprs_equal(l1, l2) && exprs_equal(r1, r2),

        (
            Expr::Unary {
                op: op1,
                argument: a1,
                ..
            },
            Expr::Unary {
                op: op2,
                argument: a2,
                ..
            },
        ) => op1 == op2 && exprs_equal(a1, a2),

        (
            Expr::Member {
                object: o1,
                property: p1,
                ..
            },
            Expr::Member {
                object: o2,
                property: p2,
                ..
            },
        ) => exprs_equal(o1, o2) && p1 == p2,

        (
            Expr::ComputedMember {
                object: o1,
                property: p1,
                ..
            },
            Expr::ComputedMember {
                object: o2,
                property: p2,
                ..
            },
        ) => exprs_equal(o1, o2) && exprs_equal(p1, p2),

        (
            Expr::Call {
                callee: c1,
                arguments: a1,
                ..
            },
            Expr::Call {
                callee: c2,
                arguments: a2,
                ..
            },
        ) => {
            exprs_equal(c1, c2)
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| exprs_equal(x, y))
        }

        (
            Expr::Conditional {
                test: t1,
                consequent: c1,
                alternate: a1,
                ..
            },
            Expr::Conditional {
                test: t2,
                consequent: c2,
                alternate: a2,
                ..
            },
        ) => exprs_equal(t1, t2) && exprs_equal(c1, c2) && exprs_equal(a1, a2),

        (
            Expr::Sequence {
                expressions: e1, ..
            },
            Expr::Sequence {
                expressions: e2, ..
            },
        ) => e1.len() == e2.len() && e1.iter().zip(e2.iter()).all(|(x, y)| exprs_equal(x, y)),

        _ => false,
    }
}

fn literals_equal(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Null, Literal::Null) => true,
        (Literal::Undefined, Literal::Undefined) => true,
        (Literal::Boolean(x), Literal::Boolean(y)) => x == y,
        (Literal::Number(x), Literal::Number(y)) => {
            // Handle NaN and negative zero
            (x.is_nan() && y.is_nan()) || (x == y && x.signum() == y.signum())
        }
        (Literal::String(x), Literal::String(y)) => x == y,
        (
            Literal::Regex {
                pattern: p1,
                flags: f1,
            },
            Literal::Regex {
                pattern: p2,
                flags: f2,
            },
        ) => p1 == p2 && f1 == f2,
        _ => false,
    }
}

fn stmts_equal(a: &Stmt, b: &Stmt) -> bool {
    match (a, b) {
        (Stmt::Empty { .. }, Stmt::Empty { .. }) => true,

        (Stmt::Expr { expression: e1, .. }, Stmt::Expr { expression: e2, .. }) => {
            exprs_equal(e1, e2)
        }

        (
            Stmt::Var {
                declarations: d1, ..
            },
            Stmt::Var {
                declarations: d2, ..
            },
        ) => {
            d1.len() == d2.len()
                && d1.iter().zip(d2.iter()).all(|(x, y)| {
                    x.name == y.name
                        && match (&x.init, &y.init) {
                            (Some(a), Some(b)) => exprs_equal(a, b),
                            (None, None) => true,
                            _ => false,
                        }
                })
        }

        (Stmt::Return { argument: a1, .. }, Stmt::Return { argument: a2, .. }) => match (a1, a2) {
            (Some(x), Some(y)) => exprs_equal(x, y),
            (None, None) => true,
            _ => false,
        },

        (Stmt::Block { body: b1, .. }, Stmt::Block { body: b2, .. }) => {
            b1.len() == b2.len() && b1.iter().zip(b2.iter()).all(|(x, y)| stmts_equal(x, y))
        }

        (
            Stmt::If {
                test: t1,
                consequent: c1,
                alternate: a1,
                ..
            },
            Stmt::If {
                test: t2,
                consequent: c2,
                alternate: a2,
                ..
            },
        ) => {
            exprs_equal(t1, t2)
                && stmts_equal(c1, c2)
                && match (a1, a2) {
                    (Some(x), Some(y)) => stmts_equal(x, y),
                    (None, None) => true,
                    _ => false,
                }
        }

        (
            Stmt::While {
                test: t1, body: b1, ..
            },
            Stmt::While {
                test: t2, body: b2, ..
            },
        ) => exprs_equal(t1, t2) && stmts_equal(b1, b2),

        _ => false,
    }
}

fn programs_equal(a: &Program, b: &Program) -> bool {
    a.statements.len() == b.statements.len()
        && a.statements
            .iter()
            .zip(b.statements.iter())
            .all(|(x, y)| stmts_equal(x, y))
}

fn parse_source(src: &str) -> Result<Program, String> {
    use crate::lexer::Token;

    let mut scanner = Scanner::new(src);
    let mut tokens = Vec::new();

    loop {
        let tok = scanner.next_token().map_err(|e| format!("{:?}", e))?;
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }

    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);
    parser.parse_program().map_err(|e| format!("{:?}", e))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_expr_round_trip(expr in expr_strategy()) {
        // Create a program with a single expression statement
        let program = Program {
            statements: vec![Stmt::Expr { expression: expr.clone(), span: span() }],
            span: span(),
        };

        // Pretty print
        let source = print_program(&program);

        // Parse back
        let parsed = parse_source(&source);

        match parsed {
            Ok(p) => {
                prop_assert!(
                    programs_equal(&program, &p),
                    "Round-trip failed!\nOriginal: {:?}\nSource: {}\nParsed: {:?}",
                    program, source, p
                );
            }
            Err(e) => {
                prop_assert!(false, "Parse failed: {}\nSource: {}", e, source);
            }
        }
    }

    #[test]
    fn prop_stmt_round_trip(stmt in stmt_strategy()) {
        let program = Program {
            statements: vec![stmt.clone()],
            span: span(),
        };

        let source = print_program(&program);
        let parsed = parse_source(&source);

        match parsed {
            Ok(p) => {
                prop_assert!(
                    programs_equal(&program, &p),
                    "Round-trip failed!\nOriginal: {:?}\nSource: {}\nParsed: {:?}",
                    program, source, p
                );
            }
            Err(e) => {
                prop_assert!(false, "Parse failed: {}\nSource: {}", e, source);
            }
        }
    }

    #[test]
    fn prop_program_round_trip(program in program_strategy()) {
        let source = print_program(&program);
        let parsed = parse_source(&source);

        match parsed {
            Ok(p) => {
                prop_assert!(
                    programs_equal(&program, &p),
                    "Round-trip failed!\nOriginal: {:?}\nSource: {}\nParsed: {:?}",
                    program, source, p
                );
            }
            Err(e) => {
                prop_assert!(false, "Parse failed: {}\nSource: {}", e, source);
            }
        }
    }
}
