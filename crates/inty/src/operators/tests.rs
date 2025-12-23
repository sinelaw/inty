//! Catalog comprehensiveness and consistency tests.

use super::*;
use crate::parser::ast::{BinOp, UnaryOp};

/// Every BinOp variant — kept in sync with the AST by the
/// `binops_exhaustive` match below, which fails to compile if a new
/// variant is added without being listed here.
const ALL_BINOPS: &[BinOp] = &[
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::Mod,
    BinOp::Pow,
    BinOp::Lt,
    BinOp::Gt,
    BinOp::LtEq,
    BinOp::GtEq,
    BinOp::EqEq,
    BinOp::NotEq,
    BinOp::EqEqEq,
    BinOp::NotEqEq,
    BinOp::And,
    BinOp::Or,
    BinOp::BitAnd,
    BinOp::BitOr,
    BinOp::BitXor,
    BinOp::LShift,
    BinOp::RShift,
    BinOp::URShift,
    BinOp::In,
    BinOp::Instanceof,
];

const ALL_UNARYOPS: &[UnaryOp] = &[
    UnaryOp::Neg,
    UnaryOp::Pos,
    UnaryOp::Not,
    UnaryOp::BitNot,
    UnaryOp::Typeof,
    UnaryOp::Void,
    UnaryOp::Delete,
    UnaryOp::Await,
    UnaryOp::PreInc,
    UnaryOp::PreDec,
    UnaryOp::PostInc,
    UnaryOp::PostDec,
];

/// Compile-time exhaustiveness check: if a new BinOp variant is added,
/// this match will fail to compile, prompting the author to update
/// `ALL_BINOPS` and the catalog.
fn binops_exhaustive(op: BinOp) {
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::Pow
        | BinOp::Lt
        | BinOp::Gt
        | BinOp::LtEq
        | BinOp::GtEq
        | BinOp::EqEq
        | BinOp::NotEq
        | BinOp::EqEqEq
        | BinOp::NotEqEq
        | BinOp::And
        | BinOp::Or
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor
        | BinOp::LShift
        | BinOp::RShift
        | BinOp::URShift
        | BinOp::In
        | BinOp::Instanceof => {}
    }
}

fn unaryops_exhaustive(op: UnaryOp) {
    match op {
        UnaryOp::Neg
        | UnaryOp::Pos
        | UnaryOp::Not
        | UnaryOp::BitNot
        | UnaryOp::Typeof
        | UnaryOp::Void
        | UnaryOp::Delete
        | UnaryOp::Await
        | UnaryOp::PreInc
        | UnaryOp::PreDec
        | UnaryOp::PostInc
        | UnaryOp::PostDec => {}
    }
}

#[test]
fn comprehensive() {
    // Reference the exhaustiveness checkers so they're not dead code.
    binops_exhaustive(BinOp::Add);
    unaryops_exhaustive(UnaryOp::Not);

    for &op in ALL_BINOPS {
        let name = binop_name(op);
        let entry = lookup(name).unwrap_or_else(|| {
            panic!("BinOp::{:?} (catalog name {:?}) has no catalog entry", op, name)
        });
        assert_eq!(entry.kind, OpKind::BinOp, "{:?} should be BinOp", op);
        assert!(
            !entry.arms.is_empty(),
            "{:?} should have at least one typing arm",
            op
        );
    }

    for &op in ALL_UNARYOPS {
        let name = unaryop_name(op);
        let entry = lookup(name).unwrap_or_else(|| {
            panic!(
                "UnaryOp::{:?} (catalog name {:?}) has no catalog entry",
                op, name
            )
        });
        assert_eq!(entry.kind, OpKind::UnOp, "{:?} should be UnOp", op);
        assert!(
            !entry.arms.is_empty(),
            "{:?} should have at least one typing arm",
            op
        );
    }

    // Pseudo-operators: member access, indexing, call, new.
    for (name, kind) in [
        (".", OpKind::MemberAccess),
        ("[]", OpKind::Index),
        ("()", OpKind::Call),
        ("new", OpKind::New),
    ] {
        let entry =
            lookup(name).unwrap_or_else(|| panic!("pseudo-op {:?} has no catalog entry", name));
        assert_eq!(entry.kind, kind, "pseudo-op {:?} kind mismatch", name);
        assert!(!entry.arms.is_empty());
    }
}

#[test]
fn names_are_unique() {
    let mut seen: Vec<&'static str> = Vec::with_capacity(OPERATORS.len());
    for op in OPERATORS {
        assert!(
            !seen.contains(&op.name),
            "duplicate catalog entry for name {:?}",
            op.name
        );
        seen.push(op.name);
    }
}

#[test]
fn typing_arm_indices_are_in_range() {
    // Every SameAsArg(N) must reference a valid input position.
    for op in OPERATORS {
        for arm in op.arms {
            let arity = arm.inputs.len();
            for input in arm.inputs {
                if let TypeShape::SameAsArg(n) = input {
                    assert!(
                        *n < arity,
                        "{}: input SameAsArg({}) out of range (arity {})",
                        op.name,
                        n,
                        arity
                    );
                }
            }
            if let TypeShape::SameAsArg(n) = arm.output {
                assert!(
                    n < arity,
                    "{}: output SameAsArg({}) out of range (arity {})",
                    op.name,
                    n,
                    arity
                );
            }
        }
    }
}

#[test]
fn classes_match_arm_metadata() {
    // If the arm has `class: Some(c)`, at least one input or the
    // output should reference that class via AnyOfClass(c).
    for op in OPERATORS {
        for arm in op.arms {
            if let Some(class) = arm.class {
                let mentions_class = arm
                    .inputs
                    .iter()
                    .chain(std::iter::once(&arm.output))
                    .any(|s| matches!(s, TypeShape::AnyOfClass(c) if *c == class));
                assert!(
                    mentions_class,
                    "{}: arm declares class {:?} but no input/output references it",
                    op.name, class
                );
            }
        }
    }
}
