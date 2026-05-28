//! Unary and binary operators.

use crate::ast::{BinOp, Expr, UnaryOp};
use crate::error::{IntyError, TypeError};
use crate::span::Span;
use crate::types::{Type, TypePred};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::InferResult;

impl InferState {
    /// Infer the type of a unary expression.
    pub(in crate::infer) fn infer_unary(
        &mut self,
        env: &TypeEnv,
        op: UnaryOp,
        argument: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let arg_type = self.infer_expr(env, argument)?;

        match op {
            UnaryOp::Neg | UnaryOp::Pos => {
                self.subsume(span, &arg_type, &Type::Number)?;
                Ok(Type::Number)
            }

            UnaryOp::Not => {
                // ! works on any type, returns boolean
                Ok(Type::Boolean)
            }

            UnaryOp::BitNot => {
                self.subsume(span, &arg_type, &Type::Number)?;
                Ok(Type::Number)
            }

            UnaryOp::Typeof => {
                // typeof works on any type, returns string
                Ok(Type::String)
            }

            UnaryOp::Void => {
                // void evaluates expr and returns undefined
                Ok(Type::Undefined)
            }

            UnaryOp::Delete => {
                // `delete o.k` has no sound counterpart in inty's row
                // algebra: a successful delete leaves `o`'s static row
                // unchanged, so a later read of `o.k` would pass
                // type-checking but fail at runtime. Emit a soft
                // diagnostic at the delete site and return
                // `Type::Error`, which is absorbed by anything
                // downstream (member access, calls, type-class
                // constraints) and prevents the spurious "well-typed"
                // signal that pure parse-acceptance would imply. The
                // diagnostic joins `state.errors`; inference of the
                // surrounding statement still succeeds so the rest of
                // the file gets checked.
                let _ = arg_type;
                self.push_error(
                    TypeError::InvalidSyntax {
                        message: "delete is not supported — construct a new \
                            object literal omitting the field instead, e.g. \
                            `const { a: _drop, ...rest } = o;`"
                            .to_string(),
                        span,
                    }
                    .into(),
                );
                Ok(Type::Error)
            }

            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
                self.subsume(span, &arg_type, &Type::Number)?;
                Ok(Type::Number)
            }

            UnaryOp::Await => {
                // `await e` unwraps `Promise<T>` to `T`. A fresh inner type
                // variable lets the unification succeed even when the
                // argument's type is still a bare variable at this point;
                // the shape `Promise<T>` pins it down either way.
                let inner = self.fresh_type_var();
                self.unify(span, &arg_type, &Type::promise(inner.clone()))?;
                Ok(self.zonk(&inner))
            }
        }
    }

    /// Infer the type of a binary expression.
    pub(in crate::infer) fn infer_binary(
        &mut self,
        env: &TypeEnv,
        op: BinOp,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let left_type = self.infer_expr(env, left)?;
        let right_type = self.infer_expr(env, right)?;

        // Record origins for the operands
        let op_str = format!("{:?}", op);
        if let Type::Var(var) = &left_type {
            if !self.type_origins.contains_key(var) {
                self.record_origin(
                    var.clone(),
                    crate::error::TypeOrigin::BinaryOp {
                        operator: op_str.clone(),
                        side: "left".to_string(),
                        span,
                    },
                );
            }
        }
        if let Type::Var(var) = &right_type {
            if !self.type_origins.contains_key(var) {
                self.record_origin(
                    var.clone(),
                    crate::error::TypeOrigin::BinaryOp {
                        operator: op_str.clone(),
                        side: "right".to_string(),
                        span,
                    },
                );
            }
        }

        match op {
            // `/` dispatches through the `Div` typeclass. Same shape
            // as `+` (Plus): widen, mint a result var, post the
            // class predicate, subsume both operands into it. The
            // solver checks the resulting type is Number at the end
            // of inference; an unresolved type variable stays
            // polymorphic.
            BinOp::Div => {
                let left_widened = left_type.widen_fresh_literals();
                let right_widened = right_type.widen_fresh_literals();
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::div(result.clone()), span);
                self.subsume(span, &left_widened, &result)?;
                self.subsume(span, &right_widened, &result)?;
                Ok(self.zonk(&result))
            }

            // Arithmetic (require numbers)
            BinOp::Sub | BinOp::Mul | BinOp::Mod | BinOp::Pow => {
                self.subsume(span, &left_type, &Type::Number)?;
                self.subsume(span, &right_type, &Type::Number)?;
                Ok(Type::Number)
            }

            // Plus is overloaded (Number or String)
            BinOp::Add => {
                // Widen operands first so `1 + 2` resolves to Number
                // rather than getting pinned to `Lit(1)` by the first
                // subsume and then failing the second. The result of
                // `+` is the operand's *base* type — the singleton
                // is meaningless once arithmetic happens.
                let left_widened = left_type.widen_fresh_literals();
                let right_widened = right_type.widen_fresh_literals();
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::plus(result.clone()), span);
                self.subsume(span, &left_widened, &result)?;
                self.subsume(span, &right_widened, &result)?;
                Ok(self.zonk(&result))
            }

            // Comparison (return boolean). The two operands need to
            // sit in a common type so the comparison is well-defined.
            // Widen both to their base first so `1 < 2` doesn't try
            // to unify `Lit(1) ~ Lit(2)`, then check that one
            // subsumes into the other (either direction is fine —
            // `String < "a"` is meaningful in both orders).
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                let left_widened = left_type.widen_fresh_literals();
                let right_widened = right_type.widen_fresh_literals();
                self.subsume_either(span, &left_widened, &right_widened)?;
                Ok(Type::Boolean)
            }

            // Equality
            BinOp::EqEq | BinOp::NotEq | BinOp::EqEqEq | BinOp::NotEqEq => {
                // Equality works on any types (but should be same for ===)
                if matches!(op, BinOp::EqEqEq | BinOp::NotEqEq) {
                    // Before unifying, record comparison origins for both sides
                    let op_str = if matches!(op, BinOp::EqEqEq) {
                        "==="
                    } else {
                        "!=="
                    };

                    // Apply substitution to get the actual type variables
                    let left_subst = self.zonk(&left_type);
                    let right_subst = self.zonk(&right_type);

                    // If left side is a variable, record comparison origin
                    if let Type::Var(var) = &left_subst {
                        self.record_origin(
                            var.clone(),
                            crate::error::TypeOrigin::Comparison {
                                operator: op_str.to_string(),
                                compared_to: right_subst.to_string(),
                                span,
                            },
                        );
                    }

                    // If right side is a variable and left side is a concrete type, record comparison origin
                    if let Type::Var(var) = &right_subst {
                        self.record_origin(
                            var.clone(),
                            crate::error::TypeOrigin::Comparison {
                                operator: op_str.to_string(),
                                compared_to: left_subst.to_string(),
                                span,
                            },
                        );
                    }

                    // `===` is total in JavaScript: comparing values
                    // of disjoint types simply returns `false`.
                    // Trying to enforce a "common type" via
                    // subsume_either would reject `Lit("a") ===
                    // Lit("b")` even though it's perfectly
                    // well-defined (always false). The narrowing
                    // analysis already emits an "always false"
                    // warning for such cases — see
                    // `warn_if_narrowing_unreachable`. So we don't
                    // type-check the operands here; we just make
                    // sure both sides type-check on their own
                    // (which they did above) and produce Boolean.
                    let _ = (left_subst, right_subst);
                }
                Ok(Type::Boolean)
            }

            // Logical
            BinOp::And | BinOp::Or => {
                // && and || return one of their operands.
                // Widen first so `true && false` doesn't try to
                // unify `Lit(true) ~ Lit(false)`.
                let left_type = left_type.widen_fresh_literals();
                let right_type = right_type.widen_fresh_literals();
                let op_name = if matches!(op, BinOp::And) { "&&" } else { "||" };
                if let Err(mut err) = self.subsume_either(span, &left_type, &right_type) {
                    // Add helpful context about the && or || operator
                    if let IntyError::Type(TypeError::UnificationError { context, .. }) = &mut err {
                        let msg = vec![
                            format!("In JavaScript, `{}` returns one of its operands", op_name),
                            "(not a boolean), so both operands must have".to_string(),
                            "compatible types.".to_string(),
                            "".to_string(),
                            format!("Left side has type:  {}", left_type),
                            format!("Right side has type: {}", right_type),
                            "".to_string(),
                            "These types cannot be unified.".to_string(),
                        ]
                        .join("\n");
                        *context = Some(msg);
                    }
                    return Err(err);
                }
                Ok(self.zonk(&left_type))
            }

            // Bitwise
            BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::LShift
            | BinOp::RShift
            | BinOp::URShift => {
                self.subsume(span, &left_type, &Type::Number)?;
                self.subsume(span, &right_type, &Type::Number)?;
                Ok(Type::Number)
            }

            // Membership
            BinOp::In => {
                // left in right: left is string/number, right is object
                Ok(Type::Boolean)
            }

            BinOp::Instanceof => {
                // expr instanceof Constructor
                Ok(Type::Boolean)
            }
        }
    }
}
