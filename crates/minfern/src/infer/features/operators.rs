//! Unary and binary operators.

use crate::error::{MinfernError, TypeError};
use crate::lexer::Span;
use crate::parser::ast::{BinOp, Expr, UnaryOp};
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
                self.unify(span, &arg_type, &Type::Number)?;
                Ok(Type::Number)
            }

            UnaryOp::Not => {
                // ! works on any type, returns boolean
                Ok(Type::Boolean)
            }

            UnaryOp::BitNot => {
                self.unify(span, &arg_type, &Type::Number)?;
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
                // delete returns boolean
                Ok(Type::Boolean)
            }

            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
                self.unify(span, &arg_type, &Type::Number)?;
                Ok(Type::Number)
            }

            UnaryOp::Await => {
                // `await e` unwraps `Promise<T>` to `T`. A fresh inner type
                // variable lets the unification succeed even when the
                // argument's type is still a bare variable at this point;
                // the shape `Promise<T>` pins it down either way.
                let inner = self.fresh_type_var();
                self.unify(span, &arg_type, &Type::promise(inner.clone()))?;
                Ok(self.apply_subst(&inner))
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
            // Arithmetic (require numbers)
            BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod | BinOp::Pow => {
                self.unify(span, &left_type, &Type::Number)?;
                self.unify(span, &right_type, &Type::Number)?;
                Ok(Type::Number)
            }

            // Plus is overloaded (Number or String)
            BinOp::Add => {
                // Both operands must have the same Plus type
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::plus(result.clone()), span);
                self.unify(span, &left_type, &result)?;
                self.unify(span, &right_type, &result)?;
                Ok(self.apply_subst(&result))
            }

            // Comparison (return boolean)
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                // Comparisons work on numbers and strings
                self.unify(span, &left_type, &right_type)?;
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
                    let left_subst = self.apply_subst(&left_type);
                    let right_subst = self.apply_subst(&right_type);

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

                    self.unify(span, &left_type, &right_type)?;
                }
                Ok(Type::Boolean)
            }

            // Logical
            BinOp::And | BinOp::Or => {
                // && and || return one of their operands
                // For type inference, we unify them and return that type
                let op_name = if matches!(op, BinOp::And) { "&&" } else { "||" };
                if let Err(mut err) = self.unify(span, &left_type, &right_type) {
                    // Add helpful context about the && or || operator
                    if let MinfernError::Type(TypeError::UnificationError { context, .. }) =
                        &mut err
                    {
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
                Ok(self.apply_subst(&left_type))
            }

            // Bitwise
            BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::LShift
            | BinOp::RShift
            | BinOp::URShift => {
                self.unify(span, &left_type, &Type::Number)?;
                self.unify(span, &right_type, &Type::Number)?;
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
