//! Unary and binary operators.

use crate::ast::{BinOp, Expr, UnaryOp};
use crate::error::TypeError;
use crate::span::Span;
use crate::types::{LitValue, Type};

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
        let arg_type = if matches!(
            op,
            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec
        ) {
            self.infer_store_target(env, argument, span, false)?
        } else {
            self.infer_expr(env, argument)?
        };

        match op {
            // `-3` is the literal `-3`.
            UnaryOp::Neg if matches!(arg_type, Type::Literal(LitValue::Number(_))) => {
                let Type::Literal(LitValue::Number(n)) = arg_type else {
                    unreachable!()
                };
                Ok(Type::Literal(LitValue::Number(-n)))
            }
            UnaryOp::Neg | UnaryOp::Pos => {
                self.require_num(span, &arg_type)?;
                Ok(Type::Number)
            }

            UnaryOp::Not => {
                // ! works on any type, returns boolean
                self.reject_promise_test(&arg_type, argument.span())?;
                Ok(Type::Boolean)
            }

            // Bitwise operators work on 32-bit integers.
            UnaryOp::BitNot => {
                self.require_num(span, &arg_type)?;
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
                self.require_num(span, &arg_type)?;
                Ok(Type::Number)
            }

            UnaryOp::Await => {
                // `await e` unwraps `Promise<T>` to `T`. A fresh inner type
                // variable lets the unification succeed even when the
                // argument's type is still a bare variable at this point;
                // the shape `Promise<T>` pins it down either way.
                let inner = self.fresh_type_var();
                self.unify(span, &arg_type, &Type::promise(inner.clone()))?;
                Ok(self.zonk_head_into(inner))
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
        if matches!(op, BinOp::And | BinOp::Or) {
            self.reject_promise_test(&left_type, left.span())?;
        }
        // The right operand of `&&` runs only when the left is truthy,
        // that of `||` only when it is falsy: `node !== null && node.ok`.
        let right_type = match op {
            BinOp::And | BinOp::Or => {
                let right_env = self.env_given(env, left, matches!(op, BinOp::And));
                self.infer_expr(&right_env, right)?
            }
            _ => self.infer_expr(env, right)?,
        };

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
            // Arithmetic: numbers in, a number out.
            BinOp::Sub | BinOp::Mul | BinOp::Mod | BinOp::FloorDiv | BinOp::Div | BinOp::Pow => {
                self.arith(span, &left_type, &right_type)
            }

            // Plus is overloaded (Number or String)
            BinOp::Add => {
                // Widen operands first so `1 + 2` resolves to Number
                // rather than getting pinned to `Lit(1)` by the first
                // subsume and then failing the second. The result of
                // `+` is the operand's *base* type — the singleton
                // is meaningless once arithmetic happens.
                let left_widened = self.widen(span, &left_type);
                let right_widened = self.widen(span, &right_type);
                self.unify_operands(span, (&left_widened, left), (&right_widened, right))?;
                self.infer_add(span, &left_widened, &right_widened)
            }

            // Comparison (return boolean): of two numbers or of two
            // strings, as `+` takes them (`Plus`), and nothing else.
            // JavaScript compares any two values after coercing them
            // (`"10" < 9`, `true < 2`, `[2] < [10]`); inty is stricter
            // and takes no coercion. Both are widened to their base
            // first, so `1 < 2` doesn't unify `Lit(1) ~ Lit(2)`.
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                let left_widened = self.widen(span, &left_type);
                let right_widened = self.widen(span, &right_type);
                self.unify_operands(span, (&left_widened, left), (&right_widened, right))?;
                self.resolve_plus(&left_widened, span)?;
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
                    // Heads only: an operand may be large (a DOM element).
                    let left_subst = self.zonk_head(&left_type);
                    let right_subst = self.zonk_head(&right_type);

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
                // With both types known, the result is what can come
                // out: `a && b` is `a` when `a` is falsy, else `b`;
                // `a || b` is `a` when it is truthy, else `b`. So
                // `cond && maybeObj` is `Boolean | Undefined | {…}` and
                // `name || "Guest"` a `String`. (With an unknown side
                // they must agree, as before: nothing is guessed.)
                let (l, r) = (self.zonk_arms(&left_type), self.zonk_head(&right_type));
                if !matches!(l, Type::Var(_)) && !matches!(r, Type::Var(_)) {
                    if let Some(part) = logical_part(&l, matches!(op, BinOp::Or)) {
                        return Ok(match part {
                            Type::Union(ref m) if m.is_empty() => r,
                            part => self.union_of(span, &part, &r),
                        });
                    }
                }
                let op_name = if matches!(op, BinOp::And) { "&&" } else { "||" };
                if let Err(mut err) = self.subsume_either(span, &left_type, &right_type) {
                    // Add helpful context about the && or || operator
                    if let Some(TypeError::UnificationError { context, .. }) = err.as_type_mut() {
                        let msg = [
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
                Ok(self.zonk_head_into(left_type))
            }

            // Bitwise
            BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::LShift
            | BinOp::RShift
            | BinOp::URShift => {
                self.require_num(span, &left_type)?;
                self.require_num(span, &right_type)?;
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

    /// `left + right` (operands widened): both operands have one type,
    /// the result's, which has `+` (`Plus`): a number or a string, so
    /// `1 + "a"` is rejected; on a variable the constraint waits.
    /// The two operands of `+` or a comparison have one type. Neither
    /// side is what the other is expected to be, but a value that may be
    /// nothing (`T | Null`) is never what an operator takes: when one
    /// operand is such a sum and the other isn't, the sum is what's found
    /// (`expected 'Number', found 'Number | Null'`), at that operand,
    /// whichever side it is on.
    fn unify_operands(
        &mut self,
        span: Span,
        (left, left_expr): (&Type, &Expr),
        (right, right_expr): (&Type, &Expr),
    ) -> InferResult<()> {
        let nullable = |s: &mut Self, t: &Type| matches!(s.zonk_head(t), Type::Maybe(..));
        match (nullable(self, left), nullable(self, right)) {
            (true, false) => self.unify(left_expr.span(), right, left)?,
            (false, true) => self.unify(right_expr.span(), left, right)?,
            _ => self.unify(span, left, right)?,
        }
        Ok(())
    }

    pub(in crate::infer) fn infer_add(
        &mut self,
        span: Span,
        left: &Type,
        right: &Type,
    ) -> InferResult<Type> {
        self.unify(span, left, right)?;
        self.resolve_plus(left, span)?;
        Ok(self.zonk_head(left))
    }
}

/// The part of `ty` that `a && b` (`truthy = false`: the falsy values) or
/// `a || b` (`truthy = true`: the truthy values) returns as `a` itself.
/// `None` when a part of `ty` isn't known yet.
fn logical_part(ty: &Type, truthy: bool) -> Option<Type> {
    let members = ty.arms();
    let mut kept = Vec::new();
    for m in members {
        let keep = match &m {
            Type::Var(_) | Type::Error => return None,
            Type::Null | Type::Undefined => !truthy,
            Type::Literal(LitValue::Bool(b)) => *b == truthy,
            Type::Literal(LitValue::Number(n)) => (*n != 0.0 && !n.is_nan()) == truthy,
            Type::Literal(LitValue::String(s)) => s.is_empty() != truthy,
            // Either way.
            Type::Boolean | Type::Number | Type::String => true,
            // Objects, arrays, functions, promises, … are always truthy.
            _ => truthy,
        };
        if keep {
            kept.push(m);
        }
    }
    Some(match kept.len() {
        0 => Type::never(),
        1 => kept.pop().expect("one"),
        _ => InferState::normalise_union_members(kept),
    })
}
