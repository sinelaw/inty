//! Inference rules for nullish coalescing (`??`) and optional
//! chaining (`?.` / `?.()` / `?.[k]`).
//!
//! ## `a ?? b`
//!
//! With `a : T | Null | Undefined`, the result is
//! `(T \ {Null, Undefined}) ∪ typeof b`. The right operand is type-
//! checked even when the left isn't nullable — its result type is
//! still unioned in, but if `a` can never be nullish then the union
//! is just `T`.
//!
//! ## `a?.b`, `a?.()`, `a?.[k]`
//!
//! With `a : T | Null | Undefined`, the result is `T_b | Undefined`
//! where `T_b` is the type of the access against the non-nullish
//! part of `a`'s type. If `a` isn't nullable, no `Undefined` is
//! introduced — `?.` types identically to `.`. The whole chain is a
//! single AST node so once any optional segment fires, the rest of
//! the chain inherits the `Undefined` carry.

use crate::infer::{InferResult, InferState, TypeEnv};
use crate::span::Span;
use crate::ast::{ChainSegment, Expr};
use crate::types::Type;

impl InferState {
    /// Infer `a ?? b`.
    pub(in crate::infer) fn infer_nullish_coalesce(
        &mut self,
        env: &TypeEnv,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let left_ty = self.infer_expr(env, left)?;
        let right_ty = self.infer_expr(env, right)?;
        let left_resolved = self.zonk(&left_ty);

        let (non_nullish, had_nullish) = strip_nullish(&left_resolved);
        if had_nullish {
            // Right side is reachable; union it in. If the non-nullish
            // part is `never` (LHS was purely nullish), `join` collapses
            // to RHS's type.
            Ok(self.join(span, &non_nullish, &right_ty))
        } else {
            // Right side is unreachable. We type-checked it for
            // well-formedness; the result is just the LHS type.
            Ok(left_resolved)
        }
    }

    /// Infer an optional-chain expression.
    pub(in crate::infer) fn infer_optional_chain(
        &mut self,
        env: &TypeEnv,
        head: &Expr,
        segments: &[ChainSegment],
        span: Span,
    ) -> InferResult<Type> {
        let head_ty = self.infer_expr(env, head)?;
        let head_resolved = self.zonk(&head_ty);
        let (mut current, head_was_nullable) = strip_nullish(&head_resolved);

        // The chain's result is `T_last | Undefined` only when at
        // least one optional segment encounters a nullable carrier
        // (or the head was nullable AND the first segment is
        // optional — otherwise the head's nullability would error
        // at the first non-optional access). A non-nullable carrier
        // makes `?.X` provably unreachable, so it doesn't widen.
        let mut may_short_circuit = false;
        let mut prev_was_nullable = head_was_nullable;

        for seg in segments {
            // Peel any nullishness off the running carrier. After the
            // first optional fires, subsequent steps see the
            // non-null tail; non-optional steps inherit whether
            // earlier optional fires occurred via
            // `may_short_circuit`.
            let (carrier, _) = strip_nullish(&current);

            let optional = matches!(
                seg,
                ChainSegment::Member { optional: true, .. }
                    | ChainSegment::Computed { optional: true, .. }
                    | ChainSegment::Call { optional: true, .. }
            );

            if optional && prev_was_nullable {
                may_short_circuit = true;
            }

            match seg {
                ChainSegment::Member {
                    property,
                    span: seg_span,
                    ..
                } => {
                    current = self.infer_member_on_type(&carrier, property, *seg_span)?;
                }
                ChainSegment::Computed {
                    property,
                    span: seg_span,
                    ..
                } => {
                    let key_ty = self.infer_expr(env, property)?;
                    current = self.index_into_type(&carrier, &key_ty, *seg_span)?;
                }
                ChainSegment::Call {
                    arguments,
                    span: seg_span,
                    ..
                } => {
                    let mut arg_types = Vec::with_capacity(arguments.len());
                    for a in arguments {
                        arg_types.push(self.infer_expr(env, a)?);
                    }
                    current = self.call_on_type(&carrier, &arg_types, *seg_span)?;
                }
            }

            // The next segment sees the result of this step. It is
            // nullable iff this step itself produced a nullable
            // carrier (e.g. an `Array.prototype.find` call returning
            // `T | Undefined`).
            let (_, next_nullable) = strip_nullish(&current);
            prev_was_nullable = next_nullable;
        }

        let _ = span;
        if may_short_circuit {
            Ok(join_with_undefined(&current))
        } else {
            Ok(current)
        }
    }

    /// Function call against a concrete carrier type. The carrier
    /// must unify with `(arg_types) => result`.
    fn call_on_type(
        &mut self,
        carrier: &Type,
        arg_types: &[Type],
        span: Span,
    ) -> InferResult<Type> {
        let result = self.fresh_type_var();
        // Expected callable shape — open callable row so the carrier
        // can be any function-like value (plain function or
        // constructor with statics). See state.rs::callable_row_open.
        let expected = self.callable_row_open(None, arg_types.to_vec(), result.clone());
        self.unify(span, carrier, &expected)?;
        Ok(self.zonk(&result))
    }
}

/// Strip `Null` and `Undefined` from a type. Returns `(non_nullish,
/// had_any_nullish_member)`. If the type is itself `Null` or
/// `Undefined`, the non-nullish part is the empty union (`never`).
fn strip_nullish(ty: &Type) -> (Type, bool) {
    match ty {
        Type::Null | Type::Undefined => (Type::never(), true),
        Type::Union(members) => {
            let mut kept = Vec::with_capacity(members.len());
            let mut had = false;
            for m in members {
                if matches!(m, Type::Null | Type::Undefined) {
                    had = true;
                } else {
                    kept.push(m.clone());
                }
            }
            (Type::union(kept), had)
        }
        _ => (ty.clone(), false),
    }
}

/// Union `T` with `Undefined`. Idempotent if `T` already contains
/// `Undefined`.
fn join_with_undefined(ty: &Type) -> Type {
    let mut members = match ty.clone() {
        Type::Union(ms) => ms,
        other => vec![other],
    };
    if !members.iter().any(|m| matches!(m, Type::Undefined)) {
        members.push(Type::Undefined);
    }
    Type::union(members)
}
