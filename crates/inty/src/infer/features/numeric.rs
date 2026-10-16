//! Numbers: one type, `Number`, as in JavaScript.
//!
//! Whether a number is an integer is not a matter of types. A code
//! generator that wants machine integers (the Go backend) works out which
//! numbers always hold integers by an analysis of its own, which can't
//! reject a program.

use crate::span::Span;
use crate::types::{LitValue, Type};

use super::super::state::InferState;
use super::super::InferResult;

impl InferState {
    /// An operand's type with its literal types widened (`1` to `Number`).
    pub(crate) fn widen(&mut self, _span: Span, ty: &Type) -> Type {
        ty.widen_fresh_literals()
    }

    /// Whether `ty` is known to be a number: `Number` or a number literal.
    pub(crate) fn is_numeric(&mut self, ty: &Type) -> bool {
        matches!(
            self.zonk_head(ty),
            Type::Number | Type::Literal(LitValue::Number(_))
        )
    }

    /// `ty` must be a number.
    pub(crate) fn require_num(&mut self, span: Span, ty: &Type) -> InferResult<()> {
        match self.zonk_head(ty) {
            Type::Number | Type::Literal(LitValue::Number(_)) | Type::Error => Ok(()),
            // (A literal of another type is reported by its base type.)
            other => self.subsume(span, &other.widen_fresh_literals(), &Type::Number),
        }
    }

    /// The type of `left ∘ right` for an arithmetic operator: both are
    /// numbers, and so is the result.
    pub(crate) fn arith(&mut self, span: Span, left: &Type, right: &Type) -> InferResult<Type> {
        self.require_num(span, left)?;
        self.require_num(span, right)?;
        Ok(Type::Number)
    }
}
