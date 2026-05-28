//! Scalar literals and template literals.

use crate::ast::{Expr, Literal};
use crate::span::Span;
use crate::types::Type;

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::InferResult;

impl InferState {
    /// Infer the type of a literal.
    pub(in crate::infer) fn infer_literal(
        &mut self,
        lit: &Literal,
        span: Span,
    ) -> InferResult<Type> {
        // Synthesise singleton types for primitive literals. Widening
        // to `Number`/`String`/`Boolean` happens at well-defined
        // binding sites (var/let without annotation, function returns,
        // operator results, joined array elements) — see
        // `Type::widen_fresh_literals`. Keeping the singleton at
        // synthesis lets contextual subsume rules (S-UnionR, row-arm
        // matching) see the literal value, which closes a soundness
        // gap where `String` could flow into a position expecting
        // `Lit(s)` via the (now-removed) symmetric base-vs-literal
        // unification rule.
        let ty = match lit {
            Literal::Null => Type::Null,
            Literal::Undefined => Type::Undefined,
            Literal::Boolean(b) => Type::lit_bool(*b),
            Literal::Number(n) => Type::lit_number(*n),
            Literal::String(s) => Type::lit_string(s.clone()),
            Literal::Regex { .. } => Type::Regex,
        };

        // Record origin for type variables (though primitives won't have vars)
        if let Type::Var(var) = &ty {
            self.record_origin(
                var.clone(),
                crate::error::TypeOrigin::Literal {
                    value: format!("{:?}", lit),
                    span,
                },
            );
        }

        Ok(ty)
    }

    /// Infer the type of a template literal.
    /// Template literals always evaluate to String.
    /// All interpolated expressions must be convertible to String (we just check them).
    pub(in crate::infer) fn infer_template_literal(
        &mut self,
        env: &TypeEnv,
        expressions: &[Expr],
        _span: Span,
    ) -> InferResult<Type> {
        // Infer the type of each interpolated expression
        // In JavaScript, any value can be converted to string via template literal
        for expr in expressions {
            self.infer_expr(env, expr)?;
        }
        // Template literals always produce String
        Ok(Type::String)
    }
}
