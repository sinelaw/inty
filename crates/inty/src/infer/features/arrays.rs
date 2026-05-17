//! Array literals and indexing.

use crate::lexer::Span;
use crate::parser::ast::Expr;
use crate::types::{RowTail, TVarName, Type, TypePred};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::InferResult;

impl InferState {
    /// Infer the type of `Expr::RestArray { source, skip }`. The
    /// source must unify with `T[]` for some `T`, and the result is
    /// `T[]` — `[head, ...tail]` always gives `tail` the same
    /// element type as the source array.
    pub(in crate::infer) fn infer_rest_array(
        &mut self,
        env: &TypeEnv,
        source: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let source_ty = self.infer_expr(env, source)?;
        let elem_var = self.fresh_type_var();
        let array_ty = Type::array(elem_var.clone());
        self.unify(span, &source_ty, &array_ty)?;
        Ok(self.zonk(&array_ty))
    }

    /// Infer the type of an array literal.
    ///
    /// Spread elements (`...xs`) require the operand to be `T[]` for
    /// some element type `T`, and `T` joins into the result element
    /// type just like a non-spread element. This means
    /// `[...xs, y]` produces `T[]` with `y : T` enforced; mismatched
    /// element types fail just as for plain literals.
    pub(in crate::infer) fn infer_array(
        &mut self,
        env: &TypeEnv,
        elements: &[Option<Expr>],
        span: Span,
    ) -> InferResult<Type> {
        // Start with a fresh elem-type variable so an empty array still
        // has a polymorphic element type. Each element joins into the
        // accumulator: when elements agree (after unification) we keep a
        // single type; when they don't, the result is a union.
        let mut acc: Type = self.fresh_type_var();

        for elem in elements.iter().flatten() {
            let elem_ty = match elem {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    // The spread operand must be an array; its
                    // element type joins the accumulator.
                    let arg_ty = self.infer_expr(env, argument)?;
                    let elem_var = self.fresh_type_var();
                    let expected = Type::array(elem_var.clone());
                    self.unify(*spread_span, &arg_ty, &expected)?;
                    self.zonk(&elem_var)
                }
                other => self.infer_expr(env, other)?,
            };
            acc = self.join(span, &acc, &elem_ty);
        }

        Ok(Type::array(self.zonk(&acc)))
    }

    /// Infer the type of a computed member access (obj[expr]).
    pub(in crate::infer) fn infer_computed_member(
        &mut self,
        env: &TypeEnv,
        object: &Expr,
        property: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let obj_type = self.infer_expr(env, object)?;
        let index_type = self.infer_expr(env, property)?;

        // Apply substitution to see if we know the object type
        let obj_type_resolved = self.zonk(&obj_type);

        // Union elimination on indexing: index every member and join.
        if let Type::Union(members) = &obj_type_resolved {
            let mut result: Option<Type> = None;
            for m in members {
                let m_resolved = self.zonk(m);
                // We re-derive the index by re-using the same `index_type`
                // expression — it's already been inferred once at the top
                // and unification against multiple member types is fine.
                let idx_ty = self.index_into_type(&m_resolved, &index_type, span)?;
                result = Some(match result {
                    None => idx_ty,
                    Some(acc) => self.join(span, &acc, &idx_ty),
                });
            }
            return Ok(result.unwrap_or_else(Type::never));
        }

        // Try to resolve immediately for known types
        match &obj_type_resolved {
            Type::Array(elem_type) => {
                // Array indexing: immediately unify index with Number and return element type
                self.subsume(span, &index_type, &Type::Number)?;
                Ok(elem_type.as_ref().clone())
            }
            Type::String => {
                // String indexing: returns String
                self.subsume(span, &index_type, &Type::Number)?;
                Ok(Type::String)
            }
            Type::Map(value_type) => {
                // Map indexing: unify index with String and return value type
                self.subsume(span, &index_type, &Type::String)?;
                Ok(value_type.as_ref().clone())
            }
            Type::Row(row) => {
                // Check if this is an array-like row (only has length property and is open)
                let is_array_like = row.props.keys().all(|k| k.0 == "length")
                    && matches!(row.tail, RowTail::Open(_));

                if is_array_like {
                    // Treat as array: create Array type and unify properly
                    let elem_type = self.fresh_type_var();
                    let array_type = Type::array(elem_type.clone());

                    // First verify the row is compatible with array structure
                    self.unify(span, &obj_type_resolved, &array_type)?;

                    // If the original obj_type is a type variable, rebind it to Array
                    // since unify only checked compatibility but didn't update the binding
                    if let Type::Var(var_name @ TVarName::Flex(_)) = &obj_type {
                        self.rebind_var(var_name.clone(), Type::array(elem_type.clone()));
                    }

                    self.subsume(span, &index_type, &Type::Number)?;
                    Ok(elem_type)
                } else {
                    // Regular object: use string indexing
                    self.subsume(span, &index_type, &Type::String)?;
                    let result_type = self.fresh_type_var();
                    self.add_constraint(
                        TypePred::indexable(obj_type, index_type, result_type.clone()),
                        span,
                    );
                    Ok(result_type)
                }
            }
            _ => {
                // Unknown type: defer to constraint resolution
                let result_type = self.fresh_type_var();
                self.add_constraint(
                    TypePred::indexable(obj_type, index_type, result_type.clone()),
                    span,
                );
                Ok(result_type)
            }
        }
    }

    /// Index a single (non-union) type with a known index-type. Used by
    /// `infer_computed_member` to elide indexing through every member of
    /// a union. Mirrors the `match obj_type_resolved` block, minus the
    /// rebind_var hook (which only fires for the top-level variable that
    /// indexed-into-a-union no longer applies to).
    pub(in crate::infer) fn index_into_type(
        &mut self,
        obj_type: &Type,
        index_type: &Type,
        span: Span,
    ) -> InferResult<Type> {
        match obj_type {
            Type::Array(elem_type) => {
                self.subsume(span, index_type, &Type::Number)?;
                Ok(elem_type.as_ref().clone())
            }
            Type::String => {
                self.subsume(span, index_type, &Type::Number)?;
                Ok(Type::String)
            }
            Type::Map(value_type) => {
                self.subsume(span, index_type, &Type::String)?;
                Ok(value_type.as_ref().clone())
            }
            _ => {
                // Defer to the constraint solver for rows / type vars.
                let result_type = self.fresh_type_var();
                self.add_constraint(
                    TypePred::indexable(obj_type.clone(), index_type.clone(), result_type.clone()),
                    span,
                );
                Ok(result_type)
            }
        }
    }
}
