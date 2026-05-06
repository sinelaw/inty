//! Object literals, member access, and row polymorphism.

use std::collections::BTreeMap;

use crate::lexer::Span;
use crate::parser::ast::{Expr, PropDef, PropKey};
use crate::types::{PropName, RowTail, RowType, TVarId, TVarName, Type, TypeScheme};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::type_parser::parse_type_annotation;
use super::super::InferResult;

impl InferState {
    /// Infer the type of an object literal.
    ///
    /// Properties are walked in source order. Object spreads
    /// (`...expr`) merge the spread argument's row in right-bias
    /// fashion: keys later in source order overwrite earlier ones.
    /// Per spec, the result row's tail is the tail of the last
    /// spread operand if that tail is a row variable; otherwise the
    /// row is closed.
    pub(in crate::infer) fn infer_object(
        &mut self,
        env: &TypeEnv,
        properties: &[PropDef],
        span: Span,
    ) -> InferResult<Type> {
        // Create a shared 'this' type for all methods in this object
        // This ensures that when one method's 'this' is unified with the object type,
        // all methods are connected, avoiding infinite types during method chaining.
        let shared_this = self.fresh_type_var();

        let mut props: BTreeMap<PropName, Type> = BTreeMap::new();
        let mut row_tail: RowTail = RowTail::Closed;
        // True if any spread was processed — even a closed-row spread
        // counts; the result is closed but `row_tail` may have been
        // set and then overridden back to Closed.
        let mut had_spread = false;

        for prop in properties {
            match prop {
                PropDef::Property {
                    key,
                    value,
                    type_annotation,
                    ..
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    let value_type = self.infer_expr(env, value)?;
                    // If the property carries an inline annotation, parse
                    // it and unify with the value's inferred type so the
                    // annotation is enforced the same way a variable
                    // declaration's annotation is.
                    let prop_type = if let Some(ann) = type_annotation {
                        let ann_span = Span::new(ann.span.start, ann.span.end);
                        let (annotated_type, _) = parse_type_annotation(
                            &ann.content,
                            ann_span,
                            self.next_var_id(),
                        )?;
                        // Annotation first: it's what the user wrote, so
                        // the error message reads as "expected <annotated>,
                        // found <value>".
                        self.unify(ann_span, &annotated_type, &value_type)?;
                        self.apply_subst(&annotated_type)
                    } else {
                        value_type
                    };
                    props.insert(prop_name, prop_type);
                }

                PropDef::Method {
                    key,
                    params,
                    body,
                    span: method_span,
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Infer method with the shared 'this' type
                    let method_type = self.infer_function_with_this(
                        env,
                        None,
                        params,
                        body,
                        &None,
                        shared_this.clone(),
                        *method_span,
                    )?;
                    props.insert(prop_name, method_type);
                }

                PropDef::Getter { key, body, span: _ } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Getter: infer body return type
                    let (ret_type, _) = self.infer_stmt(env, body)?;
                    props.insert(prop_name, ret_type);
                }

                PropDef::Setter {
                    key,
                    param,
                    body,
                    span: _,
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Setter: param type is fresh, body returns undefined
                    let param_type = self.fresh_type_var();
                    let setter_env = env.extend(param.clone(), TypeScheme::mono(param_type));
                    self.infer_stmt(&setter_env, body)?;
                    // For simplicity, we use the parameter type as the property type
                    // In a full implementation, we'd track getter/setter separately
                    props.insert(prop_name, self.fresh_type_var());
                }

                PropDef::Spread { argument, span: spread_span } => {
                    had_spread = true;
                    let arg_ty = self.infer_expr(env, argument)?;
                    let resolved = self.apply_subst(&arg_ty);
                    let spread_row = self.coerce_to_row(&resolved, *spread_span)?;
                    // Right-biased merge: this spread's properties
                    // overwrite anything earlier — including the
                    // result of an earlier spread or property.
                    for (k, v) in spread_row.props {
                        props.insert(k, v);
                    }
                    // Per spec: "the result row's tail is the tail
                    // of the last spread operand if it's a row
                    // variable." A `Closed` tail flips the result
                    // back to closed; an `Open(α)` tail makes the
                    // result open at `α` (any later spread overwrites).
                    row_tail = spread_row.tail;
                }
            }
        }

        let final_row = match row_tail {
            RowTail::Open(var) => RowType::open(props, var),
            // Closed and Recursive both produce a closed row at the
            // surface — Recursive doesn't arise from a fresh row
            // var introduced by spread inference, but if a user
            // spreads a recursive-typed value the result is still
            // soundly closed for the keys we know about.
            _ => RowType::closed(props),
        };
        let obj_type = Type::Row(final_row);

        // Unify the shared 'this' with the complete object type so
        // method bodies that mention `this.foo` see the correct
        // row. This is the equi-recursive bit.
        self.unify(span, &shared_this, &obj_type)?;

        let _ = had_spread;
        Ok(self.apply_subst(&obj_type))
    }

    /// Infer `Expr::RestRow { source, excluded }` — the synthetic
    /// node emitted when desugaring `const {a, ...rest} = obj`. The
    /// source's type must be a row (or a free variable, in which
    /// case we pin it to a row). The result is that row with
    /// `excluded` keys removed; the tail (open or closed) is
    /// preserved so a row variable still carries "the rest of the
    /// caller's row" through.
    pub(in crate::infer) fn infer_rest_row(
        &mut self,
        env: &TypeEnv,
        source: &Expr,
        excluded: &[String],
        span: Span,
    ) -> InferResult<Type> {
        let source_ty = self.infer_expr(env, source)?;
        let row = self.coerce_to_row(&source_ty, span)?;
        let mut new_props = row.props.clone();
        for key in excluded {
            new_props.remove(&PropName(key.clone()));
        }
        let new_row = RowType {
            props: new_props,
            tail: row.tail,
        };
        Ok(Type::Row(new_row))
    }

    /// Resolve a type that's expected to be a row (because an
    /// object spread or destructuring rest is operating on it).
    /// If the type is already a row, return it unchanged. If it's
    /// a free type variable, unify it with a fresh open row.
    /// Otherwise reject with a span-anchored diagnostic.
    fn coerce_to_row(&mut self, ty: &Type, span: Span) -> InferResult<RowType> {
        let resolved = self.apply_subst(ty);
        match resolved {
            Type::Row(row) => Ok(row),
            Type::Var(_) => {
                // Open row of unknown shape; pin the type variable
                // to a fresh open row so it can be merged in.
                let row_var = self.fresh_tvar_name();
                let row = RowType::empty_open(row_var);
                let row_ty = Type::Row(row.clone());
                self.unify(span, &resolved, &row_ty)?;
                Ok(row)
            }
            other => Err(crate::error::TypeError::TypeMismatch {
                expected: format!("{}", Type::Row(RowType::empty_closed())),
                found: format!("{}", other),
                span,
            }
            .into()),
        }
    }

    /// Generate a fresh row-tail variable name. Mirrors the bare
    /// type-var helper but flagged as a row variable through its
    /// usage in `RowTail::Open`.
    fn fresh_tvar_name(&mut self) -> TVarName {
        TVarName::Flex(self.next_var_id())
    }

    /// Convert a property key to a property name.
    fn prop_key_to_name(&self, key: &PropKey) -> PropName {
        match key {
            PropKey::Ident(s) => PropName(s.clone()),
            PropKey::String(s) => PropName(s.clone()),
            PropKey::Number(n) => PropName(n.to_string()),
        }
    }

    /// Infer the type of a member access (obj.prop).
    pub(in crate::infer) fn infer_member(
        &mut self,
        env: &TypeEnv,
        object: &Expr,
        property: &str,
        span: Span,
    ) -> InferResult<Type> {
        let obj_type = self.infer_expr(env, object)?;
        let obj_type = self.apply_subst(&obj_type);
        self.infer_member_on_type(&obj_type, property, span)
    }

    /// Look up a property on a (substituted) type. Used by `infer_member`
    /// after evaluating the object expression, and recursively to elide
    /// access against union members.
    pub(in crate::infer) fn infer_member_on_type(
        &mut self,
        obj_type: &Type,
        property: &str,
        span: Span,
    ) -> InferResult<Type> {
        // Union elimination: read the property from every member and join
        // the results. Fails if any member lacks the property at a
        // compatible type. This is the load-bearing rule that lets users
        // *do* something with a union after they've formed one.
        if let Type::Union(members) = obj_type {
            let mut result: Option<Type> = None;
            for m in members {
                let m_resolved = self.apply_subst(m);
                let prop_ty = self.infer_member_on_type(&m_resolved, property, span)?;
                result = Some(match result {
                    None => prop_ty,
                    Some(acc) => self.join(span, &acc, &prop_ty),
                });
            }
            // The empty union (`never`) can be accessed at any property —
            // it's unreachable. Synthesise `never` for the result.
            return Ok(result.unwrap_or_else(Type::never));
        }

        // Handle built-in properties for arrays and strings
        match obj_type {
            Type::Array(_) => {
                match property {
                    "length" => return Ok(Type::Number),
                    // Array methods could be added here
                    _ => {}
                }
            }
            Type::String => {
                match property {
                    "length" => return Ok(Type::Number),
                    // String methods could be added here
                    _ => {}
                }
            }
            Type::Row(row) => {
                // If the property exists in the row, return its type directly
                // This is more efficient and avoids creating unnecessary type variables
                if let Some(prop_type) = row.props.get(&PropName(property.to_string())) {
                    return Ok(self.apply_subst(prop_type));
                }
                // If property not found and row is closed, this will fail in unification below
            }
            Type::Module(m) => {
                if let Some(scheme) = m.exports.get(property) {
                    let ty = self.instantiate(scheme);
                    return Ok(self.apply_subst(&ty));
                }
                return Err(crate::error::TypeError::Module {
                    message: format!(
                        "module {:?} has no export named {:?}",
                        m.source, property
                    ),
                    span,
                }
                .into());
            }
            _ => {}
        }

        // For type variables, create a row constraint
        let result_type = self.fresh_type_var();

        // Record origin for the property access result
        if let Type::Var(var) = &result_type {
            self.record_origin(
                var.clone(),
                crate::error::TypeOrigin::PropertyAccess {
                    property: property.to_string(),
                    span,
                },
            );
        }

        let row_var = self.fresh_flex();
        let expected_row = Type::object_open([(property, result_type.clone())], row_var);

        self.unify(span, obj_type, &expected_row)?;

        Ok(self.apply_subst(&result_type))
    }

    /// Helper to infer member access from an already-inferred object type.
    pub(in crate::infer) fn infer_member_from_type(
        &mut self,
        obj_type: &Type,
        property: &str,
        span: Span,
    ) -> InferResult<Type> {
        // Union elimination: read the property from every member and join.
        if let Type::Union(members) = obj_type {
            let mut result: Option<Type> = None;
            for m in members {
                let m_resolved = self.apply_subst(m);
                let prop_ty = self.infer_member_from_type(&m_resolved, property, span)?;
                result = Some(match result {
                    None => prop_ty,
                    Some(acc) => self.join(span, &acc, &prop_ty),
                });
            }
            return Ok(result.unwrap_or_else(Type::never));
        }

        // Handle built-in properties for arrays and strings
        match obj_type {
            Type::Array(elem_ty) => {
                if property == "length" {
                    return Ok(Type::Number);
                }
                if let Some(ty) = crate::builtins::array_method_type(self, elem_ty, property) {
                    return Ok(ty);
                }
            }
            Type::String => {
                if property == "length" {
                    return Ok(Type::Number);
                }
                if let Some(ty) = crate::builtins::string_method_type(self, property) {
                    return Ok(ty);
                }
            }
            Type::Promise(inner_ty) => {
                if let Some(ty) = crate::builtins::promise_method_type(self, inner_ty, property) {
                    return Ok(ty);
                }
            }
            Type::Row(row) => {
                // If the property exists in the row, return its type directly
                if let Some(prop_type) = row.props.get(&PropName(property.to_string())) {
                    return Ok(self.apply_subst(prop_type));
                }
                // Property not in this row's props - check the tail
                if let Some(prop_type) = self.lookup_property_in_row_tail(row, property) {
                    return Ok(self.apply_subst(&prop_type));
                }
                // If property not found and row is closed, this will fail in unification below
            }
            Type::Module(m) => {
                if let Some(scheme) = m.exports.get(property) {
                    let ty = self.instantiate(scheme);
                    return Ok(self.apply_subst(&ty));
                }
                return Err(crate::error::TypeError::Module {
                    message: format!(
                        "module {:?} has no export named {:?}",
                        m.source, property
                    ),
                    span,
                }
                .into());
            }
            _ => {}
        }

        // For type variables, create a row constraint
        let result_type = self.fresh_type_var();

        if let Type::Var(var) = &result_type {
            self.record_origin(
                var.clone(),
                crate::error::TypeOrigin::PropertyAccess {
                    property: property.to_string(),
                    span,
                },
            );
        }

        let row_var = self.fresh_flex();
        let expected_row = Type::object_open([(property, result_type.clone())], row_var);

        self.unify(span, obj_type, &expected_row)?;

        Ok(self.apply_subst(&result_type))
    }

    /// Look up a property by following row tail chains.
    /// Returns the property type if found in any row that the tail resolves to.
    fn lookup_property_in_row_tail(&self, row: &RowType, property: &str) -> Option<Type> {
        use std::collections::HashSet;
        let prop_name = PropName(property.to_string());
        let mut visited: HashSet<TVarId> = HashSet::new();
        let mut current_tail = &row.tail;

        loop {
            match current_tail {
                RowTail::Closed => return None,
                RowTail::Open(TVarName::Flex(id)) => {
                    // Avoid infinite loops
                    if visited.contains(id) {
                        return None;
                    }
                    visited.insert(*id);

                    // Look up what this variable is bound to
                    if let Some(ty) = self.main_subst.get(&TVarName::Flex(*id)) {
                        match ty {
                            Type::Row(tail_row) => {
                                // Check if property is in this row
                                if let Some(prop_type) = tail_row.props.get(&prop_name) {
                                    return Some(prop_type.clone());
                                }
                                // Continue with this row's tail
                                current_tail = &tail_row.tail;
                            }
                            Type::Var(TVarName::Flex(next_id)) => {
                                // The variable is bound to another variable, follow it
                                if visited.contains(next_id) {
                                    return None;
                                }
                                visited.insert(*next_id);
                                if let Some(next_ty) =
                                    self.main_subst.get(&TVarName::Flex(*next_id))
                                {
                                    if let Type::Row(tail_row) = next_ty {
                                        if let Some(prop_type) = tail_row.props.get(&prop_name) {
                                            return Some(prop_type.clone());
                                        }
                                        current_tail = &tail_row.tail;
                                        continue;
                                    }
                                }
                                return None;
                            }
                            _ => return None,
                        }
                    } else {
                        return None;
                    }
                }
                RowTail::Open(TVarName::Skolem(_)) => return None,
                RowTail::Recursive(_, _) => return None,
            }
        }
    }

}
