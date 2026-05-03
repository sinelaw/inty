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
            }
        }

        let obj_type = Type::Row(RowType::closed(props));

        // Unify the shared 'this' with the complete object type
        // This creates the equi-recursive type where methods reference the containing object
        self.unify(span, &shared_this, &obj_type)?;

        Ok(self.apply_subst(&obj_type))
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

    /// Check if a property in a type scheme is polymorphic (uses quantified type variables).
    pub(in crate::infer) fn is_polymorphic_property(
        &self,
        scheme: &TypeScheme,
        property: &str,
    ) -> bool {
        use std::collections::HashSet;

        // If the scheme has no quantified variables, nothing is polymorphic
        if scheme.vars.is_empty() {
            return false;
        }

        let quantified: HashSet<_> = scheme.vars.iter().cloned().collect();

        // Look up the property type in the uninstantiated scheme body
        if let Type::Row(row) = &scheme.body.ty {
            if let Some(prop_type) = row.props.get(&PropName(property.to_string())) {
                // Check if the property type uses any quantified variables
                let prop_vars = prop_type.free_vars();
                return !prop_vars.is_disjoint(&quantified);
            }
        }

        false
    }
}
