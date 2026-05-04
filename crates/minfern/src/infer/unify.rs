//! Unification algorithm for type inference.
//!
//! Implements unification for types including:
//! - Basic types (primitives, functions, arrays)
//! - Row types with row polymorphism
//! - Recursive type detection and creation

use std::collections::BTreeMap;

use crate::error::{intyError, TypeError};
use crate::lexer::Span;
use crate::types::{PropName, RowTail, RowType, Subst, TVarId, TVarName, Type, TypeDef};

use super::state::InferState;

/// Result type for unification.
pub type UnifyResult<T> = Result<T, intyError>;

impl InferState {
    /// Unify two types, updating the substitution.
    pub fn unify(&mut self, span: Span, t1: &Type, t2: &Type) -> UnifyResult<()> {
        let t1 = self.apply_subst(t1);
        let t2 = self.apply_subst(t2);
        self.unify_impl(span, &t1, &t2)
    }

    fn unify_impl(&mut self, span: Span, t1: &Type, t2: &Type) -> UnifyResult<()> {
        match (t1, t2) {
            // Same variable
            (Type::Var(v1), Type::Var(v2)) if v1 == v2 => Ok(()),

            // Flex variable binds to anything
            (Type::Var(TVarName::Flex(n)), t) | (t, Type::Var(TVarName::Flex(n))) => {
                self.var_bind(span, *n, t)
            }

            // Literal types unify with themselves and with their base.
            // The literal-vs-base direction lets `var x: String = "hi"`
            // type-check (annotation is `String`, value infers as
            // `String`); the literal-vs-literal direction handles
            // re-unifying inside a discriminator after narrowing.
            (Type::Literal(l1), Type::Literal(l2)) => {
                if l1 == l2 {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }
            (Type::Literal(l), other) | (other, Type::Literal(l)) if &l.base_type() == other => {
                Ok(())
            }

            // Union ~ Union: if both sides are equal as sets (we already
            // normalise), accept. Otherwise reject — the calling site
            // should use join() if it wants subsumption-style behaviour.
            (Type::Union(m1), Type::Union(m2)) => {
                if m1.len() == m2.len() && m1.iter().all(|t| m2.contains(t)) {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Union ~ T: succeed if T is a member of the union (after
            // subst). This is the bridge that lets `var x: T | undefined
            // = expr` accept an `expr` that infers as `T` or `undefined`.
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                let mut matched = false;
                for m in members {
                    let m = self.apply_subst(m);
                    if &m == other {
                        matched = true;
                        break;
                    }
                    // Literal-into-base subsumption.
                    if let Type::Literal(lit) = other {
                        if m == lit.base_type() {
                            matched = true;
                            break;
                        }
                    }
                    if let Type::Literal(lit) = &m {
                        if &lit.base_type() == other {
                            matched = true;
                            break;
                        }
                    }
                }
                if matched {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Skolems must match exactly
            (Type::Var(TVarName::Skolem(n1)), Type::Var(TVarName::Skolem(n2))) if n1 == n2 => {
                Ok(())
            }

            // Primitives
            (Type::Number, Type::Number) => Ok(()),
            (Type::String, Type::String) => Ok(()),
            (Type::Boolean, Type::Boolean) => Ok(()),
            (Type::Undefined, Type::Undefined) => Ok(()),
            (Type::Null, Type::Null) => Ok(()),
            (Type::Regex, Type::Regex) => Ok(()),

            // Functions
            (
                Type::Func {
                    this_type: this1,
                    params: params1,
                    ret: ret1,
                },
                Type::Func {
                    this_type: this2,
                    params: params2,
                    ret: ret2,
                },
            ) => {
                // Unify this types:
                // - None means "static function, doesn't use this"
                // - Static functions are compatible with any this type
                match (this1, this2) {
                    (None, None) => {} // Both static, nothing to unify
                    (None, Some(_)) | (Some(_), None) => {
                        // One is static - compatible with any this
                    }
                    (Some(t1), Some(t2)) => {
                        self.unify(span, t1, t2)?;
                    }
                }

                // Unify parameter counts
                if params1.len() != params2.len() {
                    return Err(TypeError::ArityMismatch {
                        expected: params1.len(),
                        found: params2.len(),
                        span,
                    }
                    .into());
                }

                // Unify parameters (contravariant, but we unify for now)
                for (p1, p2) in params1.iter().zip(params2.iter()) {
                    self.unify(span, p1, p2)?;
                }

                // Unify return types
                self.unify(span, ret1, ret2)
            }

            // Row types
            (Type::Row(r1), Type::Row(r2)) => self.unify_rows(span, r1, r2),

            // Arrays
            (Type::Array(e1), Type::Array(e2)) => self.unify(span, e1, e2),

            // Array with row type - arrays have structural properties like `length`
            (Type::Array(elem), Type::Row(row)) | (Type::Row(row), Type::Array(elem)) => {
                self.unify_array_with_row(span, elem, row)
            }

            // Promises
            (Type::Promise(i1), Type::Promise(i2)) => self.unify(span, i1, i2),

            // Maps
            (Type::Map(v1), Type::Map(v2)) => self.unify(span, v1, v2),

            // Named types (recursive)
            (Type::Named(id1, args1), Type::Named(id2, args2)) if id1 == id2 => {
                // Same recursive type, unify arguments
                if args1.len() != args2.len() {
                    return Err(self.unification_error(span, t1, t2));
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(span, a1, a2)?;
                }
                Ok(())
            }

            // Named vs non-named: unroll the named type
            (Type::Named(id, args), other) | (other, Type::Named(id, args)) => {
                if let Some(unrolled) = self.unroll_named(*id, args) {
                    self.unify(span, &unrolled, other)
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Modules are nominally identified by source path. Two
            // namespace-import bindings of the same file unify; two
            // bindings of different files don't, even if their export
            // shapes happen to coincide. This matches ES module identity:
            // each file is its own module.
            (Type::Module(m1), Type::Module(m2)) => {
                if m1.source == m2.source {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Mismatch
            _ => Err(self.unification_error(span, t1, t2)),
        }
    }

    /// Bind a type variable to a type (with occurs check).
    fn var_bind(&mut self, span: Span, var: TVarId, ty: &Type) -> UnifyResult<()> {
        // Don't bind to itself
        if let Type::Var(TVarName::Flex(id)) = ty {
            if *id == var {
                return Ok(());
            }
        }

        // Check if this would create a recursive type inside a row
        if self.is_inside_row_type(var, ty) {
            // Create a recursive type
            return self.create_recursive_type(span, var, ty);
        }

        // Standard occurs check
        if self.occurs_in(var, ty) {
            return Err(TypeError::OccursCheck {
                var: format!("t{}", var),
                ty: ty.to_string(),
                span,
            }
            .into());
        }

        // Bind the variable
        self.extend_subst(TVarName::Flex(var), ty.clone());
        Ok(())
    }

    /// Unify an array type with a row type.
    /// Arrays have structural properties like `length: Number`.
    fn unify_array_with_row(&mut self, span: Span, elem: &Type, row: &RowType) -> UnifyResult<()> {
        // Check each property in the row against array's known properties
        for (prop_name, prop_type) in &row.props {
            match prop_name.0.as_str() {
                "length" => {
                    // Array.length is Number
                    self.unify(span, prop_type, &Type::Number)?;
                }
                _ => {
                    // Unknown property - arrays don't have arbitrary properties
                    return Err(TypeError::PropertyNotFound {
                        prop: prop_name.0.clone(),
                        obj_type: format!("{}[]", elem),
                        span,
                    }
                    .into());
                }
            }
        }

        // Handle the row tail
        match &row.tail {
            RowTail::Closed => {
                // Closed row with only known array properties - OK
                Ok(())
            }
            RowTail::Open(TVarName::Flex(id)) => {
                // Open row - bind the tail to a closed empty row
                // (arrays don't have additional arbitrary properties)
                self.extend_subst(TVarName::Flex(*id), Type::Row(RowType::empty_closed()));
                Ok(())
            }
            RowTail::Open(TVarName::Skolem(_)) => {
                // Skolem tail can't be bound
                Err(self.unification_error(
                    span,
                    &Type::Array(Box::new(elem.clone())),
                    &Type::Row(row.clone()),
                ))
            }
            RowTail::Recursive(_, _) => {
                // Recursive tail doesn't make sense for arrays
                Err(self.unification_error(
                    span,
                    &Type::Array(Box::new(elem.clone())),
                    &Type::Row(row.clone()),
                ))
            }
        }
    }

    /// Unify two row types.
    fn unify_rows(&mut self, span: Span, r1: &RowType, r2: &RowType) -> UnifyResult<()> {
        // Collect all property names from both rows
        let mut all_props: Vec<PropName> =
            r1.props.keys().chain(r2.props.keys()).cloned().collect();
        all_props.sort();
        all_props.dedup();

        // Unify common properties
        for prop in &all_props {
            match (r1.props.get(prop), r2.props.get(prop)) {
                (Some(t1), Some(t2)) => {
                    self.unify(span, t1, t2)?;
                }
                (Some(_), None) => {
                    // Property in r1 but not r2
                    // This is okay if r2 has an open tail
                    if !matches!(r2.tail, RowTail::Open(_)) {
                        return Err(TypeError::PropertyNotFound {
                            prop: prop.0.clone(),
                            obj_type: Type::Row(r2.clone()).to_string(),
                            span,
                        }
                        .into());
                    }
                }
                (None, Some(_)) => {
                    // Property in r2 but not r1
                    if !matches!(r1.tail, RowTail::Open(_)) {
                        return Err(TypeError::PropertyNotFound {
                            prop: prop.0.clone(),
                            obj_type: Type::Row(r1.clone()).to_string(),
                            span,
                        }
                        .into());
                    }
                }
                (None, None) => unreachable!(),
            }
        }

        // Unify tails
        match (&r1.tail, &r2.tail) {
            (RowTail::Closed, RowTail::Closed) => {
                // Both closed, must have same properties (already checked)
                if r1.props.len() != r2.props.len() {
                    return Err(self.unification_error(
                        span,
                        &Type::Row(r1.clone()),
                        &Type::Row(r2.clone()),
                    ));
                }
                Ok(())
            }

            (RowTail::Open(v1), RowTail::Open(v2)) if v1 == v2 => Ok(()),

            (RowTail::Open(TVarName::Flex(id)), RowTail::Closed) => {
                // Bind the row variable to an empty row
                let extra_props: BTreeMap<PropName, Type> = r2
                    .props
                    .iter()
                    .filter(|(k, _)| !r1.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                if extra_props.is_empty() {
                    self.extend_subst(TVarName::Flex(*id), Type::Row(RowType::empty_closed()));
                } else {
                    self.extend_subst(TVarName::Flex(*id), Type::Row(RowType::closed(extra_props)));
                }
                Ok(())
            }

            (RowTail::Closed, RowTail::Open(TVarName::Flex(id))) => {
                // Symmetric case
                let extra_props: BTreeMap<PropName, Type> = r1
                    .props
                    .iter()
                    .filter(|(k, _)| !r2.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                if extra_props.is_empty() {
                    self.extend_subst(TVarName::Flex(*id), Type::Row(RowType::empty_closed()));
                } else {
                    self.extend_subst(TVarName::Flex(*id), Type::Row(RowType::closed(extra_props)));
                }
                Ok(())
            }

            (RowTail::Open(TVarName::Flex(id1)), RowTail::Open(TVarName::Flex(id2))) => {
                // Both open, create a fresh row variable for the common tail
                let fresh = self.fresh_flex();

                // Calculate extra properties for each side
                let extra1: BTreeMap<PropName, Type> = r2
                    .props
                    .iter()
                    .filter(|(k, _)| !r1.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                let extra2: BTreeMap<PropName, Type> = r1
                    .props
                    .iter()
                    .filter(|(k, _)| !r2.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                // Bind both row variables
                self.extend_subst(
                    TVarName::Flex(*id1),
                    Type::Row(RowType::open(extra1, fresh.clone())),
                );
                self.extend_subst(
                    TVarName::Flex(*id2),
                    Type::Row(RowType::open(extra2, fresh)),
                );

                Ok(())
            }

            (RowTail::Recursive(id1, args1), RowTail::Recursive(id2, args2)) if id1 == id2 => {
                // Same recursive type
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(span, a1, a2)?;
                }
                Ok(())
            }

            _ => Err(self.unification_error(span, &Type::Row(r1.clone()), &Type::Row(r2.clone()))),
        }
    }

    /// Create a recursive type when occurs check detects a row cycle.
    fn create_recursive_type(&mut self, _span: Span, var: TVarId, ty: &Type) -> UnifyResult<()> {
        // Generate a new type ID
        let type_id = self.fresh_type_id();

        // Create the recursive type definition
        // The body is the type with the variable replaced by Named(type_id, [])
        let rec_ref = Type::Named(type_id, vec![]);

        // Create substitution to replace var with the recursive reference
        let mut subst = Subst::empty();
        subst.insert(TVarName::Flex(var), rec_ref.clone());
        let body = subst.apply(ty);

        let def = TypeDef {
            id: type_id,
            params: vec![],
            body,
        };

        self.register_named_type(def);

        // Bind the original variable to the recursive type
        self.extend_subst(TVarName::Flex(var), rec_ref);

        Ok(())
    }

    /// Create a unification error.
    fn unification_error(&self, span: Span, t1: &Type, t2: &Type) -> intyError {
        let expected_origin = self
            .get_origin(t1)
            .cloned()
            .or_else(|| self.find_origin_through_subst(t1));
        let found_origin = self
            .get_origin(t2)
            .cloned()
            .or_else(|| self.find_origin_through_subst(t2));

        TypeError::UnificationError {
            expected: t1.to_string(),
            found: t2.to_string(),
            span,
            context: None,
            expected_origin,
            found_origin,
        }
        .into()
    }

    /// Try to find an origin by looking through the substitution
    fn find_origin_through_subst(&self, ty: &Type) -> Option<crate::error::TypeOrigin> {
        // Look through the substitution to find if any type variable
        // was substituted to produce this type
        for (var, subst_ty) in self.main_subst.iter() {
            if subst_ty == ty {
                if let Some(origin) = self.type_origins.get(var) {
                    return Some(origin.clone());
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_same_primitive() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        assert!(state.unify(span, &Type::Number, &Type::Number).is_ok());
        assert!(state.unify(span, &Type::String, &Type::String).is_ok());
    }

    #[test]
    fn test_unify_different_primitives() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        assert!(state.unify(span, &Type::Number, &Type::String).is_err());
    }

    #[test]
    fn test_unify_var_with_type() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let var = Type::flex(0);
        assert!(state.unify(span, &var, &Type::Number).is_ok());

        // After unification, applying subst should give Number
        assert_eq!(state.apply_subst(&var), Type::Number);
    }

    #[test]
    fn test_unify_vars() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let v1 = Type::flex(0);
        let v2 = Type::flex(1);

        assert!(state.unify(span, &v1, &v2).is_ok());

        // Both should resolve to the same type after unification
        assert_eq!(state.apply_subst(&v1), state.apply_subst(&v2));
    }

    #[test]
    fn test_unify_functions() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let f1 = Type::simple_func(vec![Type::Number], Type::flex(0));
        let f2 = Type::simple_func(vec![Type::Number], Type::String);

        assert!(state.unify(span, &f1, &f2).is_ok());

        // a0 should be bound to String
        assert_eq!(state.apply_subst(&Type::flex(0)), Type::String);
    }

    #[test]
    fn test_unify_arity_mismatch() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let f1 = Type::simple_func(vec![Type::Number], Type::Number);
        let f2 = Type::simple_func(vec![Type::Number, Type::Number], Type::Number);

        assert!(state.unify(span, &f1, &f2).is_err());
    }

    #[test]
    fn test_unify_closed_rows() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let r1 = Type::object([("x", Type::Number), ("y", Type::String)]);
        let r2 = Type::object([("x", Type::Number), ("y", Type::String)]);

        assert!(state.unify(span, &r1, &r2).is_ok());
    }

    #[test]
    fn test_unify_open_row_with_closed() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // {x: Number | a0} unified with {x: Number, y: String}
        let r1 = Type::object_open([("x", Type::Number)], TVarName::Flex(0));
        let r2 = Type::object([("x", Type::Number), ("y", Type::String)]);

        assert!(state.unify(span, &r1, &r2).is_ok());

        // The row variable should be bound to {y: String}
        let row_var = state.apply_subst(&Type::flex(0));
        if let Type::Row(row) = row_var {
            assert!(row.has_prop(&"y".into()));
        } else {
            panic!("Expected row type");
        }
    }

    #[test]
    fn test_occurs_check_simple() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // a0 = a0 -> Number should fail (infinite type)
        let var = Type::flex(0);
        let func = Type::simple_func(vec![Type::flex(0)], Type::Number);

        assert!(state.unify(span, &var, &func).is_err());
    }

    #[test]
    fn test_unify_array_with_length_row() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should unify with {length: Number | a}
        let arr = Type::array(Type::Number);
        let row = Type::object_open([("length", Type::Number)], TVarName::Flex(0));

        assert!(state.unify(span, &arr, &row).is_ok());

        // The row variable should be bound to an empty closed row
        let row_var = state.apply_subst(&Type::flex(0));
        if let Type::Row(row) = row_var {
            assert!(row.props.is_empty());
            assert!(matches!(row.tail, RowTail::Closed));
        } else {
            panic!("Expected row type, got {:?}", row_var);
        }
    }

    #[test]
    fn test_unify_array_with_closed_length_row() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should unify with {length: Number}
        let arr = Type::array(Type::Number);
        let row = Type::object([("length", Type::Number)]);

        assert!(state.unify(span, &arr, &row).is_ok());
    }

    #[test]
    fn test_unify_array_with_wrong_property_fails() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should NOT unify with {foo: Number}
        let arr = Type::array(Type::Number);
        let row = Type::object([("foo", Type::Number)]);

        assert!(state.unify(span, &arr, &row).is_err());
    }

    #[test]
    fn test_unify_array_length_type_mismatch() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should NOT unify with {length: String}
        let arr = Type::array(Type::Number);
        let row = Type::object([("length", Type::String)]);

        assert!(state.unify(span, &arr, &row).is_err());
    }
}
