//! Variable bindings: declarations, assignment, value restriction.

use crate::error::TypeError;
use crate::lexer::Span;
use crate::parser::ast::{AssignOp, Expr, PropDef, VarDeclarator, VarKind};
use crate::types::{Type, TypePred, TypeScheme};

use super::super::env::{Mutability, TypeEnv};
use super::super::state::InferState;
use super::super::type_parser::parse_type_annotation;
use super::super::InferResult;

/// Check if an expression is a syntactic value (for the value restriction).
///
/// Syntactic values can be safely generalized because they don't perform
/// any computation that could create mutable state with polymorphic type.
fn is_syntactic_value(expr: &Expr) -> bool {
    match expr {
        // Literals are values
        Expr::Lit { .. } => true,

        // Variables are values
        Expr::Ident { .. } => true,

        // `this` is a value
        Expr::This { .. } => true,

        // Functions are values
        Expr::Function { .. } => true,

        // Array literals are values if all elements are values
        Expr::Array { elements, .. } => elements
            .iter()
            .all(|e| e.as_ref().map_or(true, is_syntactic_value)),

        // Object literals are values if all property values are values
        Expr::Object { properties, .. } => properties.iter().all(|p| match p {
            PropDef::Property { value, .. } => is_syntactic_value(value),
            // Getters/setters/methods are function-like, so they're values
            PropDef::Getter { .. } | PropDef::Setter { .. } | PropDef::Method { .. } => true,
        }),

        // Unary operations on values are values (e.g., -1, !true)
        Expr::Unary { argument, .. } => is_syntactic_value(argument),

        // Template literals are values if all expressions are values
        Expr::TemplateLiteral { expressions, .. } => expressions.iter().all(is_syntactic_value),

        // Everything else is NOT a syntactic value:
        // - Function calls
        // - Member access
        // - Binary operations (could have side effects)
        // - Assignments
        // - etc.
        _ => false,
    }
}

/// Check if an expression is a mutable container literal.
///
/// Mutable containers (arrays and objects) should not be generalized when
/// assigned to mutable (`var`) variables because their contents can be
/// mutated through indexing (e.g., `arr[i] = ...`), which would break
/// the polymorphic type by requiring all uses to share the same element type.
///
/// Functions, while syntactic values, are NOT mutable containers because
/// their "contents" (code) cannot be mutated at runtime.
fn is_mutable_container_literal(expr: &Expr) -> bool {
    match expr {
        // Array literals are mutable containers
        Expr::Array { .. } => true,

        // Object literals are mutable containers
        Expr::Object { .. } => true,

        // Everything else is not a mutable container
        // (functions, literals, identifiers, etc.)
        _ => false,
    }
}

impl InferState {
    /// Check if an assignment target is valid (not an immutable binding or polymorphic property).
    pub(in crate::infer) fn check_assignment_target(
        &self,
        env: &TypeEnv,
        left: &Expr,
        span: Span,
    ) -> InferResult<()> {
        match left {
            // Direct assignment to a variable
            Expr::Ident { name, .. } => {
                if let Some(binding) = env.lookup_binding(name) {
                    if binding.mutability == Mutability::Immutable {
                        return Err(TypeError::AssignmentToConstant {
                            name: name.clone(),
                            span,
                        }
                        .into());
                    }
                }
            }

            // Property assignment: obj.prop = ...
            Expr::Member {
                object,
                property,
                span: member_span,
            } => {
                // Check if the object is an immutable binding with a polymorphic property
                if let Expr::Ident { name, .. } = object.as_ref() {
                    if let Some(binding) = env.lookup_binding(name) {
                        if binding.mutability == Mutability::Immutable {
                            // Check if the property type is polymorphic
                            // (uses any of the scheme's quantified type variables)
                            if self.is_polymorphic_property(&binding.scheme, property) {
                                return Err(TypeError::AssignmentToPolymorphicProperty {
                                    object: name.clone(),
                                    property: property.clone(),
                                    span: *member_span,
                                }
                                .into());
                            }
                        }
                    }
                }
            }

            // Computed property assignment: obj[expr] = ...
            // We don't check this because we can't statically determine the property
            Expr::ComputedMember { .. } => {}

            // Other expressions (destructuring, etc.) - no special checks
            _ => {}
        }

        Ok(())
    }

    /// Infer the type of an assignment.
    pub(in crate::infer) fn infer_assign(
        &mut self,
        env: &TypeEnv,
        op: AssignOp,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        // Check for assignment to immutable bindings
        self.check_assignment_target(env, left, span)?;

        let right_type = self.infer_expr(env, right)?;
        let left_type = self.infer_expr(env, left)?;

        match op {
            AssignOp::Assign => {
                self.unify(span, &left_type, &right_type)?;
            }

            AssignOp::AddAssign => {
                // Like +, could be number or string
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::plus(result.clone()), span);
                self.unify(span, &left_type, &result)?;
                self.unify(span, &right_type, &result)?;
            }

            AssignOp::SubAssign
            | AssignOp::MulAssign
            | AssignOp::DivAssign
            | AssignOp::ModAssign
            | AssignOp::PowAssign => {
                self.unify(span, &left_type, &Type::Number)?;
                self.unify(span, &right_type, &Type::Number)?;
            }

            AssignOp::LShiftAssign
            | AssignOp::RShiftAssign
            | AssignOp::URShiftAssign
            | AssignOp::BitAndAssign
            | AssignOp::BitOrAssign
            | AssignOp::BitXorAssign => {
                self.unify(span, &left_type, &Type::Number)?;
                self.unify(span, &right_type, &Type::Number)?;
            }
        }

        Ok(self.apply_subst(&left_type))
    }

    /// Handle a `var` / `let` / `const` declaration statement.
    pub(in crate::infer) fn infer_stmt_var(
        &mut self,
        env: &TypeEnv,
        kind: VarKind,
        declarations: &[VarDeclarator],
    ) -> InferResult<(Type, TypeEnv)> {
        let mut new_env = env.clone();

        for decl in declarations {
            // Check if this is a declaration (no init, with type annotation)
            let is_declaration = decl.init.is_none() && decl.type_annotation.is_some();

            let var_type = if let Some(init) = &decl.init {
                self.infer_expr(&new_env, init)?
            } else {
                self.fresh_type_var()
            };

            // If there's a type annotation, parse and unify with it
            let var_type = if let Some(annotation) = &decl.type_annotation {
                let annotation_span = Span::new(annotation.span.start, annotation.span.end);
                let (annotated_type, _var_map) = parse_type_annotation(
                    &annotation.content,
                    annotation_span,
                    self.next_var_id(),
                )?;
                self.unify(annotation_span, &var_type, &annotated_type)?;
                self.apply_subst(&var_type)
            } else {
                var_type
            };

            // Record the type for this declaration
            self.record_decl_type(decl.span, var_type.clone());

            // Determine if we should generalize:
            // 1. Declarations (no init, with type annotation) are always generalized
            //    because they represent external bindings and are immutable.
            // 2. const declarations with syntactic value initializers are generalized.
            // 3. var declarations with syntactic values are generalized UNLESS
            //    the value is a mutable container (array/object literal), which
            //    could be mutated via indexing and break the polymorphic type.
            let scheme = if is_declaration {
                // Declarations with type annotations are always generalized
                // (they're immutable so this is sound)
                let env_free = new_env.free_vars();
                self.generalize(&env_free, &var_type)
            } else {
                match (kind, &decl.init) {
                    // const declarations: generalize all syntactic values
                    (VarKind::Const, Some(init)) if is_syntactic_value(init) => {
                        let env_free = new_env.free_vars();
                        self.generalize(&env_free, &var_type)
                    }
                    // var declarations: generalize syntactic values EXCEPT mutable containers
                    (VarKind::Var, Some(init))
                        if is_syntactic_value(init) && !is_mutable_container_literal(init) =>
                    {
                        let env_free = new_env.free_vars();
                        self.generalize(&env_free, &var_type)
                    }
                    // Everything else: don't generalize
                    _ => TypeScheme::mono(var_type),
                }
            };

            // Determine mutability:
            // 1. const declarations are always immutable
            // 2. Declarations (no init, with type annotation) are immutable
            //    (per the design doc, they represent external APIs)
            // 3. var declarations with init are mutable
            let mutability = match kind {
                VarKind::Const => Mutability::Immutable,
                VarKind::Var if is_declaration => Mutability::Immutable,
                VarKind::Var => Mutability::Mutable,
            };
            new_env = new_env.extend_with_mutability(decl.name.clone(), scheme, mutability);
        }

        Ok((Type::Undefined, new_env))
    }
}
