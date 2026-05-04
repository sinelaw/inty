//! Function expressions, calls, `new`, and function declarations.

use crate::lexer::Span;
use crate::parser::ast::{Expr, Param, Stmt, TypeAnnotation};
use crate::types::{Type, TypePred, TypeScheme};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::type_parser::parse_type_annotation;
use super::super::InferResult;

impl InferState {
    /// Infer the type of a function expression.
    pub(in crate::infer) fn infer_function(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        span: Span,
    ) -> InferResult<Type> {
        // Fresh type for 'this'
        let this_type = self.fresh_type_var();

        // Fresh types for parameters
        let param_types: Vec<Type> = params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let ty = self.fresh_type_var();
                // Record origin for parameter types
                if let Type::Var(var) = &ty {
                    self.record_origin(
                        var.clone(),
                        crate::error::TypeOrigin::Parameter {
                            param_name: param.name.clone(),
                            param_index: idx,
                            span,
                        },
                    );
                }
                ty
            })
            .collect();

        // Fresh type for return
        let ret_type = self.fresh_type_var();

        // Create function type (needed for recursion)
        let func_type = Type::func(this_type.clone(), param_types.clone(), ret_type.clone());

        // If there's a type annotation, parse and unify with it
        if let Some(annotation) = type_annotation {
            let annotation_span = Span::new(annotation.span.start, annotation.span.end);
            let (annotated_type, _var_map) =
                parse_type_annotation(&annotation.content, annotation_span, self.next_var_id())?;

            // Unify the function type with the annotated type
            self.unify(annotation_span, &func_type, &annotated_type)?;
        }

        // Extend environment with parameters and this
        let mut body_env = env.extend("this".to_string(), TypeScheme::mono(this_type));

        for (param, ty) in params.iter().zip(param_types.iter()) {
            body_env = body_env.extend(param.name.clone(), TypeScheme::mono(ty.clone()));
            // Record per-param type for the LSP / hover. Keyed by the
            // param's name span so we can look it up at any reference
            // to the parameter.
            self.record_decl_type(param.span, ty.clone());
        }

        // If function is named, add it for recursion
        if let Some(fn_name) = name {
            body_env = body_env.extend(fn_name.to_string(), TypeScheme::mono(func_type.clone()));
        }

        // Infer body type
        let (body_type, _) = self.infer_stmt(&body_env, body)?;

        // Unify return type with body type
        self.unify(span, &ret_type, &body_type)?;

        // Return the function type with substitutions applied
        Ok(self.apply_subst(&func_type))
    }

    /// Infer the type of a function expression with a pre-specified 'this' type.
    /// This is used for object literal methods to ensure all methods share the same 'this'.
    pub(in crate::infer) fn infer_function_with_this(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        this_type: Type,
        span: Span,
    ) -> InferResult<Type> {
        // Fresh types for parameters
        let param_types: Vec<Type> = params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let ty = self.fresh_type_var();
                // Record origin for parameter types
                if let Type::Var(var) = &ty {
                    self.record_origin(
                        var.clone(),
                        crate::error::TypeOrigin::Parameter {
                            param_name: param.name.clone(),
                            param_index: idx,
                            span,
                        },
                    );
                }
                ty
            })
            .collect();

        // Fresh type for return
        let ret_type = self.fresh_type_var();

        // Create function type (needed for recursion)
        let func_type = Type::func(this_type.clone(), param_types.clone(), ret_type.clone());

        // If there's a type annotation, parse and unify with it
        if let Some(annotation) = type_annotation {
            let annotation_span = Span::new(annotation.span.start, annotation.span.end);
            let (annotated_type, _var_map) =
                parse_type_annotation(&annotation.content, annotation_span, self.next_var_id())?;

            // Unify the function type with the annotated type
            self.unify(annotation_span, &func_type, &annotated_type)?;
        }

        // Extend environment with parameters and this
        let mut body_env = env.extend("this".to_string(), TypeScheme::mono(this_type));

        for (param, ty) in params.iter().zip(param_types.iter()) {
            body_env = body_env.extend(param.name.clone(), TypeScheme::mono(ty.clone()));
            self.record_decl_type(param.span, ty.clone());
        }

        // If function is named, add it for recursion
        if let Some(fn_name) = name {
            body_env = body_env.extend(fn_name.to_string(), TypeScheme::mono(func_type.clone()));
        }

        // Infer body type
        let (body_type, _) = self.infer_stmt(&body_env, body)?;

        // Unify return type with body type
        self.unify(span, &ret_type, &body_type)?;

        // Return the function type with substitutions applied
        Ok(self.apply_subst(&func_type))
    }

    /// Infer the type of a function call.
    pub(in crate::infer) fn infer_call(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        span: Span,
    ) -> InferResult<Type> {
        // For method calls, we need to infer the object only once to avoid creating
        // different fresh type variables. We'll manually extract the method type.
        let (callee_type, obj_type_for_this) = match callee {
            Expr::Member {
                object,
                property,
                span: member_span,
            } => {
                // Infer object once
                let obj_type = self.infer_expr(env, object)?;
                let obj_type_applied = self.apply_subst(&obj_type);

                // Get method type from the object without re-inferring
                let method_type =
                    self.infer_member_from_type(&obj_type_applied, property, *member_span)?;

                (method_type, Some(obj_type_applied))
            }
            Expr::ComputedMember {
                object,
                property,
                span: member_span,
            } => {
                // Infer object once
                let obj_type = self.infer_expr(env, object)?;
                let obj_type_applied = self.apply_subst(&obj_type);

                // Get computed member type
                let index_type = self.infer_expr(env, property)?;
                let result_type = self.fresh_type_var();
                self.add_constraint(
                    TypePred::indexable(obj_type_applied.clone(), index_type, result_type.clone()),
                    *member_span,
                );

                (result_type, Some(obj_type_applied))
            }
            _ => {
                // Not a method call, infer normally
                (self.infer_expr(env, callee)?, None)
            }
        };

        // Infer argument types
        let arg_types: Vec<Type> = arguments
            .iter()
            .map(|arg| self.infer_expr(env, arg))
            .collect::<InferResult<_>>()?;

        // Fresh types for this and return
        let this_type = self.fresh_type_var();
        let ret_type = self.fresh_type_var();

        // Expected function type
        let expected_func = Type::func(this_type.clone(), arg_types, ret_type.clone());

        // Unify callee with expected function type
        self.unify(span, &callee_type, &expected_func)?;

        // If this is a method call, also unify 'this' with the object type
        // This happens AFTER the main unification, so type variables in the
        // method signature have already been connected to the return type.
        if let Some(obj_type) = obj_type_for_this {
            let obj_type_applied = self.apply_subst(&obj_type);
            let this_type_applied = self.apply_subst(&this_type);
            self.unify(span, &this_type_applied, &obj_type_applied)?;
        }

        Ok(self.apply_subst(&ret_type))
    }

    /// Infer the type of a new expression.
    pub(in crate::infer) fn infer_new(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        span: Span,
    ) -> InferResult<Type> {
        let callee_type = self.infer_expr(env, callee)?;

        // Infer argument types
        let arg_types: Vec<Type> = arguments
            .iter()
            .map(|arg| self.infer_expr(env, arg))
            .collect::<InferResult<_>>()?;

        // The constructor returns some object type
        let result_type = self.fresh_type_var();
        let this_type = result_type.clone();

        // Expected constructor type: (this, args...) -> result
        // For 'new', the constructor should return something that becomes 'this'
        let expected_func = Type::func(this_type, arg_types, result_type.clone());

        self.unify(span, &callee_type, &expected_func)?;

        Ok(self.apply_subst(&result_type))
    }

    /// Infer a run of adjacent `function` declarations as a single
    /// binding group. Every name in the group is visible in every
    /// body from the start, which is what enables forward references
    /// and mutual recursion.
    pub(in crate::infer) fn infer_function_group(
        &mut self,
        env: &TypeEnv,
        group: &[Stmt],
    ) -> InferResult<TypeEnv> {
        let mut hoisted = self.hoist_function_names(env, group);

        // Pass 1: infer every body with the full hoisted env in scope, then
        // unify each function's type with its hoisted variable. Bindings
        // stay monomorphic here so peer references (still type variables at
        // this point) get filled in as their own bodies are processed.
        for stmt in group {
            if let Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                span,
            } = stmt
            {
                let func_var = hoisted
                    .lookup(name)
                    .expect("hoisted name must be in env")
                    .ty()
                    .clone();
                let func_type = self.infer_function(
                    &hoisted,
                    Some(name),
                    params,
                    body,
                    type_annotation,
                    *span,
                )?;
                self.unify(*span, &func_var, &func_type)?;
                // Key the recorded type by the *name* offset, not the
                // `function` keyword's offset, so the LSP resolver
                // (which returns the name span for go-to-def) can look
                // the type up directly.
                let name_offset = span.start + "function ".len();
                self.record_decl_type(
                    Span::new(name_offset, name_offset + name.len()),
                    func_type,
                );
            }
        }

        // Pass 2: every function in the group now has a fully resolved
        // monomorphic type sitting under its hoisted variable. Generalise
        // each against the *outer* env's free variables so all peers
        // receive the same polymorphism.
        let base_free = env.free_vars();
        for stmt in group {
            if let Stmt::FunctionDecl { name, .. } = stmt {
                let ty = hoisted
                    .lookup(name)
                    .expect("function must be in env after pass 1")
                    .ty()
                    .clone();
                let ty = self.apply_subst(&ty);
                let scheme = self.generalize(&base_free, &ty);
                hoisted = hoisted.extend(name.clone(), scheme);
            }
        }

        Ok(hoisted)
    }

    /// Pre-bind every top-level `function` declaration in `stmts` to a fresh
    /// type variable so they can refer to each other before being defined.
    ///
    /// This matches JavaScript's "hoisting" behaviour: function declarations
    /// (unlike function *expressions*) are visible throughout the enclosing
    /// scope from the moment the scope is entered. The inference side-effect
    /// is that two top-level functions can now call each other mutually,
    /// and a function can call a peer that appears later in the file.
    ///
    /// Each hoisted name is stored as a monomorphic binding so the
    /// `Stmt::FunctionDecl` handler can detect it and unify the hoisted
    /// variable with the inferred function type.
    pub(in crate::infer) fn hoist_function_names(
        &mut self,
        env: &TypeEnv,
        stmts: &[Stmt],
    ) -> TypeEnv {
        let mut new_env = env.clone();
        for stmt in stmts {
            if let Stmt::FunctionDecl { name, .. } = stmt {
                let var = self.fresh_type_var();
                new_env = new_env.extend(name.clone(), TypeScheme::mono(var));
            }
        }
        new_env
    }

    /// Handle a top-level `function` declaration statement.
    pub(in crate::infer) fn infer_stmt_function_decl(
        &mut self,
        env: &TypeEnv,
        name: &str,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        // Reuse the type variable hoisted by the enclosing scope if
        // this function was pre-bound there, otherwise start fresh.
        // Re-using the hoisted var is what lets mutually recursive
        // functions see each other's inferred types.
        let func_var = match env.lookup(name) {
            Some(scheme) if scheme.is_mono() => scheme.ty().clone(),
            _ => self.fresh_type_var(),
        };
        let pre_env = env.extend(name.to_string(), TypeScheme::mono(func_var.clone()));

        // Infer the function type
        let func_type =
            self.infer_function(&pre_env, Some(name), params, body, type_annotation, span)?;

        // Unify pre-bound type with inferred type
        self.unify(span, &func_var, &func_type)?;

        // Record the type at the *name* offset (not the `function`
        // keyword) so LSP go-to-def → hover lookups line up.
        let name_offset = span.start + "function ".len();
        self.record_decl_type(
            Span::new(name_offset, name_offset + name.len()),
            func_type.clone(),
        );

        // Generalize the function type
        let env_free = env.free_vars();
        let scheme = self.generalize(&env_free, &func_type);

        Ok((Type::Undefined, env.extend(name.to_string(), scheme)))
    }
}
