//! Function expressions, calls, `new`, and function declarations.

use crate::lexer::Span;
use crate::parser::ast::{ExportDecl, Expr, Param, Stmt, TypeAnnotation};
use crate::types::{Type, TypePred, TypeScheme};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::type_parser::{
    parse_type_annotation_with_aliases, parse_type_annotation_with_pvars,
};
use super::super::InferResult;

/// Borrow-able view of a function declaration that abstracts over
/// `Stmt::FunctionDecl` and `Stmt::Export { declaration:
/// ExportDecl::Function }`. Hoisting and group inference need to treat
/// both forms uniformly so peer forward references and mutual recursion
/// across exports type-check.
fn function_decl_parts<'a>(
    stmt: &'a Stmt,
) -> Option<(
    &'a str,
    &'a [Param],
    &'a Stmt,
    &'a Option<TypeAnnotation>,
    Span,
)> {
    match stmt {
        Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            span,
        } => Some((
            name.as_str(),
            params.as_slice(),
            body.as_ref(),
            type_annotation,
            *span,
        )),
        Stmt::Export {
            declaration:
                ExportDecl::Function {
                    name,
                    params,
                    body,
                    type_annotation,
                    span,
                },
            ..
        } => Some((
            name.as_str(),
            params.as_slice(),
            body.as_ref(),
            type_annotation,
            *span,
        )),
        _ => None,
    }
}

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
        let this_type = self.fresh_type_var();
        self.infer_function_with_this(env, name, params, body, type_annotation, this_type, span)
    }

    /// Infer the type of a function expression with a pre-specified
    /// `this` type. Object-literal methods use this to ensure every
    /// method in the literal shares the same `this`; for free functions,
    /// `infer_function` calls this with a fresh `this` variable.
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
        let param_types: Vec<Type> = params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let ty = self.fresh_type_var();
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

        let ret_type = self.fresh_type_var();

        // Build the function type up front so the body can refer to it
        // (recursion via `name`) and so any annotation can be unified
        // against it before the body is checked.
        let func_type = Type::func(this_type.clone(), param_types.clone(), ret_type.clone());

        if let Some(annotation) = type_annotation {
            let annotation_span = Span::new(annotation.span.start, annotation.span.end);
            let (annotated_type, var_map, next_pvar) = parse_type_annotation_with_pvars(
                &annotation.content,
                annotation_span,
                self.next_var_id(),
                self.next_pvar_id(),
                &self.type_aliases,
            )?;
            if let Some(&max) = var_map.values().max() {
                self.bump_var_id_to(max + 1);
            }
            self.bump_pvar_id_to(next_pvar);

            // Function annotation: pins the function's signature to
            // the declared one. Subsume rather than unify so a body
            // annotated to return `String` can hold a literal.
            self.subsume(annotation_span, &func_type, &annotated_type)?;
        }

        let mut body_env = env.extend("this".to_string(), TypeScheme::mono(this_type));

        for (param, ty) in params.iter().zip(param_types.iter()) {
            body_env = body_env.extend(param.name.clone(), TypeScheme::mono(ty.clone()));
            // Record per-param type for the LSP / hover. Keyed by the
            // param's name span so we can look it up at any reference
            // to the parameter.
            self.record_decl_type(param.span, ty.clone());
        }

        if let Some(fn_name) = name {
            body_env = body_env.extend(fn_name.to_string(), TypeScheme::mono(func_type.clone()));
        }

        let (body_type, _) = self.infer_stmt(&body_env, body)?;

        // Without an annotation pinning the return type, the inferred
        // return is a fresh-literal widening site: `function f() {
        // return "hi"; }` has return type `String`, not `Lit("hi")`,
        // matching the behaviour at `var f = "hi"`. With an annotation
        // the declared return governs and the body merely subsumes
        // into it.
        if type_annotation.is_some() {
            self.subsume(span, &body_type, &ret_type)?;
        } else {
            let widened = body_type.widen_fresh_literals();
            self.unify(span, &ret_type, &widened)?;
        }

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
                    self.infer_member_on_type(&obj_type_applied, property, *member_span)?;

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

        // Error sentinel propagates through calls. If the callee
        // already failed to infer, every `Error(args)` site
        // re-produces `Error` so a single upstream failure doesn't
        // spawn one diagnostic per call site.
        if matches!(self.apply_subst(&callee_type), Type::Error) {
            // Still walk the argument expressions so any standalone
            // type errors *inside* them surface — recovery is
            // best-effort, not silence-everything.
            for arg in arguments {
                let _ = self.infer_expr(env, arg);
            }
            return Ok(Type::Error);
        }

        // Bidirectional checking (Peyton Jones 2007 §4): pin down the
        // callee's signature first with fresh parameter variables, then
        // check each argument against its resolved parameter type via
        // `subsume`. This pushes the expected param type into the
        // argument's checking judgement so a value like
        // `{kind: "circle", r: 10}` can match a discriminated-union arm
        // through subsumption (S-UnionR) rather than failing because
        // its top-level shape only equals one arm modulo literal
        // widening — which `unify` alone can't see through.
        //
        // Synthesis order is unchanged for the spread case: an
        // `...expr` argument is synthesised before we know the
        // parameter type because we need to extract its element type.
        let param_vars: Vec<Type> = (0..arguments.len())
            .map(|_| self.fresh_type_var())
            .collect();

        // Fresh types for this and return
        let this_type = self.fresh_type_var();
        let ret_type = self.fresh_type_var();

        // Expected callable shape — an *open* callable row so the
        // callee can carry additional fields (e.g. `String`, a
        // constructor with statics). Row polymorphism's fresh tail
        // absorbs whatever extras the callee happens to have.
        let expected_func =
            self.callable_row_open(Some(this_type.clone()), param_vars.clone(), ret_type.clone());

        // Unify callee with expected function type. After this, each
        // `param_vars[i]` is bound to the callee's i-th parameter
        // type (which may itself contain unresolved variables for a
        // polymorphic callee — those resolve as we check the args).
        self.unify(span, &callee_type, &expected_func)?;

        // Check each argument against its resolved parameter type.
        // `check_expr` is the bidirectional entry point: for object
        // literals against a row/union-of-rows, it pushes the
        // expected per-field types into the property values so
        // singleton literal types survive (`{kind: "circle"}` keeps
        // `kind: "circle"`, not the widened `kind: String`). For
        // every other shape it falls back to synth + subsume.
        //
        // `...expr` (Expr::Spread) in argument position unwraps the
        // inner array to its element type and is treated as a single
        // argument — inty has no variadic call shape, so a spread
        // can't expand into N arguments. Callers that rely on
        // variadic semantics will see an arity error from the unify
        // above; callers that want a single-arg function fed from an
        // array's element will type-check correctly.
        for (arg, param) in arguments.iter().zip(param_vars.iter()) {
            let expected = self.apply_subst(param);
            match arg {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    let inner = self.infer_expr(env, argument)?;
                    let elem = self.fresh_type_var();
                    self.unify(*spread_span, &inner, &Type::Array(Box::new(elem.clone())))?;
                    let elem_resolved = self.apply_subst(&elem);
                    self.subsume(*spread_span, &elem_resolved, &expected)?;
                }
                _ => {
                    self.check_expr(env, arg, &expected)?;
                }
            }
        }

        // If this is a method call, also unify 'this' with the object type
        // This happens AFTER the main unification, so type variables in the
        // method signature have already been connected to the return type.
        // For a free call (no `obj_type_for_this`), pin `this` to
        // `Undefined`: at runtime a free invocation has no receiver,
        // so a callee whose body actually references `this.foo` —
        // i.e. whose `this` was inferred to a concrete row — would
        // crash. Unifying with `Undefined` is a no-op when the
        // callee's `this` is still a fresh variable (truly
        // `this`-agnostic functions are unaffected) and produces a
        // type error when it's a concrete row, catching detached
        // method calls like `var f = obj.m; f();` at type-check time.
        if let Some(obj_type) = obj_type_for_this {
            let obj_type_applied = self.apply_subst(&obj_type);
            let this_type_applied = self.apply_subst(&this_type);
            self.unify(span, &this_type_applied, &obj_type_applied)?;
        } else {
            let this_type_applied = self.apply_subst(&this_type);
            self.unify(span, &this_type_applied, &Type::Undefined)?;
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

        // Infer argument types. `...expr` (Expr::Spread) in argument
        // position unwraps the inner array to its element type and is
        // treated as a single argument — inty has no variadic call
        // shape, so a spread can't expand into N arguments. Callers
        // that rely on variadic semantics will see an arity error
        // here; callers that want a single-arg function fed from an
        // array's element will type-check correctly.
        let arg_types: Vec<Type> = arguments
            .iter()
            .map(|arg| match arg {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    let inner = self.infer_expr(env, argument)?;
                    let elem = self.fresh_type_var();
                    self.unify(*spread_span, &inner, &Type::Array(Box::new(elem.clone())))?;
                    Ok(self.apply_subst(&elem))
                }
                _ => self.infer_expr(env, arg),
            })
            .collect::<InferResult<_>>()?;

        // The constructor returns some object type
        let result_type = self.fresh_type_var();
        let this_type = result_type.clone();

        // Expected constructor shape — an *open* callable row so the
        // constructor value can carry additional static fields beyond
        // the call signature (matches the unified callable-row design).
        let expected_func = self.callable_row_open(Some(this_type), arg_types, result_type.clone());

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
        // Both `function f` and `export function f` participate; the
        // helper function_decl_parts unifies the two shapes.
        for stmt in group {
            if let Some((name, params, body, type_annotation, span)) = function_decl_parts(stmt) {
                let func_var = hoisted
                    .lookup(name)
                    .expect("hoisted name must be in env")
                    .ty()
                    .clone();
                let func_type =
                    self.infer_function(&hoisted, Some(name), params, body, type_annotation, span)?;
                self.unify(span, &func_var, &func_type)?;
                // Key the recorded type by the *name* offset so the LSP
                // resolver (which returns the name span for go-to-def)
                // can look the type up directly. The exported form is
                // prefixed with `export `, so the keyword offset
                // accounts for that.
                let keyword_len = if matches!(stmt, Stmt::Export { .. }) {
                    "export function ".len()
                } else {
                    "function ".len()
                };
                let name_offset = span.start + keyword_len;
                self.record_decl_type(Span::new(name_offset, name_offset + name.len()), func_type);
            }
        }

        // Pass 2: every function in the group now has a fully resolved
        // monomorphic type sitting under its hoisted variable. Generalise
        // each against the *outer* env's free variables so all peers
        // receive the same polymorphism.
        let base_free = env.free_vars();
        for stmt in group {
            if let Some((name, _, _, _, span)) = function_decl_parts(stmt) {
                let ty = hoisted
                    .lookup(name)
                    .expect("function must be in env after pass 1")
                    .ty()
                    .clone();
                let ty = self.apply_subst(&ty);
                let scheme = self.generalize(&base_free, &ty);
                let keyword_len = if matches!(stmt, Stmt::Export { .. }) {
                    "export function ".len()
                } else {
                    "function ".len()
                };
                let name_offset = span.start + keyword_len;
                self.record_decl_scheme(
                    Span::new(name_offset, name_offset + name.len()),
                    scheme.clone(),
                );
                hoisted = hoisted.extend(name.to_string(), scheme);
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
            if let Some((name, _, _, _, _)) = function_decl_parts(stmt) {
                let var = self.fresh_type_var();
                new_env = new_env.extend(name.to_string(), TypeScheme::mono(var));
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
        let name_span = Span::new(name_offset, name_offset + name.len());
        self.record_decl_type(name_span, func_type.clone());

        // Generalize the function type
        let env_free = env.free_vars();
        let scheme = self.generalize(&env_free, &func_type);
        self.record_decl_scheme(name_span, scheme.clone());

        Ok((Type::Undefined, env.extend(name.to_string(), scheme)))
    }
}
