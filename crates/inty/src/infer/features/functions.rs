//! Function expressions, calls, `new`, and function declarations.

use std::collections::HashMap;

use crate::ast::free_idents::free_identifiers_in_function_body;
use crate::ast::{ExportDecl, Expr, Literal, Param, Stmt, TypeAnnotation};
use crate::span::Span;
use crate::types::{Type, TypePred, TypeScheme};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::type_parser::parse_type_annotation_with_pvars;
use super::super::InferResult;

/// Borrow-able view of a function declaration that abstracts over
/// `Stmt::FunctionDecl` and `Stmt::Export { declaration:
/// ExportDecl::Function }`. Hoisting and group inference need to treat
/// both forms uniformly so peer forward references and mutual recursion
/// across exports type-check.
#[allow(clippy::type_complexity)]
pub(in crate::infer) fn function_decl_parts<'a>(
    stmt: &'a Stmt,
) -> Option<(
    &'a str,
    &'a [Param],
    &'a Stmt,
    &'a Option<TypeAnnotation>,
    Option<&'a crate::types::TypeAst>,
    Span,
)> {
    match stmt {
        Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            return_type_ast,
            span,
        } => Some((
            name.as_str(),
            params.as_slice(),
            body.as_ref(),
            type_annotation,
            return_type_ast.as_ref(),
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
            None,
            *span,
        )),
        _ => None,
    }
}

impl InferState {
    /// Infer the type of a function expression.
    /// Infer a function-like body in its own `return`-collection frame and
    /// derive the type it returns: the join of every explicit `return`'s
    /// value, plus `Undefined` when control can fall off the end. A body
    /// that diverges with no `return` (e.g. `while True: …`) yields
    /// `never`, which subsumes into any declared type. When `widen`, each
    /// returned literal is widened to its base (the unannotated-inference
    /// rule) *before* joining, so `return 0; return n - 1;` doesn't try to
    /// unify `Lit(0)` with `Number`.
    ///
    /// Used for plain functions, object/class methods, and getters — any
    /// body whose `return`s must not leak into an enclosing function frame.
    pub(in crate::infer) fn infer_body_return_type(
        &mut self,
        body_env: &TypeEnv,
        body: &Stmt,
        widen: bool,
        span: Span,
    ) -> InferResult<Type> {
        self.return_value_stack.push(Vec::new());
        let body_result = self.infer_stmt(body_env, body);
        let returns = self
            .return_value_stack
            .pop()
            .expect("return frame balanced");
        body_result?;

        let mut parts = returns;
        if !definitely_returns(body) {
            parts.push(self.unit_type.clone());
        }
        if widen {
            for p in parts.iter_mut() {
                *p = p.widen_fresh_literals();
            }
        }
        Ok(if parts.is_empty() {
            Type::never()
        } else {
            let mut acc = parts[0].clone();
            for t in &parts[1..] {
                acc = self.join(span, &acc, t);
            }
            acc
        })
    }

    pub(in crate::infer) fn infer_function(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
        span: Span,
    ) -> InferResult<Type> {
        let this_type = self.fresh_type_var();
        self.infer_function_with_this(
            env,
            name,
            params,
            body,
            type_annotation,
            return_type_ast,
            this_type,
            span,
        )
    }

    /// Infer the type of a function expression with a pre-specified
    /// `this` type. Object-literal methods use this to ensure every
    /// method in the literal shares the same `this`; for free functions,
    /// `infer_function` calls this with a fresh `this` variable.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn infer_function_with_this(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
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
        // against it before the body is checked. Parameters with a
        // default value (`def f(x=1)`) become presence-polymorphic so a
        // call may omit the trailing argument; the rest are required.
        let func_params: Vec<crate::types::FuncParam> = params
            .iter()
            .zip(param_types.iter())
            .map(|(param, ty)| {
                let fp = if param.optional {
                    crate::types::FuncParam::optional(self.fresh_pvar(), ty.clone())
                } else {
                    crate::types::FuncParam::required(ty.clone())
                };
                // Record the parameter name for keyword-argument resolution.
                fp.with_name(param.name.clone())
            })
            .collect();
        let func_type = Type::wrap_callable(Type::raw_func_with_params(
            Some(this_type.clone()),
            func_params,
            ret_type.clone(),
        ));

        // A parameter with a (non-`None`) default constrains its type:
        // the parameter is unified with the default's *widened* type
        // (so `def f(x=1)` gives `x: Number`, not the literal `1`). The
        // default is evaluated in the defining scope. `=None` defaults
        // carry no `default` expression by construction, so they impose
        // no constraint — Python's idiomatic optional parameter.
        for (param, ty) in params.iter().zip(param_types.iter()) {
            // An explicit annotation (`def f(x: int)`) pins the
            // parameter's type. Lowered from the shared TypeAst IR;
            // unmodelled annotations lower to a fresh variable and so
            // impose no constraint (never a false positive).
            if let Some(type_ast) = &param.type_ast {
                let annotated = self.lower_type_ast_in_env_with_span(type_ast, env, param.span);
                self.unify(param.span, ty, &annotated)?;
            }
            if let Some(default) = &param.default {
                let default_type = self.infer_expr(env, default)?;
                let widened = default_type.widen_fresh_literals();
                self.unify(param.span, ty, &widened)?;
            }
        }

        // A return annotation (`def f() -> T`) pins the return type; the
        // body's result must subsume into it (enforced after the body is
        // checked, below). Unmodelled annotations lower to a fresh
        // variable and impose no constraint.
        if let Some(ret_ast) = return_type_ast {
            let annotated_ret = self.lower_type_ast_in_env_with_span(ret_ast, env, span);
            self.unify(span, &ret_type, &annotated_ret)?;
        }

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

        // Infer the body and derive its return type from the explicit
        // `return`s plus a fall-through `Undefined`. The body's
        // *completion* value is intentionally not used as the implicit
        // return: a function that falls off the end returns
        // `None`/`undefined`, regardless of any trailing expression
        // statement's type.
        let annotated = type_annotation.is_some() || return_type_ast.is_some();
        let inferred_ret = self.infer_body_return_type(&body_env, body, !annotated, span)?;

        // Without an annotation the return is a fresh-literal widening site
        // (`function f() { return "hi"; }` returns `String`, not
        // `Lit("hi")`); `infer_body_return_type` widens for us. With an
        // annotation the declared return governs and the body subsumes.
        if annotated {
            self.subsume(span, &inferred_ret, &ret_type)?;
        } else {
            self.unify(span, &ret_type, &inferred_ret)?;
        }

        Ok(self.zonk(&func_type))
    }

    /// Infer the type of a function call.
    pub(in crate::infer) fn infer_call(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
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
                let obj_type_applied = self.zonk(&obj_type);

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
                let obj_type_applied = self.zonk(&obj_type);

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
        if matches!(self.zonk(&callee_type), Type::Error) {
            // Still walk the argument expressions so any standalone
            // type errors *inside* them surface — recovery is
            // best-effort, not silence-everything.
            for arg in arguments {
                let _ = self.infer_expr(env, arg);
            }
            return Ok(Type::Error);
        }

        // Keyword arguments take a dedicated path: they're resolved to
        // parameter positions by *name* against the callee's named params,
        // which the synthesised-row positional path below can't see.
        if !keywords.is_empty() {
            return self.infer_keyword_call(
                env,
                &callee_type,
                obj_type_for_this,
                arguments,
                keywords,
                span,
            );
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
        let expected_func = self.callable_row_open(
            Some(this_type.clone()),
            param_vars.clone(),
            ret_type.clone(),
        );

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
            let expected = self.zonk(param);
            match arg {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    let inner = self.infer_expr(env, argument)?;
                    let elem = self.fresh_type_var();
                    self.unify(*spread_span, &inner, &Type::Array(Box::new(elem.clone())))?;
                    let elem_resolved = self.zonk(&elem);
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
            let obj_type_applied = self.zonk(&obj_type);
            // A nominal brand is transparent for method-receiver binding,
            // just as it is for field access: unroll it to its
            // representation row so the method body's `this`-row unifies
            // against the instance shape. The receiver's own type stays
            // nominal everywhere else.
            let obj_for_this = match &obj_type_applied {
                Type::Named(id, args) if self.is_nominal_type(*id) => self
                    .unroll_named(*id, args)
                    .unwrap_or_else(|| obj_type_applied.clone()),
                _ => obj_type_applied.clone(),
            };
            let this_type_applied = self.zonk(&this_type);
            self.unify(span, &this_type_applied, &obj_for_this)?;
        } else {
            let this_type_applied = self.zonk(&this_type);
            self.unify(span, &this_type_applied, &Type::Undefined)?;
        }

        Ok(self.zonk(&ret_type))
    }

    /// Infer a call that has keyword arguments. Resolves each keyword to a
    /// parameter slot *by name* against the callee's named parameters,
    /// then checks every filled slot and ensures no required parameter is
    /// left unfilled. An opaque/non-function callee (a bare variable) has
    /// no names to resolve against, so its arguments are merely
    /// type-checked and the call is accepted.
    fn infer_keyword_call(
        &mut self,
        env: &TypeEnv,
        callee_type: &Type,
        obj_for_this: Option<Type>,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
        span: Span,
    ) -> InferResult<Type> {
        let callee_z = self.zonk(callee_type);
        let Some((this_opt, params, ret)) = extract_callable(&callee_z) else {
            // No resolvable signature (opaque/variadic callee): check the
            // argument and keyword-value expressions so errors inside them
            // surface, and accept — impose no constraint.
            for a in arguments {
                self.infer_expr(env, a)?;
            }
            for (_, v) in keywords {
                self.infer_expr(env, v)?;
            }
            return Ok(self.fresh_type_var());
        };

        let n = params.len();
        if arguments.len() > n {
            return Err(crate::error::TypeError::ArityMismatch {
                expected: n,
                found: arguments.len() + keywords.len(),
                span,
            }
            .into());
        }

        // Fill slots: positionals first, then keywords by name.
        let mut slots: Vec<Option<&Expr>> = vec![None; n];
        for (i, a) in arguments.iter().enumerate() {
            slots[i] = Some(a);
        }
        for (name, value) in keywords {
            let idx = params
                .iter()
                .position(|p| p.name.as_deref() == Some(name.as_str()));
            let Some(idx) = idx else {
                return Err(crate::error::TypeError::InvalidSyntax {
                    message: format!("unexpected keyword argument '{}'", name),
                    span,
                }
                .into());
            };
            if slots[idx].is_some() {
                return Err(crate::error::TypeError::InvalidSyntax {
                    message: format!("got multiple values for argument '{}'", name),
                    span,
                }
                .into());
            }
            slots[idx] = Some(value);
        }

        // Check each slot; an unfilled *required* parameter is an error.
        for (i, slot) in slots.iter().enumerate() {
            match slot {
                Some(e) => {
                    let expected = self.zonk(&params[i].ty);
                    self.check_expr(env, e, &expected)?;
                }
                None => {
                    if params[i].presence.is_pre() {
                        let missing = params[i].name.clone().unwrap_or_else(|| i.to_string());
                        return Err(crate::error::TypeError::InvalidSyntax {
                            message: format!("missing required argument '{}'", missing),
                            span,
                        }
                        .into());
                    }
                }
            }
        }

        // Bind `this` as the positional path does: the receiver for a
        // method call (nominal brands are transparent here), else
        // `Undefined` for a free call.
        if let Some(t) = this_opt {
            let t = self.zonk(&t);
            let obj = match obj_for_this {
                Some(o) => {
                    let o = self.zonk(&o);
                    match &o {
                        Type::Named(id, args) if self.is_nominal_type(*id) => {
                            self.unroll_named(*id, args).unwrap_or(o)
                        }
                        _ => o,
                    }
                }
                None => Type::Undefined,
            };
            self.unify(span, &t, &obj)?;
        }

        Ok(self.zonk(&ret))
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
                    Ok(self.zonk(&elem))
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

        Ok(self.zonk(&result_type))
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
            if let Some((name, params, body, type_annotation, return_type_ast, span)) =
                function_decl_parts(stmt)
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
                    return_type_ast,
                    span,
                )?;
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
            if let Some((name, _, _, _, _, span)) = function_decl_parts(stmt) {
                let ty = hoisted
                    .lookup(name)
                    .expect("function must be in env after pass 1")
                    .ty()
                    .clone();
                let ty = self.zonk(&ty);
                // A factory lowered from a `class` gets its inferred
                // return row branded nominally, so two structurally
                // identical classes stay distinct types.
                let ty = if self.class_brand_names.contains(name) {
                    self.brand_class_factory(name, &ty, &base_free)
                } else {
                    ty
                };
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

    /// Wrap a class factory's inferred return row in a fresh nominal
    /// brand. `ty` is the factory's callable-row type
    /// (`{ <CALL>: (params) => Row }`); the result is the same callable
    /// row with its return type replaced by `Named(id, [vars])` after
    /// registering a nominal `TypeDef` whose representation is the
    /// original return row. Type vars of the row that would be
    /// generalised (free in the row but not in the surrounding env)
    /// become the brand's parameters, so a generic class like
    /// `class Box: self.value = v` brands per instantiation
    /// (`Box(1): Box<Number>`, `Box("x"): Box<String>`). Field and
    /// method access see *through* the brand to this representation;
    /// only identity is opaque. See `docs/pyi-import-mapping.md` §8.
    fn brand_class_factory(
        &mut self,
        name: &str,
        ty: &Type,
        env_free: &std::collections::HashSet<crate::types::TVarName>,
    ) -> Type {
        use crate::types::{FieldEntry, PropName, RowType, TVarName, TypeDef, CALLABLE_KEY};

        // Navigate to the callable row's `<CALL>` field.
        let Type::Row(row) = ty else {
            return ty.clone();
        };
        let call_key = PropName(CALLABLE_KEY.to_string());
        let Some(call_entry) = row.props.get(&call_key) else {
            return ty.clone();
        };
        let Type::Func {
            this_type,
            params,
            ret,
        } = &call_entry.ty
        else {
            return ty.clone();
        };

        // Generalised type vars of the return row become brand params.
        let mut brand_vars: Vec<TVarName> = ret
            .free_vars()
            .into_iter()
            .filter(|v| v.is_flex() && !env_free.contains(v))
            .collect();
        brand_vars.sort_by_key(|v| v.id());

        let id = self.fresh_type_id();
        self.register_named_type(TypeDef::nominal(
            id,
            name.to_string(),
            brand_vars.clone(),
            (**ret).clone(),
        ));
        self.class_brand_ids.insert(name.to_string(), id);

        let args: Vec<Type> = brand_vars.iter().map(|v| Type::var(v.clone())).collect();
        let branded_func = Type::Func {
            this_type: this_type.clone(),
            params: params.clone(),
            ret: Box::new(Type::Named(id, args)),
        };

        let mut new_props = row.props.clone();
        new_props.insert(
            call_key,
            FieldEntry {
                presence: call_entry.presence.clone(),
                ty: branded_func,
            },
        );
        Type::Row(RowType {
            props: new_props,
            tail: row.tail.clone(),
        })
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
            if let Some((name, _, _, _, _, _)) = function_decl_parts(stmt) {
                let var = self.fresh_type_var();
                new_env = new_env.extend(name.to_string(), TypeScheme::mono(var));
            }
        }
        new_env
    }

    /// Handle a top-level `function` declaration statement.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn infer_stmt_function_decl(
        &mut self,
        env: &TypeEnv,
        name: &str,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
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
        let func_type = self.infer_function(
            &pre_env,
            Some(name),
            params,
            body,
            type_annotation,
            return_type_ast,
            span,
        )?;

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

// ---------------------------------------------------------------------------
// SCC partition of hoistable function declarations
//
// Given a slice of statements representing one lexical scope, this returns
// the strongly-connected components of the call graph between the
// hoistable `function` declarations in source order, ordered
// topologically (callees before callers). Each SCC's contents are
// further sorted by source position so the inside-SCC inference order
// matches the user's mental model.
//
// This is the foundation of dependency-driven binding inference (see
// docs/scc-inference.md). The output drives infer_function_group
// calls: each SCC is processed as one mutually-recursive group, with
// earlier (callee) SCCs already generalised in the env by the time a
// later (caller) SCC is inferred. Forward references and mutual
// recursion that cross non-function statements (the htmx IIFE
// library pattern) type-check.
// ---------------------------------------------------------------------------

/// One hoistable function decl identified during the SCC pre-pass.
struct HoistableNode {
    /// Index into the original `stmts` slice. Lets us recover the
    /// `Stmt` after the SCC analysis has reordered things.
    stmt_index: usize,
    /// Names referenced inside this function's body, scoped to the
    /// outer environment (i.e., not bound locally by params, vars,
    /// inner functions, etc.).
    free: std::collections::HashSet<String>,
}

/// Compute strongly-connected components of the hoistable-function
/// call graph in `stmts`, returned in topological order. Each inner
/// `Vec<usize>` lists statement indices in source order.
///
/// Statements that aren't hoistable function declarations do not
/// appear in the output. The caller is responsible for interleaving
/// non-function statements with the SCC results.
pub(in crate::infer) fn compute_scc_groups(stmts: &[Stmt]) -> Vec<Vec<usize>> {
    // Pass 1: collect the hoistable function decls and their free
    // identifiers.
    let mut nodes: Vec<HoistableNode> = Vec::new();
    let mut name_to_node: HashMap<String, usize> = HashMap::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if let Some((name, params, body, _, _, _)) = function_decl_parts(stmt) {
            let free = free_identifiers_in_function_body(Some(name), params, body);
            let node_idx = nodes.len();
            nodes.push(HoistableNode {
                stmt_index: i,
                free,
            });
            // Duplicate function names in the same scope are
            // illegal but the parser accepts them; the last one
            // wins in the dependency map. The duplicate-name
            // diagnostic is handled elsewhere.
            name_to_node.insert(name.to_string(), node_idx);
        }
    }

    if nodes.is_empty() {
        return Vec::new();
    }

    // Pass 2: build the adjacency list. There's an edge i → j iff
    // node i's body references the name of node j.
    let n = nodes.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, node) in nodes.iter().enumerate() {
        for free_name in &node.free {
            if let Some(&j) = name_to_node.get(free_name) {
                if !adj[i].contains(&j) {
                    adj[i].push(j);
                }
            }
        }
    }

    // Pass 3: Tarjan's SCC algorithm. Iterative implementation to
    // avoid blowing the stack on deep call chains (unlikely in
    // practice — htmx's ~190 function decls give a depth ≤ ~190 —
    // but the iterative form has the same complexity and is robust).
    let sccs = tarjan_scc(&adj);

    // Pass 4: translate back to statement indices and sort each SCC
    // by source position. Tarjan emits in reverse topological order
    // of the condensation graph (leaf SCCs first), which is exactly
    // the order we want for inference (callees generalised before
    // callers see them).
    sccs.into_iter()
        .map(|scc| {
            let mut indices: Vec<usize> = scc
                .into_iter()
                .map(|node_id| nodes[node_id].stmt_index)
                .collect();
            indices.sort_unstable();
            indices
        })
        .collect()
}

/// Extract `(this, params, ret)` from a callable type — a callable row
/// `{<CALL>: (params) => ret, …}` or a bare function. `None` when `ty`
/// isn't a function shape (e.g. an unresolved variable), so keyword
/// resolution can fall back to accepting the call.
fn extract_callable(ty: &Type) -> Option<(Option<Type>, Vec<crate::types::FuncParam>, Type)> {
    use crate::types::{PropName, CALLABLE_KEY};
    let func = match ty {
        Type::Row(row) => &row.props.get(&PropName(CALLABLE_KEY.to_string()))?.ty,
        Type::Func { .. } => ty,
        _ => return None,
    };
    if let Type::Func {
        this_type,
        params,
        ret,
    } = func
    {
        Some((
            this_type.as_deref().cloned(),
            params.clone(),
            (**ret).clone(),
        ))
    } else {
        None
    }
}

/// Tarjan's strongly-connected components algorithm. Iterative
/// implementation so deep call graphs don't blow the system stack.
///
/// `adj` is the adjacency list of the dependency graph (node `i`'s
/// out-edges point to other nodes it depends on). The returned
/// `Vec<Vec<usize>>` lists SCCs in reverse topological order of the
/// condensation — leaves first, roots last. That's exactly the
/// order we want for binding inference: a caller's SCC sees its
/// callees' SCCs already generalised in the environment.
fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    enum Step {
        /// First visit to `v` — assign index, push onto stack, then
        /// try to descend into successors.
        Enter(usize),
        /// Returning to `v` after its `i`'th successor `child`
        /// finished. Update lowlink, then try the next successor.
        Resume { v: usize, i: usize, child: usize },
    }

    let n = adj.len();
    let mut index: Vec<Option<usize>> = vec![None; n];
    let mut lowlink: Vec<usize> = vec![0; n];
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut result: Vec<Vec<usize>> = Vec::new();
    let mut next_index: usize = 0;
    let mut work: Vec<Step> = Vec::new();

    // Helper closure: try to descend into the `i`'th successor of
    // `v`. If one needs to be explored, push the Resume frame for
    // `v` and an Enter frame for the successor and return without
    // closing. Otherwise close v (popping any SCC it roots).
    let descend_or_close = |mut i: usize,
                            v: usize,
                            index: &mut Vec<Option<usize>>,
                            lowlink: &mut Vec<usize>,
                            on_stack: &mut Vec<bool>,
                            stack: &mut Vec<usize>,
                            result: &mut Vec<Vec<usize>>,
                            work: &mut Vec<Step>| {
        while i < adj[v].len() {
            let w = adj[v][i];
            if index[w].is_none() {
                work.push(Step::Resume { v, i, child: w });
                work.push(Step::Enter(w));
                return;
            }
            if on_stack[w] {
                lowlink[v] = lowlink[v].min(index[w].unwrap());
            }
            i += 1;
        }
        // No more successors — close v.
        if Some(lowlink[v]) == index[v] {
            let mut scc: Vec<usize> = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            result.push(scc);
        }
    };

    for root in 0..n {
        if index[root].is_some() {
            continue;
        }
        work.push(Step::Enter(root));
        while let Some(step) = work.pop() {
            match step {
                Step::Enter(v) => {
                    index[v] = Some(next_index);
                    lowlink[v] = next_index;
                    next_index += 1;
                    stack.push(v);
                    on_stack[v] = true;
                    descend_or_close(
                        0,
                        v,
                        &mut index,
                        &mut lowlink,
                        &mut on_stack,
                        &mut stack,
                        &mut result,
                        &mut work,
                    );
                }
                Step::Resume { v, i, child } => {
                    lowlink[v] = lowlink[v].min(lowlink[child]);
                    descend_or_close(
                        i + 1,
                        v,
                        &mut index,
                        &mut lowlink,
                        &mut on_stack,
                        &mut stack,
                        &mut result,
                        &mut work,
                    );
                }
            }
        }
    }
    result
}

/// Conservative "does control definitely leave via `return`/`throw`
/// rather than fall off the end" analysis, used to decide whether a
/// function's inferred return type must also include `Undefined` (the
/// implicit `None`/`undefined` of a fall-through). Erring toward `false`
/// is sound: it only adds `Undefined`, matching the runtime fall-through.
fn definitely_returns(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return { .. } | Stmt::Throw { .. } => true,
        Stmt::Block { body, .. } => body.last().is_some_and(definitely_returns),
        Stmt::Labeled { body, .. } => definitely_returns(body),
        // Both arms must return for the `if` to be exhaustive; a missing
        // `else` can fall through.
        Stmt::If {
            consequent,
            alternate: Some(alt),
            ..
        } => definitely_returns(consequent) && definitely_returns(alt),
        // `try` completes abnormally only if every path that can reach the
        // end returns: the body (and, if present, the handler). A
        // `finally` that returns dominates everything.
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            if let Some(fin) = finalizer {
                if definitely_returns(fin) {
                    return true;
                }
            }
            definitely_returns(block)
                && handler
                    .as_ref()
                    .is_some_and(|h| definitely_returns(&h.body))
        }
        // `while True:` (with no `break`) never falls through. We don't
        // scan for `break`; treating it as terminating is the common
        // infinite-loop / loop-until-return idiom.
        Stmt::While { test, .. } => {
            matches!(
                test,
                Expr::Lit {
                    value: Literal::Boolean(true),
                    ..
                }
            )
        }
        _ => false,
    }
}

#[cfg(test)]
mod scc_tests {
    use super::*;

    #[test]
    fn singleton_no_edges() {
        // a()  — no calls; one trivial SCC.
        let sccs = tarjan_scc(&vec![Vec::new()]);
        assert_eq!(sccs, vec![vec![0]]);
    }

    #[test]
    fn linear_chain_produces_singleton_sccs_in_topo_order() {
        // a → b → c (a calls b calls c).
        // Expected output: [c], [b], [a] (callees first, then callers).
        let adj = vec![vec![1], vec![2], vec![]];
        let sccs = tarjan_scc(&adj);
        assert_eq!(sccs, vec![vec![2], vec![1], vec![0]]);
    }

    #[test]
    fn mutual_recursion_collapses_to_one_scc() {
        // a ↔ b (mutual recursion). Both end up in the same SCC.
        let adj = vec![vec![1], vec![0]];
        let sccs = tarjan_scc(&adj);
        assert_eq!(sccs.len(), 1);
        let mut got = sccs[0].clone();
        got.sort();
        assert_eq!(got, vec![0, 1]);
    }

    #[test]
    fn independent_and_recursive_split_correctly() {
        // a (independent), b ↔ c (mutually recursive).
        let adj = vec![vec![], vec![2], vec![1]];
        let sccs = tarjan_scc(&adj);
        assert_eq!(sccs.len(), 2);
        // One singleton SCC {0}, one paired SCC {1, 2}.
        let mut sizes: Vec<usize> = sccs.iter().map(|s| s.len()).collect();
        sizes.sort();
        assert_eq!(sizes, vec![1, 2]);
    }

    #[test]
    fn self_loop_is_its_own_scc() {
        // a → a.
        let adj = vec![vec![0]];
        let sccs = tarjan_scc(&adj);
        assert_eq!(sccs, vec![vec![0]]);
    }

    #[test]
    fn topo_order_caller_after_callee() {
        // c is leaf, b calls c, a calls b. Expected order: c first, then b, then a.
        let adj = vec![vec![1], vec![2], vec![]];
        let sccs = tarjan_scc(&adj);
        // c, b, a
        assert_eq!(sccs[0], vec![2]);
        assert_eq!(sccs[1], vec![1]);
        assert_eq!(sccs[2], vec![0]);
    }
}
