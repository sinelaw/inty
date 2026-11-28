//! Function expressions, calls, `new`, and function declarations.

use std::collections::HashMap;

use crate::ast::free_idents::free_identifiers_in_function_body;
use crate::ast::{ExportDecl, Expr, Literal, Param, Stmt, TypeAnnotation, VarDeclarator, VarKind};
use crate::span::Span;
use crate::types::{TVarName, Type, TypePred, TypeScheme};

use super::super::env::{Mutability, TypeEnv};
use super::super::state::InferState;
use super::super::type_parser::{
    parse_type_annotation_with_preds, parse_type_annotation_with_pvars,
};
use super::super::InferResult;

/// Borrow-able view of a function declaration that abstracts over
/// `Stmt::FunctionDecl`, `Stmt::Export { declaration:
/// ExportDecl::Function }` and a function-valued `const` (see
/// [`const_function_decl`]). Hoisting and group inference need to treat
/// these forms uniformly so peer forward references and mutual recursion
/// type-check, and so a function-valued `const` has its principal
/// (generalised) type before the hoisted functions that use it.
#[allow(clippy::type_complexity)]
pub(in crate::infer) fn function_decl_parts(
    stmt: &Stmt,
) -> Option<(
    &str,
    &[Param],
    &Stmt,
    &Option<TypeAnnotation>,
    Option<&crate::types::TypeAst>,
    Span,
)> {
    match stmt {
        Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            return_type_ast,
            name_span: _,
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
                    name_span: _,
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
        _ => const_function_decl(stmt).map(|(decl, params, body, type_annotation, span)| {
            (
                decl.name.as_str(),
                params,
                body,
                type_annotation,
                None,
                span,
            )
        }),
    }
}

/// `const f = <anonymous function>` — a single-declarator, unannotated
/// `const` whose initialiser is a function (or arrow) expression.
///
/// For *typing* this behaves exactly like `function f`: the binding
/// can't be reassigned and the initialiser has no effects, so inferring
/// it in dependency order rather than source order changes nothing but
/// which types are known when. It matters because `infer_stmt_list`
/// infers every hoisted `function` before any source-order statement: a
/// hoisted function that calls `f` would otherwise see only `f`'s
/// monomorphic placeholder, pinning `f` to that one use. (Runtime TDZ is
/// unaffected — inty doesn't model it for placeholders either.)
#[allow(clippy::type_complexity)]
pub(in crate::infer) fn const_function_decl(
    stmt: &Stmt,
) -> Option<(
    &VarDeclarator,
    &[Param],
    &Stmt,
    &Option<TypeAnnotation>,
    Span,
)> {
    let Stmt::Var {
        kind: VarKind::Const,
        declarations,
        ..
    } = stmt
    else {
        return None;
    };
    let [decl] = declarations.as_slice() else {
        return None;
    };
    if decl.type_annotation.is_some() || decl.type_ast.is_some() {
        return None;
    }
    match &decl.init {
        Some(Expr::Function {
            name: None,
            params,
            body,
            type_annotation,
            arrow: _,
            span,
        }) => Some((
            decl,
            params.as_slice(),
            body.as_ref(),
            type_annotation,
            *span,
        )),
        _ => None,
    }
}

/// Whether a hoisted function is an arrow function (`const f = () => …`).
pub(in crate::infer) fn hoisted_is_arrow(stmt: &Stmt) -> bool {
    matches!(
        const_function_decl(stmt).map(|(decl, ..)| &decl.init),
        Some(Some(Expr::Function { arrow: true, .. }))
    )
}

/// Where a hoisted function's name is declared, for its binding key: the
/// statement for `function f`, the declarator for `const f = …`.
pub(in crate::infer) fn hoisted_key_span(stmt: &Stmt) -> Option<Span> {
    match stmt {
        Stmt::FunctionDecl { span, .. }
        | Stmt::Export {
            declaration: ExportDecl::Function { span, .. },
            ..
        } => Some(*span),
        _ => const_function_decl(stmt).map(|(decl, ..)| decl.span),
    }
}

/// `function f` can be reassigned; a function-valued `const` cannot.
fn hoisted_mutability(stmt: &Stmt) -> super::super::env::Mutability {
    if const_function_decl(stmt).is_some() {
        super::super::env::Mutability::Immutable
    } else {
        super::super::env::Mutability::Mutable
    }
}

/// Which function-valued `const`s in a statement list are inferred with
/// the hoisted functions (statement indices).
///
/// Only those whose bodies don't depend — directly or through other such
/// `const`s — on a binding of this scope that is still a monomorphic
/// placeholder during hoisted inference (any other `var` / `let` /
/// `const`). A `const` that does, e.g. `const g = () => alias(1)` after
/// `const alias = id`, is left in source order so it sees that binding's
/// real (possibly polymorphic) type, exactly as before.
pub(in crate::infer) fn hoistable_const_functions(
    stmts: &[Stmt],
) -> std::collections::HashSet<usize> {
    use std::collections::HashSet;
    let mut candidates: HashSet<usize> = stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| const_function_decl(s).is_some())
        .map(|(i, _)| i)
        .collect();
    let mut placeholders: HashSet<String> = HashSet::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if candidates.contains(&i) {
            continue;
        }
        let decls = match stmt {
            Stmt::Var { declarations, .. } => declarations,
            Stmt::Export {
                declaration: ExportDecl::Var { declarations, .. },
                ..
            } => declarations,
            _ => continue,
        };
        placeholders.extend(decls.iter().map(|d| d.name.clone()));
    }
    let free: std::collections::HashMap<usize, HashSet<String>> = candidates
        .iter()
        .map(|&i| {
            let (decl, params, body, _, _) = const_function_decl(&stmts[i]).expect("candidate");
            (
                i,
                free_identifiers_in_function_body(Some(&decl.name), params, body),
            )
        })
        .collect();
    loop {
        let blocked: Vec<usize> = candidates
            .iter()
            .copied()
            .filter(|i| free[i].iter().any(|n| placeholders.contains(n)))
            .collect();
        if blocked.is_empty() {
            return candidates;
        }
        for i in blocked {
            candidates.remove(&i);
            let (decl, ..) = const_function_decl(&stmts[i]).expect("candidate");
            placeholders.insert(decl.name.clone());
        }
    }
}

/// Where a hoistable declaration's name is recorded for the LSP /
/// decorator (`record_decl_type`): the identifier after the `function`
/// keyword, or the declarator of a function-valued `const`.
fn hoisted_name_span(stmt: &Stmt, name: &str, span: Span) -> Span {
    if let Some((decl, ..)) = const_function_decl(stmt) {
        return decl.span;
    }
    stmt.function_name_span()
        .unwrap_or_else(|| crate::ast::function_name_span(None, span, name))
}

impl InferState {
    /// Infer the type of a function expression.
    /// Infer a function-like body in its own `return`-collection frame and
    /// derive the type it returns: the join of every explicit `return`'s
    /// value, plus `Undefined` when control can fall off the end. A body
    /// that diverges with no `return` (e.g. `while True: …`) yields a
    /// fresh type variable: it gives no value, so any type will do. When `widen`, each
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
        self.infer_body_return_type_expecting(body_env, body, widen, None, span)
    }

    /// [`Self::infer_body_return_type`] where the return type is known
    /// (annotated): each `return` is checked against `expected` rather
    /// than the returns joined.
    pub(in crate::infer) fn infer_body_return_type_expecting(
        &mut self,
        body_env: &TypeEnv,
        body: &Stmt,
        widen: bool,
        expected: Option<Type>,
        span: Span,
    ) -> InferResult<Type> {
        let member = std::mem::take(&mut self.member_function);
        self.return_value_stack.push(Vec::new());
        self.return_expected_stack.push(expected);
        let body_result = self.infer_stmt(body_env, body);
        self.return_expected_stack.pop();
        let returns = self
            .return_value_stack
            .pop()
            .expect("return frame balanced");
        body_result?;

        let mut parts = returns;
        if !definitely_returns(body, &self.exhaustive_switches) {
            parts.push(self.unit_type.clone());
        }
        if widen {
            for p in parts.iter_mut() {
                *p = self.widen(span, p);
            }
        }
        Ok(if parts.is_empty() {
            if member {
                // A member's: the object's type holds it as it is, so a
                // type variable would be fixed by its first use (`fail`
                // used as a number, then as a string); `never` joins with
                // any type where the call's value is used.
                Type::never()
            } else {
                // A body that never completes (it only throws, or loops
                // forever) gives no value: any type is its result, a type
                // variable a binding generalises, as the Lean model leaves
                // it. (`never`, the empty union, unified with no other
                // return type: `c ? f : g` with `g` returning a number was
                // refused.)
                self.fresh_type_var()
            }
        } else {
            let mut acc = parts[0].clone();
            for t in &parts[1..] {
                acc = self.join(span, &acc, t)?;
            }
            acc
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn infer_function(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
        arrow: bool,
        span: Span,
    ) -> InferResult<Type> {
        // An arrow function has no `this` of its own, and isn't a
        // constructor.
        let this_type = if arrow {
            Type::ArrowThis
        } else {
            self.fresh_type_var()
        };
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
        self.infer_function_expecting(
            env,
            name,
            params,
            body,
            type_annotation,
            return_type_ast,
            this_type,
            None,
            span,
        )
    }

    /// Check a function literal against a known function type — an
    /// annotation (`/** const f: () => S */ const f = () => …`) or the
    /// parameter it is passed to (`xs.map((x, i) => …)`). The expected
    /// parameter types are the literal's (so its body sees them), each
    /// `return` is checked against the expected result (so a returned
    /// `{n: xs.length}` fits `{n: Number}`), and a literal with fewer
    /// parameters than expected ignores the extra arguments, as
    /// JavaScript does (`xs.map(() => 0)`): its type takes them anyway.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn check_function_literal(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        expected_params: Vec<crate::types::FuncParam>,
        expected_ret: Type,
        arrow: bool,
        span: Span,
    ) -> InferResult<Type> {
        let this_type = if arrow {
            Type::ArrowThis
        } else {
            self.fresh_type_var()
        };
        // A concise arrow (`(e) => list.push(e)`) where the result is
        // `Undefined` runs for its effect: its value is discarded, like a
        // TypeScript `void` callback's. A block body still returns what
        // it says.
        let discarded;
        let body = match (self.zonk_head(&expected_ret), concise_body(body)) {
            (Type::Undefined, Some((expr, ret_span))) => {
                let mut stmts = match body {
                    Stmt::Block { body, .. } => body[..body.len() - 1].to_vec(),
                    _ => unreachable!("a concise body is a block"),
                };
                stmts.push(Stmt::Expr {
                    expression: expr.clone(),
                    span: ret_span,
                });
                discarded = Stmt::Block {
                    body: stmts,
                    span: ret_span,
                };
                &discarded
            }
            _ => body,
        };
        self.infer_function_expecting(
            env,
            name,
            params,
            body,
            &None,
            None,
            this_type,
            Some((expected_params, expected_ret)),
            span,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_function_expecting(
        &mut self,
        env: &TypeEnv,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
        this_type: Type,
        expected: Option<(Vec<crate::types::FuncParam>, Type)>,
        span: Span,
    ) -> InferResult<Type> {
        // (Taken here, so that nothing inferred before the body, such as a
        // parameter's default, takes it.)
        let member = std::mem::take(&mut self.member_function);
        let method = std::mem::take(&mut self.annotated_method);
        // A body says whether a function is a method: one that mentions
        // `this` reads it. Recorded, so that a call that met this
        // function's `this` before it was known calls it on its receiver
        // (`settle_receivers`).
        if let Type::Var(TVarName::Flex(id)) = &this_type {
            if let Some(at) = crate::ast::free_idents::first_this_in_stmt(body) {
                self.method_this_vars.push(*id);
                self.record_origin(
                    TVarName::Flex(*id),
                    crate::error::TypeOrigin::ThisInBody { span: at },
                );
            }
        }
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
        let mut func_params: Vec<crate::types::FuncParam> = params
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
        // Checked against an expected type: the parameters are the
        // expected ones, and the arguments the literal doesn't name are
        // accepted and ignored.
        let mut expected_ret = None;
        if let Some((expected_params, ret)) = expected {
            for (i, ep) in expected_params.iter().enumerate() {
                match param_types.get(i) {
                    Some(ty) if !params[i].optional => self.unify(params[i].span, ty, &ep.ty)?,
                    Some(_) => {}
                    // A required argument the literal ignores. (An
                    // optional one is simply absent from its type.)
                    None if ep.presence.is_pre() => func_params.push(crate::types::FuncParam {
                        presence: ep.presence.clone(),
                        ty: ep.ty.clone(),
                        name: None,
                    }),
                    None => {}
                }
            }
            let ret = self.zonk_head(&ret);
            if !matches!(ret, Type::Var(TVarName::Flex(_))) {
                expected_ret = Some(ret);
            }
        }
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
                let widened = self.widen(default.span(), &default_type);
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
        if let Some(ret) = &expected_ret {
            self.unify(span, &ret_type, ret)?;
        }

        let parsed_annotation = type_annotation.as_ref().and_then(|annotation| {
            let annotation_span = Span::new(annotation.span.start, annotation.span.end);
            let parsed = parse_type_annotation_with_pvars(
                &annotation.content,
                annotation_span,
                annotation.content_start,
                self.next_var_id(),
                self.next_pvar_id(),
                &self.type_aliases,
            );
            self.annotation_or_report(parsed)
                .map(|parsed| (annotation_span, parsed))
        });
        if let Some((annotation_span, (annotated_type, var_map, next_pvar))) = parsed_annotation {
            if let Some(&max) = var_map.values().max() {
                self.bump_var_id_to(max + 1);
            }
            self.bump_pvar_id_to(next_pvar);

            // Function annotation: pins the function's signature to
            // the declared one, which is called detached unless it says
            // otherwise (a method's, with the method's `this`). Subsume
            // rather than unify so a body annotated to return `String`
            // can hold a literal.
            let called_with = if method {
                this_type.clone()
            } else {
                Type::ArrowThis
            };
            let annotated_type =
                crate::infer::lower::annotation_this(&annotated_type, &called_with);
            self.subsume(annotation_span, &func_type, &annotated_type)?;
        }

        // An arrow function's `this` is its enclosing function's.
        let mut body_env = if matches!(this_type, Type::ArrowThis) {
            env.clone()
        } else {
            env.extend("this".to_string(), TypeScheme::mono(this_type))
        };

        // The function's own name first, so a parameter of the same name
        // shadows it (`function f(f) { return f; }` returns the argument).
        // A named function expression's own name is immutable: assigning
        // to it is a `TypeError` in strict mode. A declaration's name is
        // the enclosing scope's, which can be reassigned.
        if let Some(fn_name) = name {
            let mutability = if self.resolution.constant_at(span, fn_name) {
                Mutability::Immutable
            } else {
                Mutability::Mutable
            };
            body_env = self.bind(
                &body_env,
                span,
                fn_name,
                TypeScheme::mono(func_type.clone()),
                mutability,
            )?;
        }

        for (param, ty) in params.iter().zip(param_types.iter()) {
            body_env = self.bind(
                &body_env,
                param.span,
                &param.name,
                TypeScheme::mono(ty.clone()),
                Mutability::Mutable,
            )?;
            // Record per-param type for the LSP / hover. Keyed by the
            // param's name span so we can look it up at any reference
            // to the parameter.
            self.record_decl_type(param.span, ty.clone());
        }

        // Infer the body and derive its return type from the explicit
        // `return`s plus a fall-through `Undefined`. The body's
        // *completion* value is intentionally not used as the implicit
        // return: a function that falls off the end returns
        // `None`/`undefined`, regardless of any trailing expression
        // statement's type.
        let annotated =
            type_annotation.is_some() || return_type_ast.is_some() || expected_ret.is_some();
        // An annotated return type is pushed into the `return`s.
        let expected_ret = match self.zonk_head(&ret_type) {
            Type::Var(crate::types::TVarName::Flex(_)) => None,
            t if annotated => Some(t),
            _ => None,
        };
        self.member_function = member;
        let inferred_ret =
            self.infer_body_return_type_expecting(&body_env, body, !annotated, expected_ret, span)?;

        // Without an annotation the return is a fresh-literal widening site
        // (`function f() { return "hi"; }` returns `String`, not
        // `Lit("hi")`); `infer_body_return_type` widens for us. With an
        // annotation the declared return governs and the body subsumes.
        if annotated {
            self.subsume(span, &inferred_ret, &ret_type)?;
        } else {
            self.unify(span, &ret_type, &inferred_ret)?;
        }

        // Function declarations aren't expressions, so `infer_expr`
        // never records them; key the type by the function's own span
        // so code generators can read a declaration's signature too.
        if let Some(types) = self.expr_types.as_mut() {
            types.insert((span.start, span.end), func_type.clone());
        }

        Ok(self.zonk_head_into(func_type))
    }

    /// Python / Starlark `d.get(k, default)` on a receiver already known
    /// to be a `Dict`, with a default that isn't `None`: the value type,
    /// with no `None` (see [`crate::builtins::dict_get_with_default`]).
    /// `None` for any other call, which takes `get`'s general type.
    fn dict_get_with_default(
        &mut self,
        receiver: &Type,
        property: &str,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
    ) -> Option<Type> {
        let Type::Map(value) = receiver else {
            return None;
        };
        let defaulted = matches!(
            arguments,
            [_, default] if !matches!(default, Expr::Lit { value: crate::ast::Literal::Null, .. })
        );
        (self.language.is_python_like() && property == "get" && defaulted && keywords.is_empty())
            .then(|| crate::builtins::dict_get_with_default(value))
    }

    /// Python / Starlark `r.get("key", default?)` on a receiver already
    /// known to be a record (a dict literal, or a value whose type says
    /// it is one), with a literal key: the field's type. The record type
    /// says the field is there, so the result is never `None`; a key the
    /// record doesn't have is the missing-field error a subscript gets.
    /// The default, never used, may be the field's type or `None`.
    ///
    /// `None` (not this rule) for any other call: a non-literal key, a
    /// record with a `get` field of its own, a class instance, or a
    /// receiver whose type isn't known yet at the call.
    fn record_get(
        &mut self,
        receiver: &Type,
        property: &str,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
    ) -> Option<InferResult<Type>> {
        if !self.language.is_python_like()
            || property != "get"
            || !keywords.is_empty()
            || !(1..=2).contains(&arguments.len())
        {
            return None;
        }
        let Expr::Lit {
            value: crate::ast::Literal::String(key),
            span: key_span,
        } = &arguments[0]
        else {
            return None;
        };
        // A record, or a recursive structural alias of one (not a class,
        // whose instances aren't dicts).
        let row = match receiver {
            Type::Row(_) => receiver.clone(),
            Type::Named(id, args) if self.named_types.get(id).is_some_and(|d| !d.nominal) => {
                self.unroll_named(*id, args)?
            }
            _ => return None,
        };
        let row = self.zonk_head(&row);
        if !matches!(row, Type::Row(_)) || self.row_field_entry(&row, "get").is_some() {
            return None;
        }
        Some((|| {
            let field = self.infer_member_on_type(&row, key, *key_span)?;
            let pvar = self.fresh_pvar();
            let default = Type::union([field.clone(), Type::Null]);
            Ok(Type::simple_func_with_params(
                vec![
                    crate::types::FuncParam::required(Type::String),
                    crate::types::FuncParam::optional(pvar, default),
                ],
                field,
            ))
        })())
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
        if let Some(result) = self.infer_array_from(env, callee, arguments, keywords) {
            return result;
        }
        if let Some(result) = self.infer_wasm_instantiate(env, callee, arguments, keywords, span) {
            return result;
        }
        if let Some(result) = self.infer_generator_marker(env, callee, arguments, None, span) {
            return result;
        }
        if let (Expr::Ident { name, .. }, [value]) = (callee, arguments) {
            if name == crate::types::ASYNC_RETURN {
                let ty = self.infer_expr(env, value)?;
                return Ok(self.async_return(ty, span));
            }
        }
        // `then` / `catch` callbacks this call's callee records (see
        // `builtins::promise_method_type`) are settled at its end.
        let promise_mark = self.promise_results.len();
        // For method calls, we need to infer the object only once to avoid creating
        // different fresh type variables. We'll manually extract the method type.
        let mut deferred_this: Option<Type> = None;
        let (callee_type, obj_type_for_this) = match callee {
            Expr::Member {
                object,
                property,
                span: member_span,
            } => {
                // Infer object once
                let obj_type = self.infer_expr(env, object)?;
                // Only its head: a receiver may be a large row (a DOM
                // element's), and resolving it whole copies it.
                let obj_type_applied = self.zonk_head(&obj_type);

                if matches!(obj_type_applied, Type::Var(TVarName::Flex(_))) {
                    // A receiver whose type isn't known yet: the method and
                    // the call's `this` both wait for it (`HasProp`).
                    let method_type = self.fresh_type_var();
                    let this = self.fresh_type_var();
                    // Where the member was read as a method, and where
                    // its `this` was bound to the object (when the
                    // constraint is resolved).
                    for v in [&method_type, &this] {
                        if let Type::Var(v) = v {
                            self.record_origin(
                                v.clone(),
                                crate::error::TypeOrigin::MethodCall {
                                    method: property.clone(),
                                    span: *member_span,
                                },
                            );
                        }
                    }
                    self.add_constraint(
                        TypePred::has_method(
                            obj_type_applied.clone(),
                            property,
                            method_type.clone(),
                            this.clone(),
                        ),
                        *member_span,
                    );
                    deferred_this = Some(this);
                    (method_type, Some(obj_type_applied))
                } else if let Some(method_type) =
                    self.dict_get_with_default(&obj_type_applied, property, arguments, keywords)
                {
                    (method_type, Some(obj_type_applied))
                } else if let Some(method_type) =
                    self.record_get(&obj_type_applied, property, arguments, keywords)
                {
                    (method_type?, Some(obj_type_applied))
                } else {
                    // Get method type from the object without re-inferring
                    let method_type =
                        self.infer_member_on_type(&obj_type_applied, property, *member_span)?;
                    (method_type, Some(obj_type_applied))
                }
            }
            Expr::ComputedMember {
                object,
                property,
                span: member_span,
            } => {
                // Infer object once
                let obj_type = self.infer_expr(env, object)?;
                let obj_type_applied = self.zonk_head(&obj_type);

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
        // A method's callee (`obj.m`) is typed here, not by `infer_expr`:
        // record it as that would.
        if let Some(types) = self.expr_types.as_mut() {
            let callee_span = callee.span();
            types
                .entry((callee_span.start, callee_span.end))
                .or_insert_with(|| callee_type.clone());
        }

        // A callee of a type not known yet: the call gives it the shape
        // of a function, with a `this` nothing has said anything about.
        let callee_unknown =
            self.head_is(&callee_type, |t| matches!(t, Type::Var(TVarName::Flex(_))));

        // Error sentinel propagates through calls. If the callee
        // already failed to infer, every `Error(args)` site
        // re-produces `Error` so a single upstream failure doesn't
        // spawn one diagnostic per call site.
        if self.head_is(&callee_type, |t| matches!(t, Type::Error)) {
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
        let callee_type = self.fill_optional_params(&callee_type, arguments.len(), span);
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
            match arg {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    let inner = self.infer_expr(env, argument)?;
                    let elem = self.fresh_type_var();
                    self.unify(*spread_span, &inner, &Type::Array(Box::new(elem.clone())))?;
                    let elem_resolved = self.zonk_head(&elem);
                    let expected = self.zonk_head(param);
                    self.subsume(*spread_span, &elem_resolved, &expected)?;
                }
                Expr::Object { properties, .. } => {
                    // An object literal fills or leaves out the expected
                    // record's optional fields for this call only, as a
                    // call does a function's optional parameters.
                    let param = match Self::written_keys(properties) {
                        Some(keys) => self.fill_optional_fields(param, &keys, arg.span()),
                        None => param.clone(),
                    };
                    self.check_expr(env, arg, &param)
                        .map_err(|e| self.locate_in_value(arg, e))?;
                }
                _ if self.closed_row_keys(env, arg).is_some() => {
                    // So does a value of a known record type (an options
                    // object bound to a `const`).
                    let keys = self.closed_row_keys(env, arg).unwrap_or_default();
                    let param = self.fill_optional_fields(param, &keys, arg.span());
                    self.check_expr(env, arg, &param)
                        .map_err(|e| self.locate_in_value(arg, e))?;
                }
                _ => {
                    // `check_expr` resolves what it is checked against.
                    self.check_expr(env, arg, param)
                        .map_err(|e| self.locate_in_value(arg, e))?;
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
        if self.head_is(&this_type, |t| matches!(t, Type::NewTarget)) {
            return Err(crate::error::TypeError::TypeMismatch {
                expected: "`new` (a class can only be called with `new`)".to_string(),
                found: "a call without `new`".to_string(),
                span,
            }
            .into());
        }
        if let Some(this) = deferred_this {
            // Bound to the receiver when its `HasProp` resolves.
            self.unify_this(span, &this_type, &this)?;
        } else if let Some(obj_type) = obj_type_for_this {
            let obj_for_this = self.method_receiver(&obj_type);
            // A callee not known yet (a callback stored in a field) may
            // use no `this` or read the receiver: the call doesn't decide
            // which, or a callback stored in a class's field would become
            // a method of that class. Its `this` waits, as a detached
            // call's does (`settle_receivers`).
            match self.zonk_head(&this_type) {
                Type::Var(v) if v.is_flex() && callee_unknown => {
                    self.pending_receivers
                        .push(crate::infer::state::PendingReceiver {
                            this: Type::Var(v),
                            receiver: obj_for_this.into_owned(),
                            span,
                        })
                }
                this => {
                    // A `this` not known yet: this call makes the callee
                    // a method of the receiver.
                    if let (
                        Type::Var(v @ TVarName::Flex(_)),
                        Expr::Member {
                            property,
                            span: member_span,
                            ..
                        },
                    ) = (this, callee)
                    {
                        self.record_origin(
                            v,
                            crate::error::TypeOrigin::MethodCall {
                                method: property.clone(),
                                span: *member_span,
                            },
                        );
                    }
                    self.unify_this(span, &this_type, &obj_for_this)?
                }
            }
        } else {
            self.detached_this(span, &this_type, Some(callee))?;
        }

        self.settle_promise_results(promise_mark, span)?;

        // The call may have pinned down receivers of pending property
        // reads — the callee's instantiated predicates, or a method's
        // `this` — so resolve those now: the result type is then known
        // to what follows.
        self.simplify_has_props()?;
        // Its head: a result may be a large row (`appendChild`'s, a DOM
        // element's), which resolving whole copies.
        Ok(self.zonk_head_into(ret_type))
    }

    /// A call of the standard library's `Array.from`, whose result
    /// depends on whether it is given a map function, which no one
    /// function type says:
    ///
    /// - `Array.from(it)`: `it` is iterated (`Iterable it e`), giving an
    ///   `e[]`;
    /// - `Array.from(it, f)`: `f` is called with each element and its
    ///   index (it may take only the element), giving an array of its
    ///   results; an array-like `it` (`{length: n}`, with no
    ///   `[Symbol.iterator]`) has `undefined` elements.
    ///
    /// `None` for any other call (or an `Array` the program binds itself).
    fn infer_array_from(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
    ) -> Option<InferResult<Type>> {
        let Expr::Member {
            object,
            property,
            span,
        } = callee
        else {
            return None;
        };
        let Expr::Ident {
            name,
            span: name_span,
        } = object.as_ref()
        else {
            return None;
        };
        if name != "Array"
            || property != "from"
            || !keywords.is_empty()
            || !(1..=2).contains(&arguments.len())
            || arguments.iter().any(|a| matches!(a, Expr::Spread { .. }))
            || !self.ambient.contains(&self.key_of(*name_span, name))
        {
            return None;
        }
        let span = *span;
        Some((|| {
            let source = self.infer_expr(env, &arguments[0])?;
            let element = self.fresh_type_var();
            // An array-like object: a record with a `length`, which isn't
            // iterable, read by index (`undefined`s for `{length: n}`).
            let array_like = arguments.len() == 2
                && match crate::infer::zonk::zonk_head_cow(&mut self.var_table, &source).as_ref() {
                    Type::Row(_) => {
                        self.row_field_entry(&source, crate::types::ITER_KEY)
                            .is_none()
                            && self.row_field_entry(&source, "length").is_some()
                    }
                    _ => false,
                };
            if array_like {
                let length = self
                    .row_field_entry(&source, "length")
                    .expect("just found")
                    .ty;
                self.subsume(arguments[0].span(), &length, &Type::Number)?;
                self.unify(span, &element, &Type::Undefined)?;
            } else {
                self.require_iterable(&source, &element, arguments[0].span())?;
            }
            let Some(map_fn) = arguments.get(1) else {
                return Ok(Type::array(self.zonk_head(&element)));
            };
            let result = self.fresh_type_var();
            let index = self.fresh_pvar();
            let element = self.zonk_head(&element);
            let callback = self.callable_row_open_with_params(
                vec![
                    crate::types::FuncParam::required(element),
                    crate::types::FuncParam::optional(index, Type::Number),
                ],
                result.clone(),
            );
            self.check_expr(env, map_fn, &callback)?;
            Ok(Type::array(self.zonk_head(&result)))
        })())
    }

    /// What a generator's iterator is, `Iterator<T>` (the stdlib's), for
    /// elements `element`; without the stdlib, a record iterating them.
    pub(in crate::infer) fn iterator_type(&mut self, element: Type) -> Type {
        use crate::types::{FieldEntry, PropName, RowType, ITER_KEY};
        match self.type_aliases.get("Iterator").cloned() {
            Some(def) if def.params.len() == 1 => match def.rec_id.or(def.nominal_id) {
                Some(id) => Type::Named(id, vec![element]),
                None => {
                    let subst = HashMap::from([(def.params[0], element)]);
                    super::super::type_parser::substitute_alias_body(&def.body, &subst)
                }
            },
            _ => Type::Row(RowType::closed_entries(std::collections::BTreeMap::from([
                (PropName(ITER_KEY.to_string()), FieldEntry::pre(element)),
            ]))),
        }
    }

    /// The calls a generator is lowered to (see
    /// [`crate::types::GENERATOR`]): `GENERATOR(() => body)`, an
    /// `Iterator<T>` of what `body`'s `yield`s give (`expected`, when
    /// known, says what `T` is before the body is inferred, so each
    /// `yield`'s value is checked against it); `YIELD(e)`, `e` one of the
    /// innermost generator's elements; `YIELD_STAR(it)`, each element of
    /// the iterable `it` one. A `yield` gives `undefined` (what `next()`
    /// is called with). `None` for any other call.
    pub(in crate::infer) fn infer_generator_marker(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        expected: Option<&Type>,
        span: Span,
    ) -> Option<InferResult<Type>> {
        let Expr::Ident { name, .. } = callee else {
            return None;
        };
        let name = name.as_str();
        if ![
            crate::types::GENERATOR,
            crate::types::YIELD,
            crate::types::YIELD_STAR,
        ]
        .contains(&name)
        {
            return None;
        }
        Some((|| {
            if name == crate::types::GENERATOR {
                let element = self.fresh_type_var();
                let iterator = self.iterator_type(element.clone());
                if let Some(expected) = expected {
                    self.unify(span, &iterator, expected)?;
                }
                self.generator_elements.push(element);
                let body = arguments
                    .first()
                    .map(|f| self.infer_expr(env, f))
                    .transpose();
                self.generator_elements.pop();
                body?;
                return Ok(self.zonk_head_into(iterator));
            }
            let element = self
                .generator_elements
                .last()
                .cloned()
                .unwrap_or_else(|| self.fresh_type_var());
            let element = self.zonk_head(&element);
            match (name, arguments) {
                (_, []) => self.subsume(span, &Type::Undefined, &element)?,
                (n, [value]) if n == crate::types::YIELD => {
                    self.check_expr(env, value, &element)
                        .map_err(|e| self.locate_in_value(value, e))?;
                }
                (_, [iterable]) => {
                    let it = self.infer_expr(env, iterable)?;
                    let each = self.fresh_type_var();
                    self.require_iterable(&it, &each, iterable.span())?;
                    let each = self.zonk_head(&each);
                    self.subsume(iterable.span(), &each, &element)?;
                }
                _ => {
                    for a in arguments {
                        self.infer_expr(env, a)?;
                    }
                }
            }
            Ok(Type::Undefined)
        })())
    }

    /// A call of `callee`, a function type chosen by the type of the
    /// call's first argument (`first`, already synthesised as
    /// `first_ty`): the first argument is subsumed to its parameter, the
    /// others (`rest`) checked against theirs, as an ordinary call's are.
    /// The rules that pick a signature by an argument's type (a typed
    /// array's constructor, `WebAssembly.instantiate`) synthesise it
    /// once, here, rather than again in the ordinary call.
    fn apply_with_first_typed(
        &mut self,
        env: &TypeEnv,
        callee: &Type,
        first: &Expr,
        first_ty: &Type,
        rest: &[Expr],
        span: Span,
    ) -> InferResult<Type> {
        let params: Vec<Type> = (0..=rest.len()).map(|_| self.fresh_type_var()).collect();
        let ret = self.fresh_type_var();
        let this = self.fresh_type_var();
        let expected = self.callable_row_open(Some(this), params.clone(), ret.clone());
        let callee = self.fill_optional_params(callee, params.len(), span);
        self.unify(span, &callee, &expected)?;
        let want = self.zonk_head(&params[0]);
        self.subsume(first.span(), first_ty, &want)
            .map_err(|e| self.locate_in_value(first, e))?;
        for (arg, param) in rest.iter().zip(&params[1..]) {
            self.check_expr(env, arg, param)
                .map_err(|e| self.locate_in_value(arg, e))?;
        }
        self.simplify_has_props()?;
        Ok(self.zonk_head_into(ret))
    }

    /// A call of the standard library's `WebAssembly.instantiate`, whose
    /// result depends on what it is given, which no one function type
    /// says:
    ///
    /// - `instantiate(bytes, imports?)` compiles `bytes` (its declared
    ///   type) and resolves to `{instance, module}`;
    /// - `instantiate(module, imports?)`, a compiled
    ///   `WebAssemblyModule`, resolves to the instance alone: what
    ///   `new WebAssembly.Instance(module, imports)` makes.
    ///
    /// `None` for any other call (or a `WebAssembly` the program binds
    /// itself).
    fn infer_wasm_instantiate(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        keywords: &[(String, Expr)],
        span: Span,
    ) -> Option<InferResult<Type>> {
        let Expr::Member {
            object,
            property,
            span: member_span,
        } = callee
        else {
            return None;
        };
        let Expr::Ident {
            name,
            span: name_span,
        } = object.as_ref()
        else {
            return None;
        };
        if name != "WebAssembly"
            || property != "instantiate"
            || !keywords.is_empty()
            || !(1..=2).contains(&arguments.len())
            || arguments.iter().any(|a| matches!(a, Expr::Spread { .. }))
            || !self.ambient.contains(&self.key_of(*name_span, name))
        {
            return None;
        }
        let module = self.type_aliases.get("WebAssemblyModule")?.nominal_id?;
        let member_span = *member_span;
        Some((|| {
            let wasm = self.infer_expr(env, object)?;
            let wasm = self.zonk_head(&wasm);
            let source = self.infer_expr(env, &arguments[0])?;
            let by_module = matches!(self.zonk_head(&source), Type::Named(id, _) if id == module);
            let member = if by_module { "Instance" } else { "instantiate" };
            let f = self.infer_member_on_type(&wasm, member, member_span)?;
            let made = self.apply_with_first_typed(
                env,
                &f,
                &arguments[0],
                &source,
                &arguments[1..],
                span,
            )?;
            Ok(if by_module { Type::promise(made) } else { made })
        })())
    }

    /// `new T(…)` of a standard-library typed array (`Uint8Array`, …),
    /// whose parameters depend on what its first argument is, which no
    /// one function type says:
    ///
    /// - `new T()` / `new T(length)`: a zeroed array (an argument of a
    ///   type not known yet is taken to be the length);
    /// - `new T(buffer, byteOffset?, length?)`: a view of an
    ///   `ArrayBuffer` (any call with more than one argument is one);
    /// - `new T(array)` / `new T(typedArray)`: a copy of a `Number[]` or
    ///   of another typed array (of any kind).
    ///
    /// `None` for any other `new` (or a typed array the program binds
    /// itself, or a call with a spread or more than three arguments,
    /// which the declared constructor rejects).
    fn infer_typed_array_new(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        span: Span,
    ) -> Option<InferResult<Type>> {
        use crate::types::FuncParam;
        let Expr::Ident {
            name,
            span: name_span,
        } = callee
        else {
            return None;
        };
        let kind = crate::types::TypedArrayKind::from_name(name)?;
        if arguments.len() > 3
            || arguments.iter().any(|a| matches!(a, Expr::Spread { .. }))
            || !self.ambient.contains(&self.key_of(*name_span, name))
        {
            return None;
        }
        let buffer = crate::builtins::array_buffer_type(self)?;
        Some((|| {
            // The constructor, recorded as the ordinary `new` would.
            self.infer_expr(env, callee)?;
            let made = Type::TypedArray(kind);
            let Some((first, rest)) = arguments.split_first() else {
                return Ok(made);
            };
            let source = self.infer_expr(env, first)?;
            let head = self.zonk_head(&source);
            let is_buffer = !rest.is_empty()
                || match (&head, &buffer) {
                    (Type::Named(id, _), Type::Named(b, _)) => id == b,
                    // A record of an `ArrayBuffer`'s shape (not an
                    // array-like one).
                    (Type::Row(_), _) => {
                        self.row_field_entry(&head, "byteLength").is_some()
                            && self.row_field_entry(&head, "length").is_none()
                    }
                    _ => false,
                };
            let ctor = if is_buffer {
                let (p1, p2) = (self.fresh_pvar(), self.fresh_pvar());
                Type::simple_func_with_params(
                    vec![
                        FuncParam::required(buffer.clone()),
                        FuncParam::optional(p1, Type::Number),
                        FuncParam::optional(p2, Type::Number),
                    ],
                    made,
                )
            } else {
                let from = match head {
                    Type::TypedArray(k) => Type::TypedArray(k),
                    Type::Array(_) | Type::Tuple(_) => Type::array(Type::Number),
                    _ => Type::Number,
                };
                Type::simple_func(vec![from], made)
            };
            self.apply_with_first_typed(env, &ctor, first, &source, rest, span)
        })())
    }

    /// What a method called on `receiver` sees as `this`. A nominal brand
    /// is transparent for method-receiver binding, just as it is for
    /// field access: it unrolls to its representation row so the method
    /// body's `this`-row unifies against the instance shape. The
    /// receiver's own type stays nominal everywhere else.
    pub(crate) fn method_receiver<'a>(
        &mut self,
        receiver: &'a Type,
    ) -> crate::infer::zonk::Head<'a> {
        use crate::infer::zonk::Head;
        // Only the head decides; what is below it is resolved by the
        // unification the receiver goes to.
        let receiver = crate::infer::zonk::zonk_head_cow(&mut self.var_table, receiver);
        match &*receiver {
            // `"abc".trim()`: a literal's methods are its base type's.
            Type::Literal(lit) => Head::Owned(lit.base_type()),
            Type::Named(id, args) if self.is_nominal_type(*id) => {
                match self.unroll_named(*id, args) {
                    Some(unrolled) => Head::Owned(unrolled),
                    None => receiver,
                }
            }
            _ => receiver,
        }
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
                None => return self.detached_this(span, &t, None).map(|()| self.zonk(&ret)),
            };
            self.unify_this(span, &t, &obj)?;
        }

        Ok(self.zonk_head_into(ret))
    }

    /// The callee of a call passing `given` arguments, as the call sees
    /// it: a parameter whose presence isn't decided (one declared
    /// optional, `b?: T`) is filled (when an argument is passed) or
    /// skipped, for this call only, rather than decided by it. The call
    /// leaves the callee's type as it was (as Garrigue's optional
    /// arguments), so one element's `addEventListener` can be called
    /// with and without its options. Each such parameter is recorded
    /// (`pending_optional_params`): if it is decided later, it must
    /// agree; if it is still undecided where it would be generalised,
    /// the call decides it as it did before.
    fn fill_optional_params(&mut self, callee: &Type, given: usize, span: Span) -> Type {
        use crate::types::{Presence, PropName, CALLABLE_KEY};
        let head = self.zonk_head(callee);
        let fill = |state: &mut Self, f: &Type| -> Option<Type> {
            let Type::Func {
                this_type,
                params,
                ret,
            } = f
            else {
                return None;
            };
            let mut changed = false;
            let params = params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let presence = state.main_subst.resolve_presence(&p.presence);
                    let Presence::Var(v) = presence else {
                        return p.clone();
                    };
                    changed = true;
                    let passed = i < given;
                    state.pending_optional_params.push((v, passed, span));
                    let mut p = p.clone();
                    p.presence = if passed { Presence::Pre } else { Presence::Abs };
                    p
                })
                .collect();
            changed.then(|| Type::Func {
                this_type: this_type.clone(),
                params,
                ret: ret.clone(),
            })
        };
        match &head {
            Type::Func { .. } => fill(self, &head).unwrap_or(head),
            Type::Row(row) => {
                let key = PropName(CALLABLE_KEY.to_string());
                let Some(entry) = row.props.get(&key) else {
                    return head;
                };
                let call = self.zonk_head(&entry.ty);
                let Some(filled) = fill(self, &call) else {
                    return head;
                };
                let mut row = row.clone();
                let entry = row.props[&key].with_ty(filled);
                row.props.insert(key, entry);
                Type::Row(row)
            }
            _ => head,
        }
    }

    /// `expected` (a record, or a union with records among its arms) as
    /// an object writing the fields `written` sees it: a field of undecided
    /// presence (declared optional, `x?: T`) is present when the literal
    /// writes it and absent when it doesn't, for this literal only,
    /// recorded as [`Self::fill_optional_params`] records a parameter.
    /// The fields an object literal writes, when it writes only named
    /// ones (a spread or a computed key may write any).
    fn written_keys(
        properties: &[crate::ast::PropDef],
    ) -> Option<std::collections::BTreeSet<String>> {
        let written: std::collections::BTreeSet<String> = properties
            .iter()
            .filter_map(|p| match p {
                crate::ast::PropDef::Property {
                    key: crate::ast::PropKey::Ident(k) | crate::ast::PropKey::String(k),
                    ..
                } => Some(k.clone()),
                _ => None,
            })
            .collect();
        (written.len() == properties.len()).then_some(written)
    }

    /// The fields of `arg`'s type when it is a variable of a known,
    /// closed record type with every field present.
    fn closed_row_keys(
        &mut self,
        env: &TypeEnv,
        arg: &Expr,
    ) -> Option<std::collections::BTreeSet<String>> {
        let Expr::Ident { name, span } = arg else {
            return None;
        };
        let scheme = env.lookup_key(&self.key_of(*span, name))?.scheme.clone();
        if !scheme.is_mono() {
            return None;
        }
        let Type::Row(row) = self.zonk_head(scheme.ty()) else {
            return None;
        };
        let all_present = row.props.values().all(|e| {
            matches!(
                self.main_subst.resolve_presence(&e.presence),
                crate::types::Presence::Pre
            )
        });
        (row.is_closed() && all_present).then(|| row.props.keys().map(|k| k.0.clone()).collect())
    }

    fn fill_optional_fields(
        &mut self,
        expected: &Type,
        written: &std::collections::BTreeSet<String>,
        span: Span,
    ) -> Type {
        use crate::types::Presence;
        let fill_row = |state: &mut Self, t: &Type| -> Option<Type> {
            let t = match state.zonk_head(t) {
                Type::Named(id, args) if !state.is_nominal_type(id) => {
                    state.unroll_named(id, &args)?
                }
                t => t,
            };
            let Type::Row(mut row) = t else {
                return None;
            };
            let mut changed = false;
            for (k, entry) in row.props.iter_mut() {
                let Presence::Var(v) = state.main_subst.resolve_presence(&entry.presence) else {
                    continue;
                };
                let present = written.contains(&k.0);
                state.pending_optional_params.push((v, present, span));
                entry.presence = if present {
                    Presence::Pre
                } else {
                    Presence::Abs
                };
                changed = true;
            }
            changed.then_some(Type::Row(row))
        };
        match self.zonk_head(expected) {
            Type::Union(arms) => {
                let mut changed = false;
                let arms: Vec<Type> = arms
                    .iter()
                    .map(|a| match fill_row(self, a) {
                        Some(filled) => {
                            changed = true;
                            filled
                        }
                        None => a.clone(),
                    })
                    .collect();
                if changed {
                    Type::Union(arms)
                } else {
                    expected.clone()
                }
            }
            _ => fill_row(self, expected).unwrap_or_else(|| expected.clone()),
        }
    }

    /// What an `async` body's `return e` gives its promise, for `e` of
    /// type `ty` (see [`crate::types::ASYNC_RETURN`]): a promise's value,
    /// or `e`'s own, as `then`'s callback does. A type not known yet
    /// waits (`settle_async_returns`).
    fn async_return(&mut self, ty: Type, span: Span) -> Type {
        match self.zonk_head(&ty) {
            Type::Promise(value) => *value,
            Type::Var(TVarName::Flex(_)) => {
                let value = self.fresh_type_var();
                self.pending_async_returns.push((ty, value.clone(), span));
                value
            }
            _ => ty,
        }
    }

    /// A call without a receiver (`f()`, not `o.f()`): the callee gets
    /// `this` = `undefined` (JavaScript's strict mode), so it must use no
    /// `this` (`ArrowThis`) or read it as `Undefined`; a method, which
    /// reads it as its object, can't be called so. One still to be known
    /// waits (`settle_detached`).
    pub(in crate::infer) fn detached_this(
        &mut self,
        span: Span,
        this: &Type,
        callee: Option<&Expr>,
    ) -> InferResult<()> {
        let callee = match callee {
            Some(Expr::Ident { name, .. }) => format!("`{name}`"),
            _ => "this function".to_string(),
        };
        match self.zonk_head(this) {
            Type::ArrowThis | Type::Undefined | Type::Error | Type::NewTarget => Ok(()),
            // Not known yet: it may turn out to use none, or to be one
            // that reads `this` as `undefined`, but not a method.
            v @ Type::Var(_) => {
                self.pending_detached.push((v, span, callee));
                Ok(())
            }
            _ => Err(crate::error::TypeError::DetachedThis { callee, span }.into()),
        }
    }

    /// An error checking the value `arg` (an argument) against what it is
    /// expected to be, at a member of the two (`member`): where the member
    /// is written, when `arg` is an object literal or a `const` bound to
    /// one, is where the value's side of the mismatch comes from.
    pub(in crate::infer) fn locate_in_value(
        &self,
        arg: &Expr,
        mut err: crate::error::IntyError,
    ) -> crate::error::IntyError {
        // Only an error at `arg` itself: one raised inside it (a call in
        // a field's value) is about another value, and says so already.
        if let Some(e) = err.as_type_mut() {
            if e.span() == arg.span() {
                self.locate_member_in_value(arg, e);
            }
        }
        err
    }

    fn locate_member_in_value(&self, arg: &Expr, err: &mut crate::error::TypeError) {
        use crate::error::{TypeError, TypeOrigin};
        let field = |path: &str| {
            self.literal_field(arg, path).map(|f| {
                let origin = TypeOrigin::Field {
                    name: f.path.clone(),
                    span: f.span,
                };
                (origin, f.reads_this)
            })
        };
        match err {
            // Subsumption's (`whole`): the value's side is `found`.
            TypeError::UnificationError {
                member: Some(m),
                whole: Some(_),
                found_origin,
                ..
            } => {
                if let Some((origin, _)) = field(m) {
                    *found_origin = Some(origin);
                }
            }
            TypeError::ThisMismatch {
                member: Some(m),
                without_origins,
                with_origins,
                ..
            } => {
                let side = match field(m) {
                    Some((origin, Some(false))) => Some((origin, without_origins)),
                    Some((origin, Some(true))) => Some((origin, with_origins)),
                    _ => None,
                };
                if let Some((origin, origins)) = side {
                    origins.push(origin);
                    crate::infer::state::tidy_origins(origins);
                }
            }
            TypeError::RequiredBy { inner, .. } => self.locate_member_in_value(arg, inner),
            _ => {}
        }
    }

    /// Infer the type of a new expression.
    pub(in crate::infer) fn infer_new(
        &mut self,
        env: &TypeEnv,
        callee: &Expr,
        arguments: &[Expr],
        span: Span,
    ) -> InferResult<Type> {
        if let Some(result) = self.infer_typed_array_new(env, callee, arguments, span) {
            return result;
        }
        let callee_type = self.infer_expr(env, callee)?;

        // `new F(…)` calls `F` with a fresh object as `this` and gives
        // back what the call returns if that is an object, else the fresh
        // object. inty types the result as what the call returns, so a
        // constructor returning a primitive is rejected below. `this` is
        // `NewTarget`, which nothing else gives a function: a function
        // that writes or reads `this` (a JavaScript constructor function)
        // isn't accepted here, and a class's factory, whose `this` is
        // `NewTarget`, can't be called without `new`.
        let result_type = self.fresh_type_var();
        let this_type = Type::NewTarget;

        // Expected constructor shape — an *open* callable row so the
        // constructor value can carry additional static fields beyond
        // the call signature (matches the unified callable-row design).
        // Its parameters are learnt from the callee first; each argument
        // is then checked against its parameter, exactly as for a call
        // (`new Array(3)` and `Array(3)` agree).
        let params: Vec<Type> = arguments.iter().map(|_| self.fresh_type_var()).collect();
        let expected_func =
            self.callable_row_open(Some(this_type), params.clone(), result_type.clone());
        self.unify(span, &callee_type, &expected_func)?;

        // `...expr` (Expr::Spread) in argument position unwraps the inner
        // array to its element type and is treated as a single argument —
        // inty has no variadic call shape, so a spread can't expand into N
        // arguments. Callers that rely on variadic semantics will see an
        // arity error here; callers that want a single-arg function fed
        // from an array's element will type-check correctly.
        for (arg, param) in arguments.iter().zip(&params) {
            match arg {
                Expr::Spread {
                    argument,
                    span: spread_span,
                } => {
                    let inner = self.infer_expr(env, argument)?;
                    self.unify(*spread_span, &inner, &Type::Array(Box::new(param.clone())))?;
                }
                _ => {
                    self.check_expr(env, arg, param)
                        .map_err(|e| self.locate_in_value(arg, e))?;
                }
            }
        }

        self.require_constructed_object(&result_type, span)?;
        Ok(self.zonk_head_into(result_type))
    }

    /// What `new` gives back must be what the constructor returned, so
    /// that must be an object: a primitive result is replaced by the
    /// fresh `this` at run time. A result not known yet is constrained
    /// to an object type.
    fn require_constructed_object(&mut self, result: &Type, span: Span) -> InferResult<()> {
        let not_an_object = |shown: String| -> crate::error::IntyError {
            crate::error::TypeError::TypeMismatch {
                expected: "a constructor returning an object (`new` gives back the object \
                           it made in place of a primitive result)"
                    .to_string(),
                found: format!("a function returning `{}`", shown),
                span,
            }
            .into()
        };
        // Its head decides (and a union's members' heads): resolving it
        // whole writes out a large instance type (one holding elements)
        // as a tree.
        let result = match self.zonk_head(result) {
            Type::Union(ts) => Type::Union(ts.iter().map(|t| self.zonk_head(t)).collect()),
            head => head,
        };
        let primitive = match &result {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Literal(_)
            // A sum holds its nothing.
            | Type::Maybe(..) => true,
            Type::Union(ts) => ts.iter().any(|t| {
                matches!(
                    t,
                    Type::Number
                        | Type::String
                        | Type::Boolean
                        | Type::Undefined
                        | Type::Null
                        | Type::Literal(_)
                )
            }),
            Type::Var(TVarName::Flex(_)) => {
                let rest = self.fresh_flex();
                let row = Type::Row(crate::types::RowType::open_entries(
                    std::collections::BTreeMap::new(),
                    rest,
                ));
                if self.unify(span, &result, &row).is_err() {
                    return Err(not_an_object(self.show(&result)));
                }
                return Ok(());
            }
            _ => false,
        };
        if primitive {
            return Err(not_an_object(self.show(&result)));
        }
        Ok(())
    }

    /// Infer a run of adjacent `function` declarations as a single
    /// binding group. Every name in the group is visible in every
    /// body from the start, which is what enables forward references
    /// and mutual recursion.
    /// The environment a function declaration is checked in: what is
    /// known of a binding that is written (a binding written once, see
    /// `after_sole_write`) is dropped, as the declaration is hoisted and
    /// can be called before that write runs, whatever statement it is
    /// checked after.
    fn hoisted_env(&self, env: &TypeEnv) -> TypeEnv {
        env.without_narrowings_of(|key| match key {
            crate::infer::env::Key::Local(id) => !self.resolution.is_stable(*id),
            crate::infer::env::Key::Name(_) => false,
        })
    }

    pub(in crate::infer) fn infer_function_group(
        &mut self,
        env: &TypeEnv,
        group: &[Stmt],
    ) -> InferResult<TypeEnv> {
        let env = &self.hoisted_env(env);
        let mut hoisted = self.hoist_function_names(env, group)?;

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
                let key = self.key_of(hoisted_key_span(stmt).expect("a hoisted function"), name);
                let hoisted_scheme = hoisted
                    .lookup_key(&key)
                    .expect("hoisted name must be in env")
                    .scheme
                    .clone();
                // A polymorphic annotation: the body is checked against it.
                if !hoisted_scheme.is_mono() {
                    let ann_span = type_annotation
                        .as_ref()
                        .map(|a| Span::new(a.span.start, a.span.end))
                        .unwrap_or(span);
                    let ty = self.check_function_annotation(
                        &hoisted,
                        params,
                        body,
                        span,
                        &hoisted_scheme,
                        ann_span,
                    )?;
                    self.record_decl_type(hoisted_name_span(stmt, name, span), ty);
                    continue;
                }
                let func_var = hoisted_scheme.ty().clone();
                let func_type = self.infer_function(
                    &hoisted,
                    Some(name),
                    params,
                    body,
                    type_annotation,
                    return_type_ast,
                    hoisted_is_arrow(stmt),
                    span,
                )?;
                self.unify(span, &func_var, &func_type)?;
                // Key the recorded type by the *name* offset so the LSP
                // resolver (which returns the name span for go-to-def)
                // can look the type up directly. The exported form is
                // prefixed with `export `, so the keyword offset
                // accounts for that.
                self.record_decl_type(hoisted_name_span(stmt, name, span), func_type);
            }
        }

        // Pass 2: every function in the group now has a fully resolved
        // monomorphic type sitting under its hoisted variable. Generalise
        // each against the *outer* env's free variables so all peers
        // receive the same polymorphism.
        let base_free = env.free();
        // Every member is generalised against the same pending constraints:
        // `generalize` moves the predicates that mention a member's
        // quantified variables into its scheme, and mutually recursive
        // members share variables, so the first member would otherwise take
        // a predicate the others need too (leaving `b` in `a ↔ b` with no
        // `Indexable` predicate at all). A predicate stays pending only if no
        // member took it.
        self.simplify_has_props()?;
        let pending = self.pending_constraints.clone();
        let outer = hoisted.clone();
        // The variables every member is generalised over: those any
        // member's type reaches. A member's body can use one its own type
        // doesn't mention (`f` passes a local number to `g`, whose
        // parameter it is): quantified by `g` alone, it would be left in
        // `f` with nothing to decide it. So a second round generalises
        // every member over all of them, when the first didn't.
        let mut group_vars: Vec<TVarName> = Vec::new();
        // A member whose type is too large to write out (see
        // `MAX_GENERALISED`) isn't generalised, and so neither is any
        // member of its group: one generalised over a variable another
        // keeps would come apart from it. Each keeps its monomorphic type,
        // which is sound, if less general.
        let too_large = group.iter().find_map(|stmt| {
            let (name, _, _, _, _, span) = function_decl_parts(stmt)?;
            let key = self.key_of(hoisted_key_span(stmt)?, name);
            let scheme = &hoisted.lookup_key(&key)?.scheme;
            if !scheme.is_mono() {
                return None;
            }
            let ty = scheme.ty().clone();
            self.scheme_too_large(&ty).then(|| (name.to_string(), span))
        });
        if let Some((name, span)) = too_large {
            self.warn(
                span,
                format!(
                    "`{name}`'s type is too large to write out (it nests types that mention \
                     each other many times, such as elements chained through `appendChild`), \
                     so it and the functions it calls back aren't generalised: each is \
                     checked with one type for all its uses. Annotating it with a smaller \
                     type (a project's own element type) avoids this"
                ),
            );
            return Ok(hoisted);
        }
        for round in 0..2 {
            hoisted = outer.clone();
            let mut left_by_all = vec![true; pending.len()];
            let mut schemes_vars: Vec<Vec<TVarName>> = Vec::new();
            for stmt in group {
                if let Some((name, _, _, _, _, span)) = function_decl_parts(stmt) {
                    self.pending_constraints = pending.clone();
                    self.constraint_removals += 1;
                    let key =
                        self.key_of(hoisted_key_span(stmt).expect("a hoisted function"), name);
                    let hoisted_scheme = hoisted
                        .lookup_key(&key)
                        .expect("function must be in env after pass 1")
                        .scheme
                        .clone();
                    // A polymorphic annotation's scheme is the function's
                    // already (`hoist_function_names`).
                    if !hoisted_scheme.is_mono() {
                        self.record_decl_scheme(
                            hoisted_name_span(stmt, name, span),
                            hoisted_scheme,
                        );
                        continue;
                    }
                    let ty = hoisted_scheme.ty().clone();
                    let ty = self.zonk(&ty);
                    // A factory lowered from a `class` gets its inferred
                    // return row branded nominally, so two structurally
                    // identical classes stay distinct types.
                    let ty = if self.class_brand_names.contains(name) {
                        // A JavaScript class can only be called with `new`,
                        // which alone gives `this` as `NewTarget`.
                        if self.language == crate::ast::SourceLanguage::JavaScript {
                            if let Some((Some(this), _, _)) = extract_callable(&ty) {
                                self.unify(span, &this, &Type::NewTarget)?;
                            }
                        }
                        let ty = self.zonk(&ty);
                        let (fixed, _) = self.env_fixed_vars(&base_free, &ty);
                        self.brand_class_factory(name, &ty, &fixed)
                    } else {
                        ty
                    };
                    let scheme = self.generalize_seeded(&base_free, &ty, &group_vars);
                    schemes_vars.push(scheme.vars.clone());
                    // `generalize` keeps the predicates it doesn't take, in
                    // order: mark the ones it took.
                    let mut kept = self.pending_constraints.iter().peekable();
                    for (i, c) in pending.iter().enumerate() {
                        if kept.peek() == Some(&c) {
                            kept.next();
                        } else {
                            left_by_all[i] = false;
                        }
                    }
                    self.record_decl_scheme(hoisted_name_span(stmt, name, span), scheme.clone());
                    let key_span = hoisted_key_span(stmt).expect("a hoisted function");
                    hoisted = self.rebind(
                        &hoisted,
                        key,
                        key_span,
                        name,
                        scheme,
                        hoisted_mutability(stmt),
                    )?;
                }
            }
            self.pending_constraints = pending
                .iter()
                .zip(left_by_all)
                .filter_map(|(c, left)| left.then_some(c.clone()))
                .collect();
            let all: Vec<TVarName> = {
                let mut all: Vec<TVarName> = schemes_vars.iter().flatten().cloned().collect();
                all.sort_by_key(|v| v.id());
                all.dedup();
                all
            };
            let shared = schemes_vars
                .iter()
                .all(|vs| all.iter().all(|v| vs.contains(v)));
            if round == 1 || shared {
                break;
            }
            group_vars = all;
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
        use crate::types::{PropName, RowType, TVarName, TypeDef, CALLABLE_KEY};

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
        // A method reading `this` has the instance as its receiver, a
        // row tail bound to the instance's row, which holds the method:
        // that tail is no type the class leaves open. When the instance,
        // written out whole (where the cycle is cut at a variable still
        // bound), has no variable of its own, the class has no
        // parameters. (One that has keeps its receiver tails as
        // parameters too, so each instance's methods have their own.)
        if !brand_vars.is_empty() {
            let open = self.flatten_type(ret).free_vars().into_iter().any(|v| {
                v.is_flex() && !env_free.contains(&v) && self.main_subst.resolve(&v).is_none()
            });
            if !open {
                brand_vars.clear();
            }
        }

        // The id reserved for the class before the program's aliases
        // were parsed, so they could name it (`type C = { m: InsertIx }`).
        let id = self
            .reserved_class_ids
            .remove(name)
            .unwrap_or_else(|| self.fresh_type_id());
        self.register_named_type(TypeDef::nominal(
            id,
            name.to_string(),
            brand_vars.clone(),
            (**ret).clone(),
        ));
        self.class_brand_ids.insert(name.to_string(), id);
        // A JavaScript class's name is a type in annotations
        // (`/** const xs: (A | B)[] */`), unless an alias already claims
        // it: references resolve to the brand. (Python resolves class
        // names in annotations itself.)
        if self.language == crate::ast::SourceLanguage::JavaScript {
            let reserved = self
                .type_aliases
                .get(name)
                .is_none_or(|d| d.open_arity && d.nominal_id == Some(id));
            if reserved {
                self.type_aliases.insert(
                    name.to_string(),
                    crate::infer::state::AliasDef {
                        params: brand_vars.iter().map(|v| v.id()).collect(),
                        body: (**ret).clone(),
                        nominal_id: Some(id),
                        rec_id: None,
                        open_arity: false,
                        class: true,
                    },
                );
            }
        }

        let args: Vec<Type> = brand_vars.iter().map(|v| Type::var(v.clone())).collect();
        let branded_func = Type::Func {
            this_type: this_type.clone(),
            params: params.clone(),
            ret: Box::new(Type::Named(id, args)),
        };

        let mut new_props = row.props.clone();
        new_props.insert(call_key, call_entry.with_ty(branded_func));
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
    ) -> InferResult<TypeEnv> {
        let mut new_env = env.clone();
        for stmt in stmts {
            if let Some((name, _, _, type_annotation, return_type_ast, _)) =
                function_decl_parts(stmt)
            {
                let key_span = hoisted_key_span(stmt).expect("a hoisted function");
                // A polymorphic annotation is the function's scheme from
                // the start: its peers, and its own body, use it at any
                // instance (see `function_annotation_scheme`).
                let scheme = match self.function_annotation_scheme(
                    env,
                    name,
                    type_annotation,
                    return_type_ast,
                    key_span,
                )? {
                    Some((scheme, _)) => scheme,
                    None => TypeScheme::mono(self.fresh_type_var()),
                };
                let key = self.key_of(key_span, name);
                new_env = self.rebind(
                    &new_env,
                    key,
                    key_span,
                    name,
                    scheme,
                    hoisted_mutability(stmt),
                )?;
            }
        }
        Ok(new_env)
    }

    /// A function declaration's annotation with type parameters and no
    /// constraints (`/** function id<T>(x: T) => T */`) is its scheme, as a
    /// `const`'s is (`check_polymorphic_annotation`): the function gets it,
    /// and its body is checked with the type parameters rigid
    /// (`check_function_annotation`), so a body that doesn't have every
    /// instance (`return 1`, `x + x`, `if (x)`) is rejected rather than the
    /// annotation's variables being instantiated by it. `None` for any
    /// other declaration, and for one the program reassigns (whose
    /// annotation's variables stay flexible, as a reassigned `let`'s do).
    pub(in crate::infer) fn function_annotation_scheme(
        &mut self,
        env: &TypeEnv,
        name: &str,
        type_annotation: &Option<TypeAnnotation>,
        return_type_ast: Option<&crate::types::TypeAst>,
        key_span: Span,
    ) -> InferResult<Option<(TypeScheme, Span)>> {
        let Some(annotation) = type_annotation else {
            return Ok(None);
        };
        if return_type_ast.is_some() || self.resolution.written_at(key_span, name) {
            return Ok(None);
        }
        let annotation_span = Span::new(annotation.span.start, annotation.span.end);
        let parsed = parse_type_annotation_with_preds(
            &annotation.content,
            annotation_span,
            annotation.content_start,
            self.next_var_id(),
            self.next_pvar_id(),
            &self.type_aliases,
        );
        let Some((ann_ty, var_map, next_pvar, preds)) = self.annotation_or_report(parsed) else {
            return Ok(None);
        };
        self.bump_pvar_id_to(next_pvar);
        if let Some(&max) = var_map.values().max() {
            self.bump_var_id_to(max + 1);
        }
        if var_map.is_empty() || !preds.is_empty() {
            return Ok(None);
        }
        // Called detached unless it says otherwise, as for a monomorphic
        // annotation (`infer_function_expecting`).
        let ann_ty = crate::infer::lower::annotation_this(&ann_ty, &Type::ArrowThis);
        Ok(Some((
            self.generalize(&env.free(), &ann_ty),
            annotation_span,
        )))
    }

    /// Check a function declaration's body against its polymorphic
    /// annotation's `scheme` with the type variables rigid (skolems), as a
    /// `const`'s initialiser is, and with no skolem escaping. The body sees
    /// the function's own name at the scheme (the hoisted binding in
    /// `env`), so it may call itself at any instance.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn check_function_annotation(
        &mut self,
        env: &TypeEnv,
        params: &[Param],
        body: &Stmt,
        span: Span,
        scheme: &TypeScheme,
        ann_span: Span,
    ) -> InferResult<Type> {
        let env_free_before = env.free_vars();
        // Only the type variables are rigid: an optional field's presence
        // stays flexible, as under a monomorphic annotation.
        let (skolems, rigid_ty) = self.skolemize(&TypeScheme {
            pvars: Vec::new(),
            ..scheme.clone()
        });
        let func = Expr::Function {
            name: None,
            params: params.to_vec(),
            body: Box::new(body.clone()),
            type_annotation: None,
            arrow: false,
            span,
        };
        self.check_expr(env, &func, &rigid_ty)?;
        self.simplify_has_props()?;
        self.reject_escaped_skolems(&env_free_before, skolems.clone(), ann_span)?;
        // What the body's declarations and expressions were found to be
        // (for hovers and inlay hints) is at the annotation's type
        // parameters, not at the skolems that stood for them in the check.
        let mut back = crate::types::Subst::empty();
        for (skolem, var) in skolems.iter().zip(&scheme.vars) {
            back.insert(skolem.clone(), Type::Var(var.clone()));
        }
        let inside = |at: usize| span.start <= at && at < span.end;
        let keys: Vec<usize> = self
            .decl_types
            .keys()
            .copied()
            .filter(|&k| inside(k))
            .collect();
        for k in keys {
            let ty = self.zonk(&self.decl_types[&k].clone());
            self.decl_types.insert(k, back.apply(&ty));
        }
        if let Some(mut types) = self.expr_types.take() {
            for ((start, _), ty) in types.iter_mut() {
                if inside(*start) {
                    *ty = back.apply(&self.zonk(ty));
                }
            }
            self.expr_types = Some(types);
        }
        Ok(back.apply(&rigid_ty))
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
        name_span: Option<Span>,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let env = &self.hoisted_env(env);
        // Reuse the type variable hoisted by the enclosing scope if
        // this function was pre-bound there, otherwise start fresh.
        // Re-using the hoisted var is what lets mutually recursive
        // functions see each other's inferred types.
        let key = self.key_of(span, name);
        // A polymorphic annotation is the function's scheme, which its body
        // is checked against (`function_annotation_scheme`).
        if let Some((scheme, ann_span)) =
            self.function_annotation_scheme(env, name, type_annotation, return_type_ast, span)?
        {
            let pre_env = self.rebind(env, key, span, name, scheme.clone(), Mutability::Mutable)?;
            let ty =
                self.check_function_annotation(&pre_env, params, body, span, &scheme, ann_span)?;
            let name_span = crate::ast::function_name_span(name_span, span, name);
            self.record_decl_type(name_span, ty);
            self.record_decl_scheme(name_span, scheme.clone());
            return Ok((
                Type::Undefined,
                self.bind(env, span, name, scheme, Mutability::Mutable)?,
            ));
        }
        let func_var = match env.lookup_key(&key) {
            Some(b) if b.scheme.is_mono() => b.scheme.ty().clone(),
            _ => self.fresh_type_var(),
        };
        let pre_env = self.rebind(
            env,
            key.clone(),
            span,
            name,
            TypeScheme::mono(func_var.clone()),
            Mutability::Mutable,
        )?;

        // Infer the function type
        let func_type = self.infer_function(
            &pre_env,
            Some(name),
            params,
            body,
            type_annotation,
            return_type_ast,
            false,
            span,
        )?;

        // Unify pre-bound type with inferred type
        self.unify(span, &func_var, &func_type)?;

        // Record the type at the *name* offset (not the `function`
        // keyword) so LSP go-to-def → hover lookups line up.
        let name_span = crate::ast::function_name_span(name_span, span, name);
        self.record_decl_type(name_span, func_type.clone());

        // Generalize the function type. The enclosing scope may have
        // pre-bound `name` to the placeholder `func_var` (now unified with
        // the function's own type), which must not count as the
        // environment fixing the function's variables.
        let env_free = env.remove_key(&key).free();
        self.simplify_has_props()?;
        let scheme = self.generalize(&env_free, &func_type);
        self.record_decl_scheme(name_span, scheme.clone());

        Ok((
            Type::Undefined,
            self.bind(env, span, name, scheme, Mutability::Mutable)?,
        ))
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

/// The expression of a concise arrow body (`(x) => expr`), which the
/// parser lowers to a block ending in a `return` spanning the same
/// source as the block.
fn concise_body(body: &Stmt) -> Option<(&Expr, Span)> {
    match body {
        Stmt::Block { body, span } => match body.last() {
            Some(Stmt::Return {
                argument: Some(expr),
                span: ret_span,
            }) if ret_span == span => Some((expr, *ret_span)),
            _ => None,
        },
        _ => None,
    }
}

/// The names an SCC of hoistable functions (statement indices into
/// `stmts`) reads from the enclosing scope.
pub(in crate::infer) fn group_free_names(
    stmts: &[Stmt],
    group: &[usize],
) -> std::collections::HashSet<String> {
    let mut free = std::collections::HashSet::new();
    for &i in group {
        if let Some((name, params, body, _, _, _)) = function_decl_parts(&stmts[i]) {
            free.extend(free_identifiers_in_function_body(Some(name), params, body));
        }
    }
    free
}

/// Compute strongly-connected components of the hoistable-function
/// call graph in `stmts`, returned in topological order. Each inner
/// `Vec<usize>` lists statement indices in source order.
///
/// Statements that aren't hoistable function declarations do not
/// appear in the output. The caller is responsible for interleaving
/// non-function statements with the SCC results.
pub(in crate::infer) fn compute_scc_groups(
    stmts: &[Stmt],
    const_functions: &std::collections::HashSet<usize>,
) -> Vec<Vec<usize>> {
    // Pass 1: collect the hoistable function decls (and the function-
    // valued `const`s chosen by `hoistable_const_functions`) and their
    // free identifiers.
    let mut nodes: Vec<HoistableNode> = Vec::new();
    let mut name_to_node: HashMap<String, usize> = HashMap::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if const_function_decl(stmt).is_some() && !const_functions.contains(&i) {
            continue;
        }
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
        // `free` is a hash set: without an order of their own, the
        // edges (and so the order Tarjan emits independent groups in,
        // which is the order they are inferred in) would change from
        // run to run.
        adj[i].sort_unstable();
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
pub(crate) fn extract_callable(
    ty: &Type,
) -> Option<(Option<Type>, Vec<crate::types::FuncParam>, Type)> {
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
pub(crate) fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
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
fn definitely_returns(
    stmt: &Stmt,
    exhaustive: &std::collections::HashSet<crate::span::Span>,
) -> bool {
    let returns = |s: &Stmt| definitely_returns(s, exhaustive);
    match stmt {
        Stmt::Return { .. } | Stmt::Throw { .. } => true,
        Stmt::Block { body, .. } => body.last().is_some_and(returns),
        Stmt::Labeled { body, .. } => returns(body),
        // Both arms must return for the `if` to be exhaustive; a missing
        // `else` can fall through.
        Stmt::If {
            consequent,
            alternate: Some(alt),
            ..
        } => returns(consequent) && returns(alt),
        // `try` completes abnormally only if every path that can reach the
        // end returns: the body, and the handler if there is one (without
        // one, an exception leaves the `try` abruptly). A `finally` that
        // returns dominates everything.
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            if let Some(fin) = finalizer {
                if returns(fin) {
                    return true;
                }
            }
            returns(block) && handler.as_ref().is_none_or(|h| returns(&h.body))
        }
        // `while True:` never falls through, unless a `break` leaves it.
        Stmt::While { test, body, .. } => {
            matches!(
                test,
                Expr::Lit {
                    value: Literal::Boolean(true),
                    ..
                }
            ) && !super::control::breaks_out(body)
        }
        // A switch that always takes some case, none of which breaks out
        // of it, runs on to its last case (falling through the others):
        // it returns if that one does.
        Stmt::Switch { cases, span, .. } => {
            exhaustive.contains(span)
                && !cases
                    .iter()
                    .any(|c| c.consequent.iter().any(super::control::breaks_out))
                && cases
                    .last()
                    .is_some_and(|c| c.consequent.last().is_some_and(returns))
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
        let sccs = tarjan_scc(&[Vec::new()]);
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
