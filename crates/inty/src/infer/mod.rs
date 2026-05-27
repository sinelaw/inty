//! Type inference module for inty.
//!
//! This module provides the core type inference implementation:
//! - `state`: Inference state with fresh variable generation and substitution
//! - `env`: Type environment for variable bindings
//! - `unify`: Unification algorithm with occurs check
//! - `features`: Per-feature inference rules (scalars, arrays, rows, …)
//! - `type_parser`: Parser for TypeScript-style type annotations
//! - `decorate`: AST decoration with inferred types

mod decorate;
mod env;
mod features;
mod lower;
mod narrow;
mod state;
mod type_parser;
mod unify;
mod var_table;
mod zonk;

#[cfg(test)]
mod tests;

pub use decorate::decorate_with_types;
pub use env::TypeEnv;
pub use narrow::{apply_narrowing, Narrowing, Path};
pub use state::{InferConfig, InferState, InferWarning, PendingConstraint, TypeClass};
pub use type_parser::{
    parse_type_annotation, parse_type_annotation_with_aliases, parse_type_annotation_with_pvars,
};
pub use unify::UnifyResult;

use crate::error::{IntyError, TypeError};
use crate::ast::{ExportDecl, Expr, Program, Stmt, VarDeclarator, VarKind};
use crate::types::{Type, TypeScheme};

/// Result type for inference operations.
pub type InferResult<T> = Result<T, IntyError>;

/// True when a statement is either a plain `function f() {}` declaration or
/// an `export function f() {}` — both participate in the same hoisting
/// group so peer forward references and mutual recursion work uniformly.
pub(crate) fn is_function_like_decl(stmt: &Stmt) -> bool {
    matches!(
        stmt,
        Stmt::FunctionDecl { .. }
            | Stmt::Export {
                declaration: ExportDecl::Function { .. },
                ..
            }
    )
}

/// Source-order recovery after a `Stmt` fails inference. Binds every
/// name the statement *would have* introduced (`var x`, `const y`,
/// `function f`, the equivalent `export` wrappers) to `Type::Error`
/// in `env`. Statements that don't introduce names (Expr, If, While,
/// Throw, ...) leave the env unchanged. `Type::Error` unifies trivially
/// with anything that doesn't bind free vars and propagates through
/// member access / calls / type-class constraints, so later
/// references don't trigger cascading "undefined variable" or
/// unification errors — they're absorbed by the sentinel and the
/// original error stays the only diagnostic for this site.
fn bind_failed_stmt_names_to_error(env: &TypeEnv, stmt: &Stmt) -> TypeEnv {
    let mut out = env.clone();
    let declarators = match stmt {
        Stmt::Var { declarations, .. } => Some(declarations.as_slice()),
        Stmt::Export {
            declaration: ExportDecl::Var { declarations, .. },
            ..
        } => Some(declarations.as_slice()),
        _ => None,
    };
    if let Some(decls) = declarators {
        for decl in decls {
            if decl.name.starts_with("$destr$") {
                continue;
            }
            out = out.extend(decl.name.clone(), TypeScheme::mono(Type::Error));
        }
        return out;
    }
    let fn_name = match stmt {
        Stmt::FunctionDecl { name, .. } => Some(name),
        Stmt::Export {
            declaration: ExportDecl::Function { name, .. },
            ..
        } => Some(name),
        _ => None,
    };
    if let Some(name) = fn_name {
        out = out.extend(name.clone(), TypeScheme::mono(Type::Error));
    }
    out
}

impl InferState {
    /// Infer the type of a program.
    pub fn infer_program(&mut self, env: &TypeEnv, program: &Program) -> InferResult<Type> {
        let (ty, _env) = self.infer_program_with_env(env, program)?;
        Ok(ty)
    }

    /// Infer the type of a program, returning both the type and the final environment.
    pub fn infer_program_with_env(
        &mut self,
        env: &TypeEnv,
        program: &Program,
    ) -> InferResult<(Type, TypeEnv)> {
        // Clear any stale apply_subst overflow flag from a previous
        // run on a different program. The flag is thread-local so a
        // prior overflow elsewhere would otherwise contaminate this
        // run's diagnostics.
        let _ = crate::types::subst::take_apply_subst_overflow();

        // The language's unit / "no value" type — used as the implicit
        // return of a function that falls off the end.
        self.unit_type = if program.unit_is_null {
            Type::Null
        } else {
            Type::Undefined
        };

        // Load any user-defined generic type aliases before
        // checking the program. Aliases are not nominal — referring
        // to `Foo<X>` is exactly equivalent to inlining `Foo`'s body
        // with the type argument substituted.
        self.load_type_aliases(&program.type_aliases)?;
        // Inject constructors for declared nominal types before checking
        // the body, so `Name(repr)` resolves to a branded value.
        let env = self.nominal_constructor_env(env, &program.type_aliases);
        // Record which factory functions to brand nominally (classes).
        self.class_brand_names
            .extend(program.class_brands.iter().cloned());
        let result = self.infer_stmt_list(&env, &program.statements);

        // If `Type::apply_subst` hit its recursion-depth cap during
        // this run (see `docs/scaling.md`), surface a clean
        // diagnostic. The walk has already substituted the offending
        // sites with `Type::Error`, so inference completed without a
        // SIGSEGV — but the user needs to know their input pushed
        // past inty's current scaling limit.
        if crate::types::subst::take_apply_subst_overflow() {
            let span = crate::span::Span::new(0, 0);
            self.push_error(
                crate::error::TypeError::Module {
                    message: "type checker hit its recursion-depth cap on \
                        a deeply nested type (see docs/scaling.md). Inference \
                        continued past the limit by substituting `<error>` \
                        for the affected subtree; downstream diagnostics may \
                        be incomplete."
                        .to_string(),
                    span,
                }
                .into(),
            );
        }

        result
    }

    /// Parse each declared type alias's body once, with the alias's
    /// own parameter names bound to fresh skolemised type-var IDs.
    /// Subsequent `Foo<args>` references substitute argument types
    /// for those parameter IDs.
    pub fn load_type_aliases(
        &mut self,
        aliases: &[crate::ast::TypeAlias],
    ) -> InferResult<()> {
        use crate::infer::state::AliasDef;
        use crate::types::{TVarName, TypeDef};

        // Pass 1: reserve a slot for every alias so each body can see
        // its peers (mutual references). For *nominal* aliases we also
        // allocate the brand id and parameter ids up front, so a
        // nominal body can refer to the type recursively (e.g. a class
        // method returning `Self`) and resolve to the right
        // `Type::Named(id, …)`.
        let mut nominal_param_ids: std::collections::HashMap<String, Vec<u32>> =
            std::collections::HashMap::new();
        for alias in aliases {
            let nominal_id = if alias.nominal {
                Some(self.fresh_type_id())
            } else {
                None
            };
            let params: Vec<u32> = if alias.nominal {
                let ids: Vec<u32> = alias
                    .params
                    .iter()
                    .map(|_| {
                        let TVarName::Flex(id) = self.fresh_flex() else {
                            unreachable!("fresh_flex returns Flex");
                        };
                        id
                    })
                    .collect();
                nominal_param_ids.insert(alias.name.clone(), ids.clone());
                ids
            } else {
                Vec::new()
            };
            self.type_aliases.insert(
                alias.name.clone(),
                AliasDef {
                    params,
                    body: Type::Undefined,
                    nominal_id,
                },
            );
        }

        // Pass 2: parse each body with the alias env visible.
        for alias in aliases {
            // Reuse the pass-1 parameter ids for nominal aliases (so
            // recursive references line up); allocate fresh ids for
            // structural aliases as before.
            let param_ids: Vec<u32> = if alias.nominal {
                nominal_param_ids
                    .get(&alias.name)
                    .cloned()
                    .unwrap_or_default()
            } else {
                alias
                    .params
                    .iter()
                    .map(|_| {
                        let TVarName::Flex(id) = self.fresh_flex() else {
                            unreachable!("fresh_flex returns Flex");
                        };
                        id
                    })
                    .collect()
            };

            // Resolve the body. Frontends that lower annotations through
            // the shared `TypeAst` IR (Python) supply `body_ast`; the
            // JavaScript path supplies a `body` string parsed by the
            // `type_parser`. Either way other alias references resolve,
            // since the slots reserved in pass 1 are already in scope.
            let body_ty = if let Some(ast) = &alias.body_ast {
                self.lower_type_ast(ast)
            } else {
                let mut parser = crate::infer::type_parser::TypeParser::with_aliases(
                    &alias.body,
                    alias.span,
                    self.next_var_id(),
                    &self.type_aliases,
                );
                for (name, id) in alias.params.iter().zip(param_ids.iter()) {
                    parser.preset_var(name.clone(), *id);
                }
                let parsed = parser.parse()?;
                let next = parser.next_var_id();
                self.bump_var_id_to(next);
                parsed
            };
            let body = (body_ty, 0u32);

            let nominal_id = self
                .type_aliases
                .get(&alias.name)
                .and_then(|d| d.nominal_id);

            // For a nominal alias, register the brand's representation
            // in the named-type registry so `unify`/member-access can
            // see through it.
            if let Some(id) = nominal_id {
                let tvar_params: Vec<TVarName> =
                    param_ids.iter().map(|i| TVarName::Flex(*i)).collect();
                self.register_named_type(TypeDef::nominal(
                    id,
                    alias.name.clone(),
                    tvar_params,
                    body.0.clone(),
                ));
            }

            self.type_aliases.insert(
                alias.name.clone(),
                AliasDef {
                    params: param_ids,
                    body: body.0,
                    nominal_id,
                },
            );
        }
        Ok(())
    }

    /// Extend `base` with a value-level constructor for each declared
    /// nominal alias. `nominal type Name<P> = Repr` injects
    /// `Name: <P>(Repr) => Name`, the only way to *introduce* a branded
    /// value (mirroring how calling a Python class is the only way to
    /// mint an instance). Reads see through the brand; identity does not.
    fn nominal_constructor_env(
        &self,
        base: &TypeEnv,
        aliases: &[crate::ast::TypeAlias],
    ) -> TypeEnv {
        use crate::types::{TVarName, TypeScheme};
        let mut env = base.clone();
        for alias in aliases {
            if !alias.nominal {
                continue;
            }
            let Some(def) = self.type_aliases.get(&alias.name) else {
                continue;
            };
            let Some(id) = def.nominal_id else { continue };
            let args: Vec<Type> = def.params.iter().map(|i| Type::flex(*i)).collect();
            let named = Type::Named(id, args);
            let ctor = Type::simple_func(vec![def.body.clone()], named);
            let vars: Vec<TVarName> = def.params.iter().map(|i| TVarName::Flex(*i)).collect();
            let pvars: Vec<_> = ctor.free_pvars().into_iter().collect();
            let scheme = TypeScheme::poly_with_presence(vars, pvars, ctor);
            env = env.extend(alias.name.clone(), scheme);
        }
        env
    }

    /// Infer a list of statements with ECMAScript-strict-mode function
    /// declaration hoisting (ES § 9.2.10).
    ///
    /// Every `function` declaration in this scope is collected before
    /// any body is inferred, regardless of source position. The
    /// dependency graph between those decls (built from a free-
    /// identifier analysis of each body, see
    /// `parser::free_idents`) is decomposed into strongly-connected
    /// components by Tarjan's algorithm. Each SCC is processed as
    /// one mutually-recursive group via `infer_function_group`,
    /// in topological order so a caller SCC always sees its callees'
    /// generalised schemes. Non-function statements then flow in
    /// source order against the fully-populated function env —
    /// which matches what runtime semantics do, since by the time
    /// any non-function statement executes, every `function` decl
    /// in the scope is already visible.
    ///
    /// Forward references and mutual recursion between any pair of
    /// function decls in the same scope type-check, regardless of
    /// intervening non-function statements (the htmx / jQuery /
    /// lodash IIFE library pattern). See `docs/scc-inference.md`
    /// for the full design and the ECMAScript citations.
    pub(crate) fn infer_stmt_list(
        &mut self,
        env: &TypeEnv,
        stmts: &[Stmt],
    ) -> InferResult<(Type, TypeEnv)> {
        // Track names declared via `const` in this scope to reject
        // duplicate declarations, which are almost always bugs and match
        // standard JS semantics for const. Synthesised destructuring
        // temps (`$destr$N`) are skipped — they're uniquely generated
        // per pattern and can't collide.
        let mut const_names: std::collections::HashSet<String> = std::collections::HashSet::new();

        // Pre-pass: hoist top-level `var` / `let` / `const` names so
        // hoisted function declarations (Pass 2 below) can reference
        // them even when the declaration appears later in source
        // order. This matches the IIFE-with-forward-declared-methods
        // pattern that htmx / jQuery / lodash use:
        //
        //     const lib = { foo: null, bar: null };
        //     function helper() { return lib.foo; }   // sees `lib`
        //     lib.foo = function() { return helper(); };
        //
        // Each hoisted name is pre-bound to a fresh type variable.
        // When the corresponding Var statement is inferred in Pass 3,
        // we unify the hoisted variable with the actual inferred
        // type so any function body that referenced the hoisted form
        // ends up resolving to the real type via the substitution.
        //
        // This is what TypeScript / Flow do for typing purposes —
        // TDZ violations remain runtime-only and are not enforced
        // here.
        let mut hoisted_data: std::collections::HashMap<String, Type> =
            std::collections::HashMap::new();
        let collect_hoists = |hoisted_data: &mut std::collections::HashMap<String, Type>,
                              state: &mut Self,
                              declarations: &[VarDeclarator]| {
            for decl in declarations {
                if decl.name.starts_with("$destr$") {
                    continue;
                }
                hoisted_data
                    .entry(decl.name.clone())
                    .or_insert_with(|| state.fresh_type_var());
            }
        };
        for stmt in stmts {
            match stmt {
                Stmt::Var { declarations, .. } => {
                    collect_hoists(&mut hoisted_data, self, declarations);
                }
                Stmt::Export {
                    declaration:
                        crate::ast::ExportDecl::Var { declarations, .. },
                    ..
                } => {
                    collect_hoists(&mut hoisted_data, self, declarations);
                }
                _ => {}
            }
        }

        // Pass 1: compute the SCC partition of all hoistable function
        // decls in this scope. Each inner Vec holds statement indices
        // in source order; the outer Vec is in topological order.
        let scc_groups = crate::infer::features::functions::compute_scc_groups(stmts);

        // Pass 2: type-check each SCC in topological order.
        // `infer_function_group` does the textbook let-rec inference
        // (hoist names with fresh TVars, infer bodies in shared env,
        // generalise at the boundary) — we just hand it one SCC at a
        // time.
        let mut current_env = env.clone();
        for (name, ty) in &hoisted_data {
            current_env = current_env.extend(name.clone(), TypeScheme::mono(ty.clone()));
        }
        let errors_at_entry = self.errors.len();
        for scc_indices in &scc_groups {
            // Gather the SCC's statements in source order. Cloning
            // is cheap relative to the inference work that follows.
            let group_stmts: Vec<Stmt> =
                scc_indices.iter().map(|&i| stmts[i].clone()).collect();
            match self.infer_function_group(&current_env, &group_stmts) {
                Ok(new_env) => current_env = new_env,
                Err(err) => {
                    // Best-effort recovery: bind every member of the
                    // failed SCC to `Type::Error`. The user already
                    // got one diagnostic (the original `err`);
                    // downstream uses of these names propagate Error
                    // silently through `unify`, `infer_member`,
                    // `infer_call`, and the type-class solver. This
                    // keeps unrelated SCCs and source-order
                    // statements type-checking without cascading
                    // noise. See `docs/scc-inference.md` § "Cross-SCC
                    // type errors".
                    for stmt in &group_stmts {
                        if let Some((name, _, _, _, _, _)) =
                            crate::infer::features::functions::function_decl_parts(stmt)
                        {
                            current_env = current_env
                                .extend(name.to_string(), TypeScheme::mono(Type::Error));
                        }
                    }
                    self.push_error(err);
                }
            }
        }

        // Pass 3: walk the statement list in source order. Function
        // decls are skipped (already typed in Pass 2). Non-function
        // statements are inferred normally against the now-fully-
        // populated env. On failure, recover by binding any names the
        // statement *would have* introduced to `Type::Error` so later
        // statements in the same scope can still type-check; downstream
        // uses propagate `Error` silently through unification, member
        // access, and call inference.
        let mut result = Type::Undefined;
        for stmt in stmts {
            if is_function_like_decl(stmt) {
                continue;
            }
            if let Stmt::Var {
                kind: VarKind::Const,
                declarations,
                ..
            } = stmt
            {
                for decl in declarations {
                    if decl.name.starts_with("$destr$") {
                        continue;
                    }
                    if !const_names.insert(decl.name.clone()) {
                        let err = TypeError::Module {
                            message: format!(
                                "duplicate declaration of 'const {}' in the same scope",
                                decl.name
                            ),
                            span: decl.span,
                        };
                        self.push_error(err.into());
                    }
                }
            }
            match self.infer_stmt(&current_env, stmt) {
                Ok((ty, new_env)) => {
                    result = ty;
                    current_env = new_env;
                    // If this statement bound a name we pre-hoisted,
                    // unify the hoisted variable with the actual
                    // inferred type. The hoisted variable may already
                    // carry constraints from function bodies in
                    // Pass 2 that referenced the name before its
                    // declaration; unifying propagates the real type
                    // to those references via the substitution.
                    let unify_hoisted = |state: &mut Self,
                                         declarations: &[VarDeclarator]| {
                        for decl in declarations {
                            if let Some(hoisted) = hoisted_data.get(&decl.name) {
                                if let Some(scheme) = current_env.lookup(&decl.name) {
                                    let actual = scheme.body.ty.clone();
                                    if let Err(e) = state.unify(decl.span, hoisted, &actual) {
                                        state.push_error(e);
                                    }
                                }
                            }
                        }
                    };
                    match stmt {
                        Stmt::Var { declarations, .. } => {
                            unify_hoisted(self, declarations);
                        }
                        Stmt::Export {
                            declaration:
                                crate::ast::ExportDecl::Var { declarations, .. },
                            ..
                        } => {
                            unify_hoisted(self, declarations);
                        }
                        _ => {}
                    }
                }
                Err(err) => {
                    // Source-order recovery: bind any names the
                    // statement would have introduced to `Type::Error`
                    // so later references don't cascade into new
                    // "undefined variable" noise. Statements that
                    // don't bind names (Expr, If, While, ...) just
                    // get skipped — the env is unchanged.
                    current_env = bind_failed_stmt_names_to_error(&current_env, stmt);
                    self.push_error(err);
                }
            }
        }

        // If we accumulated any errors in this `infer_stmt_list` call
        // (or one nested inside the bodies of statements we just
        // walked), surface the first new one. Callers that want every
        // error drain `state.errors` after the top-level inference
        // completes.
        if self.errors.len() > errors_at_entry {
            return Err(self.errors[errors_at_entry].clone());
        }
        Ok((result, current_env))
    }

    /// Bidirectional checking entry point: check that `expr` has type
    /// `expected`. The default rule is "synth then subsume", which
    /// covers HM-style equality plus the literal-vs-base
    /// subsumption baked into [`InferState::subsume`]. The interesting
    /// case is `Expr::Object` against a row or union of rows: rather
    /// than synthesising an object literal whose primitive field
    /// values get widened (the synthesis-mode behaviour in
    /// `infer_object`), we push the expected per-field type into each
    /// property value, preserving singleton literal types where the
    /// expected type asks for them. This is what makes
    /// `area({ kind: "circle", r: 10 })` type-check against a
    /// discriminated-union parameter without any backtracking inside
    /// `unify` — the synthesised arg already exactly equals the
    /// matching arm.
    ///
    /// Falls back to synthesis + subsume whenever the expected type
    /// is a fresh variable, a primitive, or anything else where
    /// pushing-down has no purchase.
    pub fn check_expr(
        &mut self,
        env: &TypeEnv,
        expr: &Expr,
        expected: &Type,
    ) -> InferResult<Type> {
        let expected = self.zonk(expected);
        // Object-literal special case: dispatch to the contextual
        // checking path that propagates per-field expected types.
        if let Expr::Object { properties, span } = expr {
            if let Some(ty) = self.try_check_object(env, properties, *span, &expected)? {
                return Ok(ty);
            }
        }
        // Default: synthesise, then subsume into expected.
        // When the expected type is still a fresh flex variable
        // (e.g. an un-instantiated polymorphic parameter), the
        // subsume below will simply bind it to whatever the synth
        // produced. Without widening here, that binding pins the
        // var to a singleton like `Lit(1)`, and a *second* argument
        // that shares the same var (because of a Plus / equality
        // constraint, like `add(a: a, b: a) => a`) would then be
        // forced to the *same* singleton — `add(1, 2)` would fail
        // because `Lit(2) ≰ Lit(1)`. Widen here so the binding
        // lands on the base type, matching what `var x = 1` would
        // produce at a synthesis site.
        let synth = self.infer_expr(env, expr)?;
        let synth_for_bind = if matches!(
            self.zonk(&expected),
            Type::Var(crate::types::TVarName::Flex(_))
        ) {
            synth.widen_fresh_literals()
        } else {
            synth.clone()
        };
        self.subsume(expr.span(), &synth_for_bind, &expected)?;
        Ok(self.zonk(&synth))
    }

    /// Infer the type of an expression.
    pub fn infer_expr(&mut self, env: &TypeEnv, expr: &Expr) -> InferResult<Type> {
        match expr {
            Expr::Lit { value, span } => self.infer_literal(value, *span),

            Expr::Ident { name, span } => {
                if let Some(scheme) = env.lookup(name) {
                    let ty = self.instantiate(scheme);
                    // Record origin for type variables from variable references
                    if let Type::Var(var) = &ty {
                        self.record_origin(
                            var.clone(),
                            crate::error::TypeOrigin::Variable {
                                name: name.clone(),
                                span: *span,
                            },
                        );
                    }
                    Ok(ty)
                } else {
                    Err(TypeError::UndefinedVariable {
                        name: name.clone(),
                        span: *span,
                    }
                    .into())
                }
            }

            Expr::This { span: _ } => {
                // 'this' is looked up like any other variable
                if let Some(scheme) = env.lookup("this") {
                    Ok(self.instantiate(scheme))
                } else {
                    // If 'this' is not in scope, return undefined
                    Ok(Type::Undefined)
                }
            }

            Expr::Array { elements, span } => self.infer_array(env, elements, *span),

            Expr::Tuple { elements, span } => self.infer_tuple(env, elements, *span),

            Expr::Object { properties, span } => self.infer_object(env, properties, *span),

            Expr::Function {
                name,
                params,
                body,
                type_annotation,
                span,
            } => self.infer_function(
                env,
                name.as_deref(),
                params,
                body,
                type_annotation,
                None,
                *span,
            ),

            Expr::Member {
                object,
                property,
                span,
            } => self.infer_member(env, object, property, *span),

            Expr::ComputedMember {
                object,
                property,
                span,
            } => self.infer_computed_member(env, object, property, *span),

            Expr::Call {
                callee,
                arguments,
                keywords,
                span,
            } => self.infer_call(env, callee, arguments, keywords, *span),

            Expr::New {
                callee,
                arguments,
                span,
            } => self.infer_new(env, callee, arguments, *span),

            Expr::NewTarget { span: _ } => {
                // new.target is either undefined or a function
                Ok(self.fresh_type_var())
            }

            Expr::Unary { op, argument, span } => self.infer_unary(env, *op, argument, *span),

            Expr::Binary {
                op,
                left,
                right,
                span,
            } => self.infer_binary(env, *op, left, right, *span),

            Expr::Assign {
                op,
                left,
                right,
                span,
            } => self.infer_assign(env, *op, left, right, *span),

            Expr::Conditional {
                test,
                consequent,
                alternate,
                span,
            } => self.infer_conditional(env, test, consequent, alternate, *span),

            Expr::NullishCoalesce { left, right, span } => {
                self.infer_nullish_coalesce(env, left, right, *span)
            }

            Expr::OptionalChain {
                head,
                segments,
                span,
            } => self.infer_optional_chain(env, head, segments, *span),

            Expr::Spread { span, .. } => {
                // Spread is only legal inside an array literal element
                // position or a call-argument list; the array and call
                // inference handle `Expr::Spread` directly. Reaching
                // it here means the user wrote `var x = ...y;` or
                // similar — reject with a clear diagnostic.
                Err(crate::error::TypeError::InvalidSyntax {
                    message: "spread (`...`) is only allowed in array elements, call arguments, or object spread".to_string(),
                    span: *span,
                }
                .into())
            }

            Expr::RestArray { source, span, .. } => self.infer_rest_array(env, source, *span),

            Expr::RestRow {
                source,
                excluded,
                span,
            } => self.infer_rest_row(env, source, excluded, *span),

            Expr::Sequence { expressions, span } => self.infer_sequence(env, expressions, *span),

            Expr::TemplateLiteral {
                quasis: _,
                expressions,
                span,
            } => self.infer_template_literal(env, expressions, *span),
        }
    }

    /// Infer the type of a statement.
    /// Returns the type that the statement "produces" and the updated environment.
    pub fn infer_stmt(&mut self, env: &TypeEnv, stmt: &Stmt) -> InferResult<(Type, TypeEnv)> {
        match stmt {
            Stmt::Block { body, .. } => {
                // Function declarations inside a block are hoisted within
                // the block, so we reuse the same grouping logic the
                // top-level program uses.
                let (result, _inner_env) = self.infer_stmt_list(env, body)?;
                // Block introduces a new scope, so we return the original env
                Ok((result, env.clone()))
            }

            Stmt::Empty { .. } => Ok((Type::Undefined, env.clone())),

            Stmt::Expr { expression, .. } => {
                let ty = self.infer_expr(env, expression)?;
                Ok((ty, env.clone()))
            }

            Stmt::Var {
                kind, declarations, ..
            } => self.infer_stmt_var(env, *kind, declarations),

            // Import and export are handled at the module level, not during inference
            // For now, we just skip them (module system is not yet implemented)
            Stmt::Import { .. } => {
                // TODO: Implement module resolution and import type bindings
                Ok((Type::Undefined, env.clone()))
            }

            Stmt::Export { declaration, span } => {
                // Desugar to the underlying declaration and infer that, so
                // `export var x = 1;` and `export function f() {}` end up
                // in the env exactly like their un-exported counterparts.
                // The module resolver reads the final env back out.
                let _ = span;
                match declaration {
                    ExportDecl::Var {
                        kind,
                        declarations,
                        span,
                    } => self.infer_stmt(
                        env,
                        &Stmt::Var {
                            kind: *kind,
                            declarations: declarations.clone(),
                            span: *span,
                        },
                    ),
                    ExportDecl::Function {
                        name,
                        params,
                        body,
                        type_annotation,
                        span,
                    } => self.infer_stmt(
                        env,
                        &Stmt::FunctionDecl {
                            name: name.clone(),
                            params: params.clone(),
                            body: body.clone(),
                            type_annotation: type_annotation.clone(),
                            return_type_ast: None,
                            span: *span,
                        },
                    ),
                    ExportDecl::From { .. } => {
                        // Re-exports introduce no local bindings; the
                        // resolver merges the target module's schemes
                        // directly into this module's exports table.
                        Ok((Type::Undefined, env.clone()))
                    }
                    ExportDecl::List {
                        specifiers,
                        span: _,
                    } => {
                        // `export { a, b as c };` doesn't change types — the
                        // resolver reads the exported names from a separate
                        // table built by `modules::collect_exports`. All we
                        // do here is verify each `local` is in fact declared,
                        // so a typo doesn't survive until import time.
                        for spec in specifiers {
                            if env.lookup(&spec.local).is_none() {
                                return Err(IntyError::Type(TypeError::Module {
                                    message: format!(
                                        "exported name `{}` is not declared in this module",
                                        spec.local
                                    ),
                                    span: spec.span,
                                }));
                            }
                        }
                        Ok((Type::Undefined, env.clone()))
                    }
                    ExportDecl::Default { value, span } => {
                        // `export default function f() { … }` is two bindings:
                        // a function declaration `f` and an alias `default = f`.
                        // Other RHS forms desugar to `const default = <value>;`.
                        if let Expr::Function {
                            name: Some(fn_name),
                            params,
                            body,
                            type_annotation,
                            span: f_span,
                        } = value
                        {
                            let (_, env_after_fn) = self.infer_stmt(
                                env,
                                &Stmt::FunctionDecl {
                                    name: fn_name.clone(),
                                    params: params.clone(),
                                    body: body.clone(),
                                    type_annotation: type_annotation.clone(),
                                    return_type_ast: None,
                                    span: *f_span,
                                },
                            )?;
                            let scheme = env_after_fn
                                .lookup(fn_name)
                                .cloned()
                                .expect("function decl should bind its name");
                            Ok((
                                Type::Undefined,
                                env_after_fn.extend("default".to_string(), scheme),
                            ))
                        } else {
                            self.infer_stmt(
                                env,
                                &Stmt::Var {
                                    kind: VarKind::Const,
                                    declarations: vec![VarDeclarator {
                                        name: "default".to_string(),
                                        init: Some(value.clone()),
                                        type_annotation: None,
                                        type_ast: None,
                                        kind: VarKind::Const,
                                        span: *span,
                                    }],
                                    span: *span,
                                },
                            )
                        }
                    }
                }
            }

            Stmt::If {
                test,
                consequent,
                alternate,
                span,
            } => self.infer_stmt_if(env, test, consequent, alternate, *span),

            Stmt::While { test, body, .. } => self.infer_stmt_while(env, test, body),

            Stmt::DoWhile { body, test, .. } => self.infer_stmt_do_while(env, body, test),

            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => self.infer_stmt_for(env, init, test, update, body),

            Stmt::ForIn {
                left,
                right,
                body,
                span,
            } => self.infer_stmt_for_in(env, left, right, body, *span),

            Stmt::ForOf {
                left,
                right,
                body,
                span,
            } => self.infer_stmt_for_of(env, left, right, body, *span),

            Stmt::Break { .. } | Stmt::Continue { .. } => Ok((Type::Undefined, env.clone())),

            Stmt::Return { argument, span: _ } => {
                let ret_type = if let Some(expr) = argument {
                    self.infer_expr(env, expr)?
                } else {
                    Type::Undefined
                };
                // Contribute to the enclosing function's return type. The
                // function body's *completion* value is no longer used as
                // the implicit return (a trailing bare expression statement
                // must not leak its value), so explicit returns are
                // collected here instead. Returns outside any function
                // (top-level) find no frame and are ignored.
                if let Some(frame) = self.return_value_stack.last_mut() {
                    frame.push(ret_type.clone());
                }
                Ok((ret_type, env.clone()))
            }

            Stmt::Throw { argument, .. } => {
                let _throw_type = self.infer_expr(env, argument)?;
                // throw doesn't really have a type, but we use Undefined
                Ok((Type::Undefined, env.clone()))
            }

            Stmt::Try {
                block,
                handler,
                finalizer,
                span: _,
            } => self.infer_stmt_try(env, block, handler, finalizer),

            Stmt::Switch {
                discriminant,
                cases,
                span,
            } => self.infer_stmt_switch(env, discriminant, cases, *span),

            Stmt::Labeled { body, .. } => self.infer_stmt(env, body),

            Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                return_type_ast,
                span,
            } => self.infer_stmt_function_decl(
                env,
                name,
                params,
                body,
                type_annotation,
                return_type_ast.as_ref(),
                *span,
            ),
        }
    }
}
