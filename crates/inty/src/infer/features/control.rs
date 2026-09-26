//! Conditional/sequence expressions and control-flow statements.

use crate::ast::{CatchClause, Expr, ForInLhs, ForInit, Stmt, SwitchCase, VarDeclarator};
use crate::span::Span;
use crate::types::{Type, TypeScheme};

use super::super::env::TypeEnv;
use super::super::narrow::{
    apply_narrowing, narrowing_collapsed_to_never, path_from_expr, test_facts, Facts, Narrowing,
    Path,
};
use super::super::state::InferState;
use super::super::InferResult;
use crate::ast::free_idents::{
    assign_target_names, assigned_names_in_expr, assigned_names_in_stmt,
};

/// If `ty` is a closed union whose every member is a literal type
/// (or just a single literal type), return the set of literal values.
/// Otherwise None.
fn literal_set_of_type(ty: &Type) -> Option<Vec<crate::types::LitValue>> {
    match ty {
        Type::Literal(l) => Some(vec![l.clone()]),
        Type::Union(members) => {
            let mut out = Vec::with_capacity(members.len());
            for m in members {
                if let Type::Literal(l) = m {
                    out.push(l.clone());
                } else {
                    return None;
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// Format a literal value for human-readable warning messages.
fn format_literal(l: &crate::types::LitValue) -> String {
    match l {
        crate::types::LitValue::String(s) => format!("\"{}\"", s),
        crate::types::LitValue::Number(n) => n.to_string(),
        crate::types::LitValue::Bool(b) => b.to_string(),
    }
}

/// Apply each of `facts` to `env` in turn. With `dead_warning`, a fact
/// that leaves its variable no possible type makes the branch dead, and
/// the test at `test_span` is reported as constant.
fn apply_facts(
    state: &mut InferState,
    env: &TypeEnv,
    facts: &[(Path, Narrowing)],
    dead_warning: Option<(&str, Span)>,
) -> TypeEnv {
    let mut out = env.clone();
    for (path, narrowing) in facts {
        let next = apply_narrowing(state, &out, path, narrowing);
        if let Some((message, span)) = dead_warning {
            if narrowing.warns_when_dead() && narrowing_collapsed_to_never(state, &out, &next, path)
            {
                state.warn(span, message);
            }
        }
        out = next;
    }
    out
}

/// Whether control never leaves `stmt` normally: it always returns,
/// throws, breaks or continues. Code after such a statement in the same
/// list runs only if control didn't get this far. Erring toward `false`
/// only gives up narrowing.
pub(in crate::infer) fn always_exits(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return { .. } | Stmt::Throw { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {
            true
        }
        Stmt::Block { body, .. } => body.iter().any(always_exits),
        Stmt::If {
            consequent,
            alternate: Some(alt),
            ..
        } => always_exits(consequent) && always_exits(alt),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            finalizer.as_deref().is_some_and(always_exits)
                || (always_exits(block) && handler.as_ref().is_none_or(|h| always_exits(&h.body)))
        }
        // A labeled statement can be left by a `break` to its own label.
        _ => false,
    }
}

impl InferState {
    /// Recognise `isinstance(<path>, ClassName)` as a brand narrowing.
    /// The class name is mapped to its nominal brand id via
    /// `class_brand_ids` (populated when classes are branded); an unknown
    /// class, a non-identifier class argument, or the wrong arity yields
    /// `None`, so the test falls back to a no-op narrowing.
    fn extract_isinstance(&self, test: &Expr) -> Option<(Path, Narrowing)> {
        let Expr::Call {
            callee, arguments, ..
        } = test
        else {
            return None;
        };
        let Expr::Ident { name, .. } = callee.as_ref() else {
            return None;
        };
        if name != "isinstance" || arguments.len() != 2 {
            return None;
        }
        let path = path_from_expr(&arguments[0])?;
        let Expr::Ident {
            name: class_name, ..
        } = &arguments[1]
        else {
            return None;
        };
        let id = *self.class_brand_ids.get(class_name)?;
        Some((path, Narrowing::IsInstance(id)))
    }

    /// Type-check the test of an `if`/conditional and produce the
    /// (consequent, alternate) environments after flow-sensitive
    /// narrowing. If the test matches one of the recognised patterns
    /// (`typeof x === ...`, `x === lit`, `x !== lit`, …), refine each
    /// branch's env with the predicate and its negation; otherwise both
    /// branches see the original env. Also fires the unreachable-branch
    /// warning when narrowing collapses one side to `never`.
    pub(in crate::infer) fn infer_branching_test(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
    ) -> InferResult<(TypeEnv, TypeEnv)> {
        let _test_type = self.infer_expr(env, test)?;
        let (base, facts) = self.test_facts_in(env, test, None);
        let span = test.span();
        let cons_env = apply_facts(
            self,
            &base,
            &facts.when_true,
            Some((
                "this comparison is always false: the type of the operand cannot satisfy it",
                span,
            )),
        );
        let alt_env = apply_facts(
            self,
            &base,
            &facts.when_false,
            Some((
                "this comparison is always true: the type of the operand cannot violate it",
                span,
            )),
        );
        Ok((cons_env, alt_env))
    }

    /// The facts `test` establishes, and the environment they refine:
    /// `env` less any narrowing of a variable the test assigns. Facts
    /// about variables assigned in `test` or in `guarded` (the code the
    /// test guards, when that is part of the same expression) are
    /// dropped: the value there may not be the one tested.
    fn test_facts_in(
        &self,
        env: &TypeEnv,
        test: &Expr,
        guarded: Option<&Expr>,
    ) -> (TypeEnv, Facts) {
        let mut facts = test_facts(test, &|e| self.extract_isinstance(e));
        if facts.when_true.is_empty() && facts.when_false.is_empty() && !env.has_narrowings() {
            return (env.clone(), facts);
        }
        let mut assigned = assigned_names_in_expr(test);
        if let Some(g) = guarded {
            assigned.extend(assigned_names_in_expr(g));
        }
        facts.forget(&assigned);
        (env.unnarrow(&assigned), facts)
    }

    /// The environment `guarded` is checked in when it runs only if
    /// `test` came out `outcome`: the right operand of `&&` (`true`) or
    /// `||` (`false`).
    pub(in crate::infer) fn env_given(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        outcome: bool,
        guarded: &Expr,
    ) -> TypeEnv {
        let (base, facts) = self.test_facts_in(env, test, Some(guarded));
        let facts = if outcome {
            &facts.when_true
        } else {
            &facts.when_false
        };
        apply_facts(self, &base, facts, None)
    }

    /// A loop's environment: every iteration after the first starts
    /// wherever the previous one left off, so a narrowing of a variable
    /// the loop assigns may not hold on entry.
    fn loop_entry_env(&self, env: &TypeEnv, exprs: &[Option<&Expr>], body: &Stmt) -> TypeEnv {
        if !env.has_narrowings() {
            return env.clone();
        }
        let mut assigned = assigned_names_in_stmt(body);
        for e in exprs.iter().flatten() {
            assigned.extend(assigned_names_in_expr(e));
        }
        env.unnarrow(&assigned)
    }

    /// Infer the type of a conditional expression.
    pub(in crate::infer) fn infer_conditional(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        consequent: &Expr,
        alternate: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let (cons_env, alt_env) = self.infer_branching_test(env, test)?;

        let cons_type = self.infer_expr(&cons_env, consequent)?;
        let alt_type = self.infer_expr(&alt_env, alternate)?;

        // Branches that disagree in type are merged into a union rather
        // than rejected — see InferState::join for details. The
        // joined result is then widened: `true ? 3 : 4` is `Number`,
        // not `3 | 4`. (TS does the same: branch joins are
        // synthesis-mode widening points unless the conditional is
        // contextually typed.)
        let joined = self.join(span, &cons_type, &alt_type)?;
        Ok(self.widen(span, &joined))
    }

    /// Infer the type of a sequence expression.
    pub(in crate::infer) fn infer_sequence(
        &mut self,
        env: &TypeEnv,
        expressions: &[Expr],
        _span: Span,
    ) -> InferResult<Type> {
        let mut result = Type::Undefined;
        for expr in expressions {
            result = self.infer_expr(env, expr)?;
        }
        Ok(result)
    }

    /// If the discriminant of a switch has a finite, closed type (a
    /// union of literal types, or a single literal type), return the
    /// covered literals; used by switch-exhaustiveness analysis.
    ///
    /// We rely on phase-3 union elimination having already pushed
    /// member access through unions, so `shape.kind` on a discriminated
    /// union resolves to a literal union directly.
    fn resolve_finite_literal_set(
        &self,
        _discriminant: &Expr,
        disc_type: &Type,
    ) -> Option<Vec<crate::types::LitValue>> {
        let disc = self.apply_subst(disc_type);
        literal_set_of_type(&disc)
    }

    /// Bind a list of `for`-init declarators into the loop env.
    fn bind_for_init_decls(
        &mut self,
        env: &TypeEnv,
        decls: &[VarDeclarator],
    ) -> InferResult<TypeEnv> {
        let mut new_env = env.clone();
        for decl in decls {
            // Widen like an ordinary `let`: the header variable is
            // mutable, so `let i = 0` must be `Number`, not the
            // singleton `0` (which `i++` or `a(i)` would then contradict).
            let var_type = if let Some(init_expr) = &decl.init {
                let init_type = self.infer_expr(&new_env, init_expr)?;
                self.widen(init_expr.span(), &init_type)
            } else {
                self.fresh_type_var()
            };
            // Record the type for this declaration
            self.record_decl_type(decl.span, var_type.clone());
            new_env = new_env.extend(decl.name.clone(), TypeScheme::mono(var_type));
        }
        Ok(new_env)
    }

    /// Handle an `if` statement.
    pub(in crate::infer) fn infer_stmt_if(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        consequent: &Stmt,
        alternate: &Option<Box<Stmt>>,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let (cons_env, alt_env) = self.infer_branching_test(env, test)?;

        let (cons_type, _) = self.infer_stmt(&cons_env, consequent)?;

        // A statement's value isn't joined: only whether it completes
        // matters (`never` when neither branch does).
        let _ = span;
        let is_never = |t: &Type| matches!(t, Type::Union(m) if m.is_empty());
        let result = if let Some(alt) = alternate {
            let (alt_type, _) = self.infer_stmt(&alt_env, alt)?;
            if is_never(&self.zonk(&cons_type)) && is_never(&self.zonk(&alt_type)) {
                Type::never()
            } else {
                Type::Undefined
            }
        } else {
            Type::Undefined
        };

        // When one branch always exits, what follows runs only after the
        // other, so that branch's facts still hold there (less those of
        // variables the test or that branch assigns):
        //
        //     if (node === null) return 0;
        //     return node.value;            // node is not null here
        let cons_exits = always_exits(consequent);
        let alt_exits = alternate.as_deref().is_some_and(always_exits);
        let after = match (cons_exits, alt_exits) {
            (true, false) => {
                let mut assigned = assigned_names_in_expr(test);
                if let Some(alt) = alternate {
                    assigned.extend(assigned_names_in_stmt(alt));
                }
                alt_env.unnarrow(&assigned)
            }
            (false, true) => {
                let mut assigned = assigned_names_in_expr(test);
                assigned.extend(assigned_names_in_stmt(consequent));
                cons_env.unnarrow(&assigned)
            }
            _ if env.has_narrowings() => {
                let mut assigned = assigned_names_in_expr(test);
                assigned.extend(assigned_names_in_stmt(consequent));
                if let Some(alt) = alternate {
                    assigned.extend(assigned_names_in_stmt(alt));
                }
                env.unnarrow(&assigned)
            }
            _ => env.clone(),
        };

        Ok((result, after))
    }

    /// Handle a `while` statement.
    pub(in crate::infer) fn infer_stmt_while(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        body: &Stmt,
    ) -> InferResult<(Type, TypeEnv)> {
        // The body runs while the test holds:
        //
        //     while (node !== null) { sum += node.value; node = node.next; }
        let loop_env = self.loop_entry_env(env, &[Some(test)], body);
        let (body_env, _) = self.infer_branching_test(&loop_env, test)?;
        self.infer_stmt(&body_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `do { } while` statement.
    pub(in crate::infer) fn infer_stmt_do_while(
        &mut self,
        env: &TypeEnv,
        body: &Stmt,
        test: &Expr,
    ) -> InferResult<(Type, TypeEnv)> {
        let loop_env = self.loop_entry_env(env, &[Some(test)], body);
        self.infer_stmt(&loop_env, body)?;
        let _test_type = self.infer_expr(&loop_env, test)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a C-style `for` statement.
    pub(in crate::infer) fn infer_stmt_for(
        &mut self,
        env: &TypeEnv,
        init: &Option<ForInit>,
        test: &Option<Expr>,
        update: &Option<Expr>,
        body: &Stmt,
    ) -> InferResult<(Type, TypeEnv)> {
        let loop_env = if let Some(init) = init {
            match init {
                ForInit::VarDecl(decls) => self.bind_for_init_decls(env, decls)?,
                ForInit::Expr(expr) => {
                    self.infer_expr(env, expr)?;
                    env.clone()
                }
            }
        } else {
            env.clone()
        };
        let loop_env = self.loop_entry_env(&loop_env, &[test.as_ref(), update.as_ref()], body);

        // The body runs while the test holds.
        let body_env = match test {
            Some(test) => self.infer_branching_test(&loop_env, test)?.0,
            None => loop_env.clone(),
        };

        if let Some(update) = update {
            self.infer_expr(&loop_env, update)?;
        }

        self.infer_stmt(&body_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `for-in` statement.
    pub(in crate::infer) fn infer_stmt_for_in(
        &mut self,
        env: &TypeEnv,
        left: &ForInLhs,
        right: &Expr,
        body: &Stmt,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let _right_type = self.infer_expr(env, right)?;

        let loop_env = match left {
            ForInLhs::VarDecl(name, _, decl_span) => {
                // for-in iterates over string keys
                let var_type = Type::String;
                self.record_decl_type(*decl_span, var_type.clone());
                env.extend(name.clone(), TypeScheme::mono(var_type))
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.subsume(span, &lhs_type, &Type::String)?;
                env.unnarrow(&assign_target_names(expr))
            }
        };
        let loop_env = self.loop_entry_env(&loop_env, &[], body);

        self.infer_stmt(&loop_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `for-of` statement.
    pub(in crate::infer) fn infer_stmt_for_of(
        &mut self,
        env: &TypeEnv,
        left: &ForInLhs,
        right: &Expr,
        body: &Stmt,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let right_type = self.infer_expr(env, right)?;

        // Right side should be an array
        let elem_type = self.fresh_type_var();
        self.unify(span, &right_type, &Type::array(elem_type.clone()))?;

        let loop_env = match left {
            ForInLhs::VarDecl(name, _, decl_span) => {
                let var_type = self.zonk(&elem_type);
                self.record_decl_type(*decl_span, var_type.clone());
                env.extend(name.clone(), TypeScheme::mono(var_type))
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.subsume(span, &lhs_type, &elem_type)?;
                env.unnarrow(&assign_target_names(expr))
            }
        };
        let loop_env = self.loop_entry_env(&loop_env, &[], body);

        self.infer_stmt(&loop_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `try / catch / finally` statement.
    pub(in crate::infer) fn infer_stmt_try(
        &mut self,
        env: &TypeEnv,
        block: &Stmt,
        handler: &Option<CatchClause>,
        finalizer: &Option<Box<Stmt>>,
    ) -> InferResult<(Type, TypeEnv)> {
        // Names bound in the try-body stay in scope for the handler and for
        // code after the `try` — `var`/Python function-scoping, where a
        // partially-run body may have already bound them. Inferring the
        // body's statement list directly (rather than as a fresh-scope
        // `Block`) is what threads those bindings forward.
        let (try_type, body_env) = match block {
            Stmt::Block { body, .. } => self.infer_stmt_list(env, body)?,
            other => self.infer_stmt(env, other)?,
        };

        // The handler and the `finally` block can start anywhere in the
        // body, where none of the body's narrowings need hold yet and any
        // of its assignments may have run. Dropping every narrowing there
        // is simple and safe.
        let unsure_env = body_env.without_narrowings();

        if let Some(catch) = handler {
            // The caught exception object is unmodelled, so its binding is a
            // fresh (opaque) variable. The handler runs against the
            // try-body's environment.
            let catch_env =
                unsure_env.extend(catch.param.clone(), TypeScheme::mono(self.fresh_type_var()));
            self.infer_stmt(&catch_env, &catch.body)?;
        }

        if let Some(finally) = finalizer {
            self.infer_stmt(&unsure_env, finally)?;
        }

        // After a handler, what follows may have come through it.
        let after = if handler.is_some() || finalizer.is_some() {
            unsure_env
        } else {
            body_env
        };
        Ok((try_type, after))
    }

    /// Handle a `switch` statement.
    pub(in crate::infer) fn infer_stmt_switch(
        &mut self,
        env: &TypeEnv,
        discriminant: &Expr,
        cases: &[SwitchCase],
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let disc_type = self.infer_expr(env, discriminant)?;

        // The path the switch is dispatching on (if it's an
        // identifier or member chain). Used to narrow each case
        // body's env. Falls back to no narrowing for switches on
        // arbitrary expressions.
        let disc_path = super::super::narrow::path_from_expr(discriminant);

        let mut covered_literals: Vec<crate::types::LitValue> = Vec::new();
        let mut has_default = false;

        for (i, case) in cases.iter().enumerate() {
            // A case reached by falling through from the one before has
            // none of its own facts, and is past that case's assignments.
            let falls_into = i > 0 && !cases[i - 1].consequent.iter().any(always_exits);
            let case_env = if falls_into {
                let mut assigned = std::collections::HashSet::new();
                for c in &cases[..i] {
                    for s in &c.consequent {
                        assigned.extend(assigned_names_in_stmt(s));
                    }
                }
                if let Some(test) = &case.test {
                    let test_type = self.infer_expr(env, test)?;
                    if self.is_numeric(&disc_type) || self.is_numeric(&test_type) {
                        self.require_num(span, &disc_type)?;
                        self.require_num(span, &test_type)?;
                    } else {
                        self.subsume_either(span, &disc_type, &test_type)?;
                    }
                    if let Some(lit) = super::super::narrow::literal_value_of(test) {
                        covered_literals.push(lit);
                    }
                } else {
                    has_default = true;
                }
                env.unnarrow(&assigned)
            } else if let Some(test) = &case.test {
                let test_type = self.infer_expr(env, test)?;
                // Symmetric "comparable" check, like `===`: the case
                // test value is matched against the discriminator at
                // runtime, so either may subsume the other. Numbers
                // compare whatever their kind (an `Int` case on a `Number`
                // discriminant), as with `<`.
                if self.is_numeric(&disc_type) || self.is_numeric(&test_type) {
                    self.require_num(span, &disc_type)?;
                    self.require_num(span, &test_type)?;
                } else {
                    self.subsume_either(span, &disc_type, &test_type)?;
                }

                // If the case test is a literal and we know the
                // discriminator's path, the case body gets an env
                // narrowed by `disc === literal`.
                let lit = super::super::narrow::literal_value_of(test);
                if let Some(lit) = lit.clone() {
                    covered_literals.push(lit);
                }
                match (disc_path.as_ref(), lit) {
                    (Some(path), Some(lit)) => apply_narrowing(
                        self,
                        env,
                        path,
                        &super::super::narrow::Narrowing::Equals(lit),
                    ),
                    _ => env.clone(),
                }
            } else {
                has_default = true;
                env.clone()
            };

            let mut stmt_env = case_env;
            for stmt in &case.consequent {
                stmt_env = self.infer_stmt(&stmt_env, stmt)?.1;
            }
        }

        // Phase 6 — exhaustiveness: if the discriminant resolves
        // to a closed union of literal types (after narrowing
        // through subst, which also walks through the path), and
        // the switch has no default, every literal in the union
        // must be covered by some case test. Otherwise we warn.
        // Suppressed when `config.exhaustiveness_warnings` is off.
        if !has_default && self.config.exhaustiveness_warnings {
            let disc_finite = self.resolve_finite_literal_set(discriminant, &disc_type);
            if let Some(domain) = disc_finite {
                let missing: Vec<&crate::types::LitValue> = domain
                    .iter()
                    .filter(|d| !covered_literals.contains(d))
                    .collect();
                if !missing.is_empty() {
                    let names: Vec<String> = missing.iter().map(|l| format_literal(l)).collect();
                    self.warn(
                        span,
                        format!(
                            "non-exhaustive switch: missing case(s) for {}",
                            names.join(", ")
                        ),
                    );
                }
            }
        }

        Ok((Type::Undefined, env.clone()))
    }
}
