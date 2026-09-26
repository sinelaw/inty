//! Conditional/sequence expressions and control-flow statements.

use crate::ast::{
    BinOp, CatchClause, Expr, ForInLhs, ForInit, Literal, SourceLanguage, Stmt, SwitchCase,
    VarDeclarator,
};
use crate::span::Span;
use crate::types::{LitValue, Type, TypeScheme};

use super::super::env::{Mutability, TypeEnv};
use super::super::narrow::{
    apply_narrowing, is_singleton, narrowing_is_dead, path_from_expr, test_facts, typeof_fact,
    Narrowing, Path,
};
use super::super::state::InferState;
use super::super::InferResult;

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
        if let Some((message, span)) = dead_warning {
            if narrowing.warns_when_dead() && narrowing_is_dead(state, &out, path, narrowing) {
                state.warn(span, message);
            }
        }
        out = apply_narrowing(state, &out, path, narrowing);
    }
    out
}

/// Whether `body` (a loop's) contains a `break` that can leave the loop:
/// an unlabeled one outside any nested loop or `switch`, or any labeled
/// one (conservatively). Nested functions are not searched.
fn breaks_out(body: &Stmt) -> bool {
    fn walk(s: &Stmt, nested: bool) -> bool {
        match s {
            Stmt::Break { label, .. } => label.is_some() || !nested,
            Stmt::Block { body, .. } => body.iter().any(|s| walk(s, nested)),
            Stmt::If {
                consequent,
                alternate,
                ..
            } => walk(consequent, nested) || alternate.as_deref().is_some_and(|a| walk(a, nested)),
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::For { body, .. }
            | Stmt::ForIn { body, .. }
            | Stmt::ForOf { body, .. } => walk(body, true),
            Stmt::Switch { cases, .. } => cases
                .iter()
                .any(|c| c.consequent.iter().any(|s| walk(s, true))),
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                walk(block, nested)
                    || handler.as_ref().is_some_and(|h| walk(&h.body, nested))
                    || finalizer.as_deref().is_some_and(|f| walk(f, nested))
            }
            Stmt::Labeled { body, .. } => walk(body, nested),
            _ => false,
        }
    }
    walk(body, false)
}

/// Whether `body` contains a `break label` (outside nested functions).
pub(in crate::infer) fn breaks_to(body: &Stmt, label: &str) -> bool {
    match body {
        Stmt::Break { label: Some(l), .. } => l == label,
        Stmt::Block { body, .. } => body.iter().any(|s| breaks_to(s, label)),
        Stmt::If {
            consequent,
            alternate,
            ..
        } => {
            breaks_to(consequent, label)
                || alternate.as_deref().is_some_and(|a| breaks_to(a, label))
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::ForOf { body, .. }
        | Stmt::Labeled { body, .. } => breaks_to(body, label),
        Stmt::Switch { cases, .. } => cases
            .iter()
            .any(|c| c.consequent.iter().any(|s| breaks_to(s, label))),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            breaks_to(block, label)
                || handler.as_ref().is_some_and(|h| breaks_to(&h.body, label))
                || finalizer.as_deref().is_some_and(|f| breaks_to(f, label))
        }
        _ => false,
    }
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

    /// The narrowing one comparison establishes, if any: `typeof`,
    /// `isinstance`, or `<path> OP e` read by the type of `e` (see
    /// [`Narrowing`]). Both operand orders are recognised.
    fn fact_of(&self, env: &TypeEnv, test: &Expr) -> Option<(Path, Narrowing)> {
        if let Some(fact) = typeof_fact(test).or_else(|| self.extract_isinstance(test)) {
            return Some(fact);
        }
        let Expr::Binary {
            op, left, right, ..
        } = test
        else {
            return None;
        };
        let (strict, neg) = match op {
            BinOp::EqEqEq => (true, false),
            BinOp::NotEqEq => (true, true),
            BinOp::EqEq => (false, false),
            BinOp::NotEq => (false, true),
            _ => return None,
        };
        for (a, b) in [(left, right), (right, left)] {
            let Some(path) = path_from_expr(a) else {
                continue;
            };
            let Some(single) = self.singleton_operand(env, b) else {
                continue;
            };
            let narrowing = match (strict, self.language) {
                (true, _) => Narrowing::Is(single),
                (false, SourceLanguage::Python) => Narrowing::PyEq(single),
                (false, _) if matches!(single, Type::Null | Type::Undefined) => Narrowing::Nullish,
                (false, _) => continue,
            };
            return Some((path, if neg { narrowing.negate() } else { narrowing }));
        }
        None
    }

    /// The type of a comparison operand when it has exactly one value: a
    /// literal, or a variable of a singleton type (`undefined`).
    fn singleton_operand(&self, env: &TypeEnv, e: &Expr) -> Option<Type> {
        let ty = match e {
            Expr::Lit { value, .. } => match value {
                Literal::Null => Type::Null,
                Literal::Undefined => Type::Undefined,
                Literal::String(s) => Type::Literal(LitValue::String(s.clone())),
                Literal::Number(n) => Type::Literal(LitValue::Number(*n)),
                Literal::Boolean(b) => Type::Literal(LitValue::Bool(*b)),
                Literal::Regex { .. } => return None,
            },
            Expr::Ident { name, span } => {
                let scheme = &env.lookup_key(&self.key_of(*span, name))?.scheme;
                if !scheme.is_mono() {
                    return None;
                }
                self.apply_subst(scheme.ty())
            }
            _ => return None,
        };
        is_singleton(&ty).then_some(ty)
    }

    /// Type-check the test of an `if`/conditional and produce the
    /// (consequent, alternate) environments after flow-sensitive
    /// narrowing: the facts the test establishes when true, and when
    /// false (see `narrow::test_facts`). Also fires the
    /// unreachable-branch warning when a fact collapses its variable's
    /// type to `never`.
    pub(in crate::infer) fn infer_branching_test(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
    ) -> InferResult<(TypeEnv, TypeEnv)> {
        let _test_type = self.infer_expr(env, test)?;
        let facts = test_facts(test, &|e| self.fact_of(env, e));
        let span = test.span();
        let cons_env = apply_facts(
            self,
            env,
            &facts.when_true,
            Some((
                "this comparison is always false: the type of the operand cannot satisfy it",
                span,
            )),
        );
        let alt_env = apply_facts(
            self,
            env,
            &facts.when_false,
            Some((
                "this comparison is always true: the type of the operand cannot violate it",
                span,
            )),
        );
        Ok((cons_env, alt_env))
    }

    /// The environment for code that runs only if `test` came out
    /// `outcome`: the right operand of `&&` (`true`) or `||` (`false`).
    pub(in crate::infer) fn env_given(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        outcome: bool,
    ) -> TypeEnv {
        let facts = test_facts(test, &|e| self.fact_of(env, e));
        let facts = if outcome {
            &facts.when_true
        } else {
            &facts.when_false
        };
        apply_facts(self, env, facts, None)
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
            new_env = self.bind(
                &new_env,
                decl.span,
                &decl.name,
                TypeScheme::mono(var_type),
                Mutability::Mutable,
            )?;
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
            (true, false) => alt_env,
            (false, true) => cons_env,
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
        // The body runs while the test holds, and without a `break` the
        // loop is left only when it doesn't. (Narrowed bindings are never
        // written, so a test that held stays true for the iteration.)
        let (body_env, exit_env) = self.infer_branching_test(env, test)?;
        self.infer_stmt(&body_env, body)?;
        let after = if breaks_out(body) {
            env.clone()
        } else {
            exit_env
        };
        Ok((Type::Undefined, after))
    }

    /// Handle a `do { } while` statement.
    pub(in crate::infer) fn infer_stmt_do_while(
        &mut self,
        env: &TypeEnv,
        body: &Stmt,
        test: &Expr,
    ) -> InferResult<(Type, TypeEnv)> {
        self.infer_stmt(env, body)?;
        let (_, exit_env) = self.infer_branching_test(env, test)?;
        let after = if breaks_out(body) {
            env.clone()
        } else {
            exit_env
        };
        Ok((Type::Undefined, after))
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
        // The body, and the update after it, run while the test holds,
        // as in the loop's `while` form.
        let (body_env, exit_env) = match test {
            Some(test) => self.infer_branching_test(&loop_env, test)?,
            None => (loop_env.clone(), loop_env.clone()),
        };

        if let Some(update) = update {
            self.infer_expr(&body_env, update)?;
        }

        self.infer_stmt(&body_env, body)?;
        // After the loop, the test's false facts hold, unless the loop
        // can `break`. (A fact about the loop's own `let` stays with that
        // binding: the environment is keyed by declaration.)
        let after = if test.is_some() && !breaks_out(body) {
            exit_env.with_names_of(env)
        } else {
            env.clone()
        };
        Ok((Type::Undefined, after))
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
            ForInLhs::VarDecl(name, _, decl_span, _) => {
                // for-in iterates over string keys
                let var_type = Type::String;
                self.record_decl_type(*decl_span, var_type.clone());
                self.bind(
                    env,
                    *decl_span,
                    name,
                    TypeScheme::mono(var_type),
                    Mutability::Mutable,
                )?
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.subsume(span, &lhs_type, &Type::String)?;
                env.clone()
            }
        };

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
            ForInLhs::VarDecl(name, _, decl_span, _) => {
                let var_type = self.zonk(&elem_type);
                self.record_decl_type(*decl_span, var_type.clone());
                self.bind(
                    env,
                    *decl_span,
                    name,
                    TypeScheme::mono(var_type),
                    Mutability::Mutable,
                )?
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.subsume(span, &lhs_type, &elem_type)?;
                env.clone()
            }
        };

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
        // body, before any of its tests ran: they get the narrowings in
        // force before the `try`, which still hold (narrowed bindings are
        // never written).
        let unsure_env = body_env.with_narrowings_of(env);

        if let Some(catch) = handler {
            // The caught exception object is unmodelled, so its binding is a
            // fresh (opaque) variable. The handler runs against the
            // try-body's environment.
            let param_type = self.fresh_type_var();
            let catch_env = self.bind(
                &unsure_env,
                catch.span,
                &catch.param,
                TypeScheme::mono(param_type),
                Mutability::Mutable,
            )?;
            self.infer_stmt(&catch_env, &catch.body)?;
        }

        if let Some(finally) = finalizer {
            self.infer_stmt(&unsure_env, finally)?;
        }

        // After a handler, what follows may have come through it. (A
        // `finally` alone runs after the body completed, so the body's
        // narrowings still hold.)
        let after = if handler.is_some() {
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
            let mut narrowing = None;
            if let Some(test) = &case.test {
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
                if let Some(lit) = super::super::narrow::literal_value_of(test) {
                    covered_literals.push(lit);
                }
                // `case e:` matches by `===`: a case of a singleton type
                // narrows the discriminant's path.
                narrowing = self.singleton_operand(env, test).map(Narrowing::Is);
            } else {
                has_default = true;
            }
            // A case reached by falling through from the one before gets
            // none of its own facts.
            let falls_into = i > 0 && !cases[i - 1].consequent.iter().any(always_exits);
            let case_env = match (falls_into, disc_path.as_ref(), narrowing) {
                (false, Some(path), Some(n)) => apply_narrowing(self, env, path, &n),
                _ => env.clone(),
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
