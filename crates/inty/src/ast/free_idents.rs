//! Free-identifier analysis over the public AST.
//!
//! Computes the set of identifier names that appear in **reference**
//! position inside a sub-tree and are not bound by any enclosing
//! scope visible within that sub-tree. Used by the upcoming
//! SCC-based function-decl hoisting analysis (see
//! `docs/scc-inference.md`): for each top-level hoistable function
//! `f` we want to know which other hoistable names `f`'s body
//! references, so we can build a dependency graph and compute
//! strongly-connected components.
//!
//! The walker is intentionally a pure AST pass — it has no type
//! information and no opinion about whether a reference is "really"
//! defined (that's inference's job). It just answers: "starting
//! from this sub-tree, which names look outward for a binding?"
//!
//! ## Scoping model
//!
//! Mirrors ECMAScript strict-mode semantics (see
//! `docs/scc-inference.md` § "What ECMAScript says about hoisting"):
//!
//! - **Function scopes** are introduced by `FunctionDecl`,
//!   `Expr::Function`, `PropDef::Method`, `PropDef::Getter`, and
//!   `PropDef::Setter`. Parameters bind into the function scope.
//!   `var` declarations *anywhere* inside the function body bind
//!   into the function scope (ES § 14.3.2 — variable hoisting).
//! - **Block scopes** are introduced by `Stmt::Block`, the body of
//!   `if`/`for`/`while`/`do-while`/`try`/`catch`/`switch`, and the
//!   header of `for` / `for-in` / `for-of`. `let`/`const`
//!   declarations and `function` declarations bind into the
//!   immediate enclosing block (ES § 14.2 strict-mode block
//!   scoping for function decls).
//! - **References are not bindings.** `obj.foo` references `obj`;
//!   `foo` is a member name, not an identifier. Object literal
//!   keys are the same: `{foo: x}` references `x`, not `foo`.
//!   Property shorthand `{foo}` is already desugared to `{foo: foo}`
//!   by the parser, so the walker sees the value as `Expr::Ident`
//!   and counts it as a reference automatically.
//!
//! ## Hoisting in the walker
//!
//! Each scope pre-collects its bindings before any reference is
//! evaluated. That way a forward reference (`use(g); function g(){}`)
//! correctly resolves to the local `g` and isn't reported as free.
//! `var` is collected from the entire function body (not crossing
//! nested function boundaries); other forms are collected only from
//! the immediate block.

use std::collections::HashSet;

use super::{
    CatchClause, ChainSegment, ExportDecl, Expr, ForInLhs, ForInit, ImportSpecifier, Param,
    PropDef, Stmt, SwitchCase, VarDeclarator, VarKind,
};

/// Free identifiers of a function body, given the function's name (if
/// any — function expressions can be named, function declarations
/// always are) and parameter list.
///
/// This is the primary helper for SCC analysis: each hoistable
/// function decl gets its body's free-id set computed once, then the
/// caller intersects with the set of hoistable peer names to derive
/// the dependency edges.
pub fn free_identifiers_in_function_body(
    name: Option<&str>,
    params: &[Param],
    body: &Stmt,
) -> HashSet<String> {
    let mut state = State::new();
    state.enter_function();
    if let Some(n) = name {
        state.bind_lex(n);
    }
    for p in params {
        state.bind_lex(&p.name);
    }
    state.collect_function_scope_bindings(body);
    state.visit_stmt(body);
    state.free
}

/// Free identifiers of a single statement. The walker treats the
/// statement as appearing in its own outermost scope; any binding
/// the statement *introduces* (a `var`, `let`, `function`, …)
/// suppresses the corresponding reference.
pub fn free_identifiers_in_stmt(stmt: &Stmt) -> HashSet<String> {
    let mut state = State::new();
    state.enter_block();
    state.collect_block_bindings(std::slice::from_ref(stmt));
    state.visit_stmt(stmt);
    state.free
}

/// Free identifiers of a single expression. No bindings are
/// introduced at the outer level; every `Ident` reference inside is
/// counted as free unless shadowed by an inner scope (e.g. a function
/// expression with parameters).
pub fn free_identifiers_in_expr(expr: &Expr) -> HashSet<String> {
    let mut state = State::new();
    state.visit_expr(expr);
    state.free
}

// ---------------------------------------------------------------------------
// Internal state
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    Function,
    Block,
}

struct Scope {
    kind: ScopeKind,
    names: HashSet<String>,
}

struct State {
    scopes: Vec<Scope>,
    free: HashSet<String>,
}

impl State {
    fn new() -> Self {
        State {
            scopes: Vec::new(),
            free: HashSet::new(),
        }
    }

    fn enter_function(&mut self) {
        self.scopes.push(Scope {
            kind: ScopeKind::Function,
            names: HashSet::new(),
        });
    }

    fn enter_block(&mut self) {
        self.scopes.push(Scope {
            kind: ScopeKind::Block,
            names: HashSet::new(),
        });
    }

    fn leave_scope(&mut self) {
        self.scopes.pop();
    }

    /// Bind a name into the innermost scope (block or function). Used
    /// for `let`/`const`/`function` declarations, function
    /// parameters, named function expressions, catch parameters, and
    /// `let`/`const`/`function` declarations inside blocks.
    fn bind_lex(&mut self, name: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.names.insert(name.to_string());
        }
    }

    /// Bind a name into the innermost *function* scope. Used for
    /// `var` declarations, which are function-scoped regardless of
    /// where they appear inside the function (ES § 14.3.2).
    /// If no function scope exists (top-level script), bind into
    /// the outermost block scope so the binding still suppresses
    /// references at this level.
    fn bind_var(&mut self, name: &str) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.kind == ScopeKind::Function {
                scope.names.insert(name.to_string());
                return;
            }
        }
        if let Some(scope) = self.scopes.first_mut() {
            scope.names.insert(name.to_string());
        }
    }

    fn is_bound(&self, name: &str) -> bool {
        self.scopes.iter().any(|s| s.names.contains(name))
    }

    fn record_ref(&mut self, name: &str) {
        if !self.is_bound(name) {
            self.free.insert(name.to_string());
        }
    }

    // ---------------------------------------------------------------
    // Pre-collection of bindings
    // ---------------------------------------------------------------

    /// Collect all bindings reachable in the *current function scope*:
    /// every `var` declaration anywhere in the body, plus the
    /// top-level function/let/const declarations of the function's
    /// outer block.
    ///
    /// `var` decls inside nested blocks/loops hoist out to the
    /// function scope; `let`/`const`/`function` decls inside nested
    /// blocks do *not*. So this routine handles the function-scope
    /// top level and then delegates to `collect_nested_vars` for
    /// the deeper recursion.
    fn collect_function_scope_bindings(&mut self, body: &Stmt) {
        match body {
            Stmt::Block { body, .. } => {
                self.collect_block_bindings(body);
                for s in body {
                    self.collect_nested_vars(s);
                }
            }
            other => self.collect_nested_vars(other),
        }
    }

    /// Collect immediate-block bindings: top-level `function`
    /// declarations (hoisted within the block), `let`/`const`
    /// declarations, `var` declarations (also hoisted, via
    /// `bind_var`), and imports.
    fn collect_block_bindings(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            match stmt {
                Stmt::FunctionDecl { name, .. } => {
                    self.bind_lex(name);
                }
                Stmt::Export {
                    declaration: ExportDecl::Function { name, .. },
                    ..
                } => {
                    self.bind_lex(name);
                }
                Stmt::Export {
                    declaration:
                        ExportDecl::Var {
                            kind, declarations, ..
                        },
                    ..
                } => {
                    self.bind_var_declarations(*kind, declarations);
                }
                Stmt::Var {
                    kind, declarations, ..
                } => {
                    self.bind_var_declarations(*kind, declarations);
                }
                Stmt::Import { specifiers, .. } => {
                    for spec in specifiers {
                        let local = match spec {
                            ImportSpecifier::Named { local, .. }
                            | ImportSpecifier::Default { local, .. }
                            | ImportSpecifier::Namespace { local, .. } => local,
                        };
                        self.bind_lex(local);
                    }
                }
                _ => {}
            }
        }
    }

    fn bind_var_declarations(&mut self, kind: VarKind, decls: &[VarDeclarator]) {
        for d in decls {
            match kind {
                VarKind::Var => self.bind_var(&d.name),
                VarKind::Let | VarKind::Const => self.bind_lex(&d.name),
            }
        }
    }

    /// Recursively walk into block-like containers (NOT crossing
    /// function boundaries) and bind every `var` declaration into the
    /// current function scope. This is the ES "var hoisting" rule.
    fn collect_nested_vars(&mut self, stmt: &Stmt) {
        match stmt {
            // Top-level bindings of *this* statement are handled by
            // collect_block_bindings; collect_nested_vars only descends
            // into nested containers.
            Stmt::Block { body, .. } => {
                for s in body {
                    if let Stmt::Var {
                        kind: VarKind::Var,
                        declarations,
                        ..
                    } = s
                    {
                        for d in declarations {
                            self.bind_var(&d.name);
                        }
                    }
                    self.collect_nested_vars(s);
                }
            }
            Stmt::If {
                consequent,
                alternate,
                ..
            } => {
                self.collect_nested_vars(consequent);
                if let Some(a) = alternate {
                    self.collect_nested_vars(a);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
                self.collect_nested_vars(body);
            }
            Stmt::For { init, body, .. } => {
                if let Some(ForInit::VarDecl(decls)) = init {
                    for d in decls {
                        if matches!(d.kind, VarKind::Var) {
                            self.bind_var(&d.name);
                        }
                    }
                }
                self.collect_nested_vars(body);
            }
            Stmt::ForIn { body, .. } | Stmt::ForOf { body, .. } => {
                // ForInLhs::VarDecl doesn't carry VarKind in the public
                // AST, so we conservatively treat the loop binder as
                // block-scoped (not hoisted). `for (var x in obj)` —
                // rare in modern code — won't have `x` visible outside
                // the loop. The loop body is still scanned for
                // function-scope `var` decls.
                self.collect_nested_vars(body);
            }
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                self.collect_nested_vars(block);
                if let Some(h) = handler {
                    self.collect_nested_vars(&h.body);
                }
                if let Some(f) = finalizer {
                    self.collect_nested_vars(f);
                }
            }
            Stmt::Switch { cases, .. } => {
                for c in cases {
                    for s in &c.consequent {
                        if let Stmt::Var {
                            kind: VarKind::Var,
                            declarations,
                            ..
                        } = s
                        {
                            for d in declarations {
                                self.bind_var(&d.name);
                            }
                        }
                        self.collect_nested_vars(s);
                    }
                }
            }
            Stmt::Labeled { body, .. } => self.collect_nested_vars(body),
            // Function decls don't transfer their inner `var`s to the
            // outer function scope.
            _ => {}
        }
    }

    // ---------------------------------------------------------------
    // Statement and expression walks
    // ---------------------------------------------------------------

    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Block { body, .. } => {
                self.enter_block();
                self.collect_block_bindings(body);
                for s in body {
                    self.visit_stmt(s);
                }
                self.leave_scope();
            }
            Stmt::Empty { .. } => {}
            Stmt::Expr { expression, .. } => self.visit_expr(expression),
            Stmt::Var { declarations, .. } => {
                // Bindings were pre-collected by the enclosing scope.
                // Only visit initialisers here.
                for d in declarations {
                    if let Some(init) = &d.init {
                        self.visit_expr(init);
                    }
                }
            }
            Stmt::Import { .. } => {} // bindings pre-collected; nothing else to visit
            Stmt::Export { declaration, .. } => self.visit_export(declaration),
            Stmt::If {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.visit_expr(test);
                self.visit_stmt(consequent);
                if let Some(a) = alternate {
                    self.visit_stmt(a);
                }
            }
            Stmt::While { test, body, .. } => {
                self.visit_expr(test);
                self.visit_stmt(body);
            }
            Stmt::DoWhile { body, test, .. } => {
                self.visit_stmt(body);
                self.visit_expr(test);
            }
            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => {
                // The C-style for has its own block scope spanning
                // init/test/update/body. Names declared in init are
                // visible in all three.
                self.enter_block();
                if let Some(init) = init {
                    match init {
                        ForInit::VarDecl(decls) => {
                            for d in decls {
                                match d.kind {
                                    VarKind::Var => self.bind_var(&d.name),
                                    VarKind::Let | VarKind::Const => self.bind_lex(&d.name),
                                }
                                if let Some(init_expr) = &d.init {
                                    self.visit_expr(init_expr);
                                }
                            }
                        }
                        ForInit::Expr(e) => self.visit_expr(e),
                    }
                }
                if let Some(t) = test {
                    self.visit_expr(t);
                }
                if let Some(u) = update {
                    self.visit_expr(u);
                }
                self.visit_stmt(body);
                self.leave_scope();
            }
            Stmt::ForIn {
                left, right, body, ..
            }
            | Stmt::ForOf {
                left, right, body, ..
            } => {
                // `right` is evaluated in the enclosing scope; the
                // loop binder is scoped to the loop.
                self.visit_expr(right);
                self.enter_block();
                match left {
                    ForInLhs::VarDecl(name, _, _) => self.bind_lex(name),
                    ForInLhs::Expr(e) => self.visit_expr(e),
                }
                self.visit_stmt(body);
                self.leave_scope();
            }
            Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Return { argument, .. } => {
                if let Some(e) = argument {
                    self.visit_expr(e);
                }
            }
            Stmt::Throw { argument, .. } => self.visit_expr(argument),
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                self.visit_stmt(block);
                if let Some(h) = handler {
                    self.visit_catch(h);
                }
                if let Some(f) = finalizer {
                    self.visit_stmt(f);
                }
            }
            Stmt::Switch {
                discriminant,
                cases,
                ..
            } => {
                self.visit_expr(discriminant);
                self.enter_block();
                self.collect_switch_bindings(cases);
                for c in cases {
                    if let Some(t) = &c.test {
                        self.visit_expr(t);
                    }
                    for s in &c.consequent {
                        self.visit_stmt(s);
                    }
                }
                self.leave_scope();
            }
            Stmt::Labeled { body, .. } => self.visit_stmt(body),
            Stmt::FunctionDecl {
                name: _,
                params,
                body,
                ..
            } => {
                // The function's name is already bound in the
                // enclosing scope by collect_block_bindings.
                self.enter_function();
                for p in params {
                    self.bind_lex(&p.name);
                }
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
        }
    }

    fn visit_export(&mut self, decl: &ExportDecl) {
        match decl {
            ExportDecl::Var { declarations, .. } => {
                for d in declarations {
                    if let Some(init) = &d.init {
                        self.visit_expr(init);
                    }
                }
            }
            ExportDecl::Function { params, body, .. } => {
                self.enter_function();
                for p in params {
                    self.bind_lex(&p.name);
                }
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
            ExportDecl::Default { value, .. } => self.visit_expr(value),
            ExportDecl::List { .. } => {
                // Re-exports of already-bound locals reference those
                // locals. The parser stores specifiers without
                // distinguishing the local name from the export name
                // here; we treat them as referencing the local name.
                // Conservative: don't emit refs (the resolver handles
                // export-binding errors separately).
            }
            ExportDecl::From { .. } => {
                // re-export from another module — no local refs
            }
        }
    }

    fn visit_catch(&mut self, c: &CatchClause) {
        self.enter_block();
        self.bind_lex(&c.param);
        // catch body is a block; visit_stmt will enter a *second*
        // block scope, which is fine — the catch param is still
        // visible via the outer scope.
        self.visit_stmt(&c.body);
        self.leave_scope();
    }

    fn collect_switch_bindings(&mut self, cases: &[SwitchCase]) {
        // Top-level bindings inside switch case bodies all share the
        // switch's block scope. Collect FunctionDecl + let/const at
        // the top level of each case; nested `var`s hoist to the
        // enclosing function (already collected at function entry).
        for c in cases {
            self.collect_block_bindings(&c.consequent);
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
            Expr::Ident { name, .. } => self.record_ref(name),
            Expr::Array { elements, .. } => {
                for elt in elements.iter().flatten() {
                    self.visit_expr(elt);
                }
            }
            Expr::Tuple { elements, .. } => {
                for elt in elements {
                    self.visit_expr(elt);
                }
            }
            Expr::Object { properties, .. } => {
                for p in properties {
                    self.visit_prop(p);
                }
            }
            Expr::Function {
                name, params, body, ..
            } => {
                self.enter_function();
                if let Some(n) = name {
                    self.bind_lex(n);
                }
                for p in params {
                    self.bind_lex(&p.name);
                }
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
            Expr::Member { object, .. } => self.visit_expr(object),
            Expr::ComputedMember {
                object, property, ..
            } => {
                self.visit_expr(object);
                self.visit_expr(property);
            }
            Expr::Call {
                callee, arguments, ..
            }
            | Expr::New {
                callee, arguments, ..
            } => {
                self.visit_expr(callee);
                for a in arguments {
                    self.visit_expr(a);
                }
            }
            Expr::Unary { argument, .. } => self.visit_expr(argument),
            Expr::Binary { left, right, .. } => {
                self.visit_expr(left);
                self.visit_expr(right);
            }
            Expr::Assign { left, right, .. } => {
                self.visit_expr(left);
                self.visit_expr(right);
            }
            Expr::Conditional {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.visit_expr(test);
                self.visit_expr(consequent);
                self.visit_expr(alternate);
            }
            Expr::NullishCoalesce { left, right, .. } => {
                self.visit_expr(left);
                self.visit_expr(right);
            }
            Expr::OptionalChain { head, segments, .. } => {
                self.visit_expr(head);
                for seg in segments {
                    match seg {
                        ChainSegment::Member { .. } => {}
                        ChainSegment::Computed { property, .. } => {
                            self.visit_expr(property);
                        }
                        ChainSegment::Call { arguments, .. } => {
                            for a in arguments {
                                self.visit_expr(a);
                            }
                        }
                    }
                }
            }
            Expr::Spread { argument, .. } => self.visit_expr(argument),
            Expr::RestArray { source, .. } => self.visit_expr(source),
            Expr::RestRow { source, .. } => self.visit_expr(source),
            Expr::Sequence { expressions, .. } => {
                for e in expressions {
                    self.visit_expr(e);
                }
            }
            Expr::TemplateLiteral { expressions, .. } => {
                for e in expressions {
                    self.visit_expr(e);
                }
            }
        }
    }

    fn visit_prop(&mut self, prop: &PropDef) {
        match prop {
            PropDef::Property { value, .. } => self.visit_expr(value),
            PropDef::Method { params, body, .. } => {
                self.enter_function();
                for p in params {
                    self.bind_lex(&p.name);
                }
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
            PropDef::Getter { body, .. } => {
                self.enter_function();
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
            PropDef::Setter { param, body, .. } => {
                self.enter_function();
                self.bind_lex(param);
                self.collect_function_scope_bindings(body);
                self.visit_stmt(body);
                self.leave_scope();
            }
            PropDef::Spread { argument, .. } => self.visit_expr(argument),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontends::javascript::parse;

    fn free_in(src: &str) -> Vec<String> {
        let program = parse(src).expect("parse");
        let mut state = State::new();
        state.enter_block();
        state.collect_block_bindings(&program.statements);
        for s in &program.statements {
            state.visit_stmt(s);
        }
        let mut out: Vec<String> = state.free.into_iter().collect();
        out.sort();
        out
    }

    #[test]
    fn bare_reference_is_free() {
        assert_eq!(free_in("use(x);"), vec!["use", "x"]);
    }

    #[test]
    fn var_binding_suppresses_reference() {
        assert_eq!(free_in("var x = 1; use(x);"), vec!["use"]);
    }

    #[test]
    fn let_binding_suppresses_reference() {
        assert_eq!(free_in("let x = 1; use(x);"), vec!["use"]);
    }

    #[test]
    fn forward_function_reference_via_hoisting() {
        // The hallmark gap-4 case: `use(f)` before `function f`.
        assert_eq!(free_in("use(f); function f() {}"), vec!["use"]);
    }

    #[test]
    fn forward_var_reference_via_hoisting() {
        // `var x` is name-hoisted even though its value is undefined.
        assert_eq!(free_in("use(x); var x = 1;"), vec!["use"]);
    }

    #[test]
    fn function_param_shadows_outer() {
        assert_eq!(free_in("function f(x) { return x; }"), Vec::<String>::new());
    }

    #[test]
    fn nested_function_referencing_outer_helper_is_free() {
        // `g` is not declared anywhere — free.
        assert_eq!(free_in("function f() { return g(); }"), vec!["g"]);
    }

    #[test]
    fn nested_function_referencing_sibling_is_not_free() {
        // gap-4 hoisting case: `f` and `g` both declared at top.
        assert_eq!(
            free_in("function f() { return g(); } function g() { return 1; }"),
            Vec::<String>::new()
        );
    }

    #[test]
    fn member_name_is_not_a_reference() {
        // `foo` after the dot is a property name, not a free var.
        assert_eq!(free_in("use(obj.foo);"), vec!["obj", "use"]);
    }

    #[test]
    fn object_literal_key_is_not_a_reference() {
        // The `key` token in `{key: value}` is not a binding *or* a
        // reference, only `value` references something.
        assert_eq!(free_in("var o = {foo: x};"), vec!["x"]);
    }

    #[test]
    fn object_shorthand_is_a_reference() {
        // `{x}` desugars to `{x: x}` at parse time; only the value
        // half counts as a reference.
        assert_eq!(free_in("var o = {x};"), vec!["x"]);
    }

    #[test]
    fn named_function_expression_name_is_local_to_body() {
        // `f` is visible inside the expression body but not after.
        // The inner `return f` is bound (named-function-expression
        // scope), the outer `use(f)` is free. `use` is also free.
        let src = "var x = function f() { return f; }; use(f);";
        assert_eq!(free_in(src), vec!["f", "use"]);
    }

    #[test]
    fn catch_param_is_block_scoped() {
        // `e` visible inside the catch, free after.
        let src = "try {} catch (e) { use(e); } use(e);";
        assert_eq!(free_in(src), vec!["e", "use"]);
    }

    #[test]
    fn for_let_binder_is_block_scoped_to_loop() {
        let src = "for (let i = 0; i < 10; i = i + 1) { use(i); } use(i);";
        assert_eq!(free_in(src), vec!["i", "use"]);
    }

    #[test]
    fn var_hoists_out_of_nested_block() {
        // `var y` inside an `if` hoists to the enclosing function.
        let src = "function f(cond) { if (cond) { var y = 1; } return y; }";
        assert_eq!(free_in(src), Vec::<String>::new());
    }

    #[test]
    fn let_does_not_hoist_out_of_nested_block() {
        let src = "function f(cond) { if (cond) { let y = 1; } return y; }";
        assert_eq!(free_in(src), vec!["y"]);
    }

    #[test]
    fn for_of_binder_visible_in_body() {
        let src = "for (const k of arr) { use(k); }";
        assert_eq!(free_in(src), vec!["arr", "use"]);
    }

    #[test]
    fn template_literal_interpolations_are_references() {
        // The quasi parts are static strings; only ${...} counts.
        // Note: parse() converts the template to its AST form,
        // surfacing the expressions as Expr::Ident.
        assert_eq!(free_in("var s = `hello ${name}`;"), vec!["name"]);
    }

    #[test]
    fn iife_library_pattern() {
        // The motivating gap-4c case for SCC inference.
        let src = r#"
            var lib = (function() {
                const api = {
                    run: function(x) { return helper(x); }
                };
                function helper(x) { return x; }
                return api;
            })();
            var y = lib.run(1);
        "#;
        // Top-level has no free references; the IIFE captures
        // `helper` locally and `api`/`x` are bound.
        assert_eq!(free_in(src), Vec::<String>::new());
    }

    #[test]
    fn function_body_helper_api() {
        // Sanity-check the public helper.
        let src = "function f(a) { return a + b + c; }";
        let prog = parse(src).unwrap();
        let (params, body) = match &prog.statements[0] {
            Stmt::FunctionDecl { params, body, .. } => (params.as_slice(), body.as_ref()),
            _ => panic!(),
        };
        let mut free: Vec<String> = free_identifiers_in_function_body(Some("f"), params, body)
            .into_iter()
            .collect();
        free.sort();
        // `a` is a param, `f` is the function's own name, `b` and `c`
        // are unresolved → free.
        assert_eq!(free, vec!["b", "c"]);
    }

    #[test]
    fn function_body_does_not_leak_inner_function_name() {
        // The body has a nested `function inner() {}`; the inner
        // name is bound inside the body, so a reference to `inner`
        // from inside isn't free, but `inner` itself doesn't escape.
        let src = "function f() { function inner() { return 1; } return inner(); }";
        let prog = parse(src).unwrap();
        let (params, body) = match &prog.statements[0] {
            Stmt::FunctionDecl { params, body, .. } => (params.as_slice(), body.as_ref()),
            _ => panic!(),
        };
        let free = free_identifiers_in_function_body(Some("f"), params, body);
        assert!(free.is_empty(), "expected no free vars, got {:?}", free);
    }
}
