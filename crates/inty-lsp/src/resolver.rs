//! Scope-aware name resolution for the LSP server.
//!
//! Walks the AST building three indexes:
//!
//! - `refs`: each identifier-use span -> the span of its binding site.
//! - `defs`: each binding-site span -> what kind of binding it is.
//! - `uses_of`: inverse of `refs`, used by rename / find-references.
//!
//! Plus a per-position scope chain so completions can list every
//! visible binding at the cursor.
//!
//! Scoping model (simplified for v1):
//!
//! - One scope per function (function declarations, function
//!   expressions, methods). Hoists `var` and `function` declarations
//!   from anywhere inside the function body — but not from nested
//!   functions.
//! - One scope per `catch (e)` clause, binding `e`.
//! - A top-level "module" scope that contains everything not inside a
//!   function.
//! - `const` bindings are recorded against the enclosing function or
//!   module scope; we don't model `let` block-scoping yet.
//! - Property names in object literals and member access are not
//!   resolved (they aren't bindings).

use std::collections::HashMap;

use inty::lexer::Span;
use inty::parser::ast::{
    Expr, ExportDecl, ForInLhs, ForInit, ImportSpecifier, Param, Program, PropDef, Stmt,
    VarDeclarator, VarKind,
};

/// What kind of thing a binding-site span refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefKind {
    Var,
    Let,
    Const,
    Param,
    Function,
    Catch,
    Import,
}

/// Information about one binding.
#[derive(Debug, Clone)]
pub struct Def {
    pub name: String,
    pub kind: DefKind,
    /// Span covering just the identifier text of this binding.
    pub name_span: Span,
}

/// Result of running the resolver over a program.
#[derive(Debug, Default)]
pub struct Resolution {
    /// Use-span -> def-span.
    refs: HashMap<Span, Span>,
    /// Def-span -> info about the binding.
    defs: HashMap<Span, Def>,
    /// Def-span -> all use-spans referring to it.
    uses_of: HashMap<Span, Vec<Span>>,
    /// One scope per function plus the top-level module scope.
    scopes: Vec<Scope>,
    /// `(span, scope_id)` pairs sorted by inclusion: when looking up
    /// the active scope at a byte offset, we pick the scope whose span
    /// contains the offset and is the smallest such match.
    scope_index: Vec<(Span, ScopeId)>,
}

type ScopeId = usize;

#[derive(Debug, Default)]
struct Scope {
    /// Parent scope for chained lookups. `None` for the module scope.
    parent: Option<ScopeId>,
    /// Span this scope is active over (for the cursor->scope query).
    span: Span,
    /// Bindings introduced in this scope. Ordered by name appearance.
    bindings: Vec<(String, Span)>,
    /// name -> binding span, for resolution.
    map: HashMap<String, Span>,
}

impl Resolution {
    /// Run the resolver over a parsed program.
    ///
    /// `text_len` is the byte length of the source text — used to make
    /// the module scope cover the whole file, including trailing
    /// whitespace and the gap between the last statement and EOF.
    /// Otherwise position queries past the last statement (e.g. on a
    /// blank line at the end of the file) wouldn't find any scope.
    pub fn build(program: &Program) -> Self {
        Self::build_with_len(program, program.span.end)
    }

    pub fn build_with_len(program: &Program, text_len: usize) -> Self {
        let mut r = Resolution::default();
        let module_span = Span::new(0, text_len.max(program.span.end));
        let module_scope = r.new_scope(None, module_span);
        // The module scope is also the enclosing "function scope" for
        // any `var` declared at the top level.
        hoist_scope(&program.statements, &mut r, module_scope);
        for stmt in &program.statements {
            r.visit_stmt(stmt, module_scope, module_scope);
        }
        r.finalize();
        r
    }

    /// Resolve an identifier-use span to its def. Returns `None` if the
    /// span isn't a recorded use (e.g. unresolved variable).
    pub fn def_of_use(&self, use_span: Span) -> Option<&Def> {
        let def_span = self.refs.get(&use_span)?;
        self.defs.get(def_span)
    }

    /// Look up a def by its span (i.e. clicking on the binding site
    /// itself).
    pub fn def_at(&self, span: Span) -> Option<&Def> {
        self.defs.get(&span)
    }

    /// Span (and Def) of every use of a binding, for rename.
    pub fn uses_of(&self, def_span: Span) -> &[Span] {
        self.uses_of.get(&def_span).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Iterate every binding whose name span lies inside `[start,
    /// end)`. Used by the inlay-hint feature to bound work to the
    /// editor's visible range.
    pub fn defs_in_range(
        &self,
        start: usize,
        end: usize,
    ) -> impl Iterator<Item = (Span, &Def)> + '_ {
        self.defs.iter().filter_map(move |(span, def)| {
            if span.start >= start && span.end <= end {
                Some((*span, def))
            } else {
                None
            }
        })
    }

    /// Find a binding (def *or* use) whose span contains `offset`.
    /// Returns the def-span and the actual span of the identifier hit.
    ///
    /// Picks the **smallest** matching span across both defs and refs.
    /// Some defs (notably named function expressions) are stored with a
    /// span covering the whole function, so without the smallest-span
    /// tie-breaker, hovering on an identifier inside the body would
    /// always return the enclosing function's def first.
    pub fn binding_at(&self, offset: usize) -> Option<(Span, Span)> {
        let mut best: Option<(Span, Span)> = None;
        let consider = |best: &mut Option<(Span, Span)>, def_span: Span, hit_span: Span| {
            let hit_len = hit_span.end.saturating_sub(hit_span.start);
            match *best {
                Some((_, b)) if b.end.saturating_sub(b.start) <= hit_len => {}
                _ => *best = Some((def_span, hit_span)),
            }
        };
        for (&def_span, def) in &self.defs {
            if span_contains(def.name_span, offset) {
                consider(&mut best, def_span, def.name_span);
            }
        }
        for (&use_span, &def_span) in &self.refs {
            if span_contains(use_span, offset) {
                consider(&mut best, def_span, use_span);
            }
        }
        best
    }

    /// Every binding visible at `offset`, walking the scope chain.
    /// Returns one entry per name; inner scopes shadow outer.
    pub fn visible_at(&self, offset: usize) -> Vec<&Def> {
        let scope_id = match self.scope_at(offset) {
            Some(id) => id,
            None => return Vec::new(),
        };
        let mut seen: HashMap<&str, &Def> = HashMap::new();
        let mut cur = Some(scope_id);
        while let Some(id) = cur {
            let scope = &self.scopes[id];
            for (name, span) in &scope.bindings {
                let entry = seen.entry(name.as_str());
                use std::collections::hash_map::Entry;
                if let Entry::Vacant(v) = entry {
                    if let Some(def) = self.defs.get(span) {
                        v.insert(def);
                    }
                }
            }
            cur = scope.parent;
        }
        seen.into_values().collect()
    }

    fn new_scope(&mut self, parent: Option<ScopeId>, span: Span) -> ScopeId {
        let id = self.scopes.len();
        self.scopes.push(Scope {
            parent,
            span,
            bindings: Vec::new(),
            map: HashMap::new(),
        });
        id
    }

    fn declare(&mut self, scope: ScopeId, name: &str, span: Span, kind: DefKind) {
        // First-write-wins keeps "the original binding site" stable for
        // duplicate declarations (`var x; var x;`).
        let s = &mut self.scopes[scope];
        if let std::collections::hash_map::Entry::Vacant(e) = s.map.entry(name.to_string()) {
            e.insert(span);
            s.bindings.push((name.to_string(), span));
            self.defs.insert(
                span,
                Def {
                    name: name.to_string(),
                    kind,
                    name_span: span,
                },
            );
            self.uses_of.entry(span).or_default();
        }
    }

    fn lookup(&self, scope: ScopeId, name: &str) -> Option<Span> {
        let mut cur = Some(scope);
        while let Some(id) = cur {
            if let Some(span) = self.scopes[id].map.get(name) {
                return Some(*span);
            }
            cur = self.scopes[id].parent;
        }
        None
    }

    fn record_ref(&mut self, use_span: Span, def_span: Span) {
        self.refs.insert(use_span, def_span);
        self.uses_of.entry(def_span).or_default().push(use_span);
    }

    fn finalize(&mut self) {
        // Build scope_index sorted by span length descending so that
        // when we scan for the smallest containing entry we can stop
        // early; in practice we just linear-scan and pick the smallest
        // contained span.
        let mut idx: Vec<(Span, ScopeId)> = self
            .scopes
            .iter()
            .enumerate()
            .map(|(i, s)| (s.span, i))
            .collect();
        idx.sort_by_key(|(s, _)| s.end.saturating_sub(s.start));
        self.scope_index = idx;
    }

    fn scope_at(&self, offset: usize) -> Option<ScopeId> {
        // Smallest scope whose span contains the offset (the index is
        // sorted shortest-first, so the first hit wins).
        for (span, id) in &self.scope_index {
            if span_contains(*span, offset) {
                return Some(*id);
            }
        }
        None
    }

    /// `fn_scope` is the enclosing function-or-module scope; it's where
    /// `var` and hoisted function declarations live. `scope` is the
    /// current (possibly block) scope where lookups start and where
    /// `let`/`const` bindings go.
    fn visit_stmt(&mut self, stmt: &Stmt, fn_scope: ScopeId, scope: ScopeId) {
        match stmt {
            Stmt::Block { body, span } => {
                // `let`/`const` declared inside this block are scoped
                // to the block, so we always open a new scope here.
                // It chains to the enclosing scope so lookups still
                // see outer bindings.
                let block_scope = self.new_scope(Some(scope), *span);
                for s in body {
                    self.visit_stmt(s, fn_scope, block_scope);
                }
            }
            Stmt::Expr { expression, .. } => self.visit_expr(expression, scope),
            Stmt::Var { kind, declarations, .. } => {
                self.visit_var_decls(*kind, declarations, fn_scope, scope);
            }
            Stmt::Import { specifiers, .. } => {
                for spec in specifiers {
                    let (name, span) = match spec {
                        ImportSpecifier::Named { local, span, .. } => (local.clone(), *span),
                        ImportSpecifier::Default { local, span } => (local.clone(), *span),
                        ImportSpecifier::Namespace { local, span } => (local.clone(), *span),
                    };
                    // Imports are top-level, always module-scope.
                    self.declare(fn_scope, &name, span, DefKind::Import);
                }
            }
            Stmt::Export { declaration, .. } => match declaration {
                ExportDecl::Var { kind, declarations, .. } => {
                    self.visit_var_decls(*kind, declarations, fn_scope, scope);
                }
                ExportDecl::Function {
                    name, params, body, span, ..
                } => {
                    let name_span = name_span_from_func(*span, name);
                    self.declare(fn_scope, name, name_span, DefKind::Function);
                    self.visit_function_body(*span, params, body, scope);
                }
                ExportDecl::Default { value, .. } => {
                    // `export default <expr>` — walk the expression to
                    // record any name uses inside it. The default
                    // export itself doesn't introduce a new binding in
                    // this file.
                    self.visit_expr(value, scope);
                }
                ExportDecl::List { specifiers, .. } => {
                    // `export { foo, bar as baz }` — each `local` is a
                    // use of an existing binding. Record refs so
                    // rename / find-references reach them.
                    for spec in specifiers {
                        // The spec span covers `local` (or `local as
                        // exported`). The local sits at span.start.
                        let local_span = Span::new(
                            spec.span.start,
                            spec.span.start + spec.local.len(),
                        );
                        if let Some(def_span) = self.lookup(scope, &spec.local) {
                            self.record_ref(local_span, def_span);
                        }
                    }
                }
                ExportDecl::From { .. } => {
                    // `export ... from "..."` — no local bindings or
                    // uses to record; the imported names live in the
                    // target module, not this one.
                }
            },
            Stmt::If {
                test, consequent, alternate, ..
            } => {
                self.visit_expr(test, scope);
                self.visit_stmt(consequent, fn_scope, scope);
                if let Some(a) = alternate {
                    self.visit_stmt(a, fn_scope, scope);
                }
            }
            Stmt::While { test, body, .. } | Stmt::DoWhile { test, body, .. } => {
                self.visit_expr(test, scope);
                self.visit_stmt(body, fn_scope, scope);
            }
            Stmt::For {
                init, test, update, body, span,
            } => {
                // A `for (let i = 0; …)` introduces `i` in a per-loop
                // scope. We always open a scope here so `let` lands in
                // the right place; for plain `var` it's harmless (the
                // declaration goes to fn_scope regardless).
                let for_scope = self.new_scope(Some(scope), *span);
                if let Some(init) = init {
                    match init {
                        ForInit::VarDecl(decls) => {
                            // Each declarator carries its own kind; a
                            // single for-init keyword applies to all
                            // declarators, so the first one is
                            // representative.
                            let kind = decls.first().map(|d| d.kind).unwrap_or(VarKind::Var);
                            self.visit_var_decls(kind, decls, fn_scope, for_scope);
                        }
                        ForInit::Expr(e) => self.visit_expr(e, for_scope),
                    }
                }
                if let Some(t) = test {
                    self.visit_expr(t, for_scope);
                }
                if let Some(u) = update {
                    self.visit_expr(u, for_scope);
                }
                self.visit_stmt(body, fn_scope, for_scope);
            }
            Stmt::ForIn { left, right, body, span } | Stmt::ForOf { left, right, body, span } => {
                let for_scope = self.new_scope(Some(scope), *span);
                match left {
                    ForInLhs::VarDecl(name, _, lhs_span) => {
                        // `for (var x in …)` hoists; `for (let x in …)`
                        // wouldn't, but the parser flattens both to
                        // VarDecl. Treat as `var` for compatibility.
                        self.declare(fn_scope, name, *lhs_span, DefKind::Var);
                    }
                    ForInLhs::Expr(e) => self.visit_expr(e, for_scope),
                }
                self.visit_expr(right, for_scope);
                self.visit_stmt(body, fn_scope, for_scope);
            }
            Stmt::Return { argument, .. } => {
                if let Some(a) = argument {
                    self.visit_expr(a, scope);
                }
            }
            Stmt::Throw { argument, .. } => self.visit_expr(argument, scope),
            Stmt::Try { block, handler, finalizer, .. } => {
                self.visit_stmt(block, fn_scope, scope);
                if let Some(h) = handler {
                    let catch_scope = self.new_scope(Some(scope), h.span);
                    self.declare(catch_scope, &h.param, h.span, DefKind::Catch);
                    self.visit_stmt(&h.body, fn_scope, catch_scope);
                }
                if let Some(f) = finalizer {
                    self.visit_stmt(f, fn_scope, scope);
                }
            }
            Stmt::Switch { discriminant, cases, .. } => {
                self.visit_expr(discriminant, scope);
                for c in cases {
                    if let Some(t) = &c.test {
                        self.visit_expr(t, scope);
                    }
                    for s in &c.consequent {
                        self.visit_stmt(s, fn_scope, scope);
                    }
                }
            }
            Stmt::Labeled { body, .. } => self.visit_stmt(body, fn_scope, scope),
            Stmt::FunctionDecl {
                name: _, params, body, span, ..
            } => {
                // The decl was already hoisted into `fn_scope`; we
                // still walk the body to record nested decls/uses.
                self.visit_function_body(*span, params, body, scope);
            }
            Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
        }
    }

    fn visit_var_decls(
        &mut self,
        kind: VarKind,
        decls: &[VarDeclarator],
        fn_scope: ScopeId,
        scope: ScopeId,
    ) {
        let def_kind = match kind {
            VarKind::Var => DefKind::Var,
            VarKind::Let => DefKind::Let,
            VarKind::Const => DefKind::Const,
        };
        // `var` lands in the enclosing function scope (that's where
        // hoist_scope already pre-bound it). `let`/`const` land in the
        // current (block) scope.
        let target = match kind {
            VarKind::Var => fn_scope,
            VarKind::Let | VarKind::Const => scope,
        };
        for d in decls {
            let name_span = name_span_from_decl(d);
            self.declare(target, &d.name, name_span, def_kind);
            if let Some(init) = &d.init {
                self.visit_expr(init, scope);
            }
        }
    }

    fn visit_expr(&mut self, expr: &Expr, scope: ScopeId) {
        match expr {
            Expr::Ident { name, span } => {
                if let Some(def_span) = self.lookup(scope, name) {
                    self.record_ref(*span, def_span);
                }
            }
            Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
            Expr::Array { elements, .. } => {
                for e in elements.iter().flatten() {
                    self.visit_expr(e, scope);
                }
            }
            Expr::Object { properties, .. } => {
                for p in properties {
                    match p {
                        PropDef::Property { value, .. } => self.visit_expr(value, scope),
                        PropDef::Method { params, body, span, .. } => {
                            self.visit_function_body(*span, params, body, scope);
                        }
                        PropDef::Getter { body, span, .. } => {
                            self.visit_function_body(*span, &[], body, scope);
                        }
                        PropDef::Setter { param, body, span, .. } => {
                            // Setter has a single string param; we don't
                            // get a precise span for it from the parser
                            // (the AST stores just `param: String`), so
                            // anchor at the start of the setter.
                            let params =
                                vec![Param::new(param.clone(), Span::new(span.start, span.start))];
                            self.visit_function_body(*span, &params, body, scope);
                        }
                        PropDef::Spread { argument, .. } => self.visit_expr(argument, scope),
                    }
                }
            }
            Expr::Function {
                name, params, body, span, ..
            } => {
                // Function expression: optional name binds *inside* the
                // function only. Declare it in the function scope after
                // we open it.
                self.visit_function_body_named(*span, name.as_deref(), params, body, scope);
            }
            Expr::Member { object, .. } => self.visit_expr(object, scope),
            Expr::ComputedMember { object, property, .. } => {
                self.visit_expr(object, scope);
                self.visit_expr(property, scope);
            }
            Expr::Call { callee, arguments, .. } | Expr::New { callee, arguments, .. } => {
                self.visit_expr(callee, scope);
                for a in arguments {
                    self.visit_expr(a, scope);
                }
            }
            Expr::Unary { argument, .. } => self.visit_expr(argument, scope),
            Expr::Binary { left, right, .. } => {
                self.visit_expr(left, scope);
                self.visit_expr(right, scope);
            }
            Expr::Assign { left, right, .. } => {
                self.visit_expr(left, scope);
                self.visit_expr(right, scope);
            }
            Expr::Conditional {
                test, consequent, alternate, ..
            } => {
                self.visit_expr(test, scope);
                self.visit_expr(consequent, scope);
                self.visit_expr(alternate, scope);
            }
            Expr::NullishCoalesce { left, right, .. } => {
                self.visit_expr(left, scope);
                self.visit_expr(right, scope);
            }
            Expr::Spread { argument, .. } => self.visit_expr(argument, scope),
            Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => {
                self.visit_expr(source, scope)
            }
            Expr::OptionalChain { head, segments, .. } => {
                use inty::parser::ast::ChainSegment;
                self.visit_expr(head, scope);
                for seg in segments {
                    match seg {
                        ChainSegment::Member { .. } => {}
                        ChainSegment::Computed { property, .. } => {
                            self.visit_expr(property, scope);
                        }
                        ChainSegment::Call { arguments, .. } => {
                            for a in arguments {
                                self.visit_expr(a, scope);
                            }
                        }
                    }
                }
            }
            Expr::Sequence { expressions, .. } => {
                for e in expressions {
                    self.visit_expr(e, scope);
                }
            }
            Expr::TemplateLiteral { expressions, .. } => {
                for e in expressions {
                    self.visit_expr(e, scope);
                }
            }
        }
    }

    fn visit_function_body(
        &mut self,
        span: Span,
        params: &[Param],
        body: &Stmt,
        parent: ScopeId,
    ) {
        self.visit_function_body_named(span, None, params, body, parent);
    }

    fn visit_function_body_named(
        &mut self,
        span: Span,
        self_name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        parent: ScopeId,
    ) {
        let func_scope = self.new_scope(Some(parent), span);
        if let Some(name) = self_name {
            // Named function expression: bind `name` only inside the
            // body. Use the function's whole span — there's no separate
            // span for the name on `Expr::Function`.
            self.declare(func_scope, name, span, DefKind::Function);
        }
        // Each param now has a real source span (the parser tracks
        // them), so go-to-def lands on the parameter name in the
        // header — matching what users expect.
        for p in params {
            self.declare(func_scope, &p.name, p.span, DefKind::Param);
        }
        // Hoist `var` and `function` declarations from anywhere in the
        // body that isn't itself inside a nested function.
        if let Stmt::Block { body: stmts, .. } = body {
            hoist_scope(stmts, self, func_scope);
        }
        // The function's body is *the* function scope for both
        // hoisting (var) and lookup (let/const see params). To avoid
        // visit_stmt opening a fresh block scope when it sees the
        // outer Block, we walk the body's statements directly.
        if let Stmt::Block { body: stmts, .. } = body {
            for s in stmts {
                self.visit_stmt(s, func_scope, func_scope);
            }
        } else {
            self.visit_stmt(body, func_scope, func_scope);
        }
    }
}

/// Pre-walk the body of a function (or the module) collecting all `var`
/// and `function` declarations and pre-binding them in `scope`. Skips
/// nested functions so their hoisting belongs to their own scope.
fn hoist_scope(stmts: &[Stmt], r: &mut Resolution, scope: ScopeId) {
    for s in stmts {
        hoist_stmt(s, r, scope);
    }
}

fn hoist_stmt(stmt: &Stmt, r: &mut Resolution, scope: ScopeId) {
    match stmt {
        Stmt::Var { kind: VarKind::Var, declarations, .. } => {
            // Only `var` hoists to the enclosing function scope.
            // `let`/`const` are block-scoped and bind in visit_stmt.
            for d in declarations {
                let name_span = name_span_from_decl(d);
                r.declare(scope, &d.name, name_span, DefKind::Var);
            }
        }
        // Skip Let/Const here — visit_stmt will handle them in their
        // proper block scope.
        Stmt::Var { .. } => {}
        Stmt::FunctionDecl { name, span, .. } => {
            let name_span = name_span_from_func(*span, name);
            r.declare(scope, name, name_span, DefKind::Function);
        }
        Stmt::Export { declaration, .. } => match declaration {
            ExportDecl::Var { kind: VarKind::Var, declarations, .. } => {
                for d in declarations {
                    let name_span = name_span_from_decl(d);
                    r.declare(scope, &d.name, name_span, DefKind::Var);
                }
            }
            ExportDecl::Var { .. } => {} // Let/Const not hoisted.
            ExportDecl::Function { name, span, .. } => {
                let name_span = name_span_from_func(*span, name);
                r.declare(scope, name, name_span, DefKind::Function);
            }
            // Default / List / From don't introduce new local bindings,
            // so they have nothing to hoist.
            ExportDecl::Default { .. }
            | ExportDecl::List { .. }
            | ExportDecl::From { .. } => {}
        },
        Stmt::Block { body, .. } => hoist_scope(body, r, scope),
        Stmt::If { consequent, alternate, .. } => {
            hoist_stmt(consequent, r, scope);
            if let Some(a) = alternate {
                hoist_stmt(a, r, scope);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => hoist_stmt(body, r, scope),
        Stmt::For { init, body, .. } => {
            if let Some(ForInit::VarDecl(decls)) = init {
                for d in decls {
                    if d.kind == VarKind::Var {
                        let name_span = name_span_from_decl(d);
                        r.declare(scope, &d.name, name_span, DefKind::Var);
                    }
                }
            }
            hoist_stmt(body, r, scope);
        }
        Stmt::ForIn { left, body, .. } | Stmt::ForOf { left, body, .. } => {
            if let ForInLhs::VarDecl(name, _, span) = left {
                r.declare(scope, name, *span, DefKind::Var);
            }
            hoist_stmt(body, r, scope);
        }
        Stmt::Try { block, handler, finalizer, .. } => {
            hoist_stmt(block, r, scope);
            if let Some(h) = handler {
                hoist_stmt(&h.body, r, scope);
            }
            if let Some(f) = finalizer {
                hoist_stmt(f, r, scope);
            }
        }
        Stmt::Switch { cases, .. } => {
            for c in cases {
                for s in &c.consequent {
                    hoist_stmt(s, r, scope);
                }
            }
        }
        Stmt::Labeled { body, .. } => hoist_stmt(body, r, scope),
        // Don't recurse into nested function bodies.
        _ => {}
    }
}

/// VarDeclarator.span covers the entire `name = init` so we trim it to
/// just the name's text. We use byte length of `name` from the start —
/// the lexer is tight, so this matches in practice.
fn name_span_from_decl(d: &VarDeclarator) -> Span {
    let len = d.name.len();
    Span::new(d.span.start, d.span.start.saturating_add(len))
}

/// FunctionDecl.span covers `function name(...) { ... }`. The keyword
/// `function ` is 9 ASCII bytes, so the name starts at span.start + 9.
fn name_span_from_func(decl: Span, name: &str) -> Span {
    let start = decl.start.saturating_add("function ".len());
    Span::new(start, start.saturating_add(name.len()))
}

fn span_contains(span: Span, offset: usize) -> bool {
    span.start <= offset && offset <= span.end
}

#[cfg(test)]
mod tests {
    use super::*;
    use inty::parser::parse;

    fn build(src: &str) -> Resolution {
        let program = parse(src).expect("parse");
        Resolution::build(&program)
    }

    #[test]
    fn resolves_top_level_var() {
        let src = "var x = 1; x;";
        let r = build(src);
        let use_span = src.rfind("x").map(|i| Span::new(i, i + 1)).unwrap();
        let def = r.def_of_use(use_span).expect("def");
        assert_eq!(def.name, "x");
        assert_eq!(def.kind, DefKind::Var);
    }

    #[test]
    fn function_decl_hoists() {
        let src = "f();\nfunction f() {}\n";
        let r = build(src);
        let use_span = Span::new(0, 1);
        let def = r.def_of_use(use_span).expect("hoisted def");
        assert_eq!(def.name, "f");
        assert_eq!(def.kind, DefKind::Function);
    }

    #[test]
    fn uses_collected_for_rename() {
        let src = "var x = 1; x; x + 1;";
        let r = build(src);
        let def_span = name_span_from_decl(&VarDeclarator {
            name: "x".to_string(),
            init: None,
            type_annotation: None,
            kind: VarKind::Var,
            span: Span::new(4, 9),
        });
        let uses = r.uses_of(def_span);
        assert_eq!(uses.len(), 2);
    }

    #[test]
    fn visible_at_top_level() {
        let src = "var x = 1; var y = 2;";
        let r = build(src);
        let mut names: Vec<_> = r.visible_at(0).iter().map(|d| d.name.clone()).collect();
        names.sort();
        assert_eq!(names, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn let_is_block_scoped() {
        // `let y` inside the block should NOT be visible after the
        // block ends.
        let src = "if (true) { let y = 1; }\ny;\n";
        let r = build(src);
        // Cursor on the trailing `y;` reference (line 1, col 0):
        let trailing_y = src.rfind("y;").unwrap();
        // Reference at offset `trailing_y` should not resolve.
        assert!(
            r.def_of_use(Span::new(trailing_y, trailing_y + 1)).is_none(),
            "let y should not leak out of its block"
        );
    }

    #[test]
    fn var_inside_block_hoists_to_function() {
        // `var x` inside an `if` block IS visible after the block
        // (function-scoped, hoisted).
        let src = "function f() {\n  if (true) { var x = 1; }\n  x;\n}\n";
        let r = build(src);
        // The trailing `x;` use on line 2 should resolve.
        let trailing_x = src.rfind("x;").unwrap();
        let def = r
            .def_of_use(Span::new(trailing_x, trailing_x + 1))
            .expect("var x is hoisted to f's scope");
        assert_eq!(def.name, "x");
        assert_eq!(def.kind, DefKind::Var);
    }

    #[test]
    fn const_is_block_scoped() {
        let src = "if (true) { const k = 1; }\nk;\n";
        let r = build(src);
        let trailing_k = src.rfind("k;").unwrap();
        assert!(
            r.def_of_use(Span::new(trailing_k, trailing_k + 1)).is_none(),
            "const k should not leak out of its block"
        );
    }

    #[test]
    fn param_span_lands_on_name() {
        let src = "function add(a, b) { return a + b; }\n";
        let r = build(src);
        // The use of `a` inside the body is at index 28.
        let use_a = src.find("a +").unwrap();
        let def = r
            .def_of_use(Span::new(use_a, use_a + 1))
            .expect("body `a` should resolve to a param");
        assert_eq!(def.kind, DefKind::Param);
        // Def span should land on the param `a` in the header (index 13).
        let header_a = src.find("(a").unwrap() + 1;
        assert_eq!(def.name_span, Span::new(header_a, header_a + 1));
    }

    #[test]
    fn for_let_def_lands_on_the_name() {
        // The for-let declarator's name span must cover just `i`, not
        // the `let` keyword. Otherwise hover / go-to-def on the binding
        // site itself misses (the def's name_span doesn't contain the
        // cursor on `i`).
        let src = "for (let i = 0; i < 10; i = i + 1) { i; }\n";
        let r = build(src);
        let i_off = src.find("let i").unwrap() + 4; // index of `i`
        let def = r
            .def_at(Span::new(i_off, i_off + 1))
            .expect("for-let `i` should be a def whose name span lands on `i`");
        assert_eq!(def.name, "i");
        assert_eq!(def.kind, DefKind::Let);
    }

    #[test]
    fn for_of_let_def_lands_on_the_name() {
        // Same check for `for (let x of ...)`.
        let src = "for (let x of arr) { x; }\n";
        let r = build(src);
        let x_off = src.find("let x").unwrap() + 4;
        let def = r
            .def_at(Span::new(x_off, x_off + 1))
            .expect("for-of `x` should be a def whose span lands on `x`");
        assert_eq!(def.name, "x");
    }

    #[test]
    fn export_let_is_block_scoped() {
        // `export let y = 1;` at module top level: the binding lands in
        // module scope (there's no enclosing block), but the resolver
        // must record it as `Let`, not `Var`. Previously the parser
        // collapsed `export let` into `VarKind::Var`, causing the
        // resolver to hoist it like a `var`.
        let src = "export let y = 1;\n";
        let r = build(src);
        let y_off = src.find("y").unwrap();
        let def = r.def_at(Span::new(y_off, y_off + 1)).expect("def");
        assert_eq!(def.name, "y");
        assert_eq!(def.kind, DefKind::Let);
    }

    #[test]
    fn for_let_is_per_iteration_scoped() {
        // `for (let i = 0; ...) { i; } i;` — the trailing `i;` should
        // not resolve, because `let i` is scoped to the for-loop.
        // Previously the parser stored `i` as `Var` and the resolver
        // hoisted it.
        let src = "for (let i = 0; i < 10; i = i + 1) { i; }\ni;\n";
        let r = build(src);
        let trailing_i = src.rfind("i;").unwrap();
        assert!(
            r.def_of_use(Span::new(trailing_i, trailing_i + 1)).is_none(),
            "let i should not leak out of the for-loop"
        );
        // Sanity check: the `i` inside the body still resolves.
        let body_i_off = src.find("{ i").unwrap() + 2;
        let body_def = r
            .def_of_use(Span::new(body_i_off, body_i_off + 1))
            .expect("body i should resolve");
        assert_eq!(body_def.kind, DefKind::Let);
    }

    #[test]
    fn inner_let_shadows_outer() {
        let src = "var x = 1;\n{ let x = 2; x; }\n";
        let r = build(src);
        // The use of `x` inside the block should resolve to the inner
        // `let x`, not the outer `var x`.
        let inner_use = src.rfind("x;").unwrap();
        let def = r
            .def_of_use(Span::new(inner_use, inner_use + 1))
            .expect("x should resolve to the inner let");
        assert_eq!(def.kind, DefKind::Let);
    }
}
