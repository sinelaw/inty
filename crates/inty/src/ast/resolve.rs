//! Binding resolution: which declaration each identifier refers to, and
//! which bindings are *stable* — never written after their initialiser.
//!
//! Narrowing (`infer/narrow.rs`) refines only stable bindings. A fact
//! established about a stable binding's value holds for the rest of its
//! scope, on every path and in every closure, because the value cannot
//! change; that is the whole soundness argument, so this pass has to
//! find every write. What counts as one:
//!
//! - `x = e`, `x op= e` (logical ones included), `x++`, `x--`;
//! - `x` as a destructuring target or a `for (x of …)` / `for (x in …)`
//!   target;
//! - a `var x = e` other than a single declaration that runs once, before
//!   every other occurrence of `x`: a second `var x = e`, one inside a
//!   loop, or one that an occurrence of `x` precedes (in the text, or in
//!   a hoisted function declaration, which can run first). `let` and
//!   `const` need none of this: reading them before their initialiser
//!   throws.
//!
//! Scoping follows ECMAScript as `free_idents` does (`var` hoists to the
//! function, `let`/`const`/`function` are block scoped); the Python and
//! Lua frontends lower their scopes onto the same declarations. A name
//! that resolves to no declaration is a global and never stable.
//!
//! Occurrences are keyed by their span and name, and a key two bindings
//! share (synthesised code) resolves to neither.

use std::collections::HashMap;

use super::{
    CatchClause, ChainSegment, ExportDecl, Expr, ForInLhs, ForInit, ImportSpecifier, Param,
    PropDef, Stmt, UnaryOp, VarDeclarator, VarKind,
};
use crate::span::Span;

pub type BindingId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Var,
    Let,
    Const,
    Param,
    Global,
}

#[derive(Clone, Debug)]
struct Binding {
    name: String,
    kind: Kind,
    assigned: bool,
    declarators: u32,
    /// A `var` declarator with an initialiser has run through the walk.
    declared: bool,
    has_init: bool,
    init_in_loop: bool,
    /// An occurrence may run before the `var`'s initialiser.
    read_before_init: bool,
    /// How many functions enclose the declaration.
    level: usize,
}

impl Binding {
    fn stable(&self) -> bool {
        match self.kind {
            Kind::Const => true,
            Kind::Global => false,
            Kind::Let | Kind::Param => !self.assigned,
            Kind::Var => {
                !self.assigned
                    && self.declarators <= 1
                    && (!self.has_init || (!self.init_in_loop && !self.read_before_init))
            }
        }
    }
}

/// The result of resolving a program.
#[derive(Clone, Debug, Default)]
pub struct Resolution {
    stable: Vec<bool>,
    names: Vec<String>,
    occurrences: HashMap<(usize, usize), Vec<BindingId>>,
}

impl Resolution {
    /// Resolve a program's statements.
    pub fn of_program(stmts: &[Stmt]) -> Resolution {
        let mut w = Walker::default();
        w.enter(ScopeKind::Function);
        w.collect_block(stmts);
        for s in stmts {
            w.collect_nested_vars(s);
        }
        for s in stmts {
            w.stmt(s);
        }
        let stable = w.bindings.iter().map(Binding::stable).collect();
        let names = w.bindings.into_iter().map(|b| b.name).collect();
        Resolution {
            stable,
            names,
            occurrences: w.occurrences,
        }
    }

    /// The binding the identifier `name` at `span` refers to.
    pub fn binding_at(&self, span: Span, name: &str) -> Option<BindingId> {
        let ids = self.occurrences.get(&(span.start, span.end))?;
        let mut found = ids.iter().filter(|&&id| self.names[id as usize] == name);
        let id = *found.next()?;
        if found.any(|&other| other != id) {
            return None;
        }
        Some(id)
    }

    /// Whether the identifier `name` at `span` refers to a binding that
    /// is never written after its initialiser.
    pub fn stable_at(&self, span: Span, name: &str) -> bool {
        self.binding_at(span, name)
            .is_some_and(|id| self.stable[id as usize])
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    Function,
    Block,
}

struct Scope {
    kind: ScopeKind,
    names: HashMap<String, BindingId>,
}

#[derive(Default)]
struct Walker {
    bindings: Vec<Binding>,
    scopes: Vec<Scope>,
    globals: HashMap<String, BindingId>,
    occurrences: HashMap<(usize, usize), Vec<BindingId>>,
    /// Loop nesting inside the current function, one entry per function.
    loops: Vec<u32>,
    /// Per enclosing function: whether it is a function declaration,
    /// which hoisting can run before anything around it.
    hoisted: Vec<bool>,
}

impl Walker {
    fn enter(&mut self, kind: ScopeKind) {
        self.enter_fn(kind, false);
    }

    fn enter_fn(&mut self, kind: ScopeKind, hoisted: bool) {
        self.scopes.push(Scope {
            kind,
            names: HashMap::new(),
        });
        if kind == ScopeKind::Function {
            self.loops.push(0);
            self.hoisted.push(hoisted);
        }
    }

    fn leave(&mut self) {
        if let Some(s) = self.scopes.pop() {
            if s.kind == ScopeKind::Function {
                self.loops.pop();
                self.hoisted.pop();
            }
        }
    }

    fn in_loop(&self) -> bool {
        self.loops.last().is_some_and(|&n| n > 0)
    }

    fn new_binding(&mut self, name: &str, kind: Kind) -> BindingId {
        self.bindings.push(Binding {
            name: name.to_string(),
            kind,
            assigned: false,
            declarators: 0,
            declared: false,
            has_init: false,
            init_in_loop: false,
            read_before_init: false,
            level: self.hoisted.len(),
        });
        (self.bindings.len() - 1) as BindingId
    }

    /// Declare `name` in the innermost scope (a fresh binding each time).
    fn bind_lex(&mut self, name: &str, kind: Kind) -> BindingId {
        let id = self.new_binding(name, kind);
        if let Some(s) = self.scopes.last_mut() {
            s.names.insert(name.to_string(), id);
        }
        id
    }

    /// Declare a `var` in the innermost function scope; a second `var`
    /// of the same name there is the same binding.
    fn bind_var(&mut self, name: &str) {
        let idx = self
            .scopes
            .iter()
            .rposition(|s| s.kind == ScopeKind::Function)
            .unwrap_or(0);
        if self.scopes[idx].names.contains_key(name) {
            return;
        }
        let id = self.new_binding(name, Kind::Var);
        self.scopes[idx].names.insert(name.to_string(), id);
    }

    fn lookup(&mut self, name: &str) -> BindingId {
        for s in self.scopes.iter().rev() {
            if let Some(&id) = s.names.get(name) {
                return id;
            }
        }
        if let Some(&id) = self.globals.get(name) {
            return id;
        }
        let id = self.new_binding(name, Kind::Global);
        self.globals.insert(name.to_string(), id);
        id
    }

    fn occurrence(&mut self, name: &str, span: Span) -> BindingId {
        let id = self.lookup(name);
        let b = &self.bindings[id as usize];
        // In a function declaration nested inside the `var`'s function,
        // which can be called before the initialiser runs.
        let early = !b.declared
            || self
                .hoisted
                .get(b.level..)
                .is_some_and(|h| h.contains(&true));
        if b.kind == Kind::Var && early {
            self.bindings[id as usize].read_before_init = true;
        }
        let ids = self.occurrences.entry((span.start, span.end)).or_default();
        if !ids.contains(&id) {
            ids.push(id);
        }
        id
    }

    fn write(&mut self, name: &str, span: Span) {
        let id = self.occurrence(name, span);
        self.bindings[id as usize].assigned = true;
    }

    /// Record the names an assignment target writes.
    fn write_target(&mut self, target: &Expr) {
        match target {
            Expr::Ident { name, span } => self.write(name, *span),
            Expr::Array { elements, .. } => {
                for e in elements.iter().flatten() {
                    self.write_target(e);
                }
            }
            Expr::Tuple { elements, .. } => {
                for e in elements {
                    self.write_target(e);
                }
            }
            Expr::Object { properties, .. } => {
                for p in properties {
                    match p {
                        PropDef::Property { value, .. } => self.write_target(value),
                        PropDef::Spread { argument, .. } => self.write_target(argument),
                        _ => {}
                    }
                }
            }
            Expr::Spread { argument, .. }
            | Expr::RestArray {
                source: argument, ..
            } => self.write_target(argument),
            Expr::Assign { left, right, .. } => {
                // A default in a pattern: `[x = d] = …`.
                self.write_target(left);
                self.expr(right);
            }
            other => self.expr(other),
        }
    }

    // --- pre-collection (hoisting) ---------------------------------------

    fn collect_block(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            match stmt {
                Stmt::FunctionDecl { name, .. }
                | Stmt::Export {
                    declaration: ExportDecl::Function { name, .. },
                    ..
                } => {
                    self.bind_lex(name, Kind::Let);
                }
                Stmt::Var {
                    kind, declarations, ..
                }
                | Stmt::Export {
                    declaration:
                        ExportDecl::Var {
                            kind, declarations, ..
                        },
                    ..
                } => self.collect_decls(*kind, declarations),
                Stmt::Import { specifiers, .. } => {
                    for spec in specifiers {
                        let local = match spec {
                            ImportSpecifier::Named { local, .. }
                            | ImportSpecifier::Default { local, .. }
                            | ImportSpecifier::Namespace { local, .. } => local,
                        };
                        self.bind_lex(local, Kind::Const);
                    }
                }
                _ => {}
            }
        }
    }

    fn collect_decls(&mut self, kind: VarKind, decls: &[VarDeclarator]) {
        for d in decls {
            match kind {
                VarKind::Var => self.bind_var(&d.name),
                VarKind::Let => {
                    self.bind_lex(&d.name, Kind::Let);
                }
                VarKind::Const => {
                    self.bind_lex(&d.name, Kind::Const);
                }
            }
        }
    }

    /// Bind every `var` inside nested blocks of the current function.
    fn collect_nested_vars(&mut self, stmt: &Stmt) {
        let vars_in = |w: &mut Self, stmts: &[Stmt]| {
            for s in stmts {
                if let Stmt::Var {
                    kind: VarKind::Var,
                    declarations,
                    ..
                } = s
                {
                    for d in declarations {
                        w.bind_var(&d.name);
                    }
                }
                w.collect_nested_vars(s);
            }
        };
        match stmt {
            Stmt::Block { body, .. } => vars_in(self, body),
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
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => self.collect_nested_vars(body),
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
            Stmt::ForIn { body, .. } | Stmt::ForOf { body, .. } => self.collect_nested_vars(body),
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
                    vars_in(self, &c.consequent);
                }
            }
            Stmt::Labeled { body, .. } => self.collect_nested_vars(body),
            _ => {}
        }
    }

    // --- the walk ----------------------------------------------------------

    fn function(&mut self, name: Option<&str>, params: &[Param], body: &Stmt, hoisted: bool) {
        self.enter_fn(ScopeKind::Function, hoisted);
        if let Some(n) = name {
            self.bind_lex(n, Kind::Const);
        }
        for p in params {
            let id = self.bind_lex(&p.name, Kind::Param);
            let ids = self
                .occurrences
                .entry((p.span.start, p.span.end))
                .or_default();
            if !ids.contains(&id) {
                ids.push(id);
            }
        }
        match body {
            Stmt::Block { body, .. } => {
                self.collect_block(body);
                for s in body {
                    self.collect_nested_vars(s);
                }
            }
            other => self.collect_nested_vars(other),
        }
        match body {
            // The body block shares the function scope.
            Stmt::Block { body, .. } => {
                for s in body {
                    self.stmt(s);
                }
            }
            other => self.stmt(other),
        }
        self.leave();
    }

    fn declarators(&mut self, decls: &[VarDeclarator]) {
        for d in decls {
            if let Some(init) = &d.init {
                self.expr(init);
            }
            let id = self.lookup(&d.name);
            let in_loop = self.in_loop();
            let b = &mut self.bindings[id as usize];
            if b.kind == Kind::Var {
                b.declarators += 1;
                if d.init.is_some() {
                    b.has_init = true;
                    b.init_in_loop |= in_loop;
                }
                b.declared = true;
            }
            let ids = self
                .occurrences
                .entry((d.span.start, d.span.end))
                .or_default();
            if !ids.contains(&id) {
                ids.push(id);
            }
        }
    }

    fn block(&mut self, stmts: &[Stmt]) {
        self.enter(ScopeKind::Block);
        self.collect_block(stmts);
        for s in stmts {
            self.stmt(s);
        }
        self.leave();
    }

    fn looped(&mut self, f: impl FnOnce(&mut Self)) {
        if let Some(n) = self.loops.last_mut() {
            *n += 1;
        }
        f(self);
        if let Some(n) = self.loops.last_mut() {
            *n -= 1;
        }
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Block { body, .. } => self.block(body),
            Stmt::Empty { .. } | Stmt::Import { .. } => {}
            Stmt::Expr { expression, .. } => self.expr(expression),
            Stmt::Var { declarations, .. } => self.declarators(declarations),
            Stmt::Export { declaration, .. } => match declaration {
                ExportDecl::Var { declarations, .. } => self.declarators(declarations),
                ExportDecl::Function {
                    name, params, body, ..
                } => {
                    let _ = name;
                    self.function(None, params, body, true);
                }
                ExportDecl::Default { value, .. } => self.expr(value),
                ExportDecl::List { .. } | ExportDecl::From { .. } => {}
            },
            Stmt::If {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.expr(test);
                self.stmt(consequent);
                if let Some(a) = alternate {
                    self.stmt(a);
                }
            }
            Stmt::While { test, body, .. } => self.looped(|w| {
                w.expr(test);
                w.stmt(body);
            }),
            Stmt::DoWhile { body, test, .. } => self.looped(|w| {
                w.stmt(body);
                w.expr(test);
            }),
            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => {
                self.enter(ScopeKind::Block);
                match init {
                    Some(ForInit::VarDecl(decls)) => {
                        for d in decls {
                            if !matches!(d.kind, VarKind::Var) {
                                let kind = if matches!(d.kind, VarKind::Const) {
                                    Kind::Const
                                } else {
                                    Kind::Let
                                };
                                self.bind_lex(&d.name, kind);
                            }
                        }
                        self.declarators(decls);
                    }
                    Some(ForInit::Expr(e)) => self.expr(e),
                    None => {}
                }
                self.looped(|w| {
                    if let Some(t) = test {
                        w.expr(t);
                    }
                    w.stmt(body);
                    if let Some(u) = update {
                        w.expr(u);
                    }
                });
                self.leave();
            }
            Stmt::ForIn {
                left, right, body, ..
            }
            | Stmt::ForOf {
                left, right, body, ..
            } => {
                self.expr(right);
                self.enter(ScopeKind::Block);
                match left {
                    // Checked (and compiled) as a fresh binding per
                    // iteration, like `let`.
                    ForInLhs::VarDecl(name, _, span) => {
                        let id = self.bind_lex(name, Kind::Let);
                        self.occurrences
                            .entry((span.start, span.end))
                            .or_default()
                            .push(id);
                    }
                    ForInLhs::Expr(e) => self.write_target(e),
                }
                self.looped(|w| w.stmt(body));
                self.leave();
            }
            Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Return { argument, .. } => {
                if let Some(e) = argument {
                    self.expr(e);
                }
            }
            Stmt::Throw { argument, .. } => self.expr(argument),
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                self.stmt(block);
                if let Some(CatchClause { param, body, span }) = handler {
                    self.enter(ScopeKind::Block);
                    let id = self.bind_lex(param, Kind::Let);
                    self.occurrences
                        .entry((span.start, span.end))
                        .or_default()
                        .push(id);
                    self.stmt(body);
                    self.leave();
                }
                if let Some(f) = finalizer {
                    self.stmt(f);
                }
            }
            Stmt::Switch {
                discriminant,
                cases,
                ..
            } => {
                self.expr(discriminant);
                self.enter(ScopeKind::Block);
                for c in cases {
                    self.collect_block(&c.consequent);
                }
                for c in cases {
                    if let Some(t) = &c.test {
                        self.expr(t);
                    }
                    for s in &c.consequent {
                        self.stmt(s);
                    }
                }
                self.leave();
            }
            Stmt::Labeled { body, .. } => self.stmt(body),
            Stmt::FunctionDecl {
                params, body, name, ..
            } => {
                let _ = name;
                self.function(None, params, body, true);
            }
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
            Expr::Ident { name, span } => {
                self.occurrence(name, *span);
            }
            Expr::Array { elements, .. } => {
                for e in elements.iter().flatten() {
                    self.expr(e);
                }
            }
            Expr::Tuple { elements, .. } => {
                for e in elements {
                    self.expr(e);
                }
            }
            Expr::Object { properties, .. } => {
                for p in properties {
                    self.prop(p);
                }
            }
            Expr::Function {
                name, params, body, ..
            } => self.function(name.as_deref(), params, body, false),
            Expr::Member { object, .. } => self.expr(object),
            Expr::ComputedMember {
                object, property, ..
            } => {
                self.expr(object);
                self.expr(property);
            }
            Expr::Call {
                callee, arguments, ..
            }
            | Expr::New {
                callee, arguments, ..
            } => {
                self.expr(callee);
                for a in arguments {
                    self.expr(a);
                }
            }
            Expr::Unary { op, argument, .. } => {
                if matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec
                ) {
                    self.write_target(argument);
                } else {
                    self.expr(argument);
                }
            }
            Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Assign { left, right, .. } => {
                self.expr(right);
                self.write_target(left);
            }
            Expr::Conditional {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.expr(test);
                self.expr(consequent);
                self.expr(alternate);
            }
            Expr::OptionalChain { head, segments, .. } => {
                self.expr(head);
                for seg in segments {
                    match seg {
                        ChainSegment::Member { .. } => {}
                        ChainSegment::Computed { property, .. } => self.expr(property),
                        ChainSegment::Call { arguments, .. } => {
                            for a in arguments {
                                self.expr(a);
                            }
                        }
                    }
                }
            }
            Expr::Spread { argument, .. } => self.expr(argument),
            Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => self.expr(source),
            Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
                for e in expressions {
                    self.expr(e);
                }
            }
        }
    }

    fn prop(&mut self, prop: &PropDef) {
        match prop {
            PropDef::Property { value, .. } => self.expr(value),
            PropDef::Method { params, body, .. } => self.function(None, params, body, false),
            PropDef::Getter { body, .. } => self.function(None, &[], body, false),
            PropDef::Setter { param, body, .. } => {
                self.enter(ScopeKind::Function);
                self.bind_lex(param, Kind::Param);
                self.function(None, &[], body, false);
                self.leave();
            }
            PropDef::Spread { argument, .. } => self.expr(argument),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontends::javascript::parse;

    /// Whether the last occurrence of `name` in `src` is stable.
    fn stable(src: &str, name: &str) -> bool {
        let program = parse(src).expect("parse");
        let res = Resolution::of_program(&program.statements);
        let start = src.rfind(name).expect("name in source");
        res.stable_at(Span::new(start, start + name.len()), name)
    }

    #[test]
    fn const_and_unassigned_let_are_stable() {
        assert!(stable("const q = 1; use(q);", "q"));
        assert!(stable("let q = 1; use(q);", "q"));
        assert!(stable("function f(q) { return q; }", "q"));
    }

    #[test]
    fn writes_make_a_binding_unstable() {
        assert!(!stable("let q = 1; q = 2; use(q);", "q"));
        assert!(!stable("let q = 1; q++; use(q);", "q"));
        assert!(!stable("let q = 1; q ??= 2; use(q);", "q"));
        assert!(!stable("let q = 1; [q] = [2]; use(q);", "q"));
        assert!(!stable("let q = 1; for (q of [1]) {} use(q);", "q"));
        assert!(!stable("function f(q) { q = 1; return q; }", "q"));
        // From a closure.
        assert!(!stable(
            "let q = 1; const g = () => { q = 2; }; use(q);",
            "q"
        ));
    }

    #[test]
    fn var_initialisers_that_can_run_late_are_writes() {
        assert!(stable("function f() { var q = 1; return q; }", "q"));
        assert!(!stable(
            "function f() { var q = 1; var q = 2; return q; }",
            "q"
        ));
        assert!(!stable(
            "function f() { while (c) { var q = 1; } return q; }",
            "q"
        ));
        assert!(!stable(
            "function f() { use(q); var q = 1; return q; }",
            "q"
        ));
        assert!(!stable(
            "function f() { var q = 1; function g() { return q; } return q; }",
            "q"
        ));
    }

    #[test]
    fn shadowing_is_per_binding() {
        // The inner `q` is written; the outer one is not.
        let src = "const q = 1; function g() { let q = 0; q = 1; } use(q);";
        assert!(stable(src, "q"));
        let src = "let q = 1; function g() { let q = 0; q = 1; } use(q);";
        assert!(stable(src, "q"));
    }

    #[test]
    fn globals_are_never_stable() {
        assert!(!stable("use(q);", "q"));
    }
}
