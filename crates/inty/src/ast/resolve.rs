//! Binding resolution: which declaration each identifier refers to, and
//! which bindings are *stable* — never written after their initialiser.
//!
//! This is the one authority on scoping. Inference keys its environment
//! by the [`BindingId`]s found here (`infer::env::Key`), never by name, so
//! two variables that share a name can't be confused, and whether a
//! program type-checks doesn't depend on what its variables are called.
//! Names this pass resolves to no declaration are globals (the standard
//! library, imports), which inference keys by name.
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
//!   every other occurrence of `x`: a second `var x = e` (or a `var` and a
//!   `function x`), one inside a loop, or one that an occurrence of `x`
//!   precedes (in the text, or in a hoisted function declaration, which
//!   can run first). `let` and `const` need none of this: reading them
//!   before their initialiser throws;
//! - `for (var x of …)`, and Python's `for x in …`: one function-scoped
//!   variable, written on every iteration;
//! - a Lua `function f() … end` statement where `f` is a visible local;
//! - a direct `eval(…)`, which may write anything in scope.
//!
//! Scoping follows ECMAScript: `var` and a function body's top-level
//! `function` declarations hoist to the function, `let`, `const` and
//! block-level `function`s are block scoped. The Python and Lua frontends
//! lower their scopes onto the same declarations, with two Lua rules of
//! its own: a `local` is in scope only after its declaration (`local x =
//! x` reads the outer `x`), and a `function f` statement assigns a visible
//! `f` rather than declaring one. A name that resolves to no declaration
//! — including an import, which the exporting module can reassign — is a
//! global and never stable.
//!
//! Occurrences are keyed by their span and name, and a key two bindings
//! share (synthesised code) resolves to neither.

use std::collections::HashMap;

use super::{
    CatchClause, ChainSegment, ExportDecl, Expr, ForInLhs, ForInit, Param, PropDef, SourceLanguage,
    Stmt, UnaryOp, VarDeclarator, VarKind,
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
    /// `function` declarations of this `var`-scoped name.
    fn_decls: u32,
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
                    && self.declarators + self.fn_decls <= 1
                    && (!self.has_init || (!self.init_in_loop && !self.read_before_init))
            }
        }
    }
}

/// The result of resolving a program.
#[derive(Clone, Debug, Default)]
pub struct Resolution {
    stable: Vec<bool>,
    global: Vec<bool>,
    names: Vec<String>,
    occurrences: HashMap<(usize, usize), Vec<BindingId>>,
}

impl Resolution {
    /// Resolve a program's statements. `hidden_writes` names variables
    /// the parser saw assigned in code it didn't keep (`"*"`: anything).
    pub fn of_program(stmts: &[Stmt], language: SourceLanguage) -> Resolution {
        let mut w = Walker {
            lua: language == SourceLanguage::Lua,
            ..Walker::default()
        };
        w.enter(ScopeKind::Function);
        w.collect_block(stmts);
        for s in stmts {
            w.collect_nested_vars(s);
        }
        for s in stmts {
            w.stmt(s);
        }
        let stable = w.bindings.iter().map(Binding::stable).collect();
        let global = w.bindings.iter().map(|b| b.kind == Kind::Global).collect();
        let names = w.bindings.into_iter().map(|b| b.name).collect();
        Resolution {
            stable,
            global,
            names,
            occurrences: w.occurrences,
        }
    }

    /// The program-declared binding the identifier `name` at `span` (a use
    /// or a declaration) refers to; `None` for a global.
    pub fn local_at(&self, span: Span, name: &str) -> Option<BindingId> {
        self.binding_at(span, name)
            .filter(|&id| !self.global[id as usize])
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

    /// Whether the identifier `name` at `span` refers to a binding that may
    /// be written after its initialiser. Unlike `!stable_at`, an
    /// identifier the resolution doesn't know is not written.
    pub fn written_at(&self, span: Span, name: &str) -> bool {
        self.binding_at(span, name)
            .is_some_and(|id| !self.stable[id as usize])
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
    /// Lua's scoping rules (see the module docs).
    lua: bool,
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
            fn_decls: 0,
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
    fn bind_var(&mut self, name: &str) -> BindingId {
        let idx = self
            .scopes
            .iter()
            .rposition(|s| s.kind == ScopeKind::Function)
            .unwrap_or(0);
        if let Some(&id) = self.scopes[idx].names.get(name) {
            return id;
        }
        let id = self.new_binding(name, Kind::Var);
        self.scopes[idx].names.insert(name.to_string(), id);
        id
    }

    /// Record that the identifier `name` at `span` is binding `id`.
    fn register(&mut self, span: Span, id: BindingId) {
        let ids = self.occurrences.entry((span.start, span.end)).or_default();
        if !ids.contains(&id) {
            ids.push(id);
        }
    }

    /// Declare a `function` statement's name: in a function body's top
    /// level it shares the `var` scope (and counts as one of its
    /// declarations); in a nested block it is block scoped.
    fn bind_function(&mut self, name: &str, span: Span) {
        let at_function_top = self
            .scopes
            .last()
            .is_some_and(|s| s.kind == ScopeKind::Function);
        let id = if at_function_top {
            let id = self.bind_var(name);
            self.bindings[id as usize].fn_decls += 1;
            id
        } else {
            self.bind_lex(name, Kind::Let)
        };
        self.register(span, id);
    }

    fn global_id(&mut self, name: &str) -> BindingId {
        if let Some(&id) = self.globals.get(name) {
            return id;
        }
        let id = self.new_binding(name, Kind::Global);
        self.globals.insert(name.to_string(), id);
        id
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
        self.register(span, id);
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
                // A Lua `function f` runs where it stands (see `stmt`).
                Stmt::FunctionDecl { .. } if self.lua => {}
                Stmt::FunctionDecl { name, span, .. }
                | Stmt::Export {
                    declaration: ExportDecl::Function { name, span, .. },
                    ..
                } => self.bind_function(name, *span),
                Stmt::Export {
                    declaration:
                        ExportDecl::Default {
                            value:
                                Expr::Function {
                                    name: Some(name),
                                    span,
                                    ..
                                },
                            ..
                        },
                    ..
                } => self.bind_function(name, *span),
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
                // Imports stay globals: the exporting module can
                // reassign them.
                _ => {}
            }
        }
    }

    fn collect_decls(&mut self, kind: VarKind, decls: &[VarDeclarator]) {
        for d in decls {
            match kind {
                // A Lua local is declared where it stands.
                VarKind::Let | VarKind::Const if self.lua => {}
                VarKind::Var => {
                    self.bind_var(&d.name);
                }
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
            Stmt::ForIn { left, body, .. } | Stmt::ForOf { left, body, .. } => {
                if let ForInLhs::VarDecl(name, _, _, VarKind::Var) = left {
                    self.bind_var(name);
                }
                self.collect_nested_vars(body)
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
                    vars_in(self, &c.consequent);
                }
            }
            Stmt::Labeled { body, .. } => self.collect_nested_vars(body),
            // A `var` directly under an `if`, a loop or a label.
            Stmt::Var {
                kind: VarKind::Var,
                declarations,
                ..
            } => {
                for d in declarations {
                    self.bind_var(&d.name);
                }
            }
            _ => {}
        }
    }

    // --- the walk ----------------------------------------------------------

    fn function(
        &mut self,
        name: Option<(&str, Span)>,
        params: &[Param],
        body: &Stmt,
        hoisted: bool,
    ) {
        self.enter_fn(ScopeKind::Function, hoisted);
        // A named function expression's own name, visible in its body.
        if let Some((n, span)) = name {
            let id = self.bind_lex(n, Kind::Const);
            self.register(span, id);
        }
        for p in params {
            let id = self.bind_lex(&p.name, Kind::Param);
            self.register(p.span, id);
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
            let id = match d.kind {
                VarKind::Let if self.lua => self.bind_lex(&d.name, Kind::Let),
                VarKind::Const if self.lua => self.bind_lex(&d.name, Kind::Const),
                _ => self.lookup(&d.name),
            };
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
            self.register(d.span, id);
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
                ExportDecl::Function { params, body, .. } => {
                    self.function(None, params, body, true);
                }
                // `export default function f` declares `f` in the module
                // (see `collect_block`).
                ExportDecl::Default {
                    value:
                        Expr::Function {
                            name: Some(_),
                            params,
                            body,
                            ..
                        },
                    ..
                } => self.function(None, params, body, true),
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
                    // `for (var x …)`: the one function-scoped `x`,
                    // written by every iteration.
                    ForInLhs::VarDecl(name, _, span, VarKind::Var) => self.write(name, *span),
                    // `let`/`const`: a fresh binding per iteration.
                    ForInLhs::VarDecl(name, _, span, kind) => {
                        let kind = if *kind == VarKind::Const {
                            Kind::Const
                        } else {
                            Kind::Let
                        };
                        let id = self.bind_lex(name, kind);
                        self.register(*span, id);
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
                    self.register(*span, id);
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
            // A Lua `function f` assigns a visible `f`, or else declares
            // one here; it runs in order, like any assignment.
            Stmt::FunctionDecl {
                params,
                body,
                name,
                span,
                ..
            } if self.lua => {
                let visible = self
                    .scopes
                    .iter()
                    .rev()
                    .find_map(|s| s.names.get(name.as_str()).copied());
                match visible {
                    Some(_) => self.write(name, *span),
                    None => {
                        let id = self.bind_lex(name, Kind::Let);
                        self.register(*span, id);
                    }
                }
                self.function(None, params, body, false);
            }
            Stmt::FunctionDecl { params, body, .. } => {
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
                name,
                params,
                body,
                span,
                ..
            } => self.function(name.as_deref().map(|n| (n, *span)), params, body, false),
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
                // A direct `eval` can assign anything in scope.
                if let Expr::Ident { name, .. } = &**callee {
                    if name == "eval" && self.lookup("eval") == self.global_id("eval") {
                        let in_scope: Vec<BindingId> = self
                            .scopes
                            .iter()
                            .flat_map(|s| s.names.values().copied())
                            .collect();
                        for id in in_scope {
                            self.bindings[id as usize].assigned = true;
                        }
                    }
                }
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
            // The parameter is keyed by the setter's span (it has none of
            // its own).
            PropDef::Setter {
                param, body, span, ..
            } => {
                let param = Param {
                    name: param.clone(),
                    span: *span,
                    optional: false,
                    default: None,
                    type_ast: None,
                };
                self.function(None, std::slice::from_ref(&param), body, false);
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
        let res = Resolution::of_program(&program.statements, program.language);
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
