//! Use-before-initialisation ("temporal dead zone") analysis.
//!
//! Every `var` / `let` / `const` name of a scope is visible to the whole
//! scope for *typing* (so hoisted functions can refer to bindings declared
//! later — the IIFE-library pattern), but at runtime reading a `let` /
//! `const` before its declaration has run throws a `ReferenceError`, and a
//! `var` read before its assignment is `undefined`, not a value of its
//! declared type. Neither is visible to type inference, so this pass checks
//! it separately.
//!
//! It is an abstract interpretation of *execution order*: statements are
//! walked in the order they run, tracking which bindings have been
//! initialised.
//!
//! * A direct call of a known function — a `function` declaration, a
//!   function-valued `let` / `const` / `var`, or an immediately-invoked
//!   function expression — runs its body at that point, in the scope chain
//!   where the function was defined, so `f(); const x = 1; function f() {
//!   return x; }` is caught.
//! * A function that is only *referenced* (stored, returned, passed as a
//!   callback) is assumed to run later; its body is checked at the end,
//!   once everything that was going to be initialised has been. That keeps
//!   the pass free of false positives for event handlers, exported APIs and
//!   methods, at the cost of missing a callback invoked synchronously
//!   before the binding it reads (`[1].forEach(g); const x = 1;` with `g`
//!   reading `x`).
//!
//! Recursion is cut, and each function body is re-walked only when some
//! binding was initialised since its last walk, so the pass is linear in
//! practice.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::{
    ChainSegment, ExportDecl, Expr, ForInLhs, ForInit, ImportSpecifier, Param, PropDef, Stmt,
    VarDeclarator, VarKind,
};
use crate::span::Span;

/// A read (or write) of a binding before its initialisation has run.
#[derive(Debug, Clone, PartialEq)]
pub struct TdzViolation {
    pub name: String,
    pub span: Span,
    pub kind: VarKind,
}

impl TdzViolation {
    pub fn message(&self) -> String {
        match self.kind {
            VarKind::Var => format!(
                "'{}' is read before it is assigned: it is still `undefined` here, not a value of its declared type",
                self.name
            ),
            VarKind::Let | VarKind::Const => format!(
                "'{}' is used before its declaration has run (temporal dead zone): this throws a ReferenceError",
                self.name
            ),
        }
    }
}

/// Check a whole program (or module) body.
pub fn check_program(stmts: &[Stmt]) -> Vec<TdzViolation> {
    let mut w = Walker::default();
    w.frames.push(Frame {
        bindings: HashMap::new(),
        is_function: true,
    });
    w.walk_stmts(stmts, &[0], false);
    // Functions that were only referenced run "later": check their bodies
    // now that the program has run to completion.
    while let Some(f) = w.deferred.pop() {
        if !w.ever.contains(&f.id) {
            w.call(&f);
        }
    }
    w.violations
}

#[derive(Clone)]
struct FuncRef<'a> {
    /// Identity of the function literal (address of its body).
    id: usize,
    name: Option<&'a str>,
    params: &'a [Param],
    body: &'a Stmt,
    /// Scope chain (frame indices) where the function was defined.
    def_chain: Rc<Vec<usize>>,
}

#[derive(Clone, Copy, PartialEq)]
enum State {
    /// Parameters, function declarations, imports, catch parameters.
    Always,
    Uninit(VarKind),
    Init,
}

struct Binding<'a> {
    state: State,
    func: Option<FuncRef<'a>>,
}

struct Frame<'a> {
    bindings: HashMap<String, Binding<'a>>,
    /// `var` declarations bind in the nearest function frame.
    is_function: bool,
}

#[derive(Default)]
struct Walker<'a> {
    frames: Vec<Frame<'a>>,
    violations: Vec<TdzViolation>,
    seen: HashSet<(usize, usize)>,
    /// Bumped whenever a binding becomes initialised.
    epoch: u64,
    /// Epoch at which each function body was last walked.
    walked_at: HashMap<usize, u64>,
    /// Functions whose body is being walked (recursion guard).
    active: HashSet<usize>,
    /// Functions walked at least once.
    ever: HashSet<usize>,
    /// Functions referenced but not (yet) called.
    deferred: Vec<FuncRef<'a>>,
}

fn func_id(body: &Stmt) -> usize {
    body as *const Stmt as usize
}

fn function_init(d: &VarDeclarator) -> Option<(Option<&str>, &[Param], &Stmt)> {
    match &d.init {
        Some(Expr::Function {
            name, params, body, ..
        }) => Some((name.as_deref(), params.as_slice(), body.as_ref())),
        _ => None,
    }
}

impl<'a> Walker<'a> {
    // ---- scopes -------------------------------------------------------

    fn lookup(&self, chain: &[usize], name: &str) -> Option<usize> {
        chain
            .iter()
            .rev()
            .copied()
            .find(|&f| self.frames[f].bindings.contains_key(name))
    }

    fn bind(&mut self, frame: usize, name: &str, state: State, func: Option<FuncRef<'a>>) {
        self.frames[frame]
            .bindings
            .insert(name.to_string(), Binding { state, func });
    }

    fn function_frame(&self, chain: &[usize]) -> usize {
        chain
            .iter()
            .rev()
            .copied()
            .find(|&f| self.frames[f].is_function)
            .unwrap_or(chain[0])
    }

    fn new_frame(&mut self, is_function: bool) -> usize {
        self.frames.push(Frame {
            bindings: HashMap::new(),
            is_function,
        });
        self.frames.len() - 1
    }

    fn func_ref(
        &self,
        name: Option<&'a str>,
        params: &'a [Param],
        body: &'a Stmt,
        chain: &[usize],
    ) -> FuncRef<'a> {
        FuncRef {
            id: func_id(body),
            name,
            params,
            body,
            def_chain: Rc::new(chain.to_vec()),
        }
    }

    fn violation(&mut self, name: &str, span: Span, kind: VarKind) {
        if self.seen.insert((span.start, span.end)) {
            self.violations.push(TdzViolation {
                name: name.to_string(),
                span,
                kind,
            });
        }
    }

    /// A read of `name`; returns the function it is bound to, if known.
    fn read(&mut self, chain: &[usize], name: &str, span: Span) -> Option<FuncRef<'a>> {
        let frame = self.lookup(chain, name)?;
        let b = &self.frames[frame].bindings[name];
        match b.state {
            State::Uninit(kind) => {
                self.violation(name, span, kind);
                None
            }
            _ => b.func.clone(),
        }
    }

    fn initialise(&mut self, chain: &[usize], name: &str) {
        if let Some(frame) = self.lookup(chain, name) {
            let b = self.frames[frame].bindings.get_mut(name).expect("bound");
            if matches!(b.state, State::Uninit(_)) {
                b.state = State::Init;
                self.epoch += 1;
            }
        }
    }

    // ---- functions ----------------------------------------------------

    /// Run a function's body now.
    fn call(&mut self, f: &FuncRef<'a>) {
        if self.active.contains(&f.id) || self.walked_at.get(&f.id) == Some(&self.epoch) {
            return;
        }
        self.walked_at.insert(f.id, self.epoch);
        self.ever.insert(f.id);
        self.active.insert(f.id);
        let frame = self.new_frame(true);
        let mut chain = (*f.def_chain).clone();
        chain.push(frame);
        if let Some(name) = f.name {
            self.bind(frame, name, State::Always, Some(f.clone()));
        }
        for p in f.params {
            self.bind(frame, &p.name, State::Always, None);
        }
        for p in f.params {
            if let Some(d) = &p.default {
                self.walk_expr(d, &chain);
            }
        }
        match f.body {
            Stmt::Block { body, .. } => self.walk_stmts(body, &chain, false),
            other => self.walk_stmts(std::slice::from_ref(other), &chain, false),
        }
        self.active.remove(&f.id);
    }

    fn defer(
        &mut self,
        name: Option<&'a str>,
        params: &'a [Param],
        body: &'a Stmt,
        chain: &[usize],
    ) {
        let f = self.func_ref(name, params, body, chain);
        self.deferred.push(f);
    }

    // ---- statements ---------------------------------------------------

    fn walk_stmts(&mut self, stmts: &'a [Stmt], chain: &[usize], new_frame: bool) {
        let mut chain = chain.to_vec();
        if new_frame {
            let f = self.new_frame(false);
            chain.push(f);
        }
        let here = *chain.last().expect("chain");
        for stmt in stmts {
            self.hoist(stmt, &chain, here);
        }
        for stmt in stmts {
            self.walk_stmt(stmt, &chain);
        }
    }

    /// Bind the names a statement declares in its scope, before any of the
    /// scope's statements run.
    fn hoist(&mut self, stmt: &'a Stmt, chain: &[usize], here: usize) {
        match stmt {
            Stmt::FunctionDecl {
                name, params, body, ..
            }
            | Stmt::Export {
                declaration:
                    ExportDecl::Function {
                        name, params, body, ..
                    },
                ..
            } => {
                let f = self.func_ref(Some(name), params, body, chain);
                self.bind(here, name, State::Always, Some(f));
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
            } => self.hoist_decls(*kind, declarations, chain, here),
            Stmt::Import { specifiers, .. } => {
                for s in specifiers {
                    let local = match s {
                        ImportSpecifier::Named { local, .. }
                        | ImportSpecifier::Default { local, .. }
                        | ImportSpecifier::Namespace { local, .. } => local,
                    };
                    self.bind(here, local, State::Always, None);
                }
            }
            _ => {}
        }
    }

    fn hoist_decls(
        &mut self,
        kind: VarKind,
        decls: &'a [VarDeclarator],
        chain: &[usize],
        here: usize,
    ) {
        for d in decls {
            let func = function_init(d)
                .map(|(name, params, body)| self.func_ref(name, params, body, chain));
            match kind {
                VarKind::Let | VarKind::Const => {
                    self.bind(here, &d.name, State::Uninit(kind), func);
                }
                VarKind::Var => {
                    let target = self.function_frame(chain);
                    if !self.frames[target].bindings.contains_key(&d.name) {
                        self.bind(target, &d.name, State::Uninit(VarKind::Var), func);
                    }
                }
            }
        }
    }

    fn walk_decls(&mut self, decls: &'a [VarDeclarator], chain: &[usize]) {
        for d in decls {
            if let Some(init) = &d.init {
                // A function initialiser doesn't run its body.
                if let Some((name, params, body)) = function_init(d) {
                    self.defer(name, params, body, chain);
                } else {
                    self.walk_expr(init, chain);
                }
                self.initialise(chain, &d.name);
            } else if !d.name.starts_with("$destr$") {
                // `let x;` holds `undefined` from here on, so it leaves the
                // dead zone. A `const x;` with no initialiser is not real
                // JavaScript: in declaration files (`.d.js`) it declares an
                // external binding, which is always initialised. A `var x;`
                // stays unassigned until something assigns it.
                if let Some(frame) = self.lookup(chain, &d.name) {
                    let state = self.frames[frame].bindings[&d.name].state;
                    if matches!(
                        state,
                        State::Uninit(VarKind::Let) | State::Uninit(VarKind::Const)
                    ) {
                        self.initialise(chain, &d.name);
                    }
                }
            }
        }
    }

    fn walk_stmt(&mut self, stmt: &'a Stmt, chain: &[usize]) {
        match stmt {
            Stmt::Block { body, .. } => self.walk_stmts(body, chain, true),
            Stmt::Empty { .. }
            | Stmt::Break { .. }
            | Stmt::Continue { .. }
            | Stmt::Import { .. } => {}
            Stmt::Expr { expression, .. } => self.walk_expr(expression, chain),
            Stmt::Var { declarations, .. } => self.walk_decls(declarations, chain),
            Stmt::Export { declaration, .. } => match declaration {
                ExportDecl::Var { declarations, .. } => self.walk_decls(declarations, chain),
                ExportDecl::Function {
                    name, params, body, ..
                } => self.defer(Some(name), params, body, chain),
                ExportDecl::Default { value, .. } => self.walk_expr(value, chain),
                ExportDecl::List { specifiers, span } => {
                    for s in specifiers {
                        if s.local != "default" {
                            self.read(chain, &s.local, *span);
                        }
                    }
                }
                ExportDecl::From { .. } => {}
            },
            Stmt::FunctionDecl {
                name, params, body, ..
            } => self.defer(Some(name), params, body, chain),
            Stmt::If {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.walk_expr(test, chain);
                self.walk_stmt(consequent, chain);
                if let Some(a) = alternate {
                    self.walk_stmt(a, chain);
                }
            }
            Stmt::While { test, body, .. } | Stmt::DoWhile { body, test, .. } => {
                self.walk_expr(test, chain);
                self.walk_stmt(body, chain);
            }
            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => {
                let f = self.new_frame(false);
                let mut inner = chain.to_vec();
                inner.push(f);
                match init {
                    Some(ForInit::VarDecl(decls)) => {
                        let kind = if decls.iter().all(|d| d.kind == VarKind::Var) {
                            VarKind::Var
                        } else {
                            decls.first().map(|d| d.kind).unwrap_or(VarKind::Let)
                        };
                        self.hoist_decls(kind, decls, &inner, f);
                        self.walk_decls(decls, &inner);
                    }
                    Some(ForInit::Expr(e)) => self.walk_expr(e, &inner),
                    None => {}
                }
                if let Some(t) = test {
                    self.walk_expr(t, &inner);
                }
                self.walk_stmt(body, &inner);
                if let Some(u) = update {
                    self.walk_expr(u, &inner);
                }
            }
            Stmt::ForIn {
                left, right, body, ..
            }
            | Stmt::ForOf {
                left, right, body, ..
            } => {
                self.walk_expr(right, chain);
                let f = self.new_frame(false);
                let mut inner = chain.to_vec();
                inner.push(f);
                match left {
                    ForInLhs::VarDecl(name, _, _) => self.bind(f, name, State::Always, None),
                    ForInLhs::Expr(e) => self.walk_target(e, &inner, false),
                }
                self.walk_stmt(body, &inner);
            }
            Stmt::Return { argument, .. } => {
                if let Some(a) = argument {
                    self.walk_expr(a, chain);
                }
            }
            Stmt::Throw { argument, .. } => self.walk_expr(argument, chain),
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                self.walk_stmt(block, chain);
                if let Some(h) = handler {
                    let f = self.new_frame(false);
                    let mut inner = chain.to_vec();
                    inner.push(f);
                    self.bind(f, &h.param, State::Always, None);
                    self.walk_stmt(&h.body, &inner);
                }
                if let Some(fin) = finalizer {
                    self.walk_stmt(fin, chain);
                }
            }
            Stmt::Switch {
                discriminant,
                cases,
                ..
            } => {
                self.walk_expr(discriminant, chain);
                // The case clauses share one block scope.
                let f = self.new_frame(false);
                let mut inner = chain.to_vec();
                inner.push(f);
                for c in cases {
                    for s in &c.consequent {
                        self.hoist(s, &inner, f);
                    }
                }
                for c in cases {
                    if let Some(t) = &c.test {
                        self.walk_expr(t, &inner);
                    }
                    for s in &c.consequent {
                        self.walk_stmt(s, &inner);
                    }
                }
            }
            Stmt::Labeled { body, .. } => self.walk_stmt(body, chain),
        }
    }

    // ---- expressions --------------------------------------------------

    /// An assignment target. `compound` targets (`x += 1`, `x++`) read
    /// the old value first.
    fn walk_target(&mut self, target: &'a Expr, chain: &[usize], compound: bool) {
        match target {
            Expr::Ident { name, span } => {
                let Some(frame) = self.lookup(chain, name) else {
                    return;
                };
                match self.frames[frame].bindings[name.as_str()].state {
                    State::Uninit(VarKind::Var) if !compound => self.initialise(chain, name),
                    State::Uninit(kind) => self.violation(name, *span, kind),
                    _ => {}
                }
            }
            other => self.walk_expr(other, chain),
        }
    }

    fn walk_expr(&mut self, expr: &'a Expr, chain: &[usize]) {
        match expr {
            Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
            Expr::Ident { name, span } => {
                self.read(chain, name, *span);
            }
            Expr::Array { elements, .. } => {
                for e in elements.iter().flatten() {
                    self.walk_expr(e, chain);
                }
            }
            Expr::Tuple { elements, .. }
            | Expr::Sequence {
                expressions: elements,
                ..
            } => {
                for e in elements {
                    self.walk_expr(e, chain);
                }
            }
            Expr::TemplateLiteral { expressions, .. } => {
                for e in expressions {
                    self.walk_expr(e, chain);
                }
            }
            Expr::Object { properties, .. } => {
                for p in properties {
                    match p {
                        PropDef::Property { value, .. } => self.walk_expr(value, chain),
                        PropDef::Spread { argument, .. } => self.walk_expr(argument, chain),
                        PropDef::Method { params, body, .. } => {
                            self.defer(None, params, body, chain)
                        }
                        PropDef::Getter { body, .. } => self.defer(None, &[], body, chain),
                        PropDef::Setter { body, .. } => self.defer(None, &[], body, chain),
                    }
                }
            }
            Expr::Function {
                name, params, body, ..
            } => self.defer(name.as_deref(), params, body, chain),
            Expr::Member { object, .. } => self.walk_expr(object, chain),
            Expr::ComputedMember {
                object, property, ..
            } => {
                self.walk_expr(object, chain);
                self.walk_expr(property, chain);
            }
            Expr::Call {
                callee,
                arguments,
                keywords,
                ..
            } => {
                let target = match callee.as_ref() {
                    Expr::Ident { name, span } => self.read(chain, name, *span),
                    // An immediately-invoked function expression.
                    Expr::Function {
                        name, params, body, ..
                    } => Some(self.func_ref(name.as_deref(), params, body, chain)),
                    other => {
                        self.walk_expr(other, chain);
                        None
                    }
                };
                for a in arguments {
                    self.walk_expr(a, chain);
                }
                for (_, a) in keywords {
                    self.walk_expr(a, chain);
                }
                if let Some(f) = target {
                    self.call(&f);
                }
            }
            Expr::New {
                callee, arguments, ..
            } => {
                let target = match callee.as_ref() {
                    Expr::Ident { name, span } => self.read(chain, name, *span),
                    other => {
                        self.walk_expr(other, chain);
                        None
                    }
                };
                for a in arguments {
                    self.walk_expr(a, chain);
                }
                if let Some(f) = target {
                    self.call(&f);
                }
            }
            Expr::Unary { op, argument, .. } => {
                use super::UnaryOp::*;
                match op {
                    PreInc | PreDec | PostInc | PostDec => self.walk_target(argument, chain, true),
                    // `typeof x` doesn't throw for an undeclared global, but
                    // does in the dead zone; keep it a read.
                    _ => self.walk_expr(argument, chain),
                }
            }
            Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
                self.walk_expr(left, chain);
                self.walk_expr(right, chain);
            }
            Expr::Assign {
                op, left, right, ..
            } => {
                let compound = *op != super::AssignOp::Assign;
                if compound {
                    self.walk_target(left, chain, true);
                }
                self.walk_expr(right, chain);
                if !compound {
                    self.walk_target(left, chain, false);
                }
            }
            Expr::Conditional {
                test,
                consequent,
                alternate,
                ..
            } => {
                self.walk_expr(test, chain);
                self.walk_expr(consequent, chain);
                self.walk_expr(alternate, chain);
            }
            Expr::OptionalChain { head, segments, .. } => {
                self.walk_expr(head, chain);
                for s in segments {
                    match s {
                        ChainSegment::Member { .. } => {}
                        ChainSegment::Computed { property, .. } => self.walk_expr(property, chain),
                        ChainSegment::Call { arguments, .. } => {
                            for a in arguments {
                                self.walk_expr(a, chain);
                            }
                        }
                    }
                }
            }
            Expr::Spread { argument, .. } => self.walk_expr(argument, chain),
            Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => {
                self.walk_expr(source, chain)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn violations(src: &str) -> Vec<String> {
        let program = crate::frontends::javascript::parse_source(src).unwrap();
        check_program(&program.statements)
            .into_iter()
            .map(|v| v.name)
            .collect()
    }

    #[test]
    fn direct_use_before_const() {
        assert_eq!(
            violations("const r = f(1);\nconst f = (x) => x + 1;"),
            ["f"]
        );
        assert_eq!(violations("const a = b;\nconst b = a;"), ["b"]);
        assert_eq!(violations("const x = x + 1;"), ["x"]);
    }

    #[test]
    fn hoisted_function_call_reads_later_const() {
        assert_eq!(
            violations("f();\nconst x = 1;\nfunction f() { return x; }"),
            ["x"]
        );
        // Called only after the const: fine.
        assert!(violations("const x = 1;\nfunction f() { return x; }\nf();").is_empty());
    }

    #[test]
    fn deferred_functions_are_fine() {
        // Declared and referenced before `lib`, but only run later.
        assert!(violations(
            "function helper() { return lib.foo; }\n\
             const lib = { foo: 1, run: helper };\n\
             const r = helper();"
        )
        .is_empty());
        assert!(violations("const g = () => later;\nconst later = 2;\ng();").is_empty());
        assert!(violations("function f(x) { return x + 1; }\nconst r = f(1);").is_empty());
    }

    #[test]
    fn iife_runs_immediately() {
        assert_eq!(
            violations("(function() { return x; })();\nconst x = 1;"),
            ["x"]
        );
        assert!(violations("const x = 1;\n(function() { return x; })();").is_empty());
    }

    #[test]
    fn transitive_calls_and_recursion() {
        assert_eq!(
            violations(
                "a();\nconst z = 1;\n\
                 function a() { return b(); }\n\
                 function b() { return z + a(); }"
            ),
            ["z"]
        );
    }

    #[test]
    fn var_read_before_assignment() {
        assert_eq!(violations("const y = v * 2;\nvar v = 3;"), ["v"]);
        assert!(violations("var v = 3;\nconst y = v * 2;").is_empty());
        assert!(violations("var v;\nv = 3;\nconst y = v * 2;").is_empty());
    }

    #[test]
    fn inner_function_order() {
        assert_eq!(
            violations("function g() { h(); const y = 1; function h() { return y; } }"),
            ["y"]
        );
    }

    #[test]
    fn let_without_initialiser_leaves_the_dead_zone() {
        assert!(violations("let x;\nconst y = x;\nx = 1;").is_empty());
    }
}
