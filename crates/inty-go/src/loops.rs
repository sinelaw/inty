//! Which arrays a loop may keep in a local slice header.
//!
//! An ordinary array is a Go `*[]T`, so `a[i]` loads the slice header
//! through the pointer. Go reloads it after every store to memory: its
//! optimiser can't tell that storing a `float64` element leaves `*a`
//! unchanged. In a loop, the emitter can copy the header into a local
//! once (`h := *a`) and index that instead, when nothing in the loop can
//! change `*a` other than the loop's own stores to `a` (which hand back
//! the grown header, see `intySetH`). This module decides when that is
//! so, from the loop's syntax alone:
//!
//! - The loop runs no code that isn't in it: no calls (`Math.*` aside),
//!   `new`, closures, accessors or optional chains. So only its own
//!   statements can touch an array.
//! - The name is never declared or assigned in the loop, so it denotes
//!   the same array throughout, and it appears only as `a[i]`,
//!   `a[i] = v` or `a.length`. So no test in the loop can narrow it: its
//!   type at those uses, which can't be `null`, is its type at the loop's
//!   entry, where the header is loaded.
//! - No store through anything else (`o.xs[i] = v`, `xs.length = n`)
//!   can grow or shrink an array that one of the names aliases.
//! - Two cached arrays of the same element type might be one array; if
//!   either is stored to, a grow through one would leave the other's
//!   header stale, so neither is cached.
//!
//! A typed array's header never changes (it has a fixed length), so it
//! may be cached in a loop with calls too, when its binding is never
//! reassigned anywhere (the resolver's "stable").

use std::collections::{HashMap, HashSet};

use inty::ast::{
    AssignOp, ChainSegment, Expr, ForInLhs, ForInit, PropDef, Stmt, UnaryOp, VarDeclarator,
};
use inty::span::Span;

/// How a loop uses one name.
#[derive(Default, Clone)]
pub struct Use {
    /// As `a[i]`, `a[i] = v` or `a.length`.
    pub indexed: bool,
    /// As `a[i] = v`, which can grow the array.
    pub stored: bool,
    /// Any other way (passed, compared, assigned, a field other than
    /// `length`, ...).
    pub other: bool,
    /// The span of one occurrence (for the resolver's lookup).
    pub span: Option<Span>,
}

#[derive(Default)]
pub struct LoopScan {
    /// The loop may run code that isn't in it.
    pub calls: bool,
    /// A store that could change the header of an array not named by a
    /// plain identifier (or one we can't see).
    pub foreign_store: bool,
    pub uses: HashMap<String, Use>,
    /// Names the loop declares (a use of such a name may be another
    /// binding).
    pub declared: HashSet<String>,
    /// Whether `Math` is the built-in (not a program binding).
    math_builtin: bool,
}

impl LoopScan {
    /// Scan a `while`, `do`-`while` or `for` statement.
    pub fn of_loop(s: &Stmt, math_builtin: bool) -> LoopScan {
        let mut scan = LoopScan {
            math_builtin,
            ..LoopScan::default()
        };
        scan.stmt(s);
        scan
    }

    fn mark(&mut self, name: &str, span: Span, f: impl FnOnce(&mut Use)) {
        let u = self.uses.entry(name.to_string()).or_default();
        u.span.get_or_insert(span);
        f(u);
    }

    fn decls(&mut self, ds: &[VarDeclarator]) {
        for d in ds {
            self.declared.insert(d.name.clone());
            if let Some(e) = &d.init {
                self.expr(e);
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Block { body, .. } => body.iter().for_each(|s| self.stmt(s)),
            Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Expr { expression, .. } => self.expr(expression),
            Stmt::Var { declarations, .. } => self.decls(declarations),
            Stmt::Import { .. } | Stmt::Export { .. } => self.calls = true,
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
            Stmt::While { test, body, .. } | Stmt::DoWhile { body, test, .. } => {
                self.expr(test);
                self.stmt(body);
            }
            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => {
                match init {
                    Some(ForInit::VarDecl(ds)) => self.decls(ds),
                    Some(ForInit::Expr(e)) => self.expr(e),
                    None => {}
                }
                if let Some(t) = test {
                    self.expr(t);
                }
                if let Some(u) = update {
                    self.expr(u);
                }
                self.stmt(body);
            }
            Stmt::ForIn {
                left, right, body, ..
            }
            | Stmt::ForOf {
                left, right, body, ..
            } => {
                match left {
                    ForInLhs::VarDecl(name, ..) => {
                        self.declared.insert(name.clone());
                    }
                    ForInLhs::Expr(target) => self.target(AssignOp::Assign, target),
                }
                self.expr(right);
                self.stmt(body);
            }
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
                if let Some(h) = handler {
                    self.declared.insert(h.param.clone());
                    self.stmt(&h.body);
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
                for c in cases {
                    if let Some(t) = &c.test {
                        self.expr(t);
                    }
                    c.consequent.iter().for_each(|s| self.stmt(s));
                }
            }
            Stmt::Labeled { body, .. } => self.stmt(body),
            Stmt::FunctionDecl { name, .. } => {
                self.declared.insert(name.clone());
                self.calls = true;
            }
        }
    }

    /// The target of an assignment (or of a `for`-`of` binding).
    fn target(&mut self, op: AssignOp, left: &Expr) {
        match left {
            Expr::Ident { name, span } => self.mark(name, *span, |u| u.other = true),
            Expr::ComputedMember {
                object, property, ..
            } => {
                match &**object {
                    Expr::Ident { name, span } => self.mark(name, *span, |u| {
                        u.indexed = true;
                        if op == AssignOp::Assign {
                            u.stored = true;
                        }
                    }),
                    other => {
                        // Only a plain store can grow the array.
                        if op == AssignOp::Assign {
                            self.foreign_store = true;
                        }
                        self.expr(other);
                    }
                }
                self.expr(property);
            }
            Expr::Member {
                object, property, ..
            } => {
                if property == "length" {
                    self.foreign_store = true;
                }
                // A field store replaces a value; it changes no array's
                // header. The object is used as a value.
                self.expr(object);
            }
            other => {
                self.foreign_store = true;
                self.expr(other);
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        match e {
            Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
            Expr::Ident { name, span } => self.mark(name, *span, |u| u.other = true),
            Expr::Array { elements, .. } => elements.iter().flatten().for_each(|x| self.expr(x)),
            Expr::Tuple { elements, .. } => elements.iter().for_each(|x| self.expr(x)),
            Expr::Object { properties, .. } => {
                for p in properties {
                    match p {
                        PropDef::Property { value, .. } => self.expr(value),
                        PropDef::Spread { argument, .. } => self.expr(argument),
                        PropDef::Getter { .. }
                        | PropDef::Setter { .. }
                        | PropDef::Method { .. } => self.calls = true,
                    }
                }
            }
            Expr::Function { .. } | Expr::New { .. } => self.calls = true,
            Expr::Member {
                object, property, ..
            } => match &**object {
                Expr::Ident { name, span } if property == "length" => {
                    self.mark(name, *span, |u| u.indexed = true)
                }
                other => self.expr(other),
            },
            Expr::ComputedMember {
                object, property, ..
            } => {
                match &**object {
                    Expr::Ident { name, span } => self.mark(name, *span, |u| u.indexed = true),
                    other => self.expr(other),
                }
                self.expr(property);
            }
            Expr::Call {
                callee,
                arguments,
                keywords,
                ..
            } => {
                let math = self.math_builtin
                    && matches!(&**callee, Expr::Member { object, .. }
                        if matches!(&**object, Expr::Ident { name, .. } if name == "Math"));
                if !math {
                    self.calls = true;
                    self.expr(callee);
                }
                arguments.iter().for_each(|a| self.expr(a));
                keywords.iter().for_each(|(_, a)| self.expr(a));
            }
            Expr::Unary { op, argument, .. } => match op {
                UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec => {
                    // An update never grows an array.
                    self.target(AssignOp::AddAssign, argument)
                }
                UnaryOp::Delete => {
                    self.calls = true;
                    self.expr(argument);
                }
                _ => self.expr(argument),
            },
            Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Assign {
                op, left, right, ..
            } => {
                self.target(*op, left);
                self.expr(right);
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
                self.calls = true;
                self.expr(head);
                for s in segments {
                    match s {
                        ChainSegment::Member { .. } => {}
                        ChainSegment::Computed { property, .. } => self.expr(property),
                        ChainSegment::Call { arguments, .. } => {
                            arguments.iter().for_each(|a| self.expr(a))
                        }
                    }
                }
            }
            Expr::Spread { argument, .. } => self.expr(argument),
            Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => self.expr(source),
            Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
                expressions.iter().for_each(|x| self.expr(x))
            }
        }
    }

    /// The names whose header may be held in a local through the loop:
    /// `growable` for ordinary arrays (with their element type's key, for
    /// the aliasing rule), `fixed` for typed arrays. `stable(name, span)`
    /// says whether the binding is never reassigned.
    pub fn cacheable<K: Eq + std::hash::Hash + Clone>(
        &self,
        kind_of: impl Fn(&str) -> Option<ArrayKind<K>>,
        stable: impl Fn(&str, Span) -> bool,
    ) -> Vec<String> {
        let mut out = Vec::new();
        let mut growable: HashMap<K, Vec<(String, bool)>> = HashMap::new();
        let mut names: Vec<&String> = self.uses.keys().collect();
        names.sort();
        for name in names {
            let u = &self.uses[name];
            if !u.indexed || u.other || self.declared.contains(name) {
                continue;
            }
            match kind_of(name) {
                Some(ArrayKind::Fixed) => {
                    if !self.calls || u.span.is_some_and(|s| stable(name, s)) {
                        out.push(name.clone());
                    }
                }
                Some(ArrayKind::Growable(key)) => {
                    if !self.calls && !self.foreign_store {
                        growable
                            .entry(key)
                            .or_default()
                            .push((name.clone(), u.stored));
                    }
                }
                None => {}
            }
        }
        for (_, group) in growable {
            let any_store = group.iter().any(|(_, s)| *s);
            if group.len() == 1 || !any_store {
                out.extend(group.into_iter().map(|(n, _)| n));
            }
        }
        out.sort();
        out
    }
}

pub enum ArrayKind<K> {
    /// A typed array: its header never changes.
    Fixed,
    /// An ordinary array, keyed by its Go element type.
    Growable(K),
}
