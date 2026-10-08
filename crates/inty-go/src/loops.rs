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
                Some(ArrayKind::Fixed)
                    if !self.calls || u.span.is_some_and(|s| stable(name, s)) =>
                {
                    out.push(name.clone());
                }
                Some(ArrayKind::Growable(key)) if !self.calls && !self.foreign_store => {
                    growable
                        .entry(key)
                        .or_default()
                        .push((name.clone(), u.stored));
                }
                _ => {}
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

/// The stores `a[j] = v`, among a loop body's statements, whose index is
/// known to be in bounds, so that the store can't grow the array: the
/// same statement list has already read (or stored) `a[j]`
/// unconditionally, and nothing since can have changed `j`. A read out
/// of bounds stops the program, and in a loop that holds `a`'s header
/// (see [`LoopScan::cacheable`]) the array can only grow. `j` is a name
/// or an integer literal.
pub fn in_bounds_stores(body: &Stmt, out: &mut HashSet<Span>) {
    match body {
        Stmt::Block { body, .. } => in_bounds_list(body, out),
        Stmt::If {
            consequent,
            alternate,
            ..
        } => {
            in_bounds_stores(consequent, out);
            if let Some(a) = alternate {
                in_bounds_stores(a, out);
            }
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForOf { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::Labeled { body, .. } => in_bounds_stores(body, out),
        Stmt::Switch { cases, .. } => {
            for c in cases {
                in_bounds_list(&c.consequent, out);
            }
        }
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            in_bounds_stores(block, out);
            if let Some(h) = handler {
                in_bounds_stores(&h.body, out);
            }
            if let Some(f) = finalizer {
                in_bounds_stores(f, out);
            }
        }
        _ => {}
    }
}

fn in_bounds_list(stmts: &[Stmt], out: &mut HashSet<Span>) {
    for (k, s) in stmts.iter().enumerate() {
        in_bounds_stores(s, out);
        let Stmt::Expr {
            expression:
                Expr::Assign {
                    op: AssignOp::Assign,
                    left,
                    right,
                    span,
                },
            ..
        } = s
        else {
            continue;
        };
        let Expr::ComputedMember {
            object, property, ..
        } = &**left
        else {
            continue;
        };
        let (Expr::Ident { name: array, .. }, Some(index)) = (&**object, index_key(property))
        else {
            continue;
        };
        if let Index::Name(j) = &index {
            if assigns_in_expr(right, j) {
                continue;
            }
        }
        let known = reads(right, array, &index)
            || stmts[..k]
                .iter()
                .rev()
                .map(|p| fact(p, array, &index))
                .find(|f| *f != Fact::Unknown)
                == Some(Fact::InBounds);
        if known {
            out.insert(*span);
        }
    }
}

#[derive(Clone, PartialEq)]
enum Index {
    Name(String),
    Const(i64),
}

fn index_key(e: &Expr) -> Option<Index> {
    match e {
        Expr::Ident { name, .. } => Some(Index::Name(name.clone())),
        Expr::Lit {
            value: inty::ast::Literal::Number(n),
            ..
        } if n.fract() == 0.0 && *n >= 0.0 && *n < 1e15 => Some(Index::Const(*n as i64)),
        _ => None,
    }
}

#[derive(PartialEq)]
enum Fact {
    /// `a[j]` was accessed, `j` unchanged since.
    InBounds,
    /// `j` may have changed (or we can't tell): look no further back.
    Lost,
    /// Says nothing: look further back.
    Unknown,
}

/// What an earlier statement `p` says about `a[j]` at the end of it.
fn fact(p: &Stmt, array: &str, index: &Index) -> Fact {
    let assigns = match index {
        Index::Name(j) => assigns_in_stmt(p, j),
        Index::Const(_) => false,
    };
    if assigns {
        return Fact::Lost;
    }
    let evaluated = match p {
        Stmt::Expr { expression, .. } => Some(expression),
        Stmt::Var { declarations, .. } => {
            return if declarations
                .iter()
                .filter_map(|d| d.init.as_ref())
                .any(|e| reads(e, array, index))
            {
                Fact::InBounds
            } else {
                Fact::Unknown
            };
        }
        // An `if`'s test runs whichever branch follows.
        Stmt::If { test, .. } => Some(test),
        Stmt::Empty { .. } => None,
        // Anything else that doesn't write `j` says nothing.
        _ => None,
    };
    match evaluated {
        Some(e) if reads(e, array, index) => Fact::InBounds,
        _ => Fact::Unknown,
    }
}

/// Whether evaluating `e` always accesses `array[index]` (so that, if it
/// finishes, the index was in bounds): not under `&&`, `||`, `??`, `?:`
/// or an optional chain, where it may be skipped.
fn reads(e: &Expr, array: &str, index: &Index) -> bool {
    let r = |x: &Expr| reads(x, array, index);
    match e {
        Expr::ComputedMember {
            object, property, ..
        } => {
            let hit = matches!(&**object, Expr::Ident { name, .. } if name == array)
                && index_key(property).as_ref() == Some(index);
            hit || r(object) || r(property)
        }
        Expr::Member { object, .. } => r(object),
        Expr::Binary {
            op, left, right, ..
        } => {
            use inty::ast::BinOp;
            match op {
                BinOp::And | BinOp::Or => r(left),
                _ => r(left) || r(right),
            }
        }
        Expr::NullishCoalesce { left, .. } => r(left),
        Expr::Conditional { test, .. } => r(test),
        Expr::Unary { argument, .. } => r(argument),
        Expr::Assign { left, right, .. } => {
            // `a[j] = v` stores (growing the array if needed): either way
            // `j` is in bounds afterwards.
            r(left) || r(right)
        }
        Expr::Call { arguments, .. } => arguments.iter().any(r),
        Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
            expressions.iter().any(r)
        }
        Expr::Array { elements, .. } => elements.iter().flatten().any(r),
        Expr::Tuple { elements, .. } => elements.iter().any(r),
        _ => false,
    }
}

/// Whether running `s` may assign (or declare) `name`.
fn assigns_in_stmt(s: &Stmt, name: &str) -> bool {
    let e = |x: &Expr| assigns(x, name);
    let st = |x: &Stmt| assigns_in_stmt(x, name);
    let decls = |ds: &[VarDeclarator]| {
        ds.iter()
            .any(|d| d.name == name || d.init.as_ref().is_some_and(e))
    };
    match s {
        Stmt::Block { body, .. } => body.iter().any(st),
        Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => false,
        Stmt::Expr { expression, .. } => e(expression),
        Stmt::Var { declarations, .. } => decls(declarations),
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => e(test) || st(consequent) || alternate.as_deref().is_some_and(st),
        Stmt::While { test, body, .. } | Stmt::DoWhile { body, test, .. } => e(test) || st(body),
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            (match init {
                Some(ForInit::VarDecl(ds)) => decls(ds),
                Some(ForInit::Expr(x)) => e(x),
                None => false,
            }) || test.as_ref().is_some_and(e)
                || update.as_ref().is_some_and(e)
                || st(body)
        }
        Stmt::ForIn {
            left, right, body, ..
        }
        | Stmt::ForOf {
            left, right, body, ..
        } => {
            (match left {
                ForInLhs::VarDecl(n, ..) => n == name,
                ForInLhs::Expr(t) => matches!(t, Expr::Ident { name: n, .. } if n == name) || e(t),
            }) || e(right)
                || st(body)
        }
        Stmt::Return { argument, .. } => argument.as_ref().is_some_and(e),
        Stmt::Throw { argument, .. } => e(argument),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            st(block)
                || handler
                    .as_ref()
                    .is_some_and(|h| h.param == name || st(&h.body))
                || finalizer.as_deref().is_some_and(st)
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            e(discriminant)
                || cases
                    .iter()
                    .any(|c| c.test.as_ref().is_some_and(e) || c.consequent.iter().any(st))
        }
        Stmt::Labeled { body, .. } => st(body),
        // Closures, and statements that shouldn't be in such a loop.
        Stmt::FunctionDecl { .. } | Stmt::Import { .. } | Stmt::Export { .. } => true,
    }
}

fn assigns_in_expr(e: &Expr, name: &str) -> bool {
    assigns(e, name)
}

/// Whether `e` assigns (or updates) `name`.
fn assigns(e: &Expr, name: &str) -> bool {
    let a = |x: &Expr| assigns(x, name);
    match e {
        Expr::Assign { left, right, .. } => {
            matches!(&**left, Expr::Ident { name: n, .. } if n == name) || a(left) || a(right)
        }
        Expr::Unary { op, argument, .. } => {
            (matches!(
                op,
                UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
            ) && matches!(&**argument, Expr::Ident { name: n, .. } if n == name))
                || a(argument)
        }
        Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
            a(left) || a(right)
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => a(test) || a(consequent) || a(alternate),
        Expr::Member { object, .. } => a(object),
        Expr::ComputedMember {
            object, property, ..
        } => a(object) || a(property),
        Expr::Call {
            callee, arguments, ..
        } => a(callee) || arguments.iter().any(a),
        Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
            expressions.iter().any(a)
        }
        Expr::Array { elements, .. } => elements.iter().flatten().any(a),
        Expr::Tuple { elements, .. } => elements.iter().any(a),
        Expr::Spread { argument, .. } => a(argument),
        // Closures and anything else: assume it may.
        Expr::Function { .. }
        | Expr::OptionalChain { .. }
        | Expr::Object { .. }
        | Expr::New { .. } => true,
        Expr::Lit { .. } | Expr::Ident { .. } | Expr::This { .. } | Expr::NewTarget { .. } => false,
        Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => a(source),
    }
}
