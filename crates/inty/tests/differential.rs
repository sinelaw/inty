//! Differential testing against the Lean model (`lean/`) and a JavaScript
//! engine.
//!
//! Generates random programs in the formalized core calculus, writes each
//! one as JavaScript for inty and the engine and in the model's wire format
//! (`lean/Inty/Wire.lean`) for `inty-model`, and compares:
//!
//! - **soundness**: a program inty accepts must not get stuck in
//!   `dynamics`, and one the model's inference accepts must not get stuck
//!   in the model's interpreter (the latter is a theorem; seeing it would
//!   mean a harness bug);
//! - **semantics**: when both interpreters finish, they agree on the value,
//!   or on getting stuck;
//! - **typing**: inty and the model's inference accept the same programs,
//!   at the same type;
//! - **the engine**: where `dynamics` or the model finishes, Node agrees
//!   with it, and Node raises no native error (`TypeError`,
//!   `ReferenceError`) on a program inty or the model accepts. This ties
//!   both interpreters, and so the model's soundness theorem, to real
//!   JavaScript.
//!
//! Disagreements the model doesn't cover yet are counted per category and
//! printed; any other disagreement fails the test.
//!
//! The model is `lean/.lake/build/bin/inty-model` (`cd lean && lake build`),
//! or `INTY_LEAN_MODEL`. Without it the test is skipped. `INTY_DIFF_CASES`
//! sets the number of programs (default 3000), `INTY_DIFF_SEED` the seed.
//! The engine is `node` (or `INTY_NODE`) running `tests/differential/engine.js`;
//! without it the engine comparison is skipped, except on CI.

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use inty::builtins::initial_env;
use inty::dynamics::{run_to_end_with_fuel, Stuck, Value};
use inty::infer::InferState;
use inty::types::{LitValue, Type};

// ---- The core calculus ---------------------------------------------------

#[derive(Clone, Debug)]
enum Core {
    /// `m × 10^-e`.
    Num(u64, u32),
    Str(String),
    Bool(bool),
    Undef,
    Null,
    /// A de Bruijn index; one past the scope is an unbound variable.
    Var(usize),
    /// `function f(x₀, …, xₙ₋₁) { body }`: in `body`, `i < n` is `xᵢ`, `n`
    /// is `f` and `n + 1` is `this`.
    Func(usize, Box<Core>),
    /// A call outside any receiver, so `this` is `undefined`.
    App(Box<Core>, Vec<Core>),
    /// `const v = e₁; e₂` (`false`) or `let v = e₁; e₂` (`true`); only in
    /// statement position.
    Let(bool, Box<Core>, Box<Core>),
    /// `x = e`, for a `let` or a parameter.
    Assign(usize, Box<Core>),
    Cond(Box<Core>, Box<Core>, Box<Core>),
    Not(Box<Core>),
    Typeof(Box<Core>),
    Neg(Box<Core>),
    Plus(Box<Core>, Box<Core>),
    Minus(Box<Core>, Box<Core>),
    /// `return e;`, in a function's statement position.
    Ret(Box<Core>),
    /// `throw e;`, in statement position.
    Throw(Box<Core>),
    /// `e₁; e₂`, in statement position.
    Seq(Box<Core>, Box<Core>),
    /// `while (c) { body }`, in statement position; it completes with
    /// `undefined`.
    While(Box<Core>, Box<Core>),
    /// `break;` and `continue;`, inside a loop.
    Break,
    Continue,
    /// `try { body } catch (e) { handler }`, with `e` bound in `handler`.
    TryCatch(Box<Core>, Box<Core>),
    /// `try { body } finally { fin }`.
    TryFinally(Box<Core>, Box<Core>),
    /// An object literal `{l₀: e₀, …}`, its fields in order.
    Obj(Vec<(String, Core)>),
    /// `e.l`.
    Get(Box<Core>, String),
    /// `e.l = v`.
    Set(Box<Core>, String, Box<Core>),
}

use Core::*;

fn b(e: Core) -> Box<Core> {
    Box::new(e)
}

/// The model's wire format.
fn wire(e: &Core) -> String {
    match e {
        Num(m, x) => format!("(num {} {})", m, x),
        Str(s) => format!("(str s:{})", s),
        Bool(v) => format!("(bool {})", v),
        Undef => "(undef)".into(),
        Null => "(null)".into(),
        Var(i) => format!("(var {})", i),
        Func(n, body) => format!("(func {} {})", n, wire(body)),
        App(f, args) => {
            let args: Vec<String> = args.iter().map(wire).collect();
            format!(
                "(app {}{}{})",
                wire(f),
                if args.is_empty() { "" } else { " " },
                args.join(" ")
            )
        }
        Let(m, e1, e2) => format!(
            "({} {} {})",
            if *m { "letmut" } else { "let" },
            wire(e1),
            wire(e2)
        ),
        Assign(i, e) => format!("(assign {} {})", i, wire(e)),
        Cond(c, t, e) => format!("(cond {} {} {})", wire(c), wire(t), wire(e)),
        Not(e) => format!("(not {})", wire(e)),
        Typeof(e) => format!("(typeof {})", wire(e)),
        Neg(e) => format!("(neg {})", wire(e)),
        Plus(x, y) => format!("(plus {} {})", wire(x), wire(y)),
        Minus(x, y) => format!("(minus {} {})", wire(x), wire(y)),
        Ret(e) => format!("(ret {})", wire(e)),
        Throw(e) => format!("(throw {})", wire(e)),
        Seq(x, y) => format!("(seq {} {})", wire(x), wire(y)),
        While(c, body) => format!("(while {} {})", wire(c), wire(body)),
        Break => "(break)".into(),
        Continue => "(continue)".into(),
        TryCatch(x, y) => format!("(trycatch {} {})", wire(x), wire(y)),
        TryFinally(x, y) => format!("(tryfinally {} {})", wire(x), wire(y)),
        Obj(fields) => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(l, e)| format!(" (field s:{} {})", l, wire(e)))
                .collect();
            format!("(obj{})", fields.concat())
        }
        Get(e, l) => format!("(get {} s:{})", wire(e), l),
        Set(e, l, v) => format!("(set {} s:{} {})", wire(e), l, wire(v)),
    }
}

/// Whether a program ends in a statement rather than an expression: inty
/// then types the program `Undefined`, whatever the statement.
fn ends_in_statement(e: &Core) -> bool {
    match e {
        Let(_, _, rest) | Seq(_, rest) => ends_in_statement(rest),
        Throw(_) | Ret(_) | While(..) | Break | Continue | TryCatch(..) | TryFinally(..) => true,
        Cond(_, t, f) => is_stmt(t) || is_stmt(f),
        _ => false,
    }
}

/// Whether `e` must be printed as statements: JavaScript has no expression
/// form for it.
fn is_stmt(e: &Core) -> bool {
    match e {
        Ret(_) | Throw(_) | Seq(..) | Let(..) | While(..) | Break | Continue | TryCatch(..)
        | TryFinally(..) => true,
        Cond(_, t, f) => is_stmt(t) || is_stmt(f),
        _ => false,
    }
}

/// The program with every number literal fractional (`n` becomes `n.5`),
/// so that inty types no number `Int`.
fn fractional(e: &Core) -> Core {
    let f = |e: &Core| b(fractional(e));
    match e {
        Num(m, x) => Num(m * 10 + 5, x + 1),
        Func(n, body) => Func(*n, f(body)),
        App(x, args) => App(f(x), args.iter().map(fractional).collect()),
        Let(m, x, y) => Let(*m, f(x), f(y)),
        Assign(i, x) => Assign(*i, f(x)),
        Cond(c, t, e) => Cond(f(c), f(t), f(e)),
        Not(x) => Not(f(x)),
        Typeof(x) => Typeof(f(x)),
        Neg(x) => Neg(f(x)),
        Plus(x, y) => Plus(f(x), f(y)),
        Minus(x, y) => Minus(f(x), f(y)),
        Ret(x) => Ret(f(x)),
        Throw(x) => Throw(f(x)),
        Seq(x, y) => Seq(f(x), f(y)),
        While(x, y) => While(f(x), f(y)),
        TryCatch(x, y) => TryCatch(f(x), f(y)),
        TryFinally(x, y) => TryFinally(f(x), f(y)),
        Obj(fields) => Obj(fields
            .iter()
            .map(|(l, e)| (l.clone(), fractional(e)))
            .collect()),
        Get(x, l) => Get(f(x), l.clone()),
        Set(x, l, y) => Set(f(x), l.clone(), f(y)),
        other => other.clone(),
    }
}

/// JavaScript, with a fresh name for every binder.
struct Js {
    names: Vec<String>,
    next: usize,
}

impl Js {
    fn fresh(&mut self, prefix: &str) -> String {
        self.next += 1;
        format!("{}{}", prefix, self.next)
    }

    fn name(&self, i: usize) -> String {
        if i < self.names.len() {
            self.names[self.names.len() - 1 - i].clone()
        } else {
            "unbound".into()
        }
    }

    fn expr(&mut self, e: &Core) -> String {
        match e {
            Num(m, 0) => m.to_string(),
            Num(m, x) => {
                let digits = format!("{:0>width$}", m, width = *x as usize + 1);
                let (int, frac) = digits.split_at(digits.len() - *x as usize);
                format!("{}.{}", int, frac)
            }
            Str(s) => format!("\"{}\"", s),
            Bool(v) => v.to_string(),
            Undef => "(void 0)".into(),
            Null => "null".into(),
            Var(i) => self.name(*i),
            Func(n, body) => {
                let f = self.fresh("f");
                let xs: Vec<String> = (0..*n).map(|_| self.fresh("x")).collect();
                // `this` is printed as `this` where it is the innermost
                // function's; a function inside it that refers to it
                // needs an alias.
                let alias = refers_from_inner(body, n + 1, false).then(|| self.fresh("t"));
                self.names
                    .push(alias.clone().unwrap_or_else(|| "this".into()));
                self.names.push(f.clone());
                for x in xs.iter().rev() {
                    self.names.push(x.clone());
                }
                let body = self.stmts(body, "return ");
                self.names.truncate(self.names.len() - n - 2);
                let prelude = alias
                    .map(|t| format!("const {t} = this; "))
                    .unwrap_or_default();
                format!(
                    "(function {}({}) {{ {}{} }})",
                    f,
                    xs.join(", "),
                    prelude,
                    body
                )
            }
            App(f, args) => {
                let args: Vec<String> = args.iter().map(|a| self.expr(a)).collect();
                // A call of a property is a method call in JavaScript,
                // with the object as `this`; the calculus's calls have no
                // receiver, as `(0, o.f)(…)` hasn't.
                let callee = match **f {
                    Get(..) => format!("(0, {})", self.expr(f)),
                    _ => format!("({})", self.expr(f)),
                };
                format!("{}({})", callee, args.join(", "))
            }
            Let(..) | Ret(_) | Throw(_) | Seq(..) | While(..) | Break | Continue | TryCatch(..)
            | TryFinally(..) => {
                unreachable!("statements only in statement position: {e:?}")
            }
            Assign(i, e) => format!("({} = {})", self.name(*i), self.expr(e)),
            Cond(c, t, e) => format!("({} ? {} : {})", self.expr(c), self.expr(t), self.expr(e)),
            Not(e) => format!("!({})", self.expr(e)),
            Typeof(e) => format!("typeof ({})", self.expr(e)),
            Neg(e) => format!("-({})", self.expr(e)),
            Plus(x, y) => format!("({} + {})", self.expr(x), self.expr(y)),
            Minus(x, y) => format!("({} - {})", self.expr(x), self.expr(y)),
            Obj(fields) => {
                let fields: Vec<String> = fields
                    .iter()
                    .map(|(l, e)| format!("{}: {}", l, self.expr(e)))
                    .collect();
                format!("({{{}}})", fields.join(", "))
            }
            Get(e, l) => format!("({}).{}", self.expr(e), l),
            Set(e, l, v) => format!("(({}).{} = {})", self.expr(e), l, self.expr(v)),
        }
    }

    /// A program or function body: statements, then `last` and the value
    /// (`return` in a function, an expression statement at the top).
    fn stmts(&mut self, e: &Core, last: &str) -> String {
        match e {
            Let(m, e1, e2) => {
                let v = self.fresh("v");
                let init = self.expr(e1);
                self.names.push(v.clone());
                let rest = self.stmts(e2, last);
                self.names.pop();
                let keyword = if *m { "let" } else { "const" };
                format!("{} {} = {}; {}", keyword, v, init, rest)
            }
            Seq(e1, e2) => {
                let first = self.stmts(e1, "");
                format!("{} {}", first, self.stmts(e2, last))
            }
            Ret(e) => format!("return {};", self.expr(e)),
            Throw(e) => format!("throw {};", self.expr(e)),
            // A loop completes with `undefined`: in a function, the
            // function returns it; at the top, it is the program's value
            // (where a bare loop's would be its body's last).
            While(c, body) => format!(
                "while ({}) {{ {} }} {}(void 0);",
                self.expr(c),
                self.stmts(body, ""),
                last
            ),
            Break => "break;".into(),
            Continue => "continue;".into(),
            TryCatch(body, handler) => {
                let body = self.stmts(body, last);
                let v = self.fresh("e");
                self.names.push(v.clone());
                let handler = self.stmts(handler, last);
                self.names.pop();
                format!("try {{ {} }} catch ({}) {{ {} }}", body, v, handler)
            }
            TryFinally(body, fin) => format!(
                "try {{ {} }} finally {{ {} }}",
                self.stmts(body, last),
                self.stmts(fin, "")
            ),
            Cond(c, t, f) if is_stmt(t) || is_stmt(f) => format!(
                "if ({}) {{ {} }} else {{ {} }}",
                self.expr(c),
                self.stmts(t, last),
                self.stmts(f, last)
            ),
            e => format!("{}{};", last, self.expr(e)),
        }
    }
}

/// Whether `e` refers to variable `i` from inside a function nested in it
/// (`inner`: already inside one), where JavaScript's `this` would mean the
/// nested function's.
fn refers_from_inner(e: &Core, i: usize, inner: bool) -> bool {
    match e {
        Var(j) => inner && *j == i,
        Func(n, body) => refers_from_inner(body, i + n + 2, true),
        Let(_, x, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i + 1, inner),
        Assign(j, x) => (inner && *j == i) || refers_from_inner(x, i, inner),
        App(f, args) => {
            refers_from_inner(f, i, inner) || args.iter().any(|a| refers_from_inner(a, i, inner))
        }
        Cond(c, t, e) => {
            refers_from_inner(c, i, inner)
                || refers_from_inner(t, i, inner)
                || refers_from_inner(e, i, inner)
        }
        Not(x) | Typeof(x) | Neg(x) | Ret(x) | Throw(x) => refers_from_inner(x, i, inner),
        Plus(x, y) | Minus(x, y) | Seq(x, y) | While(x, y) | TryFinally(x, y) => {
            refers_from_inner(x, i, inner) || refers_from_inner(y, i, inner)
        }
        TryCatch(x, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i + 1, inner),
        Break | Continue => false,
        Num(..) | Str(_) | Bool(_) | Undef | Null => false,
        Obj(fields) => fields.iter().any(|(_, e)| refers_from_inner(e, i, inner)),
        Get(x, _) => refers_from_inner(x, i, inner),
        Set(x, _, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i, inner),
    }
}

fn javascript(e: &Core) -> String {
    Js {
        names: Vec::new(),
        next: 0,
    }
    .stmts(e, "")
}

// ---- Generation ----------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

#[derive(Clone, Debug, PartialEq)]
enum T {
    Num,
    Str,
    Bool,
    Undef,
    Null,
    /// A function's parameter and result types. Its `this` is `undefined`:
    /// the generated programs only call functions outside a receiver.
    Arrow(Vec<T>, Box<T>),
    /// An object with these fields, sorted by label.
    Obj(Vec<(String, T)>),
}

/// The property labels the generated programs use.
const LABELS: [&str; 3] = ["a", "b", "c"];

/// What a variable in scope may be used as.
#[derive(Clone, Debug)]
enum Binding {
    Mono(T),
    /// A `let` or a parameter, of one type: it may be assigned.
    Mut(T),
    /// `const id = function (x) { return x; }`: any `(a) => a`.
    PolyId,
    /// Untyped generation doesn't track types.
    Unknown,
    /// Untyped, and assignable: a `let` or a parameter.
    UnknownMut,
}

struct Gen {
    rng: Rng,
    /// The return types of the functions being generated, innermost last
    /// (`None` for an untyped one); empty at the top level.
    funcs: Vec<Option<T>>,
    /// How many loops enclose the point being generated, in the innermost
    /// function (the first entry is the top level's).
    loops: Vec<usize>,
}

impl Gen {
    fn base(&mut self) -> T {
        match self.rng.below(5) {
            0 => T::Num,
            1 => T::Str,
            2 => T::Bool,
            3 => T::Undef,
            _ => T::Null,
        }
    }

    /// An object type with the field `l` of type `t`, and others.
    fn obj_with(&mut self, l: &str, t: &T, depth: usize) -> T {
        let mut fields = vec![(l.to_string(), t.clone())];
        for other in LABELS {
            if other != l && self.rng.chance(30) {
                fields.push((other.to_string(), self.ty(depth.saturating_sub(1))));
            }
        }
        fields.sort_by(|x, y| x.0.cmp(&y.0));
        T::Obj(fields)
    }

    fn label(&mut self) -> String {
        LABELS[self.rng.below(LABELS.len())].to_string()
    }

    fn ty(&mut self, depth: usize) -> T {
        if depth > 0 && self.rng.chance(15) {
            let l = self.label();
            let t = self.ty(depth - 1);
            return self.obj_with(&l, &t, depth);
        }
        if depth > 0 && self.rng.chance(25) {
            let n = self.rng.below(3);
            T::Arrow(
                (0..n).map(|_| self.ty(depth - 1)).collect(),
                b2(self.ty(depth - 1)),
            )
        } else {
            self.base()
        }
    }

    fn num(&mut self) -> Core {
        match self.rng.below(10) {
            0 => Num(15, 1),         // 1.5
            1 => Num(1073741824, 0), // 2^30
            2 => Num(0, 0),
            _ => Num(self.rng.below(100) as u64, 0),
        }
    }

    fn string(&mut self) -> Core {
        const WORDS: [&str; 4] = ["", "a", "ab", "xyz"];
        Str(WORDS[self.rng.below(WORDS.len())].to_string())
    }

    fn literal(&mut self, t: &T) -> Option<Core> {
        Some(match t {
            T::Num => self.num(),
            T::Str => self.string(),
            T::Bool => Bool(self.rng.chance(50)),
            T::Undef => Undef,
            T::Null => Null,
            T::Arrow(..) | T::Obj(_) => return None,
        })
    }

    /// A program of type `t`, mostly well typed.
    fn typed(&mut self, t: &T, depth: usize, scope: &mut Vec<Binding>, stmt: bool) -> Core {
        // A variable of the right type.
        let fits: Vec<usize> = (0..scope.len())
            .filter(|&i| match &scope[scope.len() - 1 - i] {
                Binding::Mono(u) | Binding::Mut(u) => u == t,
                Binding::PolyId => matches!(t, T::Arrow(ps, r) if ps.len() == 1 && ps[0] == **r),
                Binding::Unknown | Binding::UnknownMut => false,
            })
            .collect();
        if !fits.is_empty() && self.rng.chance(if depth == 0 { 80 } else { 30 }) {
            return Var(fits[self.rng.below(fits.len())]);
        }
        // An assignment to a `let` or a parameter of this type, whose value
        // is the assignment's.
        let assignable: Vec<usize> = (0..scope.len())
            .filter(|&i| matches!(&scope[scope.len() - 1 - i], Binding::Mut(u) if u == t))
            .collect();
        if depth > 0 && !assignable.is_empty() && self.rng.chance(20) {
            let i = assignable[self.rng.below(assignable.len())];
            return Assign(i, b(self.typed(t, depth - 1, scope, false)));
        }
        if depth == 0 {
            if let Some(l) = self.literal(t) {
                return l;
            }
        }
        let d = depth.saturating_sub(1);
        if stmt && depth > 0 && self.rng.chance(30) {
            if let Some(s) = self.statement(t, d, scope) {
                return s;
            }
        }
        // A read, or a write, of a property of this type.
        if depth > 0 && self.rng.chance(12) {
            let l = self.label();
            let o = self.obj_with(&l, t, d);
            let obj = self.typed(&o, d, scope, false);
            return if self.rng.chance(70) {
                Get(b(obj), l)
            } else {
                Set(b(obj), l, b(self.typed(t, d, scope, false)))
            };
        }
        if stmt && depth > 0 && self.rng.chance(25) {
            // `const`: sometimes the polymorphic identity, used at
            // several types below.
            if self.rng.chance(30) {
                scope.push(Binding::PolyId);
                let rest = self.typed(t, d, scope, true);
                scope.pop();
                return Let(false, b(Func(1, b(Var(0)))), b(rest));
            }
            // `const`, or `let`, which may be assigned below.
            let s = self.ty(1);
            let e1 = self.typed(&s, d, scope, false);
            let mutable = self.rng.chance(50);
            scope.push(if mutable {
                Binding::Mut(s)
            } else {
                Binding::Mono(s)
            });
            let rest = self.typed(t, d, scope, true);
            scope.pop();
            return Let(mutable, b(e1), b(rest));
        }
        match self.rng.below(6) {
            0 => {
                let c = self.any(d, scope, false);
                Cond(
                    b(c),
                    b(self.typed(t, d, scope, false)),
                    b(self.typed(t, d, scope, false)),
                )
            }
            1 => {
                let n = self.rng.below(3);
                let ss: Vec<T> = (0..n).map(|_| self.ty(1)).collect();
                let f = self.typed(&T::Arrow(ss.clone(), b2(t.clone())), d, scope, false);
                let args = ss.iter().map(|s| self.typed(s, d, scope, false)).collect();
                App(b(f), args)
            }
            _ => match t {
                T::Num => match self.rng.below(4) {
                    0 => Neg(b(self.typed(&T::Num, d, scope, false))),
                    1 => Minus(
                        b(self.typed(&T::Num, d, scope, false)),
                        b(self.typed(&T::Num, d, scope, false)),
                    ),
                    2 => Plus(
                        b(self.typed(&T::Num, d, scope, false)),
                        b(self.typed(&T::Num, d, scope, false)),
                    ),
                    _ => self.num(),
                },
                T::Str => match self.rng.below(3) {
                    0 => Plus(
                        b(self.typed(&T::Str, d, scope, false)),
                        b(self.typed(&T::Str, d, scope, false)),
                    ),
                    1 => Typeof(b(self.any(d, scope, false))),
                    _ => self.string(),
                },
                T::Bool => match self.rng.below(2) {
                    0 => Not(b(self.any(d, scope, false))),
                    _ => Bool(self.rng.chance(50)),
                },
                T::Arrow(ps, r) => {
                    // `this`, the function itself, then the parameters,
                    // the first innermost.
                    scope.push(Binding::Mono(T::Undef));
                    scope.push(Binding::Mono(t.clone()));
                    for p in ps.iter().rev() {
                        scope.push(Binding::Mut(p.clone()));
                    }
                    self.funcs.push(Some((**r).clone()));
                    self.loops.push(0);
                    let body = self.typed(r, d, scope, true);
                    self.loops.pop();
                    self.funcs.pop();
                    scope.truncate(scope.len() - ps.len() - 2);
                    Func(ps.len(), b(body))
                }
                // An object literal, its fields in any order.
                T::Obj(fields) => {
                    let mut fields: Vec<(String, Core)> = fields
                        .iter()
                        .map(|(l, u)| (l.clone(), self.typed(u, d, scope, false)))
                        .collect();
                    if fields.len() > 1 && self.rng.chance(50) {
                        fields.reverse();
                    }
                    Obj(fields)
                }
                _ => self.literal(t).unwrap(),
            },
        }
    }

    /// A statement of type `t` (it completes with a `t`, or not at all):
    /// `return`, `throw`, a sequence, or an `if` with statement branches.
    /// `None` when none fits here.
    fn statement(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Option<Core> {
        let in_func = !self.funcs.is_empty();
        let in_loop = self.loops.last().is_some_and(|&n| n > 0);
        match self.rng.below(9) {
            0 if in_func => {
                let e = match self.funcs.last().cloned().flatten() {
                    Some(rt) => self.typed(&rt, d, scope, false),
                    None => self.any(d, scope, false),
                };
                Some(Ret(b(e)))
            }
            1 => Some(Throw(b(self.any(d, scope, false)))),
            2 => {
                let first = if self.rng.chance(50) {
                    self.any(d, scope, true)
                } else {
                    let s = self.ty(1);
                    self.typed(&s, d, scope, true)
                };
                Some(Seq(b(first), b(self.typed(t, d, scope, true))))
            }
            // An `if` statement only in a function, where its branches end
            // in `return`.
            3 if in_func => {
                let c = self.any(d, scope, false);
                Some(Cond(
                    b(c),
                    b(self.typed(t, d, scope, true)),
                    b(self.typed(t, d, scope, true)),
                ))
            }
            // A counted loop, then the rest.
            4 => {
                let rest = self.typed(t, d, scope, true);
                Some(Seq(b(self.counted_loop(d, scope, false)), b(rest)))
            }
            5 | 6 if in_loop => Some(if self.rng.chance(50) { Break } else { Continue }),
            // Both branches have the type: inty doesn't type a statement's
            // value, but the model does.
            7 => {
                let body = self.typed(t, d, scope, true);
                scope.push(Binding::Unknown);
                let handler = self.typed(t, d, scope, true);
                scope.pop();
                Some(TryCatch(b(body), b(handler)))
            }
            8 => {
                let body = self.typed(t, d, scope, true);
                let s = self.ty(1);
                let fin = self.typed(&s, d, scope, true);
                Some(TryFinally(b(body), b(fin)))
            }
            _ => None,
        }
    }

    /// `let i = n; while (i) { i = i - 1; body }`, whose body may `break` and
    /// `continue`. Typed (`any` false) or not.
    fn counted_loop(&mut self, d: usize, scope: &mut Vec<Binding>, any: bool) -> Core {
        let n = 1 + self.rng.below(3) as u64;
        scope.push(Binding::Mut(T::Num));
        *self.loops.last_mut().unwrap() += 1;
        let body = if any {
            self.any(d, scope, true)
        } else {
            let s = self.ty(1);
            self.typed(&s, d, scope, true)
        };
        *self.loops.last_mut().unwrap() -= 1;
        scope.pop();
        let step = Assign(0, b(Minus(b(Var(0)), b(Num(1, 0)))));
        Let(
            true,
            b(Num(n, 0)),
            b(While(b(Var(0)), b(Seq(b(step), b(body))))),
        )
    }

    /// Any program: types aren't tracked, so many are ill typed.
    fn any(&mut self, depth: usize, scope: &mut Vec<Binding>, stmt: bool) -> Core {
        if depth == 0 || self.rng.chance(20) {
            return match self.rng.below(8) {
                0 if !scope.is_empty() => Var(self.rng.below(scope.len())),
                // Rarely, an unbound variable.
                1 if self.rng.chance(10) => Var(scope.len()),
                2 => self.string(),
                3 => Bool(self.rng.chance(50)),
                4 => Undef,
                5 => Null,
                _ => self.num(),
            };
        }
        let d = depth - 1;
        if stmt && self.rng.chance(20) {
            let in_func = !self.funcs.is_empty();
            let in_loop = self.loops.last().is_some_and(|&n| n > 0);
            match self.rng.below(8) {
                0 if in_func => return Ret(b(self.any(d, scope, false))),
                1 => return Throw(b(self.any(d, scope, false))),
                2 => return Seq(b(self.any(d, scope, true)), b(self.any(d, scope, true))),
                3 if in_func => {
                    return Cond(
                        b(self.any(d, scope, false)),
                        b(self.any(d, scope, true)),
                        b(self.any(d, scope, true)),
                    )
                }
                4 => {
                    let rest = self.any(d, scope, true);
                    return Seq(b(self.counted_loop(d, scope, true)), b(rest));
                }
                5 if in_loop => return if self.rng.chance(50) { Break } else { Continue },
                // `try`/`catch` only where typed: inty doesn't type a
                // statement's value, and two branches of any types would
                // tell the model and inty apart.
                6 => return TryFinally(b(self.any(d, scope, true)), b(self.any(d, scope, true))),
                _ => {}
            }
        }
        match self.rng.below(if stmt { 11 } else { 10 }) {
            0 => {
                let n = self.rng.below(3);
                // `this` and the function's own name can't be assigned;
                // the parameters can.
                scope.push(Binding::Unknown);
                scope.push(Binding::Unknown);
                for _ in 0..n {
                    scope.push(Binding::UnknownMut);
                }
                self.funcs.push(None);
                self.loops.push(0);
                let body = self.any(d, scope, true);
                self.loops.pop();
                self.funcs.pop();
                scope.truncate(scope.len() - n - 2);
                Func(n, b(body))
            }
            1 | 2 => {
                let f = self.any(d, scope, false);
                let n = self.rng.below(3);
                App(b(f), (0..n).map(|_| self.any(d, scope, false)).collect())
            }
            3 => {
                // An assignment to a `let` or a parameter, of any value.
                let assignable: Vec<usize> = (0..scope.len())
                    .filter(|&i| {
                        matches!(
                            &scope[scope.len() - 1 - i],
                            Binding::UnknownMut | Binding::Mut(_)
                        )
                    })
                    .collect();
                if !assignable.is_empty() && self.rng.chance(50) {
                    let i = assignable[self.rng.below(assignable.len())];
                    Assign(i, b(self.any(d, scope, false)))
                } else {
                    Cond(
                        b(self.any(d, scope, false)),
                        b(self.any(d, scope, false)),
                        b(self.any(d, scope, false)),
                    )
                }
            }
            4 if self.rng.chance(40) => {
                let n = self.rng.below(3);
                let fields = (0..n)
                    .map(|_| (self.label(), self.any(d, scope, false)))
                    .collect();
                Obj(fields)
            }
            4 => Not(b(self.any(d, scope, false))),
            5 if self.rng.chance(40) => {
                let o = self.any(d, scope, false);
                let l = self.label();
                if self.rng.chance(60) {
                    Get(b(o), l)
                } else {
                    Set(b(o), l, b(self.any(d, scope, false)))
                }
            }
            5 => Typeof(b(self.any(d, scope, false))),
            6 => Neg(b(self.any(d, scope, false))),
            7 | 8 => Plus(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            9 => Minus(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            _ => {
                let e1 = self.any(d, scope, false);
                let mutable = self.rng.chance(50);
                scope.push(if mutable {
                    Binding::UnknownMut
                } else {
                    Binding::Unknown
                });
                let rest = self.any(d, scope, true);
                scope.pop();
                Let(mutable, b(e1), b(rest))
            }
        }
    }

    fn program(&mut self) -> Core {
        let mut scope = Vec::new();
        if self.rng.chance(65) {
            let t = self.ty(1);
            self.typed(&t, 4, &mut scope, true)
        } else {
            self.any(4, &mut scope, true)
        }
    }
}

fn b2(t: T) -> Box<T> {
    Box::new(t)
}

// ---- Running both sides --------------------------------------------------

/// inty's verdict on a program, in the model's terms.
#[derive(Clone, Debug, PartialEq)]
enum Typing {
    Type(String),
    Reject,
}

/// An interpreter's verdict.
#[derive(Clone, Debug, PartialEq)]
enum Run {
    Value(String),
    /// An uncaught `throw` of this value.
    Thrown(String),
    /// A `return` that escaped to the top (the model only; typing rules it out).
    Returned(String),
    Stuck(String),
    Timeout,
    Unsupported,
    /// The engine raised its own error (a `TypeError`, say).
    NativeError(String),
    /// The engine hit a resource limit: its stack, a string's length, time.
    Limit,
}

fn core_type(t: &Type) -> String {
    match t {
        Type::Number | Type::Int | Type::Literal(LitValue::Number(_)) => "number".into(),
        Type::String | Type::Literal(LitValue::String(_)) => "string".into(),
        Type::Boolean | Type::Literal(LitValue::Bool(_)) => "boolean".into(),
        Type::Undefined => "undefined".into(),
        Type::Null => "null".into(),
        Type::Func { .. } => "fun".into(),
        Type::Row(_) if t.as_callable().is_some() => "fun".into(),
        Type::Row(_) => "obj".into(),
        Type::Var(_) => "var".into(),
        // The empty union: what doesn't complete, such as a `throw`.
        Type::Union(ts) if ts.is_empty() => "never".into(),
        Type::Union(ts) => {
            let parts: Vec<String> = ts.iter().map(core_type).collect();
            if parts.iter().all(|p| p == &parts[0]) {
                parts[0].clone()
            } else {
                format!("union({})", parts.join("|"))
            }
        }
        other => format!("other({})", other),
    }
}

/// Features inty's typing used that the model doesn't have yet, read off
/// the types inty gave the program's expressions.
type Features = std::collections::BTreeSet<&'static str>;

/// A function type's number of parameters: a `Func`'s, or a row's call
/// signature's.
fn param_count(t: &Type) -> Option<usize> {
    match t {
        Type::Func { params, .. } => Some(params.len()),
        Type::Row(row) => row.props.values().find_map(|f| param_count(&f.ty)),
        _ => None,
    }
}

/// The parameters of the function literal written at the start of `text`
/// (`(function f(x, y) { …`), as the generator prints them.
fn literal_arity(text: &str) -> Option<usize> {
    let text = text.strip_prefix('(').unwrap_or(text);
    let rest = text.strip_prefix("function ")?;
    let open = rest.find('(')?;
    let close = rest[open..].find(')')? + open;
    let params = rest[open + 1..close].trim();
    Some(if params.is_empty() {
        0
    } else {
        params.split(',').count()
    })
}

fn inty_typing(program: &inty::ast::Program, source: &str) -> (Typing, Features) {
    let mut state = InferState::new();
    state.expr_types = Some(std::collections::HashMap::new());
    // As the CLI checks: infer, then resolve the class constraints.
    let mut errors = Vec::new();
    let typing = match state.infer_program(&initial_env(), program) {
        Ok(ty) => {
            errors.extend(state.take_errors().iter().map(|e| e.to_string()));
            if let Err(e) = state.resolve_constraints() {
                errors.push(e.to_string());
            }
            if errors.is_empty() {
                Typing::Type(core_type(&state.apply_subst(&ty)))
            } else {
                Typing::Reject
            }
        }
        Err(e) => {
            errors.push(e.to_string());
            Typing::Reject
        }
    };
    // The evidence: the types inty gave the program's expressions, and its
    // errors (inference may stop before recording the types that show it).
    let expr_types = state.expr_types.take().unwrap_or_default();
    // A function literal typed with more parameters than it has: inty
    // checks a literal against the function type expected of it, and
    // lets it ignore the extra arguments, as JavaScript does.
    let fewer_params = expr_types.iter().any(|(&(start, end), ty)| {
        let Some(arity) = source.get(start..end).and_then(literal_arity) else {
            return false;
        };
        param_count(&state.flatten_type(ty)).is_some_and(|n| n > arity)
    });
    let mut shown: Vec<String> = expr_types
        .values()
        .map(|ty| format!("{}", state.flatten_type(ty)))
        .collect();
    shown.extend(errors);
    let mut features = Features::new();
    if fewer_params {
        features.insert("fewer parameters");
    }
    for text in &shown {
        if text.contains('μ') {
            features.insert("recursive types");
        }
        if text.contains(" | ") {
            features.insert("unions");
        }
        if text.contains("never") {
            features.insert("never");
        }
    }
    (typing, features)
}

fn number_wire(n: f64) -> String {
    // One NaN, whatever its payload.
    let n = if n.is_nan() { f64::NAN } else { n };
    format!("num {}", n.to_bits())
}

fn value_wire(v: Value) -> String {
    match v {
        Value::Number(n) => number_wire(n),
        Value::String(s) => format!("str s:{}", s),
        Value::Boolean(v) => format!("bool {}", v),
        Value::Undefined => "undef".into(),
        Value::Null => "null".into(),
        Value::Closure(_) | Value::Builtin(_) => "fun".into(),
        Value::Object(_) => "obj".into(),
        other => format!("other {}", other),
    }
}

fn inty_run(program: &inty::ast::Program) -> Run {
    match run_to_end_with_fuel(program, 1_500) {
        Ok(v) => Run::Value(value_wire(v)),
        Err(Stuck::UncaughtThrow(v)) => Run::Thrown(value_wire(v)),
        Err(Stuck::FuelExhausted) => Run::Timeout,
        Err(Stuck::NotImplemented(_)) => Run::Unsupported,
        Err(Stuck::UndefinedVariable(_)) => Run::Stuck("undefinedVariable".into()),
        Err(Stuck::NotCallable(_)) => Run::Stuck("notCallable".into()),
        Err(Stuck::TypeMismatch { .. }) => Run::Stuck("typeMismatch".into()),
        Err(Stuck::ArityMismatch { .. }) => Run::Stuck("arityMismatch".into()),
        Err(Stuck::NotIndexable(_)) => Run::Stuck("notIndexable".into()),
        Err(Stuck::PropertyNotFound { .. }) => Run::Stuck("propertyNotFound".into()),
        Err(Stuck::BadAssignmentTarget) => Run::Stuck("badAssignmentTarget".into()),
        Err(other) => Run::Stuck(format!("other {}", other)),
    }
}

/// An interpreter's verdict in the model's wire format (`value V`,
/// `thrown V`, ...), as both the model and the engine print it.
fn parse_run(run: &str) -> Run {
    // Canonicalise NaN the same way as inty's side.
    let value = |v: &str| match v.strip_prefix("num ") {
        Some(bits) => number_wire(f64::from_bits(bits.parse().expect(run))),
        None => v.to_string(),
    };
    if run == "timeout" {
        Run::Timeout
    } else if run == "limit" {
        Run::Limit
    } else if let Some(v) = run.strip_prefix("value ") {
        Run::Value(value(v))
    } else if let Some(v) = run.strip_prefix("thrown ") {
        Run::Thrown(value(v))
    } else if let Some(v) = run.strip_prefix("returned ") {
        Run::Returned(value(v))
    } else if let Some(name) = run.strip_prefix("error ") {
        Run::NativeError(name.to_string())
    } else {
        Run::Stuck(run.strip_prefix("stuck ").expect(run).to_string())
    }
}

fn parse_model_line(line: &str) -> (Typing, Run) {
    let (typing, run) = line
        .split_once(';')
        .unwrap_or_else(|| panic!("bad model line: {line}"));
    let typing = match typing {
        "reject" => Typing::Reject,
        t => Typing::Type(t.strip_prefix("type ").expect(line).to_string()),
    };
    (typing, parse_run(run))
}

/// Run a process on one line per input, and read its one line per input.
fn run_lines(mut command: Command, what: &str, input: String, n: usize) -> Vec<String> {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("start {what}: {e}"));
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || {
        stdin.write_all(input.as_bytes()).unwrap();
    });
    let out: Vec<String> = BufReader::new(child.stdout.take().unwrap())
        .lines()
        .map(|l| l.unwrap())
        .collect();
    writer.join().unwrap();
    assert!(child.wait().unwrap().success(), "{what} failed");
    assert_eq!(out.len(), n, "{what} answered too few lines");
    out
}

/// Run the model on every program, in one process.
fn run_model(model: &PathBuf, programs: &[Core]) -> Vec<(Typing, Run)> {
    let input: String = programs.iter().map(|p| wire(p) + "\n").collect();
    if let Some(path) = std::env::var_os("INTY_DIFF_DUMP") {
        std::fs::write(path, &input).unwrap();
    }
    run_lines(Command::new(model), "inty-model", input, programs.len())
        .iter()
        .map(|l| parse_model_line(l))
        .collect()
}

/// Run every program in a JavaScript engine (`tests/differential/engine.js`
/// under Node, or `INTY_NODE`), in one process. `None` when there is no
/// engine; on CI that fails the test instead.
fn run_engine(sources: &[String]) -> Option<Vec<Run>> {
    let node = std::env::var_os("INTY_NODE").unwrap_or_else(|| "node".into());
    if Command::new(&node).arg("--version").output().is_err() {
        assert!(
            std::env::var_os("CI").is_none(),
            "no JavaScript engine ({node:?}) on CI"
        );
        return None;
    }
    let script = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/differential/engine.js");
    let mut command = Command::new(node);
    command.arg(script);
    // The generated JavaScript is one line per program.
    let input: String = sources.iter().map(|s| s.clone() + "\n").collect();
    Some(
        run_lines(command, "the JavaScript engine", input, sources.len())
            .iter()
            .map(|l| parse_run(l))
            .collect(),
    )
}

fn model_path() -> Option<PathBuf> {
    let path = match std::env::var_os("INTY_LEAN_MODEL") {
        Some(p) => PathBuf::from(p),
        None => {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean/.lake/build/bin/inty-model")
        }
    };
    path.exists().then_some(path)
}

fn env_or(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

// ---- Comparing -----------------------------------------------------------

/// A disagreement the model is known not to cover yet, or `None`. Each is
/// an acceptance by inty of a program the model rejects, explained by a
/// feature inty's types show it used.
fn known_divergence(inty: &Typing, features: &Features, model: &Typing) -> Option<&'static str> {
    match (inty, model) {
        // Roadmap phase 6: `c ? 1 : null` is `Number | Null` in inty, and
        // `c ? undefined : x` is `Undefined | t`, where the model unifies.
        (Typing::Type(_), Typing::Reject) if features.contains("unions") => {
            Some("unions (a nullable join)")
        }
        (Typing::Type(t), Typing::Type(_)) if t.starts_with("union(") => {
            Some("unions (a nullable join)")
        }
        // Roadmap phase 10 (optional parameters): a function literal with
        // fewer parameters than the function type expected of it, which
        // ignores the extra arguments, as JavaScript does.
        (Typing::Type(_), Typing::Reject) if features.contains("fewer parameters") => {
            Some("fewer parameters than the expected function type")
        }
        // Roadmap phase 8: `function f(x) { return f; }`.
        (Typing::Type(_), Typing::Reject) if features.contains("recursive types") => {
            Some("equi-recursive types")
        }
        // inty types what never returns (a function that only throws)
        // `never`, the empty union, which unifies with nothing else and
        // can't be called, as in TypeScript; the model leaves it a free
        // type variable.
        (Typing::Reject, Typing::Type(_)) if features.contains("never") => {
            Some("never (a function that only throws)")
        }
        (Typing::Type(t), Typing::Type(_)) if t == "never" => {
            Some("never (a function that only throws)")
        }
        // The model types a program that can't complete normally (it only
        // throws, or a function in it falls off its end only after a
        // `throw`) with a free type variable, which no value has; inty
        // gives it a type of its own, such as `undefined` for a function
        // body that ends in a statement.
        (Typing::Type(_), Typing::Type(m)) if m == "var" => {
            Some("what doesn't complete (the model's free type variable)")
        }
        // Roadmap phase 5, the other way: the model folds `Int` into
        // `number`, but in inty `Int ≤ Number` holds for values only, so
        // `(a) => Int` and `(b) => Number` don't join. Evidence: inty
        // accepts the program once no literal is an `Int`.
        (Typing::Reject, Typing::Type(_)) if features.contains("Int") => {
            Some("Int and Number (the model has only number)")
        }
        // inty's nullable join (`c ? undefined : x` is `Undefined | t`
        // even for an unknown `t`) can make an HM-typable program an
        // infinite type, or fail to unify.
        (Typing::Reject, Typing::Type(_)) if features.contains("unions") => {
            Some("unions (inty's nullable join rejects an HM-typable program)")
        }
        _ => None,
    }
}

#[test]
fn inty_agrees_with_the_lean_model() {
    let Some(model) = model_path() else {
        eprintln!("skipping differential test: no inty-model (cd lean && lake build)");
        return;
    };
    let cases = env_or("INTY_DIFF_CASES", 3000) as usize;
    let seed = env_or("INTY_DIFF_SEED", 0x1d1f_f00d);
    // splitmix64, so nearby seeds give unrelated programs.
    let mut z = seed.wrapping_add(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    let mut gen = Gen {
        rng: Rng((z ^ (z >> 31)) | 1),
        funcs: Vec::new(),
        loops: vec![0],
    };
    let programs: Vec<Core> = (0..cases).map(|_| gen.program()).collect();
    let answers = run_model(&model, &programs);
    let sources: Vec<String> = programs.iter().map(javascript).collect();
    let engine = run_engine(&sources);
    if engine.is_none() {
        eprintln!("no JavaScript engine (node): not comparing with one");
    }

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut known: BTreeMap<&str, (usize, String)> = BTreeMap::new();
    let mut failures = Vec::new();
    let mut engine_stuck: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for (i, (core, (model_typing, model_run))) in programs.iter().zip(answers).enumerate() {
        let js = sources[i].clone();
        let engine_run = engine.as_ref().map(|e| e[i].clone());
        if std::env::var_os("INTY_DIFF_TRACE").is_some() {
            eprintln!("{js}");
        }
        // Parsing, inference and the recursive dynamics need inty's big
        // stack.
        let source = js.clone();
        let fractional_source = javascript(&fractional(core));
        let (typing, features, run) =
            inty::worker::run_with_inference_stack("inty-differential", move || {
                let parse = |src: &str| {
                    inty::frontends::javascript::parse_source(src).unwrap_or_else(|e| {
                        panic!("generated JavaScript doesn't parse: {e}\n{src}")
                    })
                };
                let program = parse(&source);
                let (typing, mut features) = inty_typing(&program, &source);
                if typing == Typing::Reject
                    && matches!(
                        inty_typing(&parse(&fractional_source), &fractional_source).0,
                        Typing::Type(_)
                    )
                {
                    features.insert("Int");
                }
                (typing, features, inty_run(&program))
            });
        let report = |what: &str| {
            format!(
                "{what}\n  js:     {js}\n  core:   {}\n  inty:   {:?} / {:?}\n  model:  {:?} / {:?}\n  engine: {:?}",
                wire(core),
                typing,
                run,
                model_typing,
                model_run,
                engine_run
            )
        };
        let accepted = matches!(typing, Typing::Type(_));
        let model_accepted = matches!(model_typing, Typing::Type(_));
        *counts
            .entry(format!(
                "inty {}, model {}",
                if accepted { "accepts" } else { "rejects" },
                match model_typing {
                    Typing::Type(_) => "accepts",
                    _ => "rejects",
                }
            ))
            .or_default() += 1;

        // Soundness.
        if accepted && matches!(run, Run::Stuck(_)) {
            failures.push(report("inty accepts a program that gets stuck"));
        }
        if model_accepted && matches!(model_run, Run::Stuck(_)) {
            failures.push(report(
                "the model accepts a program that gets stuck (harness bug)",
            ));
        }
        // Semantics: both finished, so they must agree.
        let finished = |r: &Run| matches!(r, Run::Value(_) | Run::Stuck(_) | Run::Thrown(_));
        if finished(&run) && finished(&model_run) && run != model_run {
            failures.push(report("the interpreters disagree"));
        }
        // The engine. Where an interpreter finishes, the engine agrees; a
        // program inty or the model accepts raises no native error (it may
        // still exhaust a resource, as unbounded recursion does).
        if let Some(engine_run) = &engine_run {
            let finished = |r: &Run| matches!(r, Run::Value(_) | Run::Thrown(_));
            if finished(&run) && &run != engine_run {
                failures.push(report("inty's dynamics and the engine disagree"));
            }
            if finished(&model_run) && &model_run != engine_run {
                failures.push(report("the model and the engine disagree"));
            }
            if let Run::NativeError(name) = engine_run {
                if accepted {
                    failures.push(report(&format!(
                        "inty accepts a program that raises {name}"
                    )));
                }
                if model_accepted {
                    failures.push(report(&format!(
                        "the model accepts a program that raises {name}"
                    )));
                }
            }
            // Where the dynamics gets stuck, JavaScript raises an error or
            // coerces; count which.
            if let Run::Stuck(why) = &run {
                let what = match engine_run {
                    Run::NativeError(name) => format!("raises {name}"),
                    Run::Limit => "hits a limit".into(),
                    _ => "coerces".into(),
                };
                let entry = engine_stuck
                    .entry(format!("{why}: the engine {what}"))
                    .or_insert((0, js.clone()));
                entry.0 += 1;
                if js.len() < entry.1.len() {
                    entry.1 = js.clone();
                }
            }
        }

        // Typing. inty's `never` (what doesn't complete) is the model's
        // unconstrained type variable.
        let same = typing == model_typing
            || (typing == Typing::Type("never".into())
                && model_typing == Typing::Type("var".into()))
            // A program ending in a statement: compare acceptance only.
            || (ends_in_statement(core) && accepted && model_accepted);
        if !same && (accepted || model_accepted) {
            match known_divergence(&typing, &features, &model_typing) {
                Some(why) => {
                    let entry = known.entry(why).or_insert((0, report(why)));
                    entry.0 += 1;
                }
                None => failures.push(report("inty and the model type it differently")),
            }
        }
    }

    eprintln!("{cases} programs (seed {seed:#x}):");
    for (k, n) in &counts {
        eprintln!("  {n:5}  {k}");
    }
    if !engine_stuck.is_empty() {
        eprintln!("where inty's dynamics gets stuck:");
        for (k, (n, example)) in &engine_stuck {
            eprintln!("  {n:5}  {k}, as in\n           {example}");
        }
    }
    for (why, (n, example)) in &known {
        eprintln!("  {n:5}  known divergence: {why}; for example\n{example}");
    }
    let shown: Vec<&String> = failures.iter().take(10).collect();
    assert!(
        failures.is_empty(),
        "{} disagreements; the first {}:\n\n{}",
        failures.len(),
        shown.len(),
        shown
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    );
}
