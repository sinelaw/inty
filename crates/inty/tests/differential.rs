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
//! or `INTY_LEAN_MODEL`. Without it the test is skipped, unless
//! `INTY_REQUIRE_MODEL` is set (as CI does), which fails it. `INTY_DIFF_CASES`
//! sets the number of programs (default 3000), `INTY_DIFF_SEED` the seed,
//! and `INTY_DIFF_SUMS=1` prints each disagreement on a program with a sum
//! (`T | Null`, `T | Undefined`, a variant) or a test for nothing (`!= null`,
//! `??`) or of a variant's tag.
//! The engine is `node` (or `INTY_NODE`) running `tests/differential/engine.js`;
//! without it the engine comparison is skipped, except on CI.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use inty::builtins::initial_env;
use inty::infer::InferState;
use inty::types::Type;

mod oracle;
use oracle::*;

// ---- The core calculus ---------------------------------------------------

/// The operators beside `+` and `-`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Op2 {
    Times,
    Div,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Op2 {
    const NUMERIC: [Op2; 2] = [Op2::Times, Op2::Div];
    const COMPARE: [Op2; 4] = [Op2::Lt, Op2::Le, Op2::Gt, Op2::Ge];

    fn wire(self) -> &'static str {
        match self {
            Op2::Times => "times",
            Op2::Div => "div",
            Op2::Lt => "lt",
            Op2::Le => "le",
            Op2::Gt => "gt",
            Op2::Ge => "ge",
            Op2::Eq => "eq",
            Op2::Ne => "ne",
        }
    }

    fn js(self) -> &'static str {
        match self {
            Op2::Times => "*",
            Op2::Div => "/",
            Op2::Lt => "<",
            Op2::Le => "<=",
            Op2::Gt => ">",
            Op2::Ge => ">=",
            Op2::Eq => "===",
            Op2::Ne => "!==",
        }
    }
}

/// A variant's tag: the string or the boolean its tag field holds.
#[derive(Clone, Debug, PartialEq)]
enum Tag {
    Str(String),
    Bool(bool),
}

impl Tag {
    /// The tag as JavaScript writes it, a literal.
    fn js(&self) -> String {
        match self {
            Tag::Str(s) => format!("{s:?}"),
            Tag::Bool(b) => b.to_string(),
        }
    }
    /// The tag in the wire format's `casetag`.
    fn wire(&self) -> String {
        match self {
            Tag::Str(s) => format!("s:{s}"),
            Tag::Bool(b) => b.to_string(),
        }
    }
    /// The type of a tag field holding it, in the wire format.
    fn wire_ty(&self) -> String {
        match self {
            Tag::Str(s) => format!("(strlit s:{s})"),
            Tag::Bool(b) => format!("(boollit {b})"),
        }
    }
    /// The literal holding it.
    fn core(&self) -> Core {
        match self {
            Tag::Str(s) => Str(s.clone()),
            Tag::Bool(b) => Bool(*b),
        }
    }
}

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
    /// A method `l(x₀, …) { body }`, only as an object literal's field:
    /// it runs as `l: function (…) { body }` does, but has no name of its
    /// own (its body never refers to variable `n`), and inty types its
    /// `this` as the literal itself.
    Method(usize, Box<Core>),
    /// A getter `get l() { body }`, only as an object literal's field: a
    /// method of no parameters (`this` is variable 1) run when `l` is read.
    Getter(Box<Core>),
    /// A call outside any receiver, so `this` is `undefined`.
    App(Box<Core>, Vec<Core>),
    /// `const v = e₁; e₂` (`false`) or `let v = e₁; e₂` (`true`); only in
    /// statement position. An annotation `/** const v: T */` declares
    /// `v`'s type.
    Let(bool, Option<T>, Box<Core>, Box<Core>),
    /// `x = e`, for a `let` or a parameter.
    Assign(usize, Box<Core>),
    Cond(Box<Core>, Box<Core>, Box<Core>),
    Not(Box<Core>),
    Typeof(Box<Core>),
    Neg(Box<Core>),
    Plus(Box<Core>, Box<Core>),
    Minus(Box<Core>, Box<Core>),
    /// `*`, `/`, a comparison, `===` or `!==`.
    Bin(Op2, Box<Core>, Box<Core>),
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
    /// `{...e₁, ...e₂}`.
    Spread(Box<Core>, Box<Core>),
    /// An array literal `[e₀, …]`.
    Arr(Vec<Core>),
    /// `e[i]`.
    Index(Box<Core>, Box<Core>),
    /// `e[i] = v`.
    SetIndex(Box<Core>, Box<Core>, Box<Core>),
    /// `e.l(a₀, …)`: a method call, with `e` as `this`.
    MCall(Box<Core>, String, Vec<Core>),
    /// A class of a constructor of `n` parameters, `ctor n (cls …)`: its
    /// members in order, each a field (`this.l = e;` in the constructor,
    /// seeing the fields before it, the latest innermost), an arrow field
    /// (`this.l = (…) => {…};`, a `Func` whose `this` is the instance and
    /// which never refers to itself), a method or a getter (on the
    /// prototype, a `Func` that sees no constructor parameter). Only as a
    /// `const`'s value, printed as a class declaration; the constructor's
    /// `this` and the class itself are never referred to inside it.
    Class(usize, Vec<(String, Member, Core)>),
    /// `new f(a₀, …)`.
    New(Box<Core>, Vec<Core>),
    /// `const v = e₁; v != null ? e₃ : e₂`, with `v` bound in `e₃`; only
    /// in statement position. `e₁ ?? e₂` is `Unwrap(e₁, e₂, Var(0))`.
    Unwrap(Box<Core>, Box<Core>, Box<Core>),
    /// `const v = e₁; v.l === "t" ? e₃ : e₂`, a variant tagged by `l` taken
    /// apart by its tag: `v` bound in both branches, in `e₃` as the case of
    /// the tag `t`, in `e₂` as the rest; only in statement position.
    CaseTag(Box<Core>, String, Tag, Box<Core>, Box<Core>),
    /// `const v = e₁; typeof v === "t" ? e₃ : e₂`, a sum told apart by
    /// `typeof` taken apart by its tag: `v` bound in both branches, in `e₃`
    /// as the case of the tag `t`, in `e₂` as the rest; only in statement
    /// position.
    TypeTest(Box<Core>, String, Box<Core>, Box<Core>),
}

/// How a class holds a member.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Member {
    Field,
    Arrow,
    Method,
    Getter,
}

use Core::*;

fn b(e: Core) -> Box<Core> {
    Box::new(e)
}

/// Whether the model takes `t` as an annotation: a type without records,
/// whose labels are the program's.
fn annotatable(t: &T) -> bool {
    match t {
        T::Num | T::Str | T::Bool | T::Undef | T::Null | T::StrLit(_) => true,
        T::Arrow(ps, r) => ps.iter().all(annotatable) && annotatable(r),
        T::Arr(t) | T::Maybe(_, t) => annotatable(t),
        T::Variant(_, cases) => cases
            .iter()
            .all(|(_, fs)| fs.iter().all(|(_, t)| annotatable(t))),
        // Only the polymorphic identity's annotation has variables.
        T::Sum(arms) => arms.iter().all(annotatable),
        T::Obj(_) | T::TVar(_) => false,
    }
}

/// A type in the wire format.
fn wire_ty(t: &T) -> String {
    match t {
        T::Num => "number".to_string(),
        T::Str => "string".to_string(),
        T::Bool => "boolean".to_string(),
        T::Undef => "undefined".to_string(),
        T::Null => "null".to_string(),
        T::Arrow(ps, r) => {
            let mut parts = vec!["fn".to_string(), wire_ty(r)];
            parts.extend(ps.iter().map(wire_ty));
            format!("({})", parts.join(" "))
        }
        T::Arr(t) => format!("(arr {})", wire_ty(t)),
        T::Maybe(true, t) => format!("(nullable {})", wire_ty(t)),
        T::Maybe(false, t) => format!("(optional {})", wire_ty(t)),
        T::TVar(i) => format!("(tv {})", i),
        T::StrLit(s) => format!("(strlit s:{s})"),
        T::Variant(l, cases) => {
            let cases: Vec<String> = cases
                .iter()
                .map(|(tag, fs)| {
                    let mut fields = vec![(l.clone(), tag.wire_ty())];
                    fields.extend(fs.iter().map(|(f, t)| (f.clone(), wire_ty(t))));
                    fields.sort();
                    let fields: Vec<String> = fields
                        .iter()
                        .map(|(f, t)| format!(" (s:{f} {t})"))
                        .collect();
                    format!(" (rec{})", fields.concat())
                })
                .collect();
            format!("(variant s:{}{})", l, cases.concat())
        }
        T::Sum(arms) => {
            let arms: Vec<String> = arms.iter().map(|t| format!(" {}", wire_ty(t))).collect();
            format!("(sum{})", arms.concat())
        }
        // Only as a sum's case.
        T::Obj(fs) => {
            let fields: Vec<String> = fs
                .iter()
                .map(|(f, t)| format!(" (s:{f} {})", wire_ty(t)))
                .collect();
            format!("(rec{})", fields.concat())
        }
    }
}

/// A type as inty's annotations write it.
fn js_ty(t: &T) -> String {
    match t {
        T::Num => "Number".to_string(),
        T::Str => "String".to_string(),
        T::Bool => "Boolean".to_string(),
        T::Undef => "Undefined".to_string(),
        T::Null => "Null".to_string(),
        T::Arrow(ps, r) => format!(
            "(({}) => {})",
            ps.iter().map(js_ty).collect::<Vec<_>>().join(", "),
            js_ty(r)
        ),
        T::Arr(t) => format!("{}[]", js_ty(t)),
        T::Maybe(true, t) => format!("({} | Null)", js_ty(t)),
        T::Maybe(false, t) => format!("({} | Undefined)", js_ty(t)),
        T::TVar(i) => tvar_name(*i),
        T::StrLit(s) => format!("{s:?}"),
        T::Variant(l, cases) => {
            let cases: Vec<String> = cases
                .iter()
                .map(|(tag, fs)| {
                    let mut fields = vec![format!("{l}: {}", tag.js())];
                    fields.extend(fs.iter().map(|(f, t)| format!("{f}: {}", js_ty(t))));
                    format!("{{{}}}", fields.join(", "))
                })
                .collect();
            format!("({})", cases.join(" | "))
        }
        T::Sum(arms) => format!(
            "({})",
            arms.iter().map(js_ty).collect::<Vec<_>>().join(" | ")
        ),
        T::Obj(fs) => format!(
            "{{{}}}",
            fs.iter()
                .map(|(f, t)| format!("{f}: {}", js_ty(t)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// A polymorphic annotation's quantified variable `i`'s name.
fn tvar_name(i: usize) -> String {
    char::from(b'a' + i as u8).to_string()
}

/// How many variables an annotation quantifies: one past the greatest.
fn tvar_count(t: &T) -> usize {
    match t {
        T::TVar(i) => i + 1,
        T::Arrow(ps, r) => ps
            .iter()
            .map(tvar_count)
            .chain([tvar_count(r)])
            .max()
            .unwrap_or(0),
        T::Arr(t) | T::Maybe(_, t) => tvar_count(t),
        T::Obj(fs) => fs.iter().map(|(_, t)| tvar_count(t)).max().unwrap_or(0),
        T::Variant(_, cases) => cases
            .iter()
            .flat_map(|(_, fs)| fs.iter().map(|(_, t)| tvar_count(t)))
            .max()
            .unwrap_or(0),
        T::Sum(arms) => arms.iter().map(tvar_count).max().unwrap_or(0),
        T::Num | T::Str | T::Bool | T::Undef | T::Null | T::StrLit(_) => 0,
    }
}

/// An annotation as inty reads it: a polymorphic one says its
/// quantified variables, `<a, b>(a) => b`.
fn js_scheme(t: &T) -> String {
    match (tvar_count(t), t) {
        (0, _) => js_ty(t),
        (n, T::Arrow(ps, r)) => format!(
            "<{}>({}) => {}",
            (0..n).map(tvar_name).collect::<Vec<_>>().join(", "),
            ps.iter().map(js_ty).collect::<Vec<_>>().join(", "),
            js_ty(r)
        ),
        (n, _) => format!(
            "<{}>{}",
            (0..n).map(tvar_name).collect::<Vec<_>>().join(", "),
            js_ty(t)
        ),
    }
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
        Func(n, body) | Method(n, body) => format!("(func {} {})", n, wire(body)),
        Getter(body) => format!("(func 0 {})", wire(body)),
        App(f, args) => {
            let args: Vec<String> = args.iter().map(wire).collect();
            format!(
                "(app {}{}{})",
                wire(f),
                if args.is_empty() { "" } else { " " },
                args.join(" ")
            )
        }
        Let(m, None, e1, e2) => format!(
            "({} {} {})",
            if *m { "letmut" } else { "let" },
            wire(e1),
            wire(e2)
        ),
        Let(false, Some(t), e1, e2) if tvar_count(t) > 0 => format!(
            "(letpoly {} {} {} {})",
            tvar_count(t),
            wire_ty(t),
            wire(e1),
            wire(e2)
        ),
        Let(m, Some(t), e1, e2) => format!(
            "({} {} {} {})",
            if *m { "letmutann" } else { "letann" },
            wire_ty(t),
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
        Bin(o, x, y) => format!("({} {} {})", o.wire(), wire(x), wire(y)),
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
                .map(|(l, e)| {
                    let kind = match e {
                        Method(..) => "method",
                        Getter(_) => "getter",
                        _ => "field",
                    };
                    format!(" ({} s:{} {})", kind, l, wire(e))
                })
                .collect();
            format!("(obj{})", fields.concat())
        }
        Get(e, l) => format!("(get {} s:{})", wire(e), l),
        Set(e, l, v) => format!("(set {} s:{} {})", wire(e), l, wire(v)),
        Spread(x, y) => format!("(spread {} {})", wire(x), wire(y)),
        Arr(es) => {
            let es: Vec<String> = es.iter().map(|e| format!(" {}", wire(e))).collect();
            format!("(arr{})", es.concat())
        }
        Index(e, i) => format!("(index {} {})", wire(e), wire(i)),
        SetIndex(e, i, v) => format!("(setindex {} {} {})", wire(e), wire(i), wire(v)),
        MCall(e, l, args) => {
            let args: Vec<String> = args.iter().map(|a| format!(" {}", wire(a))).collect();
            format!("(mcall {} s:{}{})", wire(e), l, args.concat())
        }
        Class(n, members) => {
            let members: Vec<String> = members
                .iter()
                .map(|(l, m, e)| {
                    let kind = match m {
                        Member::Field => "field",
                        Member::Arrow => "arrow",
                        Member::Method => "method",
                        Member::Getter => "getter",
                    };
                    format!(" ({} s:{} {})", kind, l, wire(e))
                })
                .collect();
            format!("(ctor {} (class{}))", n, members.concat())
        }
        New(f, args) => {
            let args: Vec<String> = args.iter().map(|a| format!(" {}", wire(a))).collect();
            format!("(new {}{})", wire(f), args.concat())
        }
        Unwrap(x, y, z) => format!("(unwrap {} {} {})", wire(x), wire(y), wire(z)),
        CaseTag(x, l, t, y, z) => format!(
            "(casetag {} s:{} {} {} {})",
            wire(x),
            l,
            t.wire(),
            wire(y),
            wire(z)
        ),
        TypeTest(x, t, y, z) => format!("(typetest {} s:{} {} {})", wire(x), t, wire(y), wire(z)),
    }
}

/// Whether a program ends in a statement rather than an expression: inty
/// then types the program `Undefined`, whatever the statement.
fn ends_in_statement(e: &Core) -> bool {
    match e {
        Let(_, _, _, rest) | Seq(_, rest) => ends_in_statement(rest),
        Throw(_) | Ret(_) | While(..) | Break | Continue | TryCatch(..) | TryFinally(..) => true,
        Cond(_, t, f) | Unwrap(_, t, f) | CaseTag(_, _, _, t, f) | TypeTest(_, _, t, f) => {
            is_stmt(t) || is_stmt(f)
        }
        _ => false,
    }
}

/// Whether `e` must be printed as statements: JavaScript has no expression
/// form for it.
fn is_stmt(e: &Core) -> bool {
    match e {
        Ret(_) | Throw(_) | Seq(..) | Let(..) | While(..) | Break | Continue | TryCatch(..)
        | TryFinally(..) | Unwrap(..) | CaseTag(..) | TypeTest(..) => true,
        Cond(_, t, f) => is_stmt(t) || is_stmt(f),
        _ => false,
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
                let (f, rest) = self.function(*n, body);
                format!("(function {}{})", f, rest)
            }
            Method(..) | Getter(_) => {
                unreachable!("a method only as an object literal's field: {e:?}")
            }
            App(f, args) => {
                let args: Vec<String> = args.iter().map(|a| self.expr(a)).collect();
                // A call of a property is a method call in JavaScript,
                // with the object as `this`; the calculus's calls have no
                // receiver, as `(0, o.f)(…)` hasn't.
                let callee = match **f {
                    Get(..) | Index(..) => format!("(0, {})", self.expr(f)),
                    // A class's field read in a later one's initialiser,
                    // `this.l`.
                    Var(i) if self.name(i).contains('.') => format!("(0, {})", self.expr(f)),
                    _ => format!("({})", self.expr(f)),
                };
                format!("{}({})", callee, args.join(", "))
            }
            Let(..) | Ret(_) | Throw(_) | Seq(..) | While(..) | Break | Continue | TryCatch(..)
            | TryFinally(..) | Unwrap(..) | CaseTag(..) | TypeTest(..) => {
                unreachable!("statements only in statement position: {e:?}")
            }
            Assign(i, e) => format!("({} = {})", self.name(*i), self.expr(e)),
            Cond(c, t, e) => format!("({} ? {} : {})", self.expr(c), self.expr(t), self.expr(e)),
            Not(e) => format!("!({})", self.expr(e)),
            Typeof(e) => format!("typeof ({})", self.expr(e)),
            Neg(e) => format!("-({})", self.expr(e)),
            Plus(x, y) => format!("({} + {})", self.expr(x), self.expr(y)),
            Minus(x, y) => format!("({} - {})", self.expr(x), self.expr(y)),
            Bin(o, x, y) => format!("({} {} {})", self.expr(x), o.js(), self.expr(y)),
            Obj(fields) => {
                let fields: Vec<String> = fields
                    .iter()
                    .map(|(l, e)| match e {
                        // `l(…) { … }`: the function's name is never used.
                        Method(n, body) => format!("{}{}", l, self.function(*n, body).1),
                        Getter(body) => format!("get {}{}", l, self.function(0, body).1),
                        _ => format!("{}: {}", l, self.expr(e)),
                    })
                    .collect();
                format!("({{{}}})", fields.join(", "))
            }
            Get(e, l) => format!("({}).{}", self.expr(e), l),
            Set(e, l, v) => format!("(({}).{} = {})", self.expr(e), l, self.expr(v)),
            Spread(x, y) => format!("({{...({}), ...({})}})", self.expr(x), self.expr(y)),
            Arr(es) => {
                let es: Vec<String> = es.iter().map(|e| self.expr(e)).collect();
                format!("[{}]", es.join(", "))
            }
            Index(e, i) => format!("({})[{}]", self.expr(e), self.expr(i)),
            SetIndex(e, i, v) => {
                format!("(({})[{}] = {})", self.expr(e), self.expr(i), self.expr(v))
            }
            MCall(e, l, args) => {
                let obj = self.expr(e);
                let args: Vec<String> = args.iter().map(|a| self.expr(a)).collect();
                format!("({}).{}({})", obj, l, args.join(", "))
            }
            New(f, args) => {
                let f = self.expr(f);
                let args: Vec<String> = args.iter().map(|a| self.expr(a)).collect();
                format!("(new ({})({}))", f, args.join(", "))
            }
            Class(..) => unreachable!("a class only as a `const`'s value: {e:?}"),
        }
    }

    /// `class C { constructor(x₀, …) { this.l = …; … } m(…) { … } get g() { … } }`.
    fn class(&mut self, name: &str, n: usize, members: &[(String, Member, Core)]) -> String {
        let xs: Vec<String> = (0..n).map(|_| self.fresh("x")).collect();
        // The constructor's `this`, the class, then its parameters, the
        // first innermost: what each member sees.
        self.names.push("this".into());
        self.names.push(name.to_string());
        for x in xs.iter().rev() {
            self.names.push(x.clone());
        }
        let base = self.names.len();
        let (mut ctor, mut body) = (Vec::new(), Vec::new());
        // A field's initialiser sees the fields before it, read off `this`.
        let mut fields: Vec<String> = Vec::new();
        for (l, m, e) in members {
            match (m, e) {
                (Member::Field, e) => {
                    self.names.extend(fields.iter().cloned());
                    let v = self.expr(e);
                    self.names.truncate(base);
                    ctor.push(format!("this.{} = {};", l, v));
                    fields.push(format!("this.{}", l));
                }
                (Member::Arrow, Func(k, f)) => {
                    let v = self.arrow(*k, f);
                    ctor.push(format!("this.{} = {};", l, v));
                }
                (Member::Method, Func(k, f)) => {
                    body.push(format!("{}{}", l, self.function(*k, f).1));
                }
                (Member::Getter, Func(0, f)) => {
                    body.push(format!("get {}{}", l, self.function(0, f).1));
                }
                _ => unreachable!("a class's function member is a function: {e:?}"),
            }
        }
        self.names.truncate(base - n - 2);
        format!(
            "class {} {{ constructor({}) {{ {} }} {} }}",
            name,
            xs.join(", "),
            ctor.join(" "),
            body.join(" ")
        )
    }

    /// An arrow function `(x₀, …) => { … }`, whose `this` is the enclosing
    /// one's, and which never refers to itself.
    fn arrow(&mut self, n: usize, body: &Core) -> String {
        let xs: Vec<String> = (0..n).map(|_| self.fresh("x")).collect();
        let alias = refers_from_inner(body, n + 1, false).then(|| self.fresh("t"));
        self.names
            .push(alias.clone().unwrap_or_else(|| "this".into()));
        self.names.push("unbound".into());
        for x in xs.iter().rev() {
            self.names.push(x.clone());
        }
        let body = self.stmts(body, "return ");
        self.names.truncate(self.names.len() - n - 2);
        let prelude = alias
            .map(|t| format!("const {t} = this; "))
            .unwrap_or_default();
        format!("({}) => {{ {}{} }}", xs.join(", "), prelude, body)
    }

    /// A function's name, then its parameters and body, `(x₀, …) { … }`.
    fn function(&mut self, n: usize, body: &Core) -> (String, String) {
        let f = self.fresh("f");
        let xs: Vec<String> = (0..n).map(|_| self.fresh("x")).collect();
        // `this` is printed as `this` where it is the innermost function's;
        // a function inside it that refers to it needs an alias.
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
        (f, format!("({}) {{ {}{} }}", xs.join(", "), prelude, body))
    }

    /// A program or function body: statements, then `last` and the value
    /// (`return` in a function, an expression statement at the top).
    fn stmts(&mut self, e: &Core, last: &str) -> String {
        match e {
            Let(false, None, e1, e2) if matches!(**e1, Class(..)) => {
                let Class(n, members) = &**e1 else {
                    unreachable!()
                };
                let c = self.fresh("C");
                let class = self.class(&c, *n, members);
                self.names.push(c);
                let rest = self.stmts(e2, last);
                self.names.pop();
                format!("{} {}", class, rest)
            }
            Let(m, a, e1, e2) => {
                let v = self.fresh("v");
                let init = self.expr(e1);
                self.names.push(v.clone());
                let rest = self.stmts(e2, last);
                self.names.pop();
                let keyword = if *m { "let" } else { "const" };
                let ann = a
                    .as_ref()
                    .map(|t| format!("/** {} {}: {} */ ", keyword, v, js_scheme(t)))
                    .unwrap_or_default();
                format!("{}{} {} = {}; {}", ann, keyword, v, init, rest)
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
            // `const v = e₁;`, then a test that `v` holds something, which
            // inty narrows `v` by in the branch that sees it.
            Unwrap(e1, e2, e3) => {
                let v = self.fresh("v");
                let init = self.expr(e1);
                if is_stmt(e2) || is_stmt(e3) {
                    let none = self.stmts(e2, last);
                    self.names.push(v.clone());
                    let some = self.stmts(e3, last);
                    self.names.pop();
                    format!("const {v} = {init}; if ({v} != null) {{ {some} }} else {{ {none} }}")
                } else {
                    let none = self.expr(e2);
                    self.names.push(v.clone());
                    let some = self.expr(e3);
                    self.names.pop();
                    format!("const {v} = {init}; {last}({v} != null ? {some} : {none});")
                }
            }
            // `const v = e₁;`, then a test of `v`'s tag, which inty narrows
            // `v` by in each branch.
            CaseTag(e1, l, t, e2, e3) => {
                let v = self.fresh("v");
                let init = self.expr(e1);
                self.names.push(v.clone());
                let test = format!("{v}.{l} === {}", t.js());
                let out = if is_stmt(e2) || is_stmt(e3) {
                    let rest = self.stmts(e2, last);
                    let case = self.stmts(e3, last);
                    format!("const {v} = {init}; if ({test}) {{ {case} }} else {{ {rest} }}")
                } else {
                    let rest = self.expr(e2);
                    let case = self.expr(e3);
                    format!("const {v} = {init}; {last}({test} ? {case} : {rest});")
                };
                self.names.pop();
                out
            }
            // `const v = e₁;`, then a test of `v`'s `typeof`, which inty
            // narrows `v` by in each branch.
            TypeTest(e1, t, e2, e3) => {
                let v = self.fresh("v");
                let init = self.expr(e1);
                self.names.push(v.clone());
                let test = format!("typeof {v} === \"{t}\"");
                let out = if is_stmt(e2) || is_stmt(e3) {
                    let rest = self.stmts(e2, last);
                    let case = self.stmts(e3, last);
                    format!("const {v} = {init}; if ({test}) {{ {case} }} else {{ {rest} }}")
                } else {
                    let rest = self.expr(e2);
                    let case = self.expr(e3);
                    format!("const {v} = {init}; {last}({test} ? {case} : {rest});")
                };
                self.names.pop();
                out
            }
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
        Func(n, body) | Method(n, body) => refers_from_inner(body, i + n + 2, true),
        Getter(body) => refers_from_inner(body, i + 2, true),
        Let(_, _, x, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i + 1, inner),
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
        Plus(x, y)
        | Minus(x, y)
        | Bin(_, x, y)
        | Seq(x, y)
        | While(x, y)
        | TryFinally(x, y)
        | Spread(x, y)
        | Index(x, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i, inner),
        TryCatch(x, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i + 1, inner),
        Unwrap(x, y, z) => {
            refers_from_inner(x, i, inner)
                || refers_from_inner(y, i, inner)
                || refers_from_inner(z, i + 1, inner)
        }
        CaseTag(x, _, _, y, z) | TypeTest(x, _, y, z) => {
            refers_from_inner(x, i, inner)
                || refers_from_inner(y, i + 1, inner)
                || refers_from_inner(z, i + 1, inner)
        }
        Break | Continue => false,
        Num(..) | Str(_) | Bool(_) | Undef | Null => false,
        Obj(fields) => fields.iter().any(|(_, e)| refers_from_inner(e, i, inner)),
        Get(x, _) => refers_from_inner(x, i, inner),
        Set(x, _, y) => refers_from_inner(x, i, inner) || refers_from_inner(y, i, inner),
        Arr(es) => es.iter().any(|e| refers_from_inner(e, i, inner)),
        SetIndex(x, j, y) => {
            refers_from_inner(x, i, inner)
                || refers_from_inner(j, i, inner)
                || refers_from_inner(y, i, inner)
        }
        MCall(x, _, args) | New(x, args) => {
            refers_from_inner(x, i, inner) || args.iter().any(|a| refers_from_inner(a, i, inner))
        }
        // The constructor is a function: its parameters, itself and its
        // `this`, then, for a field, the fields before it.
        Class(n, members) => {
            let mut fields = 0;
            members.iter().any(|(_, m, e)| match m {
                Member::Field => {
                    fields += 1;
                    refers_from_inner(e, i + n + 2 + fields - 1, true)
                }
                _ => refers_from_inner(e, i + n + 2, true),
            })
        }
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
    /// An array of these elements.
    Arr(Box<T>),
    /// A sum: `Nullable<t>` (`true`) or `Optional<t>`, only as an
    /// annotation's (`ty` never makes one).
    Maybe(bool, Box<T>),
    /// A polymorphic annotation's quantified variable `i`, written `a`,
    /// `b`, … (`ty` never makes one).
    TVar(usize),
    /// A variant tagged by its field `l`: its cases, each a tag and the
    /// case's other fields, sorted by label; only as an annotation's
    /// (`ty` never makes one).
    Variant(String, Vec<(Tag, Vec<(String, T)>)>),
    /// A sum told apart by `typeof` (`Number | String`): its cases, of
    /// different `typeof`s; only as an annotation's (`ty` never makes one).
    Sum(Vec<T>),
    /// The type of the one string, `"s"`; only as an annotation's (`ty`
    /// never makes one).
    StrLit(String),
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
    /// A method's `this`: an object with these data fields (and methods,
    /// which aren't tracked).
    This(Vec<(String, T)>),
    /// In scope in the model but never referred to: what JavaScript has no
    /// name for (an arrow function itself, a method's own name), or a
    /// variable whose JavaScript reading differs (a constructor's
    /// parameters in a method, its `this`, the class inside itself, and
    /// the class outside `new`).
    Hidden,
}

struct Gen {
    rng: Rng,
    /// The return types of the functions being generated, innermost last
    /// (`None` for an untyped one); empty at the top level.
    funcs: Vec<Option<T>>,
    /// How many loops enclose the point being generated, in the innermost
    /// function (the first entry is the top level's).
    loops: Vec<usize>,
    /// Inside a constructor's field initialiser or an arrow field: a
    /// function there never refers to its own `this` (inty rejects that
    /// before any typing: the instance isn't complete yet), and holds no
    /// class.
    no_this: usize,
}

impl Gen {
    /// A function's `this`, as `b` but where it mustn't be referred to.
    fn this_binding(&self, b: Binding) -> Binding {
        if self.no_this > 0 {
            Binding::Hidden
        } else {
            b
        }
    }

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
        if depth > 0 && self.rng.chance(8) {
            return T::Arr(b2(self.ty(depth - 1)));
        }
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

    /// A type to annotate with: one `annotatable` takes.
    fn ann_ty(&mut self, depth: usize) -> T {
        loop {
            let t = self.ty(depth);
            if annotatable(&t) {
                return t;
            }
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
            T::StrLit(s) => Str(s.clone()),
            T::Arrow(..)
            | T::Obj(_)
            | T::Arr(_)
            | T::Maybe(..)
            | T::TVar(_)
            | T::Variant(..)
            | T::Sum(_) => return None,
        })
    }

    /// A variant tagged by one of the labels, of two or three cases told
    /// apart by strings, or of two told apart by `true` and `false`, each
    /// with some of the other labels' fields.
    fn variant_ty(&mut self) -> T {
        const TAGS: [&str; 3] = ["circle", "square", "line"];
        let l = self.label();
        let tags: Vec<Tag> = if self.rng.chance(30) {
            vec![Tag::Bool(true), Tag::Bool(false)]
        } else {
            let n = 2 + self.rng.below(2);
            TAGS[..n].iter().map(|t| Tag::Str(t.to_string())).collect()
        };
        let mut cases = Vec::new();
        for tag in tags {
            let mut fields = Vec::new();
            for f in LABELS {
                if f != l && self.rng.chance(50) {
                    fields.push((f.to_string(), self.base()));
                }
            }
            cases.push((tag, fields));
        }
        T::Variant(l, cases)
    }

    /// A value of the variant `t`: a variable of its type, or an object
    /// literal of one of its cases, its tag written as a string, which
    /// only checking it against `t` takes as the case's.
    fn variant_value(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let T::Variant(l, cases) = t else {
            unreachable!()
        };
        let fits: Vec<usize> = (0..scope.len())
            .filter(|&i| matches!(&scope[scope.len() - 1 - i], Binding::Mono(u) if u == t))
            .collect();
        if !fits.is_empty() && self.rng.chance(50) {
            return Var(fits[self.rng.below(fits.len())]);
        }
        let (tag, fs) = cases[self.rng.below(cases.len())].clone();
        let mut fields = vec![(l.clone(), tag.core())];
        fields.extend(
            fs.iter()
                .map(|(f, u)| (f.clone(), self.typed(u, d, scope, false))),
        );
        if self.rng.chance(50) {
            fields.reverse();
        }
        Obj(fields)
    }

    /// A variant's variable `x`, of the variant `v`, taken apart by one of
    /// its tags: each branch of type `t` sees the variable as the case's
    /// fields, or as the rest (another variant, or the one case left).
    fn case_on(&mut self, x: Core, v: &T, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let T::Variant(l, cases) = v else {
            unreachable!()
        };
        let k = self.rng.below(cases.len());
        let (tag, fs) = cases[k].clone();
        let mut rest = cases.clone();
        rest.remove(k);
        scope.push(if rest.len() == 1 {
            Binding::This(rest[0].1.clone())
        } else {
            Binding::Mono(T::Variant(l.clone(), rest))
        });
        let e2 = self.typed(t, d, scope, true);
        scope.pop();
        scope.push(Binding::This(fs));
        let e3 = self.typed(t, d, scope, true);
        scope.pop();
        CaseTag(b(x), l.clone(), tag, b(e2), b(e3))
    }

    /// A program of type `t` with a variant: one annotated `const` of a
    /// variant type, or one in scope, taken apart by its tag.
    fn variant_use(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let existing: Vec<(usize, T)> = (0..scope.len())
            .filter_map(|i| match &scope[scope.len() - 1 - i] {
                Binding::Mono(v @ T::Variant(..)) => Some((i, v.clone())),
                _ => None,
            })
            .collect();
        if !existing.is_empty() && self.rng.chance(60) {
            let (i, v) = existing[self.rng.below(existing.len())].clone();
            return self.case_on(Var(i), &v, t, d, scope);
        }
        let v = self.variant_ty();
        let e1 = self.variant_value(&v, d, scope);
        scope.push(Binding::Mono(v.clone()));
        let rest = if self.rng.chance(70) {
            self.case_on(Var(0), &v, t, d, scope)
        } else {
            self.typed(t, d, scope, true)
        };
        scope.pop();
        Let(false, Some(v), b(e1), b(rest))
    }

    /// A sum told apart by `typeof`, of two or three of a number, a string,
    /// a boolean and a function.
    fn sum_ty(&mut self) -> T {
        let field = if self.rng.chance(50) { T::Num } else { T::Str };
        let mut arms = vec![
            T::Num,
            T::Str,
            T::Bool,
            T::Arrow(vec![T::Num], b2(T::Num)),
            T::Obj(vec![("a".into(), field)]),
        ];
        let n = 2 + self.rng.below(2);
        while arms.len() > n {
            let i = self.rng.below(arms.len());
            arms.remove(i);
        }
        T::Sum(arms)
    }

    /// A value of the sum `t`: a variable of its type, or a value of one of
    /// its cases, which checking it against `t` injects.
    fn sum_value(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let T::Sum(arms) = t else { unreachable!() };
        let fits: Vec<usize> = (0..scope.len())
            .filter(|&i| matches!(&scope[scope.len() - 1 - i], Binding::Mono(u) if u == t))
            .collect();
        if !fits.is_empty() && self.rng.chance(50) {
            return Var(fits[self.rng.below(fits.len())]);
        }
        let arm = arms[self.rng.below(arms.len())].clone();
        self.typed(&arm, d, scope, false)
    }

    /// The `typeof` of a sum's case.
    fn type_tag(t: &T) -> &'static str {
        match t {
            T::Num => "number",
            T::Str => "string",
            T::Bool => "boolean",
            T::Arrow(..) => "function",
            T::Obj(_) => "object",
            _ => unreachable!("a sum's cases are told apart by typeof"),
        }
    }

    /// A program of type `t` with a sum told apart by `typeof`: one
    /// annotated `const`, or one in scope, taken apart by a test of its
    /// `typeof`.
    fn sum_use(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let existing: Vec<(usize, T)> = (0..scope.len())
            .filter_map(|i| match &scope[scope.len() - 1 - i] {
                Binding::Mono(v @ T::Sum(_)) => Some((i, v.clone())),
                _ => None,
            })
            .collect();
        let (x, s, bind) = if !existing.is_empty() && self.rng.chance(60) {
            let (i, s) = existing[self.rng.below(existing.len())].clone();
            (Var(i), s, None)
        } else {
            let s = self.sum_ty();
            let e1 = self.sum_value(&s, d, scope);
            (Var(0), s, Some(e1))
        };
        if bind.is_some() {
            scope.push(Binding::Mono(s.clone()));
        }
        let T::Sum(arms) = &s else { unreachable!() };
        let k = self.rng.below(arms.len());
        let mut rest = arms.clone();
        let case = rest.remove(k);
        scope.push(Binding::Mono(if rest.len() == 1 {
            rest[0].clone()
        } else {
            T::Sum(rest)
        }));
        let e2 = self.typed(t, d, scope, true);
        scope.pop();
        scope.push(Binding::Mono(case.clone()));
        let e3 = self.typed(t, d, scope, true);
        scope.pop();
        let test = TypeTest(b(x), Self::type_tag(&case).to_string(), b(e2), b(e3));
        match bind {
            Some(e1) => {
                scope.pop();
                Let(false, Some(s), b(e1), b(test))
            }
            None => test,
        }
    }

    /// A program of type `t` with a string literal type: a `const`
    /// annotated with the type of one string, checked by another annotated
    /// `const` into `String`, a sum of `String`, a sum told apart by `typeof`
    /// with a string case, or a string literal type (mostly its own), alone
    /// or as a branch of `?:`.
    fn lit_use(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let Str(s) = self.string() else {
            unreachable!()
        };
        let lit = T::StrLit(s.clone());
        let target = match self.rng.below(6) {
            0 | 1 => T::Str,
            2 => T::Maybe(self.rng.chance(50), b2(T::Str)),
            3 => loop {
                let sum = self.sum_ty();
                if matches!(&sum, T::Sum(arms) if arms.contains(&T::Str)) {
                    break sum;
                }
            },
            4 => lit.clone(),
            _ => {
                let Str(o) = self.string() else {
                    unreachable!()
                };
                T::StrLit(o)
            }
        };
        scope.push(Binding::Mono(lit.clone()));
        let e2 = if self.rng.chance(30) {
            let other = if self.rng.chance(50) {
                Str(s.clone())
            } else {
                self.string()
            };
            let (x, y) = if self.rng.chance(50) {
                (Var(0), other)
            } else {
                (other, Var(0))
            };
            Cond(b(Bool(self.rng.chance(50))), b(x), b(y))
        } else {
            Var(0)
        };
        scope.push(Binding::Mono(target.clone()));
        let rest = self.typed(t, d, scope, true);
        scope.pop();
        scope.pop();
        Let(
            false,
            Some(lit),
            b(Str(s)),
            b(Let(false, Some(target), b(e2), b(rest))),
        )
    }

    /// A program of type `t`, mostly well typed.
    fn typed(&mut self, t: &T, depth: usize, scope: &mut Vec<Binding>, stmt: bool) -> Core {
        if matches!(t, T::Variant(..)) {
            return self.variant_value(t, depth.saturating_sub(1), scope);
        }
        if matches!(t, T::Sum(_)) {
            return self.sum_value(t, depth.saturating_sub(1), scope);
        }
        // A variable of the right type.
        let fits: Vec<usize> = (0..scope.len())
            .filter(|&i| match &scope[scope.len() - 1 - i] {
                Binding::Mono(u) | Binding::Mut(u) => u == t,
                Binding::PolyId => matches!(t, T::Arrow(ps, r) if ps.len() == 1 && ps[0] == **r),
                Binding::Unknown | Binding::UnknownMut | Binding::This(_) | Binding::Hidden => {
                    false
                }
            })
            .collect();
        if !fits.is_empty() && self.rng.chance(if depth == 0 { 80 } else { 30 }) {
            return Var(fits[self.rng.below(fits.len())]);
        }
        // A field of this type of a method's `this`.
        let this_fields: Vec<(usize, String)> = (0..scope.len())
            .flat_map(|i| match &scope[scope.len() - 1 - i] {
                Binding::This(fields) => fields
                    .iter()
                    .filter(|(_, u)| u == t)
                    .map(|(l, _)| (i, l.clone()))
                    .collect(),
                _ => Vec::new(),
            })
            .collect();
        if !this_fields.is_empty() && self.rng.chance(if depth == 0 { 60 } else { 25 }) {
            let (i, l) = this_fields[self.rng.below(this_fields.len())].clone();
            return Get(b(Var(i)), l);
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
        // A read, or a write, of an array's element of this type (or a
        // string's character), or an array's or a string's `length`.
        if depth > 0 && self.rng.chance(10) {
            let i = self.index(d, scope);
            if *t == T::Str && self.rng.chance(30) {
                return Index(b(self.typed(&T::Str, d, scope, false)), b(i));
            }
            if *t == T::Num && self.rng.chance(30) {
                let c = if self.rng.chance(50) {
                    T::Str
                } else {
                    T::Arr(b2(self.ty(1)))
                };
                return Get(b(self.typed(&c, d, scope, false)), "length".into());
            }
            let a = self.typed(&T::Arr(b2(t.clone())), d, scope, false);
            return if self.rng.chance(70) {
                Index(b(a), b(i))
            } else {
                SetIndex(b(a), b(i), b(self.typed(t, d, scope, false)))
            };
        }
        // A method call on an object literal with a method `m`.
        if depth > 0 && self.no_this == 0 && self.rng.chance(8) {
            return self.method_call(t, d, scope);
        }
        // A class, and a member of type `t` of a new instance.
        if stmt && depth > 0 && self.no_this == 0 && self.rng.chance(8) {
            return self.class_use(t, d, scope);
        }
        // A variant, taken apart by its tag.
        if stmt && depth > 0 && self.rng.chance(6) {
            return self.variant_use(t, d, scope);
        }
        // A sum told apart by `typeof`, taken apart by a test of it.
        if stmt && depth > 0 && self.rng.chance(6) {
            return self.sum_use(t, d, scope);
        }
        // A value of a string literal type, checked into another type.
        if stmt && depth > 0 && self.rng.chance(4) {
            return self.lit_use(t, d, scope);
        }
        // A sum's binding, or another value that isn't nothing, tested for
        // nothing: `v != null ? … : …`, or `v ?? …`.
        if stmt && depth > 0 && self.rng.chance(8) {
            let sums: Vec<(usize, T)> = (0..scope.len())
                .filter_map(|i| match &scope[scope.len() - 1 - i] {
                    Binding::Mono(T::Maybe(_, u)) | Binding::Mut(T::Maybe(_, u)) => {
                        Some((i, (**u).clone()))
                    }
                    _ => None,
                })
                .collect();
            let (e1, inner) = if !sums.is_empty() && self.rng.chance(70) {
                let (i, u) = sums[self.rng.below(sums.len())].clone();
                (Var(i), u)
            } else {
                let s = loop {
                    let s = self.ty(1);
                    if !matches!(s, T::Null | T::Undef) {
                        break s;
                    }
                };
                (self.typed(&s, d, scope, false), s)
            };
            let e2 = self.typed(t, d, scope, true);
            scope.push(Binding::Mono(inner.clone()));
            let e3 = if inner == *t && self.rng.chance(40) {
                Var(0)
            } else {
                self.typed(t, d, scope, true)
            };
            scope.pop();
            return Unwrap(b(e1), b(e2), b(e3));
        }
        if stmt && depth > 0 && self.rng.chance(25) {
            // `const`: sometimes the polymorphic identity, used at
            // several types below; sometimes annotated with its type,
            // `<a>(a) => a`, and then sometimes with an initialiser that
            // isn't that polymorphic, which the annotation rejects.
            if self.rng.chance(30) {
                let ann = self
                    .rng
                    .chance(50)
                    .then(|| T::Arrow(vec![T::TVar(0)], b2(T::TVar(0))));
                let init = if ann.is_some() && self.rng.chance(15) {
                    Func(1, b(self.num()))
                } else {
                    Func(1, b(Var(0)))
                };
                scope.push(Binding::PolyId);
                let rest = self.typed(t, d, scope, true);
                scope.pop();
                return Let(false, ann, b(init), b(rest));
            }
            // `const`, or `let`, which may be assigned below; sometimes
            // annotated, mostly with its type.
            let s = self.ty(1);
            let mutable = self.rng.chance(50);
            // Sometimes a sum: `/** const v: S | Null */`, holding nothing
            // or an `S`.
            if self.rng.chance(20) && annotatable(&s) && !matches!(s, T::Null | T::Undef) {
                let null = self.rng.chance(50);
                let e1 = if self.rng.chance(30) {
                    if null {
                        Null
                    } else {
                        Undef
                    }
                } else {
                    self.typed(&s, d, scope, false)
                };
                let m = T::Maybe(null, b2(s));
                scope.push(if mutable {
                    Binding::Mut(m.clone())
                } else {
                    Binding::Mono(m.clone())
                });
                let rest = self.typed(t, d, scope, true);
                scope.pop();
                return Let(mutable, Some(m), b(e1), b(rest));
            }
            let e1 = self.typed(&s, d, scope, false);
            let ann = if self.rng.chance(30) && annotatable(&s) {
                Some(if self.rng.chance(80) {
                    s.clone()
                } else {
                    self.ann_ty(1)
                })
            } else {
                None
            };
            scope.push(if mutable {
                Binding::Mut(s)
            } else {
                Binding::Mono(s)
            });
            let rest = self.typed(t, d, scope, true);
            scope.pop();
            return Let(mutable, ann, b(e1), b(rest));
        }
        // (At depth 0, the value itself: a conditional or a call there
        // would spawn more than one subprogram at depth 0 on average, and
        // the program might never end.)
        match if depth == 0 { 5 } else { self.rng.below(6) } {
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
                T::Num => match self.rng.below(5) {
                    3 => {
                        let o = Op2::NUMERIC[self.rng.below(2)];
                        Bin(
                            o,
                            b(self.typed(&T::Num, d, scope, false)),
                            b(self.typed(&T::Num, d, scope, false)),
                        )
                    }
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
                T::Bool => match self.rng.below(4) {
                    0 => Not(b(self.any(d, scope, false))),
                    // A comparison of numbers.
                    1 => {
                        let o = Op2::COMPARE[self.rng.below(4)];
                        Bin(
                            o,
                            b(self.typed(&T::Num, d, scope, false)),
                            b(self.typed(&T::Num, d, scope, false)),
                        )
                    }
                    // `===` of two values of some type, not functions (the
                    // model's functions have no identity).
                    2 => {
                        let mut u = self.ty(1);
                        if matches!(u, T::Arrow(..)) {
                            u = T::Num;
                        }
                        let o = if self.rng.chance(50) {
                            Op2::Eq
                        } else {
                            Op2::Ne
                        };
                        Bin(
                            o,
                            b(self.typed(&u, d, scope, false)),
                            b(self.typed(&u, d, scope, false)),
                        )
                    }
                    _ => Bool(self.rng.chance(50)),
                },
                T::Arrow(ps, r) => {
                    // `this`, the function itself, then the parameters,
                    // the first innermost.
                    scope.push(self.this_binding(Binding::Mono(T::Undef)));
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
                // A spread: each field from the later operand, the earlier
                // one, or both (the later one's winning, the earlier one's
                // of any type).
                T::Obj(fields) if depth > 0 && self.rng.chance(30) => {
                    let (mut earlier, mut later) = (Vec::new(), Vec::new());
                    for (l, u) in fields {
                        match self.rng.below(3) {
                            0 => earlier.push((l.clone(), u.clone())),
                            1 => later.push((l.clone(), u.clone())),
                            _ => {
                                earlier.push((l.clone(), self.ty(0)));
                                later.push((l.clone(), u.clone()));
                            }
                        }
                    }
                    let e1 = self.typed(&T::Obj(earlier), d, scope, false);
                    let e2 = self.typed(&T::Obj(later), d, scope, false);
                    Spread(b(e1), b(e2))
                }
                T::Arr(u) => {
                    let n = self.rng.below(4);
                    Arr((0..n).map(|_| self.typed(u, d, scope, false)).collect())
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

    /// A method call of type `t` on an object literal `{a: …, m: function
    /// (…) { … }}`: the method returns a `t`, reading the object's fields
    /// through `this`; or it returns `this` (after storing a field), and is
    /// called twice before a field of type `t` is read. Either makes the
    /// object's type recursive.
    fn method_call(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let mut data: Vec<(String, T)> = Vec::new();
        for l in LABELS {
            if self.rng.chance(50) {
                data.push((l.to_string(), self.ty(1)));
            }
        }
        let chain = self.rng.chance(40);
        if chain && !data.iter().any(|(_, u)| u == t) {
            let l = self.label();
            data.retain(|(m, _)| *m != l);
            data.push((l, t.clone()));
            data.sort_by(|x, y| x.0.cmp(&y.0));
        }
        let mut fields: Vec<(String, Core)> = data
            .iter()
            .map(|(l, u)| (l.clone(), self.typed(u, d, scope, false)))
            .collect();
        if !chain && self.rng.chance(30) {
            // A getter `g` returning a `t`, read: `get g() { … }`, in a
            // function of no parameters, its `this` variable 1.
            scope.push(Binding::This(data.clone()));
            scope.push(Binding::Unknown);
            self.funcs.push(Some(t.clone()));
            self.loops.push(0);
            let body = self.typed(t, d, scope, true);
            self.loops.pop();
            self.funcs.pop();
            scope.truncate(scope.len() - 2);
            if !refers_from_inner(&body, 0, true) {
                fields.push(("g".into(), Getter(b(body))));
                if fields.len() > 1 && self.rng.chance(50) {
                    fields.reverse();
                }
                return Get(b(Obj(fields)), "g".into());
            }
        }
        if chain {
            // `function () { this.l = …; return this; }`: in a function of
            // no parameters, `this` is variable 1.
            let (l, u) = data[self.rng.below(data.len())].clone();
            scope.push(Binding::This(data.clone()));
            scope.push(Binding::Unknown);
            let v = self.typed(&u, d.saturating_sub(1), scope, false);
            scope.truncate(scope.len() - 2);
            let body = if self.rng.chance(50) {
                Seq(b(Set(b(Var(1)), l, b(v))), b(Ret(b(Var(1)))))
            } else {
                Ret(b(Var(1)))
            };
            let m = self.method(0, body);
            fields.push(("m".into(), m));
            let (l, _) = data.iter().find(|(_, u)| u == t).unwrap().clone();
            let calls = 1 + self.rng.below(2);
            let mut e = Obj(fields);
            for _ in 0..calls {
                e = MCall(b(e), "m".into(), Vec::new());
            }
            return Get(b(e), l);
        }
        let n = self.rng.below(3);
        let ps: Vec<T> = (0..n).map(|_| self.ty(1)).collect();
        scope.push(Binding::This(data));
        scope.push(Binding::Unknown);
        for p in ps.iter().rev() {
            scope.push(Binding::Mut(p.clone()));
        }
        self.funcs.push(Some(t.clone()));
        self.loops.push(0);
        let body = self.typed(t, d, scope, true);
        self.loops.pop();
        self.funcs.pop();
        scope.truncate(scope.len() - n - 2);
        let m = self.method(n, body);
        fields.push(("m".into(), m));
        if fields.len() > 1 && self.rng.chance(50) {
            fields.reverse();
        }
        let args = ps.iter().map(|p| self.typed(p, d, scope, false)).collect();
        MCall(b(Obj(fields)), "m".into(), args)
    }

    /// A function member of a class, of `n` parameters: a method or a
    /// getter (`arrow` false), which sees `scope` but not the constructor's
    /// `n_ctor` parameters, the class or the constructor's `this`; or an
    /// arrow field, which sees the parameters. Neither refers to itself.
    /// Its `this` is the instance, of the data fields `this_fields` (`None`:
    /// not referred to), and it returns a `t` (`None`: untyped). The
    /// function, and its parameters' types.
    #[allow(clippy::too_many_arguments)]
    fn class_function(
        &mut self,
        n: usize,
        t: Option<&T>,
        this_fields: Option<&[(String, T)]>,
        arrow: bool,
        n_ctor: usize,
        d: usize,
        scope: &mut Vec<Binding>,
    ) -> (Core, Vec<T>) {
        let saved = scope.clone();
        if !arrow {
            let k = scope.len();
            for i in 0..n_ctor + 2 {
                scope[k - 1 - i] = Binding::Hidden;
            }
        }
        scope.push(match (this_fields, t) {
            (Some(fields), Some(_)) => Binding::This(fields.to_vec()),
            (Some(_), None) => Binding::Unknown,
            (None, _) => Binding::Hidden,
        });
        scope.push(Binding::Hidden);
        let ps: Vec<T> = (0..n).map(|_| self.ty(1)).collect();
        for p in ps.iter().rev() {
            scope.push(if t.is_some() {
                Binding::Mut(p.clone())
            } else {
                Binding::UnknownMut
            });
        }
        self.funcs.push(t.cloned());
        self.loops.push(0);
        self.no_this += usize::from(arrow);
        let body = match t {
            Some(t) => self.typed(t, d, scope, true),
            None => self.any(d, scope, true),
        };
        self.no_this -= usize::from(arrow);
        self.loops.pop();
        self.funcs.pop();
        *scope = saved;
        (Func(n, b(body)), ps)
    }

    /// A class's members other than its fields: each of a method `m`, a
    /// getter `g` and an arrow field `f` sometimes, and `want` always,
    /// returning a `t` (an arrow field to be called outside a receiver not
    /// referring to `this`). Each member, and the parameter types of the
    /// one wanted.
    fn class_functions(
        &mut self,
        want: Option<(Member, bool, &T)>,
        data: Option<&[(String, T)]>,
        n_ctor: usize,
        d: usize,
        scope: &mut Vec<Binding>,
    ) -> (Vec<(String, Member, Core)>, Vec<T>) {
        let typed = data.is_some();
        let mut members = Vec::new();
        let mut wanted_params = Vec::new();
        for (l, m) in [
            ("m", Member::Method),
            ("g", Member::Getter),
            ("f", Member::Arrow),
        ] {
            let wanted = want.filter(|(k, _, _)| *k == m);
            if wanted.is_none() && !self.rng.chance(30) {
                continue;
            }
            let n = if m == Member::Getter {
                0
            } else {
                self.rng.below(3)
            };
            let other = self.ty(1);
            let t = match wanted {
                Some((_, _, t)) => Some(t),
                None if typed => Some(&other),
                None => None,
            };
            let detached = wanted.is_some_and(|(_, detached, _)| detached);
            let no_fields: [(String, T); 0] = [];
            let this_fields = match data {
                _ if detached => None,
                Some(fields) => Some(fields),
                None => Some(&no_fields[..]),
            };
            let (f, ps) =
                self.class_function(n, t, this_fields, m == Member::Arrow, n_ctor, d, scope);
            if wanted.is_some() {
                wanted_params = ps;
            }
            members.push((l.to_string(), m, f));
        }
        (members, wanted_params)
    }

    /// A class's fields, in order, each initialiser seeing the fields
    /// before it: of the types `data`, or untyped (`labels`).
    fn class_fields(
        &mut self,
        data: &[(String, Option<T>)],
        d: usize,
        scope: &mut Vec<Binding>,
    ) -> Vec<(String, Member, Core)> {
        let mut members = Vec::new();
        self.no_this += 1;
        for (j, (l, u)) in data.iter().enumerate() {
            let base = scope.len();
            let gen = |g: &mut Gen, scope: &mut Vec<Binding>| match u {
                Some(u) => g.typed(u, d, scope, false),
                None => g.any(d, scope, false),
            };
            for (_, v) in &data[..j] {
                scope.push(match v {
                    Some(v) => Binding::Mono(v.clone()),
                    None => Binding::Unknown,
                });
            }
            let mut e = gen(self, scope);
            // A field is read off `this`, which a function inside the
            // initialiser has its own of.
            if (0..j).any(|k| refers_from_inner(&e, k, false)) {
                scope.truncate(base);
                scope.extend((0..j).map(|_| Binding::Hidden));
                e = gen(self, scope);
            }
            scope.truncate(base);
            members.push((l.clone(), Member::Field, e));
        }
        self.no_this -= 1;
        members
    }

    /// `class C { … }; <use>`, where the use is of type `t`: a field, a
    /// method's result, a getter's, or an arrow field's (called on the
    /// instance, or outside it) of a new instance.
    fn class_use(&mut self, t: &T, d: usize, scope: &mut Vec<Binding>) -> Core {
        let mut data: Vec<(String, T)> = Vec::new();
        for l in LABELS {
            if self.rng.chance(40) {
                data.push((l.to_string(), self.ty(1)));
            }
        }
        // Sometimes `new` on an arrow field returning a `t`, which gives
        // the object it returns but throws in JavaScript: an arrow
        // function isn't a constructor.
        let probe = matches!(t, T::Obj(_)) && self.rng.chance(30);
        let kind = if probe { 3 } else { self.rng.below(5) };
        if kind == 0 && !data.iter().any(|(_, u)| u == t) {
            let l = self.label();
            data.retain(|(m, _)| *m != l);
            data.push((l, t.clone()));
            data.sort_by(|x, y| x.0.cmp(&y.0));
        }
        let n = self.rng.below(3);
        let ps: Vec<T> = (0..n).map(|_| self.ty(1)).collect();
        // The constructor's `this` and the class, then its parameters.
        let mark = scope.len();
        scope.push(Binding::Hidden);
        scope.push(Binding::Hidden);
        for p in ps.iter().rev() {
            scope.push(Binding::Mono(p.clone()));
        }
        let typed_data: Vec<(String, Option<T>)> = data
            .iter()
            .map(|(l, u)| (l.clone(), Some(u.clone())))
            .collect();
        let mut members = self.class_fields(&typed_data, d, scope);
        let want = match kind {
            1 => Some((Member::Method, false, t)),
            2 => Some((Member::Getter, false, t)),
            3 => Some((Member::Arrow, false, t)),
            4 => Some((Member::Arrow, true, t)),
            _ => None,
        };
        let (functions, fps) = self.class_functions(want, Some(&data), n, d, scope);
        members.extend(functions);
        scope.truncate(mark);
        // The class, only under `new`.
        scope.push(Binding::Hidden);
        let args: Vec<Core> = ps.iter().map(|p| self.typed(p, d, scope, false)).collect();
        let instance = New(b(Var(0)), args);
        let fargs: Vec<Core> = fps.iter().map(|p| self.typed(p, d, scope, false)).collect();
        let use_ = match kind {
            0 => {
                let (l, _) = data.iter().find(|(_, u)| u == t).unwrap().clone();
                Get(b(instance), l)
            }
            1 => MCall(b(instance), "m".into(), fargs),
            2 => Get(b(instance), "g".into()),
            3 if probe => New(b(Get(b(instance), "f".into())), fargs),
            3 => MCall(b(instance), "f".into(), fargs),
            _ => App(b(Get(b(instance), "f".into())), fargs),
        };
        scope.pop();
        Let(false, None, b(Class(n, members)), b(use_))
    }

    /// An untyped class and a use of a new instance: a member read or
    /// called, `new` on its arrow field (which JavaScript rejects), or the
    /// arrow field called outside the instance when it doesn't refer to
    /// `this` (inty doesn't type such a call when it does).
    fn any_class(&mut self, d: usize, scope: &mut Vec<Binding>) -> Core {
        let n = self.rng.below(3);
        let mark = scope.len();
        scope.push(Binding::Hidden);
        scope.push(Binding::Hidden);
        for _ in 0..n {
            scope.push(Binding::Unknown);
        }
        let data: Vec<(String, Option<T>)> = LABELS
            .iter()
            .filter(|_| self.rng.chance(40))
            .map(|l| (l.to_string(), None))
            .collect();
        let mut members = self.class_fields(&data, d, scope);
        let (functions, _) = self.class_functions(None, None, n, d, scope);
        members.extend(functions);
        scope.truncate(mark);
        scope.push(Binding::Hidden);
        let args: Vec<Core> = (0..n).map(|_| self.any(d, scope, false)).collect();
        let instance = New(b(Var(0)), args);
        let k = self.rng.below(2);
        let fargs: Vec<Core> = (0..k).map(|_| self.any(d, scope, false)).collect();
        let l = match self.rng.below(5) {
            0 => "m".to_string(),
            1 => "g".to_string(),
            2 | 3 => "f".to_string(),
            _ => self.label(),
        };
        let arrow_this = members.iter().any(|(_, m, f)| match (m, f) {
            (Member::Arrow, Func(k, body)) => refers_from_inner(body, k + 1, true),
            _ => false,
        });
        let use_ = match self.rng.below(5) {
            0 => Get(b(instance), l),
            1 => MCall(b(instance), l, fargs),
            2 => New(b(Get(b(instance), "f".into())), fargs),
            3 if !arrow_this => App(b(Get(b(instance), "f".into())), fargs),
            _ => instance,
        };
        scope.pop();
        Let(false, None, b(Class(n, members)), b(use_))
    }

    /// An object literal's function field, of `n` parameters: written as a
    /// method `m(…) { … }` half the time, when it doesn't refer to itself
    /// (a method has no name of its own).
    fn method(&mut self, n: usize, body: Core) -> Core {
        if !refers_from_inner(&body, n, true) && self.rng.chance(50) {
            Method(n, b(body))
        } else {
            Func(n, b(body))
        }
    }

    /// An array index: mostly a small one, in bounds or just past the end;
    /// sometimes any number.
    fn index(&mut self, d: usize, scope: &mut Vec<Binding>) -> Core {
        if self.rng.chance(70) {
            Num(self.rng.below(3) as u64, 0)
        } else {
            self.typed(&T::Num, d, scope, false)
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
                let first = match self.rng.below(5) {
                    0 | 1 => self.any(d, scope, true),
                    2 | 3 => {
                        let s = self.ty(1);
                        self.typed(&s, d, scope, true)
                    }
                    _ => self.dropped(d, scope),
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
                let fin = if self.rng.chance(25) {
                    self.dropped(d, scope)
                } else {
                    let s = self.ty(1);
                    self.typed(&s, d, scope, true)
                };
                Some(TryFinally(b(body), b(fin)))
            }
            _ => None,
        }
    }

    /// A statement whose value is dropped (the model checks it against
    /// `unknown`): an `if` or a `?:`, or a `try`/`catch`, whose branches
    /// have types of their own.
    fn dropped(&mut self, d: usize, scope: &mut Vec<Binding>) -> Core {
        let (s1, s2) = (self.ty(1), self.ty(1));
        if self.rng.chance(60) {
            let c = self.any(d, scope, false);
            let t = self.typed(&s1, d, scope, true);
            let e = self.typed(&s2, d, scope, true);
            Cond(b(c), b(t), b(e))
        } else {
            let body = self.typed(&s1, d, scope, true);
            scope.push(Binding::Unknown);
            let handler = self.typed(&s2, d, scope, true);
            scope.pop();
            TryCatch(b(body), b(handler))
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
        } else if self.rng.chance(25) {
            self.dropped(d, scope)
        } else {
            let s = self.ty(1);
            self.typed(&s, d, scope, true)
        };
        *self.loops.last_mut().unwrap() -= 1;
        scope.pop();
        let step = Assign(0, b(Minus(b(Var(0)), b(Num(1, 0)))));
        Let(
            true,
            None,
            b(Num(n, 0)),
            b(While(b(Var(0)), b(Seq(b(step), b(body))))),
        )
    }

    /// Any program: types aren't tracked, so many are ill typed.
    fn any(&mut self, depth: usize, scope: &mut Vec<Binding>, stmt: bool) -> Core {
        if depth == 0 || self.rng.chance(20) {
            let visible: Vec<usize> = (0..scope.len())
                .filter(|&i| !matches!(scope[scope.len() - 1 - i], Binding::Hidden))
                .collect();
            return match self.rng.below(8) {
                0 if !visible.is_empty() => Var(visible[self.rng.below(visible.len())]),
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
        if stmt && self.no_this == 0 && self.rng.chance(6) {
            return self.any_class(d, scope);
        }
        match self.rng.below(if stmt { 11 } else { 10 }) {
            0 => {
                let n = self.rng.below(3);
                // `this` and the function's own name can't be assigned;
                // the parameters can.
                scope.push(self.this_binding(Binding::Unknown));
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
            4 if self.rng.chance(15) => {
                Spread(b(self.any(d, scope, false)), b(self.any(d, scope, false)))
            }
            4 if self.rng.chance(40) => {
                let n = self.rng.below(3);
                let mut fields: Vec<(String, Core)> = (0..n)
                    .map(|_| (self.label(), self.any(d, scope, false)))
                    .collect();
                if self.rng.chance(30) {
                    // A method, which may use `this`.
                    let k = self.rng.below(2);
                    scope.push(self.this_binding(Binding::Unknown));
                    scope.push(Binding::Unknown);
                    for _ in 0..k {
                        scope.push(Binding::UnknownMut);
                    }
                    self.funcs.push(None);
                    self.loops.push(0);
                    let body = self.any(d, scope, true);
                    self.loops.pop();
                    self.funcs.pop();
                    scope.truncate(scope.len() - k - 2);
                    let m = self.method(k, body);
                    fields.push(("m".into(), m));
                }
                if self.rng.chance(20) {
                    // A getter, which may use `this` (variable 1).
                    scope.push(self.this_binding(Binding::Unknown));
                    scope.push(Binding::Unknown);
                    self.funcs.push(None);
                    self.loops.push(0);
                    let body = self.any(d, scope, true);
                    self.loops.pop();
                    self.funcs.pop();
                    scope.truncate(scope.len() - 2);
                    if !refers_from_inner(&body, 0, true) {
                        fields.push(("g".into(), Getter(b(body))));
                    }
                }
                Obj(fields)
            }
            4 if self.rng.chance(30) => {
                let o = self.any(d, scope, false);
                let l = if self.rng.chance(70) {
                    "m".to_string()
                } else {
                    self.label()
                };
                let n = self.rng.below(2);
                MCall(b(o), l, (0..n).map(|_| self.any(d, scope, false)).collect())
            }
            4 => Not(b(self.any(d, scope, false))),
            5 if self.rng.chance(40) => {
                let o = self.any(d, scope, false);
                // Sometimes the getter `g` an object literal may have.
                let l = if self.rng.chance(15) {
                    "g".to_string()
                } else {
                    self.label()
                };
                if self.rng.chance(60) {
                    Get(b(o), l)
                } else {
                    Set(b(o), l, b(self.any(d, scope, false)))
                }
            }
            5 if self.rng.chance(30) => {
                let a = self.any(d, scope, false);
                // Numeric indices only: the model reads a property of an
                // object by a string index, but inty doesn't.
                let i = Num(self.rng.below(3) as u64, 0);
                if self.rng.chance(60) {
                    Index(b(a), b(i))
                } else {
                    SetIndex(b(a), b(i), b(self.any(d, scope, false)))
                }
            }
            5 if self.rng.chance(20) => {
                let n = self.rng.below(3);
                Arr((0..n).map(|_| self.any(d, scope, false)).collect())
            }
            5 => Typeof(b(self.any(d, scope, false))),
            6 => Neg(b(self.any(d, scope, false))),
            7 | 8 => Plus(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            9 if self.rng.chance(50) => {
                Minus(b(self.any(d, scope, false)), b(self.any(d, scope, false)))
            }
            // `*` and `/` want numbers in both. (No `===` of anything: of
            // a function with itself, JavaScript says true, the model
            // false; the typed generator compares values of one type, not
            // functions.)
            9 => {
                let o = Op2::NUMERIC[self.rng.below(2)];
                Bin(
                    o,
                    b(self.any(d, scope, false)),
                    b(self.any(d, scope, false)),
                )
            }
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
                Let(mutable, None, b(e1), b(rest))
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
                // A recursive type, by its unfolding, as the model prints it.
                let mut ty = state.apply_subst(&ty);
                if let Type::Named(id, args) = &ty {
                    if let Some(unrolled) = state.unroll_named(*id, args) {
                        ty = unrolled;
                    }
                }
                Typing::Type(core_type(&ty))
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
    let mut features = Features::new();
    if fewer_params {
        features.insert("fewer parameters");
    }
    // inty's unifier gave up on a recursive type (`TypeError::UnifyDepth`).
    if errors.iter().any(|e| e.contains("Type too complex")) {
        features.insert("unify depth");
    }
    shown.extend(errors);
    // A spread over an operand of an unknown type: inty gives a field it
    // may or may not write a union with a type variable (`String | b`).
    if source.contains("...")
        && shown.iter().any(|t| {
            t.split(" | ").skip(1).any(|m| {
                let v: String = m
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric())
                    .collect();
                v.len() == 1 && v.chars().all(|c| c.is_ascii_lowercase())
            })
        })
    {
        features.insert("spread of unknown");
    }
    for text in &shown {
        if text.contains("never") {
            features.insert("never");
        }
    }
    (typing, features)
}

/// Whether the program's last statement is a `try`: inty types the last
/// expression of a program, but one inside a `try` block as a statement,
/// where the model types it as the program's value.
fn ends_in_try(e: &Core) -> bool {
    match e {
        Let(_, _, _, body) | Seq(_, body) => ends_in_try(body),
        TryCatch(..) | TryFinally(..) => true,
        _ => false,
    }
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
        // Roadmap phase 7 (optional parameters): a function literal with
        // fewer parameters than the function type expected of it, which
        // ignores the extra arguments, as JavaScript does.
        (Typing::Type(_), Typing::Reject) if features.contains("fewer parameters") => {
            Some("fewer parameters than the expected function type")
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
        // inty's unifier gives up ("Type too complex") on some spreads over
        // an object whose type is recursive through a method's `this`
        // (`this.a = {...this.a}` in a method that returns `this`): its
        // spread shares the operand's open row tail where the model merges
        // slot by slot (roadmap: a deferred `Spread` constraint).
        (Typing::Reject, Typing::Type(_)) if features.contains("unify depth") => {
            Some("inty's unifier gives up on a spread over a recursive type")
        }
        // The same roadmap item: a spread over an operand of an unknown
        // type, whose fields the model merges once the operand is known.
        (Typing::Reject, Typing::Type(_)) if features.contains("spread of unknown") => {
            Some("inty's spread over an operand of an unknown type")
        }
        // inty reads a field every arm of a discriminated union has (its
        // tag, say) without a test of the tag; the model reads a variant's
        // fields only once a test has taken it apart.
        (Typing::Type(_), Typing::Reject) if features.contains("variant field") => {
            Some("a variant's field read without a test of its tag")
        }
        // inty joins a sum (or a variant) with one of its cases to the sum;
        // the model's branches must agree (sum-types-design: a waiting
        // `Join` constraint is still to come).
        (Typing::Type(_), Typing::Reject) if features.contains("try at end") => {
            Some("a `try` ending the program, whose value only the model types")
        }
        (Typing::Type(_), Typing::Reject) if features.contains("sum join") => {
            Some("a sum joined with one of its cases")
        }
        // inty keeps a record case after `typeof x !== "object"`: a
        // declaration may type a function as a record (`Promise`); the
        // model's records are only object literals'.
        (Typing::Reject | Typing::Type(_), Typing::Type(_))
            if features.contains("typeof object") =>
        {
            Some("a record case kept after `typeof x !== \"object\"`")
        }
        _ => None,
    }
}

/// Whether `e` reads a property of a variable that holds a variant (an
/// annotated one, an alias of one, or the rest of one a test of its tag
/// took apart, if two cases or more are left).
fn reads_variant_field(e: &Core) -> bool {
    scan_held(e, &mut Vec::new(), true, &|e, held, _| match e {
        Get(x, _) | Set(x, _, _) | MCall(x, _, _) => {
            matches!(held_by(held, x), Some(T::Variant(..)))
        }
        _ => false,
    })
}

/// Whether `e` joins a variable that holds a sum (one told apart by
/// `typeof`, a nullable or optional one, or a variant) with something
/// else, where the joined value is used: a branch of a conditional, or an
/// array's element. inty joins a sum with one of its cases to the sum; the
/// model's branches agree on one type.
fn joins_sum(e: &Core) -> bool {
    // `x` holds a sum `y` doesn't (`y` another variable of the same sum is
    // no join).
    let joins = |held: &[Option<T>], x: &Core, y: &Core| {
        held_by(held, x).is_some_and(|t| held_by(held, y) != Some(t))
    };
    scan_held(e, &mut Vec::new(), true, &|e, held, used| match e {
        Cond(_, y, z) => used && (joins(held, y, z) || joins(held, z, y)),
        Arr(es) => es.iter().any(|x| es.iter().any(|y| joins(held, x, y))),
        _ => false,
    })
}

/// Whether `e` tests a value's `typeof` against `"object"`.
fn tests_typeof_object(e: &Core) -> bool {
    scan_held(
        e,
        &mut Vec::new(),
        true,
        &|e, _, _| matches!(e, TypeTest(_, t, _, _) if t == "object"),
    )
}

/// The sum variable `x` holds, if it's one.
fn held_by(held: &[Option<T>], x: &Core) -> Option<T> {
    match x {
        Var(i) if held.len() > *i => held[held.len() - 1 - i].clone(),
        _ => None,
    }
}

/// Whether `hit` holds of a subterm of `e`, `held` giving the sum each
/// variable in scope holds, if any (an annotated one, an alias of one, or
/// the rest of one a test took apart, if two cases or more are left), and
/// `used` whether `e`'s value is used (not a statement's, dropped).
fn scan_held(
    e: &Core,
    held: &mut Vec<Option<T>>,
    used: bool,
    hit: &dyn Fn(&Core, &[Option<T>], bool) -> bool,
) -> bool {
    if hit(e, held, used) {
        return true;
    }
    let under = |held: &mut Vec<Option<T>>, bound: &[Option<T>], x: &Core, used: bool| {
        held.extend_from_slice(bound);
        let r = scan_held(x, held, used, hit);
        held.truncate(held.len() - bound.len());
        r
    };
    let go = |held: &mut Vec<Option<T>>, x: &Core| scan_held(x, held, true, hit);
    match e {
        Let(_, ann, x, y) => {
            let v = match ann {
                Some(t @ (T::Variant(..) | T::Sum(_) | T::Maybe(..))) => Some(t.clone()),
                _ => held_by(held, x),
            };
            go(held, x) || under(held, &[v], y, used)
        }
        CaseTag(x, _, t, y, z) => {
            let rest = match held_by(held, x) {
                Some(T::Variant(l, cases)) => {
                    let rest: Vec<_> = cases.into_iter().filter(|(tag, _)| tag != t).collect();
                    (rest.len() > 1).then_some(T::Variant(l, rest))
                }
                _ => None,
            };
            go(held, x) || under(held, &[rest], y, used) || under(held, &[None], z, used)
        }
        TypeTest(x, t, y, z) => {
            let rest = match held_by(held, x) {
                Some(T::Sum(arms)) => {
                    let rest: Vec<_> = arms.into_iter().filter(|a| Gen::type_tag(a) != t).collect();
                    (rest.len() > 1).then_some(T::Sum(rest))
                }
                _ => None,
            };
            go(held, x) || under(held, &[rest], y, used) || under(held, &[None], z, used)
        }
        Func(n, body) | Method(n, body) => under(held, &vec![None; n + 2], body, true),
        Getter(body) => under(held, &[None, None], body, true),
        TryCatch(x, y) => scan_held(x, held, used, hit) || under(held, &[None], y, used),
        Unwrap(x, y, z) => {
            go(held, x) || scan_held(y, held, used, hit) || under(held, &[None], z, used)
        }
        // A class's members see binders of its own; not followed.
        Class(..) => false,
        App(f, args) | New(f, args) | MCall(f, _, args) => {
            go(held, f) || args.iter().any(|a| go(held, a))
        }
        Assign(_, x) | Not(x) | Typeof(x) | Neg(x) | Ret(x) | Throw(x) | Get(x, _) => go(held, x),
        // A statement's value is dropped.
        Seq(x, y) => scan_held(x, held, false, hit) || scan_held(y, held, used, hit),
        While(x, y) => go(held, x) || scan_held(y, held, false, hit),
        TryFinally(x, y) => scan_held(x, held, used, hit) || scan_held(y, held, false, hit),
        Plus(x, y) | Minus(x, y) | Bin(_, x, y) | Spread(x, y) | Index(x, y) | Set(x, _, y) => {
            go(held, x) || go(held, y)
        }
        Cond(x, y, z) => {
            go(held, x) || scan_held(y, held, used, hit) || scan_held(z, held, used, hit)
        }
        SetIndex(x, y, z) => go(held, x) || go(held, y) || go(held, z),
        Obj(fields) => fields.iter().any(|(_, e)| go(held, e)),
        Arr(es) => es.iter().any(|e| go(held, e)),
        Num(..) | Str(_) | Bool(_) | Undef | Null | Var(_) | Break | Continue => false,
    }
}

#[test]
fn inty_agrees_with_the_lean_model() {
    let Some(model) = model_path() else {
        assert!(
            std::env::var_os("INTY_REQUIRE_MODEL").is_none(),
            "no inty-model, and INTY_REQUIRE_MODEL is set"
        );
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
        no_this: 0,
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
        let reads_variant = reads_variant_field(core);
        let sum_join = joins_sum(core);
        let (typing, mut features, run) =
            inty::worker::run_with_inference_stack("inty-differential", move || {
                let parse = |src: &str| {
                    inty::frontends::javascript::parse_source(src).unwrap_or_else(|e| {
                        panic!("generated JavaScript doesn't parse: {e}\n{src}")
                    })
                };
                let program = parse(&source);
                let (typing, features) = inty_typing(&program, &source);
                (typing, features, inty_run(&program))
            });
        if reads_variant {
            features.insert("variant field");
        }
        if sum_join {
            features.insert("sum join");
        }
        if tests_typeof_object(core) {
            features.insert("typeof object");
        }
        if ends_in_try(core) {
            features.insert("try at end");
        }
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
        if wire(&programs[i]).contains("(mcall") && accepted && model_accepted {
            *counts
                .entry("both accept, with a method call".into())
                .or_default() += 1;
        }
        if wire(&programs[i]).contains("(method ") && accepted && model_accepted {
            *counts
                .entry("both accept, with a method written `m() {…}`".into())
                .or_default() += 1;
        }
        if wire(&programs[i]).contains("(ctor ") {
            *counts
                .entry(format!(
                    "with a class, {}",
                    match (accepted, model_accepted) {
                        (true, true) => "both accept",
                        (false, false) => "both reject",
                        _ => "they disagree",
                    }
                ))
                .or_default() += 1;
        }
        if wire(&programs[i]).contains("(new (get ") {
            *counts
                .entry(format!(
                    "`new` on an arrow field, {}",
                    if accepted || model_accepted {
                        "accepted"
                    } else {
                        "both reject"
                    }
                ))
                .or_default() += 1;
        }
        // `INTY_DIFF_SUMS=1` prints every disagreement on a program with a
        // sum or a test for nothing or of a tag, whatever it is put down to.
        if std::env::var_os("INTY_DIFF_SUMS").is_some()
            && accepted != model_accepted
            && [
                "(unwrap ",
                "(nullable ",
                "(optional ",
                "(variant ",
                "(casetag ",
                "(sum ",
                "(typetest ",
            ]
            .iter()
            .any(|f| wire(&programs[i]).contains(f))
        {
            eprintln!("{}", report("sum disagreement"));
        }
        for (form, what) in [
            ("(unwrap ", "with a test for nothing (`!= null`, `??`)"),
            ("(nullable ", "with a `T | Null` annotation"),
            ("(optional ", "with a `T | Undefined` annotation"),
            ("(variant ", "with a variant annotation"),
            ("(casetag ", "with a test of a variant's tag"),
            ("(sum ", "with a sum told apart by typeof"),
            ("(typetest ", "with a test of typeof"),
            ("(times ", "with `*`"),
            ("(div ", "with `/`"),
            ("(lt ", "with `<`"),
            ("(ge ", "with `>=`"),
            ("(eq ", "with `===`"),
        ] {
            if wire(&programs[i]).contains(form) {
                *counts
                    .entry(format!(
                        "{what}, {}",
                        match (accepted, model_accepted) {
                            (true, true) => "both accept",
                            (false, false) => "both reject",
                            _ => "they disagree",
                        }
                    ))
                    .or_default() += 1;
            }
        }
        if wire(&programs[i]).contains("ann ") {
            *counts
                .entry(format!(
                    "with an annotation, {}",
                    match (accepted, model_accepted) {
                        (true, true) => "both accept",
                        (false, false) => "both reject",
                        _ => "they disagree",
                    }
                ))
                .or_default() += 1;
        }
        if wire(&programs[i]).contains("(getter ") {
            *counts
                .entry(format!(
                    "with a getter, {}",
                    match (accepted, model_accepted) {
                        (true, true) => "both accept",
                        (false, false) => "both reject",
                        _ => "they disagree",
                    }
                ))
                .or_default() += 1;
        }

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
        let finished = |r: &Run| {
            matches!(
                r,
                Run::Value(_) | Run::Stuck(_) | Run::Thrown(_) | Run::Fault(_)
            )
        };
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
            // An index out of bounds is a fault in inty and the model, where
            // JavaScript reads `undefined` and goes on, perhaps to an error.
            let faulted = matches!(run, Run::Fault(_)) || matches!(model_run, Run::Fault(_));
            // Unbounded recursion runs both interpreters out of fuel, where
            // the engine overflows its stack with a `RangeError`, which a
            // `catch` can catch, going on to code they never reach.
            let both_timed_out = run == Run::Timeout && model_run == Run::Timeout;
            if let (Run::NativeError(name), false) = (engine_run, faulted || both_timed_out) {
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
