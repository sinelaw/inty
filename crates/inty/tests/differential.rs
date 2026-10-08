//! Differential testing against the Lean model (`lean/`).
//!
//! Generates random programs in the formalized core calculus, writes each
//! one as JavaScript for inty and in the model's wire format
//! (`lean/Inty/Wire.lean`) for `inty-model`, and compares:
//!
//! - **soundness**: a program inty accepts must not get stuck in
//!   `dynamics`, and one the model's inference accepts must not get stuck
//!   in the model's interpreter (the latter is a theorem; seeing it would
//!   mean a harness bug);
//! - **semantics**: when both interpreters finish, they agree on the value,
//!   or on getting stuck;
//! - **typing**: inty and the model's inference accept the same programs,
//!   at the same type.
//!
//! Disagreements the model doesn't cover yet are counted per category and
//! printed; any other disagreement fails the test.
//!
//! The model is `lean/.lake/build/bin/inty-model` (`cd lean && lake build`),
//! or `INTY_LEAN_MODEL`. Without it the test is skipped. `INTY_DIFF_CASES`
//! sets the number of programs (default 3000), `INTY_DIFF_SEED` the seed.

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
    /// `function f(x) { body }`: in `body`, 0 is `x` and 1 is `f`.
    Func(Box<Core>),
    App(Box<Core>, Box<Core>),
    /// `const v = e₁; e₂`; only at the top of a program or function body.
    Let(Box<Core>, Box<Core>),
    Cond(Box<Core>, Box<Core>, Box<Core>),
    Not(Box<Core>),
    Typeof(Box<Core>),
    Neg(Box<Core>),
    Plus(Box<Core>, Box<Core>),
    Minus(Box<Core>, Box<Core>),
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
        Func(body) => format!("(func {})", wire(body)),
        App(f, a) => format!("(app {} {})", wire(f), wire(a)),
        Let(e1, e2) => format!("(let {} {})", wire(e1), wire(e2)),
        Cond(c, t, e) => format!("(cond {} {} {})", wire(c), wire(t), wire(e)),
        Not(e) => format!("(not {})", wire(e)),
        Typeof(e) => format!("(typeof {})", wire(e)),
        Neg(e) => format!("(neg {})", wire(e)),
        Plus(x, y) => format!("(plus {} {})", wire(x), wire(y)),
        Minus(x, y) => format!("(minus {} {})", wire(x), wire(y)),
    }
}

/// The program with every number literal fractional (`n` becomes `n.5`),
/// so that inty types no number `Int`.
fn fractional(e: &Core) -> Core {
    let f = |e: &Core| b(fractional(e));
    match e {
        Num(m, x) => Num(m * 10 + 5, x + 1),
        Func(body) => Func(f(body)),
        App(x, y) => App(f(x), f(y)),
        Let(x, y) => Let(f(x), f(y)),
        Cond(c, t, e) => Cond(f(c), f(t), f(e)),
        Not(x) => Not(f(x)),
        Typeof(x) => Typeof(f(x)),
        Neg(x) => Neg(f(x)),
        Plus(x, y) => Plus(f(x), f(y)),
        Minus(x, y) => Minus(f(x), f(y)),
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
            Func(body) => {
                let (f, x) = (self.fresh("f"), self.fresh("x"));
                self.names.push(f.clone());
                self.names.push(x.clone());
                let body = self.body(body, "return ");
                self.names.truncate(self.names.len() - 2);
                format!("(function {}({}) {{ {} }})", f, x, body)
            }
            App(f, a) => format!("({})({})", self.expr(f), self.expr(a)),
            Let(..) => unreachable!("`const` only in statement position"),
            Cond(c, t, e) => format!("({} ? {} : {})", self.expr(c), self.expr(t), self.expr(e)),
            Not(e) => format!("!({})", self.expr(e)),
            Typeof(e) => format!("typeof ({})", self.expr(e)),
            Neg(e) => format!("-({})", self.expr(e)),
            Plus(x, y) => format!("({} + {})", self.expr(x), self.expr(y)),
            Minus(x, y) => format!("({} - {})", self.expr(x), self.expr(y)),
        }
    }

    /// A program or function body: its `const`s, then `last` and the value
    /// (`return` in a function, an expression statement at the top).
    fn body(&mut self, e: &Core, last: &str) -> String {
        let mut out = String::new();
        let mut pushed = 0;
        let mut e = e;
        while let Let(e1, e2) = e {
            let v = self.fresh("v");
            out += &format!("const {} = {}; ", v, self.expr(e1));
            self.names.push(v);
            pushed += 1;
            e = e2;
        }
        out += &format!("{}{};", last, self.expr(e));
        self.names.truncate(self.names.len() - pushed);
        out
    }
}

fn javascript(e: &Core) -> String {
    Js {
        names: Vec::new(),
        next: 0,
    }
    .body(e, "")
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
    Arrow(Box<T>, Box<T>),
}

/// What a variable in scope may be used as.
#[derive(Clone, Debug)]
enum Binding {
    Mono(T),
    /// `const id = function (x) { return x; }`: any `a → a`.
    PolyId,
    /// Untyped generation doesn't track types.
    Unknown,
}

struct Gen {
    rng: Rng,
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

    fn ty(&mut self, depth: usize) -> T {
        if depth > 0 && self.rng.chance(25) {
            T::Arrow(b2(self.ty(depth - 1)), b2(self.ty(depth - 1)))
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
            T::Arrow(..) => return None,
        })
    }

    /// A program of type `t`, mostly well typed.
    fn typed(&mut self, t: &T, depth: usize, scope: &mut Vec<Binding>, stmt: bool) -> Core {
        // A variable of the right type.
        let fits: Vec<usize> = (0..scope.len())
            .filter(|&i| match &scope[scope.len() - 1 - i] {
                Binding::Mono(u) => u == t,
                Binding::PolyId => matches!(t, T::Arrow(a, r) if a == r),
                Binding::Unknown => false,
            })
            .collect();
        if !fits.is_empty() && self.rng.chance(if depth == 0 { 80 } else { 30 }) {
            return Var(fits[self.rng.below(fits.len())]);
        }
        if depth == 0 {
            if let Some(l) = self.literal(t) {
                return l;
            }
        }
        let d = depth.saturating_sub(1);
        if stmt && depth > 0 && self.rng.chance(25) {
            // `const`: sometimes the polymorphic identity, used at
            // several types below.
            if self.rng.chance(30) {
                scope.push(Binding::PolyId);
                let rest = self.typed(t, d, scope, true);
                scope.pop();
                return Let(b(Func(b(Var(0)))), b(rest));
            }
            let s = self.ty(1);
            let e1 = self.typed(&s, d, scope, false);
            scope.push(Binding::Mono(s));
            let rest = self.typed(t, d, scope, true);
            scope.pop();
            return Let(b(e1), b(rest));
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
                let s = self.ty(1);
                let f = self.typed(&T::Arrow(b2(s.clone()), b2(t.clone())), d, scope, false);
                App(b(f), b(self.typed(&s, d, scope, false)))
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
                T::Arrow(a, r) => {
                    scope.push(Binding::Mono(t.clone()));
                    scope.push(Binding::Mono((**a).clone()));
                    let body = self.typed(r, d, scope, true);
                    scope.truncate(scope.len() - 2);
                    Func(b(body))
                }
                _ => self.literal(t).unwrap(),
            },
        }
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
        match self.rng.below(if stmt { 11 } else { 10 }) {
            0 => {
                scope.push(Binding::Unknown);
                scope.push(Binding::Unknown);
                let body = self.any(d, scope, true);
                scope.truncate(scope.len() - 2);
                Func(b(body))
            }
            1 | 2 => App(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            3 => Cond(
                b(self.any(d, scope, false)),
                b(self.any(d, scope, false)),
                b(self.any(d, scope, false)),
            ),
            4 => Not(b(self.any(d, scope, false))),
            5 => Typeof(b(self.any(d, scope, false))),
            6 => Neg(b(self.any(d, scope, false))),
            7 | 8 => Plus(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            9 => Minus(b(self.any(d, scope, false)), b(self.any(d, scope, false))),
            _ => {
                let e1 = self.any(d, scope, false);
                scope.push(Binding::Unknown);
                let rest = self.any(d, scope, true);
                scope.pop();
                Let(b(e1), b(rest))
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
    Ambiguous,
    Reject,
}

/// An interpreter's verdict.
#[derive(Clone, Debug, PartialEq)]
enum Run {
    Value(String),
    Stuck(String),
    Timeout,
    Unsupported,
}

fn core_type(t: &Type) -> String {
    match t {
        Type::Number | Type::Int | Type::Literal(LitValue::Number(_)) => "number".into(),
        Type::String | Type::Literal(LitValue::String(_)) => "string".into(),
        Type::Boolean | Type::Literal(LitValue::Bool(_)) => "boolean".into(),
        Type::Undefined => "undefined".into(),
        Type::Null => "null".into(),
        Type::Func { .. } | Type::Row(_) => "fun".into(),
        Type::Var(_) => "var".into(),
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

fn inty_typing(program: &inty::ast::Program) -> (Typing, Features) {
    let mut state = InferState::new();
    state.expr_types = Some(std::collections::HashMap::new());
    // As the CLI checks: infer, then resolve the class constraints.
    let typing = match state.infer_program(&initial_env(), program) {
        Ok(ty) if state.take_errors().is_empty() && state.resolve_constraints().is_ok() => {
            Typing::Type(core_type(&state.apply_subst(&ty)))
        }
        _ => Typing::Reject,
    };
    let mut features = Features::new();
    for ty in state.expr_types.take().unwrap_or_default().values() {
        let ty = state.flatten_type(ty);
        if format!("{}", ty).contains('μ') {
            features.insert("recursive types");
        }
        if core_type(&ty).contains("union(") {
            features.insert("unions");
        }
    }
    (typing, features)
}

fn number_wire(n: f64) -> String {
    // One NaN, whatever its payload.
    let n = if n.is_nan() { f64::NAN } else { n };
    format!("num {}", n.to_bits())
}

fn inty_run(program: &inty::ast::Program) -> Run {
    match run_to_end_with_fuel(program, 1_500) {
        Ok(v) => Run::Value(match v {
            Value::Number(n) => number_wire(n),
            Value::String(s) => format!("str s:{}", s),
            Value::Boolean(v) => format!("bool {}", v),
            Value::Undefined => "undef".into(),
            Value::Null => "null".into(),
            Value::Closure(_) | Value::Builtin(_) => "fun".into(),
            other => format!("other {}", other),
        }),
        Err(Stuck::FuelExhausted) => Run::Timeout,
        Err(Stuck::NotImplemented(_)) => Run::Unsupported,
        Err(Stuck::UndefinedVariable(_)) => Run::Stuck("undefinedVariable".into()),
        Err(Stuck::NotCallable(_)) => Run::Stuck("notCallable".into()),
        Err(Stuck::TypeMismatch { .. }) => Run::Stuck("typeMismatch".into()),
        Err(other) => Run::Stuck(format!("other {}", other)),
    }
}

fn parse_model_line(line: &str) -> (Typing, Run) {
    let (typing, run) = line
        .split_once(';')
        .unwrap_or_else(|| panic!("bad model line: {line}"));
    let typing = match typing {
        "reject" => Typing::Reject,
        "ambiguous" => Typing::Ambiguous,
        t => Typing::Type(t.strip_prefix("type ").expect(line).to_string()),
    };
    let run = if run == "timeout" {
        Run::Timeout
    } else if let Some(v) = run.strip_prefix("value ") {
        // Canonicalise NaN the same way as inty's side.
        Run::Value(match v.strip_prefix("num ") {
            Some(bits) => number_wire(f64::from_bits(bits.parse().expect(line))),
            None => v.to_string(),
        })
    } else {
        Run::Stuck(run.strip_prefix("stuck ").expect(line).to_string())
    };
    (typing, run)
}

/// Run the model on every program, in one process.
fn run_model(model: &PathBuf, programs: &[Core]) -> Vec<(Typing, Run)> {
    let mut child = Command::new(model)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("start inty-model");
    let input: String = programs.iter().map(|p| wire(p) + "\n").collect();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || {
        stdin.write_all(input.as_bytes()).unwrap();
    });
    let out: Vec<(Typing, Run)> = BufReader::new(child.stdout.take().unwrap())
        .lines()
        .map(|l| parse_model_line(&l.unwrap()))
        .collect();
    writer.join().unwrap();
    assert!(child.wait().unwrap().success(), "inty-model failed");
    assert_eq!(
        out.len(),
        programs.len(),
        "inty-model answered too few lines"
    );
    out
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
        // A `Plus` constraint nothing resolves (lean/README.md, roadmap
        // step 2): inty defaults it; the model has no defaulting.
        (Typing::Type(_), Typing::Ambiguous) => Some("ambiguous Plus constraint"),
        // Roadmap step 7: `c ? 1 : null` is `Number | Null` in inty, and
        // `c ? undefined : x` is `Undefined | t`, where the model unifies.
        (Typing::Type(_), Typing::Reject) if features.contains("unions") => {
            Some("unions (a nullable join)")
        }
        (Typing::Type(t), Typing::Type(_)) if t.starts_with("union(") => {
            Some("unions (a nullable join)")
        }
        // Roadmap step 10: `function f(x) { return f; }`.
        (Typing::Type(_), Typing::Reject) if features.contains("recursive types") => {
            Some("equi-recursive types")
        }
        // Roadmap step 7, the other way: the model folds `Int` into
        // `number`, but in inty `Int ≤ Number` holds for values only, so
        // `(a) => Int` and `(b) => Number` don't join. Evidence: inty
        // accepts the program once no literal is an `Int`.
        (Typing::Reject, Typing::Type(_)) if features.contains("Int") => {
            Some("Int and Number (the model has only number)")
        }
        // inty's nullable join (`c ? undefined : x` is `Undefined | t`
        // even for an unknown `t`) can make an HM-typable program an
        // infinite type, or fail to unify.
        (Typing::Reject, Typing::Type(_) | Typing::Ambiguous) if features.contains("unions") => {
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
    };
    let programs: Vec<Core> = (0..cases).map(|_| gen.program()).collect();
    let answers = run_model(&model, &programs);

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut known: BTreeMap<&str, (usize, String)> = BTreeMap::new();
    let mut failures = Vec::new();
    for (core, (model_typing, model_run)) in programs.iter().zip(answers) {
        let js = javascript(core);
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
                let (typing, mut features) = inty_typing(&program);
                if typing == Typing::Reject
                    && matches!(inty_typing(&parse(&fractional_source)).0, Typing::Type(_))
                {
                    features.insert("Int");
                }
                (typing, features, inty_run(&program))
            });
        let report = |what: &str| {
            format!(
                "{what}\n  js:    {js}\n  core:  {}\n  inty:  {:?} / {:?}\n  model: {:?} / {:?}",
                wire(core),
                typing,
                run,
                model_typing,
                model_run
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
                    Typing::Ambiguous => "is ambiguous",
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
        let finished = |r: &Run| matches!(r, Run::Value(_) | Run::Stuck(_));
        if finished(&run) && finished(&model_run) && run != model_run {
            failures.push(report("the interpreters disagree"));
        }
        // Typing.
        if typing != model_typing
            && (accepted || model_accepted || model_typing == Typing::Ambiguous)
        {
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
