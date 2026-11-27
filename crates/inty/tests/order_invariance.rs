//! Order-invariance property tests: what a program's bindings are typed
//! doesn't depend on the order the checker meets things in.
//!
//! Each property generates a program (functions, nested functions,
//! objects whose methods use `this`, closures, calls, member reads), checks
//! it, applies a change that keeps its meaning (as far as types go), checks
//! that, and asserts the two agree: the same type for every binding both
//! have, and errors in both or neither. The changes:
//!
//! - none: the same program checked twice (hash seeds differ between
//!   runs, so anything that depends on a hash map's order shows here);
//! - unrelated code added anywhere (new names, at the top level and in
//!   function bodies), which only adds to the substitution, the pending
//!   constraints and the recursive types inference keeps;
//! - function declarations (hoisted, so their order means nothing)
//!   reordered;
//! - each comparison's operands swapped, and each object literal's
//!   fields and methods written in the other order, which flips the order
//!   in which unification meets them.

use std::collections::{BTreeMap, BTreeSet};

use proptest::prelude::*;

// -------------------------------------------------------------------------
// Programs, as a small model rendered to source.
// -------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum E {
    Num(i32),
    Str(&'static str),
    Bool(bool),
    Ref(String),
    This(&'static str),
    Member(Box<E>, &'static str),
    Call(String, Vec<E>),
    MethodCall(Box<E>, &'static str, Vec<E>),
    Eq(Box<E>, Box<E>),
    Add(Box<E>, Box<E>),
    Obj(Vec<(&'static str, E)>),
    Arrow(Vec<String>, Box<E>),
    Arr(Vec<E>),
}

#[derive(Debug, Clone)]
struct Method {
    key: &'static str,
    params: Vec<String>,
    ret: E,
}

#[derive(Debug, Clone)]
enum Item {
    Fn {
        name: String,
        params: Vec<String>,
        body: Vec<Item>,
        ret: E,
    },
    Const {
        name: String,
        init: E,
    },
    Obj {
        name: String,
        fields: Vec<(&'static str, E)>,
        methods: Vec<Method>,
    },
    Expr(E),
}

#[derive(Debug, Clone)]
struct Prog {
    items: Vec<Item>,
}

/// How to write a program out: the order of object fields and methods,
/// and of comparison operands.
#[derive(Clone, Copy, Default)]
struct Style {
    flip: bool,
}

fn render_e(e: &E, st: Style, out: &mut String) {
    match e {
        E::Num(n) => out.push_str(&n.to_string()),
        E::Str(s) => out.push_str(&format!("{s:?}")),
        E::Bool(b) => out.push_str(&b.to_string()),
        E::Ref(n) => out.push_str(n),
        E::This(k) => out.push_str(&format!("this.{k}")),
        E::Member(o, k) => {
            out.push('(');
            render_e(o, st, out);
            out.push_str(&format!(").{k}"));
        }
        E::Call(f, args) => {
            out.push_str(f);
            render_args(args, st, out);
        }
        E::MethodCall(o, k, args) => {
            out.push('(');
            render_e(o, st, out);
            out.push_str(&format!(").{k}"));
            render_args(args, st, out);
        }
        E::Eq(l, r) => {
            let (l, r) = if st.flip { (r, l) } else { (l, r) };
            out.push('(');
            render_e(l, st, out);
            out.push_str(" === ");
            render_e(r, st, out);
            out.push(')');
        }
        E::Add(l, r) => {
            out.push('(');
            render_e(l, st, out);
            out.push_str(" + ");
            render_e(r, st, out);
            out.push(')');
        }
        E::Obj(fields) => {
            out.push_str("({");
            let mut fs: Vec<&(&str, E)> = fields.iter().collect();
            if st.flip {
                fs.reverse();
            }
            for (i, (k, v)) in fs.into_iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!("{k}: "));
                render_e(v, st, out);
            }
            out.push_str("})");
        }
        E::Arrow(params, body) => {
            out.push_str(&format!("(({}) => ", params.join(", ")));
            render_e(body, st, out);
            out.push(')');
        }
        E::Arr(es) => {
            out.push('[');
            for (i, e) in es.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_e(e, st, out);
            }
            out.push(']');
        }
    }
}

fn render_args(args: &[E], st: Style, out: &mut String) {
    out.push('(');
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        render_e(a, st, out);
    }
    out.push(')');
}

fn render_items(items: &[Item], st: Style, indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    for item in items {
        out.push_str(&pad);
        match item {
            Item::Fn {
                name,
                params,
                body,
                ret,
            } => {
                out.push_str(&format!("function {name}({}) {{\n", params.join(", ")));
                render_items(body, st, indent + 1, out);
                out.push_str(&format!("{pad}  return "));
                render_e(ret, st, out);
                out.push_str(&format!(";\n{pad}}}\n"));
            }
            Item::Const { name, init } => {
                out.push_str(&format!("const {name} = "));
                render_e(init, st, out);
                out.push_str(";\n");
            }
            Item::Obj {
                name,
                fields,
                methods,
            } => {
                out.push_str(&format!("const {name} = {{\n"));
                let mut parts: Vec<String> = Vec::new();
                for (k, v) in fields {
                    let mut s = format!("{pad}  {k}: ");
                    render_e(v, st, &mut s);
                    parts.push(s);
                }
                for m in methods {
                    let mut s = format!("{pad}  {}({}) {{ return ", m.key, m.params.join(", "));
                    render_e(&m.ret, st, &mut s);
                    s.push_str("; }");
                    parts.push(s);
                }
                if st.flip {
                    parts.reverse();
                }
                out.push_str(&parts.join(",\n"));
                out.push_str(&format!("\n{pad}}};\n"));
            }
            Item::Expr(e) => {
                out.push('(');
                render_e(e, st, out);
                out.push_str(");\n");
            }
        }
    }
}

fn render(p: &Prog, st: Style) -> String {
    let mut out = String::new();
    render_items(&p.items, st, 0, &mut out);
    out
}

// -------------------------------------------------------------------------
// Generation: from a seed, a program that mostly checks. Each name is
// used as what it is (a number, a string, a record, a function of some
// parameters, an object of some fields and methods), so most programs
// have no error and their types say something. A parameter is a number,
// a string, or generic: one that is only passed on, stored or returned,
// so its function is polymorphic. Every function of a scope is known to
// the bodies in it (they are hoisted), so groups of mutually recursive
// functions come up; values are known after they are declared. Objects'
// methods read their object's fields and call its methods through
// `this`, which is what makes recursive types.
// -------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// What a value is.
#[derive(Debug, Clone, PartialEq)]
enum K {
    Num,
    Str,
    Bool,
    /// A generic parameter, by name: only it gives one.
    Any(String),
    Rec(Vec<(&'static str, K)>),
}

#[derive(Debug, Clone)]
struct Sig {
    params: Vec<(String, K)>,
    ret: K,
}

#[derive(Debug, Clone)]
enum Bound {
    Val(K),
    Func(Sig),
    Obj {
        fields: Vec<(&'static str, K)>,
        methods: Vec<(&'static str, Sig)>,
    },
}

/// One way to make an expression.
type Make<'a> = Box<dyn Fn(&mut Gen) -> E + 'a>;
type Fields = Vec<(&'static str, K)>;
type Methods = Vec<(&'static str, Sig)>;

#[derive(Clone, Default)]
struct Scope {
    names: Vec<(String, Bound)>,
    /// Inside a method: its object's fields and methods.
    this: Option<(Fields, Methods)>,
    /// Inside a function: calls pass a number to a generic parameter
    /// (a call inside a recursive group isn't polymorphic).
    in_function: bool,
}

struct Gen {
    rng: Rng,
    next_name: usize,
}

const KEYS: &[&str] = &["k", "v", "w"];
const MKEYS: &[&str] = &["m", "n", "q"];

impl Gen {
    fn name(&mut self, prefix: &str) -> String {
        self.next_name += 1;
        format!("{prefix}{}", self.next_name)
    }

    fn kind(&mut self, depth: u32) -> K {
        match self.rng.below(if depth == 0 { 3 } else { 4 }) {
            0 => K::Num,
            1 => K::Str,
            2 => K::Bool,
            _ => {
                let n = 1 + self.rng.below(2);
                K::Rec(
                    KEYS[..n]
                        .iter()
                        .map(|k| (*k, self.kind(depth - 1)))
                        .collect(),
                )
            }
        }
    }

    fn sig(&mut self, prefix: &str) -> Sig {
        let n = self.rng.below(3);
        let params: Vec<(String, K)> = (0..n)
            .map(|_| {
                let name = self.name(prefix);
                // (A record parameter's fields are read: until a use
                // decides them, they are variables its type holds.)
                let k = match self.rng.below(4) {
                    0 => K::Num,
                    1 => K::Str,
                    2 => K::Any(name.clone()),
                    _ => K::Rec(vec![("k", self.kind(0)), ("v", self.kind(0))]),
                };
                (name, k)
            })
            .collect();
        let generic: Vec<&(String, K)> = params
            .iter()
            .filter(|(_, k)| matches!(k, K::Any(_)))
            .collect();
        let ret = if !generic.is_empty() && self.rng.chance(40) {
            generic[self.rng.below(generic.len())].1.clone()
        } else {
            self.kind(1)
        };
        Sig { params, ret }
    }

    fn args(&mut self, sc: &Scope, sig: &Sig, depth: u32) -> Vec<E> {
        sig.params
            .iter()
            .map(|(_, k)| match k {
                K::Any(_) => {
                    let k = if sc.in_function { K::Num } else { self.kind(1) };
                    self.expr(sc, &k, depth)
                }
                k => self.expr(sc, k, depth),
            })
            .collect()
    }

    /// An expression giving a `want`.
    fn expr(&mut self, sc: &Scope, want: &K, depth: u32) -> E {
        let mut options: Vec<Make<'_>> = Vec::new();
        match want {
            K::Num => options.push(Box::new(|g| E::Num(g.rng.below(7) as i32 - 3))),
            K::Str => options.push(Box::new(|g| E::Str(["s", "t"][g.rng.below(2)]))),
            K::Bool => options.push(Box::new(|g| E::Bool(g.rng.chance(50)))),
            K::Any(p) => options.push(Box::new(move |_| E::Ref(p.clone()))),
            K::Rec(fields) => options.push(Box::new(move |g| {
                E::Obj(
                    fields
                        .iter()
                        .map(|(k, fk)| (*k, g.expr(sc, fk, depth.saturating_sub(1))))
                        .collect(),
                )
            })),
        }
        for (name, b) in &sc.names {
            match b {
                Bound::Val(k) if k == want => options.push(Box::new(move |_| E::Ref(name.clone()))),
                Bound::Val(K::Rec(fs)) => {
                    for (key, fk) in fs {
                        if fk == want {
                            options.push(Box::new(move |_| {
                                E::Member(Box::new(E::Ref(name.clone())), key)
                            }));
                        }
                    }
                }
                Bound::Func(sig) if depth > 0 && &sig.ret == want => {
                    options.push(Box::new(move |g| {
                        E::Call(name.clone(), g.args(sc, sig, depth - 1))
                    }))
                }
                Bound::Obj { fields, methods } => {
                    for (key, fk) in fields {
                        if fk == want {
                            options.push(Box::new(move |_| {
                                E::Member(Box::new(E::Ref(name.clone())), key)
                            }));
                        }
                    }
                    for (key, sig) in methods {
                        if depth > 0 && &sig.ret == want {
                            options.push(Box::new(move |g| {
                                E::MethodCall(
                                    Box::new(E::Ref(name.clone())),
                                    key,
                                    g.args(sc, sig, depth - 1),
                                )
                            }));
                        }
                    }
                }
                _ => {}
            }
        }
        if let Some((fields, methods)) = &sc.this {
            for (key, fk) in fields {
                if fk == want {
                    options.push(Box::new(move |_| E::This(key)));
                }
            }
            for (key, sig) in methods {
                if depth > 0 && &sig.ret == want {
                    options.push(Box::new(move |g| {
                        E::MethodCall(
                            Box::new(E::Ref("this".into())),
                            key,
                            g.args(sc, sig, depth - 1),
                        )
                    }));
                }
            }
        }
        if depth > 0 {
            match want {
                K::Num | K::Str => options.push(Box::new(move |g| {
                    E::Add(
                        Box::new(g.expr(sc, want, depth - 1)),
                        Box::new(g.expr(sc, want, depth - 1)),
                    )
                })),
                K::Bool => options.push(Box::new(move |g| {
                    let k = [K::Num, K::Str][g.rng.below(2)].clone();
                    E::Eq(
                        Box::new(g.expr(sc, &k, depth - 1)),
                        Box::new(g.expr(sc, &k, depth - 1)),
                    )
                })),
                _ => {}
            }
        }
        let i = self.rng.below(options.len());
        options[i](self)
    }

    /// A scope's items: `n` of them, its functions known throughout.
    fn items(&mut self, outer: &Scope, n: usize, depth: u32) -> Vec<Item> {
        enum Plan {
            Fn(String, Sig),
            Local,
            Const,
            Obj,
            Expr,
        }
        let plans: Vec<Plan> = (0..n)
            .map(|_| match self.rng.below(if depth == 0 { 7 } else { 6 }) {
                0 | 1 => {
                    let name = self.name("f");
                    let sig = self.sig("x");
                    Plan::Fn(name, sig)
                }
                2 => Plan::Local,
                3 => Plan::Const,
                4 => Plan::Obj,
                _ => Plan::Expr,
            })
            .collect();
        let mut sc = outer.clone();
        for p in &plans {
            if let Plan::Fn(name, sig) = p {
                sc.names.push((name.clone(), Bound::Func(sig.clone())));
            }
        }
        let mut items = Vec::new();
        for p in plans {
            match p {
                Plan::Fn(name, sig) => {
                    let mut inner = sc.clone();
                    inner.in_function = true;
                    inner.this = None;
                    for (pn, pk) in &sig.params {
                        inner.names.push((pn.clone(), Bound::Val(pk.clone())));
                    }
                    let body = if depth > 0 && self.rng.chance(50) {
                        let n = 1 + self.rng.below(2);
                        self.items(&inner, n, depth - 1)
                    } else {
                        Vec::new()
                    };
                    let ret = self.expr(&inner, &sig.ret, 2);
                    items.push(Item::Fn {
                        name,
                        params: sig.params.iter().map(|(n, _)| n.clone()).collect(),
                        body,
                        ret,
                    });
                }
                // A function as a `const`: not hoisted, so generalised where
                // it is, after what the scope did before it (which may have
                // decided more of what the environment holds).
                Plan::Local => {
                    let sig = self.sig("u");
                    let mut inner = sc.clone();
                    inner.in_function = true;
                    inner.this = None;
                    for (pn, pk) in &sig.params {
                        inner.names.push((pn.clone(), Bound::Val(pk.clone())));
                    }
                    let body = self.expr(&inner, &sig.ret, 2);
                    let name = self.name("l");
                    let params = sig.params.iter().map(|(n, _)| n.clone()).collect();
                    sc.names.push((name.clone(), Bound::Func(sig)));
                    items.push(Item::Const {
                        name,
                        init: E::Arrow(params, Box::new(body)),
                    });
                }
                Plan::Const => {
                    let k = self.kind(1);
                    let init = self.expr(&sc, &k, 2);
                    let name = self.name("c");
                    sc.names.push((name.clone(), Bound::Val(k)));
                    items.push(Item::Const { name, init });
                }
                Plan::Obj => {
                    let nf = 1 + self.rng.below(2);
                    let fields: Vec<(&'static str, K)> =
                        KEYS[..nf].iter().map(|k| (*k, self.kind(0))).collect();
                    let nm = self.rng.below(3);
                    let msigs: Vec<(&'static str, Sig)> =
                        MKEYS[..nm].iter().map(|k| (*k, self.sig("y"))).collect();
                    let mut fvals = Vec::new();
                    for (k, fk) in &fields {
                        fvals.push((*k, self.expr(&sc, fk, 1)));
                    }
                    let mut methods = Vec::new();
                    for (key, sig) in &msigs {
                        let mut inner = sc.clone();
                        inner.in_function = true;
                        inner.this = Some((fields.clone(), msigs.clone()));
                        for (pn, pk) in &sig.params {
                            inner.names.push((pn.clone(), Bound::Val(pk.clone())));
                        }
                        let ret = self.expr(&inner, &sig.ret, 2);
                        methods.push(Method {
                            key,
                            params: sig.params.iter().map(|(n, _)| n.clone()).collect(),
                            ret,
                        });
                    }
                    let name = self.name("o");
                    sc.names.push((
                        name.clone(),
                        Bound::Obj {
                            fields,
                            methods: msigs,
                        },
                    ));
                    items.push(Item::Obj {
                        name,
                        fields: fvals,
                        methods,
                    });
                }
                Plan::Expr => {
                    let k = self.kind(1);
                    items.push(Item::Expr(self.expr(&sc, &k, 2)));
                }
            }
        }
        items
    }
}

fn program() -> impl Strategy<Value = Prog> {
    (any::<u64>(), 1usize..8).prop_map(|(seed, n)| {
        let mut g = Gen {
            rng: Rng(seed | 1),
            next_name: 0,
        };
        Prog {
            items: g.items(&Scope::default(), n, 2),
        }
    })
}

// -------------------------------------------------------------------------
// The changes.
// -------------------------------------------------------------------------

/// Code that mentions nothing of the program's: names `z0`, `z1`, … of
/// its own, literals, and its own parameters and `this`.
fn unrelated(n: usize) -> Item {
    let z = |i: usize| format!("z{}", n * 10 + i);
    match n % 4 {
        0 => Item::Obj {
            name: z(0),
            fields: vec![("k", E::Num(1))],
            methods: vec![Method {
                key: "m",
                params: vec!["x".into()],
                ret: E::Add(Box::new(E::This("k")), Box::new(E::Ref("x".into()))),
            }],
        },
        1 => Item::Fn {
            name: z(0),
            params: vec!["x".into()],
            body: vec![Item::Fn {
                name: z(1),
                params: vec!["y".into()],
                body: vec![],
                ret: E::Obj(vec![("v", E::Ref("x".into())), ("k", E::Ref("y".into()))]),
            }],
            ret: E::Call(z(1), vec![E::Ref("x".into())]),
        },
        2 => Item::Const {
            name: z(0),
            init: E::Arrow(
                vec!["x".into()],
                Box::new(E::Member(Box::new(E::Ref("x".into())), "k")),
            ),
        },
        _ => Item::Const {
            name: z(0),
            init: E::Obj(vec![("k", E::Arr(vec![E::Str("s"), E::Str("t")]))]),
        },
    }
}

/// `p` with unrelated code put in at the places `at` picks (each a
/// position at the top level, or in a function's body).
fn with_unrelated(p: &Prog, at: &[usize]) -> Prog {
    let mut p = p.clone();
    for (n, &pos) in at.iter().enumerate() {
        let extra = unrelated(n);
        let fns: Vec<usize> = p
            .items
            .iter()
            .enumerate()
            .filter(|(_, it)| matches!(it, Item::Fn { .. }))
            .map(|(i, _)| i)
            .collect();
        if pos % 2 == 1 && !fns.is_empty() {
            if let Item::Fn { body, .. } = &mut p.items[fns[pos / 2 % fns.len()]] {
                let i = pos / 3 % (body.len() + 1);
                body.insert(i, extra);
                continue;
            }
        }
        let i = pos / 2 % (p.items.len() + 1);
        p.items.insert(i, extra);
    }
    p
}

/// `p` with its top-level function declarations in another order (the
/// other items stay where they are).
fn with_functions_reordered(p: &Prog, order: &[usize]) -> Prog {
    let slots: Vec<usize> = p
        .items
        .iter()
        .enumerate()
        .filter(|(_, it)| matches!(it, Item::Fn { .. }))
        .map(|(i, _)| i)
        .collect();
    let mut fns: Vec<Item> = slots.iter().map(|&i| p.items[i].clone()).collect();
    // A permutation from `order`'s keys.
    let mut keyed: Vec<(usize, Item)> = fns
        .drain(..)
        .enumerate()
        .map(|(i, f)| (order.get(i).copied().unwrap_or(i), f))
        .collect();
    keyed.sort_by_key(|(k, _)| *k);
    let mut items = p.items.clone();
    for (slot, (_, f)) in slots.into_iter().zip(keyed) {
        items[slot] = f;
    }
    Prog { items }
}

// -------------------------------------------------------------------------
// The oracle.
// -------------------------------------------------------------------------

/// How a program checked (as a module an importer uses: see `check`):
/// whether it raised errors, and each top-level
/// binding's printed type (variables named in order of appearance, so
/// the numbering of variables doesn't show).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Checked {
    errors: bool,
    bindings: BTreeMap<String, String>,
}

fn check(src: &str) -> Checked {
    let program = inty::frontends::javascript::parse_source(src)
        .unwrap_or_else(|e| panic!("generated program doesn't parse: {e:?}\n{src}"));
    inty::worker::run_with_inference_stack("inty-order-invariance", move || {
        let (env, mut state) = inty::stdlib::initial_env_with_stdlib().expect("stdlib");
        let base: BTreeSet<String> = env.names().cloned().collect();
        let result = state.infer_program_with_env(&env, &program);
        let mut errors = !state.take_errors().is_empty();
        let bindings = match result {
            Ok((_, final_env)) => {
                // Ended as a module an importer still uses is: what its
                // bindings reach is left for that importer to decide.
                let keep = state.reachable_vars(&final_env);
                if state.resolve_constraints_keeping(&keep).is_err()
                    || !state.take_errors().is_empty()
                {
                    errors = true;
                }
                final_env
                    .iter()
                    .filter(|(n, _)| !base.contains(*n))
                    .map(|(n, s)| (n.clone(), state.display_scheme(s).to_string()))
                    .collect()
            }
            Err(_) => {
                errors = true;
                BTreeMap::new()
            }
        };
        Checked { errors, bindings }
    })
}

/// Whether two printed type schemes are the same up to the names of
/// their quantified variables, and the order of the entries in a brace
/// group (a scheme's constraints on one variable, `a has {k: b, k: c}`,
/// come in the order they were posed; the variables are named in the
/// order the printer meets them, so two constraints alike but for their
/// variables can swap names).
fn equivalent(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    // Quantified or not (a binding that isn't generalised prints its free
    // variables named in the same order), its variables are renamed: the
    // lists `<a, b, …>` are alike once renamed, so what follows them is
    // compared.
    let body = |t: &str| match t.strip_prefix('<') {
        Some(_) => t
            .find('>')
            .map_or(t.to_string(), |i| t[i + 1..].to_string()),
        None => t.to_string(),
    };
    let (a, b) = (body(a), body(b));
    let (va, vb) = (variables(&a), variables(&b));
    if va.len() != vb.len() {
        return false;
    }
    // Too many to try each renaming: the types with their variables left
    // out are compared.
    if va.len() > 7 {
        return canonical(&rename_all(&a, &va, "_")) == canonical(&rename_all(&b, &vb, "_"));
    }
    let ca = canonical(&a);
    let mut perm: Vec<usize> = (0..vb.len()).collect();
    loop {
        let renamed = rename(&b, &vb, &perm, &va);
        if canonical(&renamed) == ca {
            return true;
        }
        if !next_permutation(&mut perm) {
            return false;
        }
    }
}

/// The type variables a printed type names (`a`, `b`, …, `a1`, …: a
/// lowercase letter and digits, not a field's name), in order.
fn variables(t: &str) -> Vec<String> {
    let chars: Vec<char> = t.chars().collect();
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i].is_ascii_alphabetic() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            let is_key = chars.get(i) == Some(&':') || chars.get(i) == Some(&'?');
            let is_var = word.len() <= 3
                && word.starts_with(|c: char| c.is_ascii_lowercase())
                && word[1..].chars().all(|c| c.is_ascii_digit())
                && !(start > 0 && chars[start - 1] == '.');
            if is_var && !is_key && !out.contains(&word) {
                out.push(word);
            }
        } else {
            i += 1;
        }
    }
    out
}

/// `t` with each variable `from[perm[i]]` written `to[i]` (an identifier
/// followed by `:` is a field's name, not a variable).
fn rename(t: &str, from: &[String], perm: &[usize], to: &[String]) -> String {
    let map: BTreeMap<&str, &str> = perm
        .iter()
        .enumerate()
        .map(|(i, &j)| (from[j].as_str(), to[i].as_str()))
        .collect();
    let chars: Vec<char> = t.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i].is_ascii_alphabetic() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            let is_key = chars.get(i) == Some(&':') || chars.get(i) == Some(&'?');
            match map.get(word.as_str()) {
                Some(new) if !is_key => out.push_str(new),
                _ => out.push_str(&word),
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

/// `t` with each of `vars` written `to`.
fn rename_all(t: &str, vars: &[String], to: &str) -> String {
    let to: Vec<String> = vars.iter().map(|_| to.to_string()).collect();
    let perm: Vec<usize> = (0..vars.len()).collect();
    rename(t, vars, &perm, &to)
}

/// `t` with the top-level entries of each brace group sorted (innermost
/// first), and the constraints of its `where` clause sorted.
fn canonical(t: &str) -> String {
    let t = canonical_groups(t);
    let Some(rest) = t.trim_start().strip_prefix("where ") else {
        return t;
    };
    // The clause ends at the first `=>` outside brackets.
    let chars: Vec<char> = rest.chars().collect();
    let (mut depth, mut end, mut i) = (0i32, chars.len(), 0);
    while i < chars.len() {
        match chars[i] {
            '(' | '[' | '{' | '<' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            '>' if i > 0 && chars[i - 1] == '=' => {
                if depth == 0 {
                    end = i - 1;
                    break;
                }
            }
            '>' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    let clause: String = chars[..end].iter().collect();
    let mut preds: Vec<String> = Vec::new();
    let (mut cur, mut depth) = (String::new(), 0i32);
    for c in clause.chars() {
        match c {
            '(' | '[' | '{' | '<' => depth += 1,
            ')' | ']' | '}' | '>' => depth -= 1,
            ',' if depth == 0 => {
                preds.push(cur.trim().to_string());
                cur.clear();
                continue;
            }
            _ => {}
        }
        cur.push(c);
    }
    preds.push(cur.trim().to_string());
    preds.sort();
    let after: String = chars[end..].iter().collect();
    format!("where {} {}", preds.join(", "), after.trim_start())
}

fn canonical_groups(t: &str) -> String {
    fn group(chars: &[char], i: &mut usize) -> String {
        // At `{`: its entries, sorted, closed.
        *i += 1;
        let mut entries = vec![String::new()];
        let mut depth = 0;
        while *i < chars.len() {
            let c = chars[*i];
            match c {
                '{' => {
                    let inner = group(chars, i);
                    entries.last_mut().unwrap().push_str(&inner);
                    continue;
                }
                '}' if depth == 0 => {
                    *i += 1;
                    break;
                }
                '(' | '[' | '<' => depth += 1,
                ')' | ']' | '>' if depth > 0 => depth -= 1,
                ',' if depth == 0 => {
                    entries.push(String::new());
                    *i += 1;
                    continue;
                }
                _ => {}
            }
            entries.last_mut().unwrap().push(c);
            *i += 1;
        }
        let mut entries: Vec<String> = entries.into_iter().map(|e| e.trim().to_string()).collect();
        entries.sort();
        format!("{{{}}}", entries.join(", "))
    }
    let chars: Vec<char> = t.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '{' {
            out.push_str(&group(&chars, &mut i));
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn next_permutation(p: &mut [usize]) -> bool {
    let Some(i) = (1..p.len()).rev().find(|&i| p[i - 1] < p[i]) else {
        return false;
    };
    let j = (i..p.len())
        .rev()
        .find(|&j| p[j] > p[i - 1])
        .expect("one is larger");
    p.swap(i - 1, j);
    p[i..].reverse();
    true
}

/// `a` and `b` agree: errors in both or neither, and the same type (see
/// [`equivalent`]) for each binding they both have (but the names `z…`,
/// `b`'s own).
fn assert_agree(label: &str, src_a: &str, a: &Checked, src_b: &str, b: &Checked) {
    let mut b_bindings = b.bindings.clone();
    b_bindings.retain(|n, _| !n.starts_with('z'));
    let same = a.bindings.len() == b_bindings.len()
        && a.bindings
            .iter()
            .all(|(n, t)| b_bindings.get(n).is_some_and(|u| equivalent(t, u)));
    assert!(
        a.errors == b.errors && same,
        "{label}: the checks disagree\n--- a ---\n{src_a}\n{a:#?}\n--- b ---\n{src_b}\n{b:#?}"
    );
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128,
        max_shrink_iters: 2000,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn checking_twice_gives_the_same(p in program()) {
        let src = render(&p, Style::default());
        assert_agree("checked twice", &src, &check(&src), &src, &check(&src));
    }

    #[test]
    fn unrelated_code_changes_no_type(
        p in program(),
        at in prop::collection::vec(0usize..64, 1..5),
    ) {
        let a = render(&p, Style::default());
        let b = render(&with_unrelated(&p, &at), Style::default());
        assert_agree("unrelated code added", &a, &check(&a), &b, &check(&b));
    }

    #[test]
    fn function_declaration_order_changes_no_type(
        p in program(),
        order in prop::collection::vec(0usize..8, 0..8),
    ) {
        let a = render(&p, Style::default());
        let b = render(&with_functions_reordered(&p, &order), Style::default());
        assert_agree("functions reordered", &a, &check(&a), &b, &check(&b));
    }

    #[test]
    fn unification_order_changes_no_type(p in program()) {
        let a = render(&p, Style::default());
        let b = render(&p, Style { flip: true });
        assert_agree("operands and fields flipped", &a, &check(&a), &b, &check(&b));
    }
}

#[test]
fn schemes_alike_but_for_their_variables_names_are_equivalent() {
    assert!(equivalent(
        "<a, b, c, d> where a has {k: b, k: c} => (a, d) => {k: b, v: c}",
        "<a, b, c, d> where a has {k: b, k: c} => (a, d) => {k: c, v: b}",
    ));
    assert!(!equivalent("<a, b> (a, b) => a", "<a, b> (a, b) => b",));
    assert!(!equivalent("{k: Number}", "{k: String}"));
    assert!(equivalent(
        "<a, b, c, d, e, f> where a has {v: b, v: c, v: f}, d has {k: e} => (d, a) => Boolean",
        "<a, b, c, d, e, f> where a has {k: b}, c has {v: d, v: e, v: f} => (a, c) => Boolean",
    ));
    assert!(equivalent("{k: a, m: (b) => c}", "{k: c, m: (a) => b}"));
}

/// The generator's programs mostly check, with generic types among them:
/// else the properties above compare errors with errors and say little.
#[test]
fn generated_programs_mostly_check() {
    use proptest::strategy::ValueTree;
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let (mut clean, mut generic, n) = (0, 0, 64);
    for _ in 0..n {
        let p = program()
            .new_tree(&mut runner)
            .expect("a program")
            .current();
        let c = check(&render(&p, Style::default()));
        if !c.errors {
            clean += 1;
            if c.bindings.values().any(|t| t.starts_with('<')) {
                generic += 1;
            }
        }
    }
    assert!(
        clean * 4 >= n * 3,
        "only {clean} of {n} generated programs check"
    );
    assert!(
        generic * 3 >= n,
        "only {generic} of {n} generated programs have a generic type"
    );
}
