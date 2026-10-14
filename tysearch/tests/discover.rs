//! Each language's discovered type system, pinned. The sorts are named in
//! the order their first members turn up, so the names are stable.

use tysearch::discover::{discover, generalisable, Config, Discovery};
use tysearch::infer::Policy;
use tysearch::lang::{Atom, Language, Term};
use tysearch::langs::{arith::Arith, core::Core, model::Model};

fn rules(d: &Discovery) -> Vec<String> {
    let mut r = d.rule_strings();
    r.sort();
    r
}

fn sorted(rs: &[&str]) -> Vec<String> {
    let mut r: Vec<String> = rs.iter().map(|s| s.to_string()).collect();
    r.sort();
    r
}

/// TAPL chapter 8's typing rules for the arithmetic language: T0 is Bool,
/// T1 is Nat.
#[test]
fn arith_finds_bool_and_nat() {
    let d = discover(&Arith::default(), &Config::default());
    assert_eq!(d.sort_names.len(), 2);
    assert_eq!(
        rules(&d),
        sorted(&[
            "true : T0",
            "false : T0",
            "zero : T1",
            "succ : (T1) -> T1",
            "pred : (T1) -> T1",
            "iszero : (T1) -> T0",
            "if : (T0, a, a) -> a",
        ])
    );
    assert_eq!(d.check.unsound, 0);
    // The price of compositional types: a conditional whose branches
    // differ is safe and untyped.
    assert!(d.check.untyped_safe > 0);
}

/// `+` is overloaded on numbers and strings: two rules, whose lgg is one
/// schema over a class, inty's `Plus`.
#[test]
fn core_finds_the_plus_class() {
    let d = discover(&Core::default(), &Config::default());
    assert_eq!(d.sort_names.len(), 3);
    assert_eq!(
        rules(&d),
        sorted(&[
            "num : T0",
            "str : T1",
            "true : T2",
            "false : T2",
            "+ : (T0, T0) -> T0",
            "+ : (T1, T1) -> T1",
            "- : (T0, T0) -> T0",
            "< : (T0, T0) -> T2",
            "=== : (a, b) -> T2",
            "typeof : (a) -> T1",
            "length : (T1) -> T0",
            "if : (T2, a, a) -> a",
        ])
    );
    let plus = d.search("+");
    let (schema, _) = tysearch::types::lgg(&plus.chosen).unwrap();
    assert_eq!(d.names().schema(&schema.normalize()), "+ : (a, a) -> a");
    assert_eq!(d.check.unsound, 0);
}

/// Iterations 1, 3 and 4: functions, calls, `let`, assignment and
/// `e₁; e₂`. The rules are the Lean model's (`lean/Inty/Typing.lean`),
/// found from its semantics alone: T3 and T4 are the functions of one and
/// two parameters, refined by what a call gives (`T3<a -> b>` is
/// `(a) => b`). Where they differ, the semantics allows more than inty's
/// rules do, soundly:
///
/// - T2 is booleans with `undefined` and `null`: nothing in this fragment
///   gets stuck on one and not the other.
/// - A conditional on a function takes its first branch: functions are
///   truthy.
/// - A one-parameter function may be called with two arguments: the extra
///   one is ignored.
///
/// And `let` generalises only syntactic values, inty's value restriction:
/// generalising always is refuted by a closure over a fresh cell that
/// hands back at one instance what it stored at another, which the search
/// builds itself.
#[test]
fn model_finds_functions_state_and_the_value_restriction() {
    let m = Model::default();
    let cfg = Config::default();
    let d = discover(&m, &cfg);
    assert_eq!(
        rules(&d),
        sorted(&[
            "num : T0",
            "str : T1",
            "true : T2",
            "false : T2",
            "undefined : T2",
            "null : T2",
            "! : (a) -> T2",
            "typeof : (a) -> T1",
            "neg : (T0) -> T0",
            "+ : (T0, T0) -> T0",
            "+ : (T1, T1) -> T1",
            "- : (T0, T0) -> T0",
            "* : (T0, T0) -> T0",
            "< : (T0, T0) -> T2",
            "=== : (a, b) -> T2",
            "cond : (a, b, b) -> b",
            "cond : (T3<a -> b>, c, d) -> c",
            "cond : (T4<a, b -> c>, d, e) -> d",
            "let : (a, [x0: a] b) -> b",
            "func1 : ([x0: a, x1: T3<a -> b>] b) -> T3<a -> b>",
            "func2 : ([x0: a, x1: b, x2: T4<a, b -> c>] c) -> T4<a, b -> c>",
            "app1 : (T3<a -> b>, a) -> b",
            "app2 : (T3<a -> b>, a, c) -> b",
            "app2 : (T4<a, b -> c>, a, b) -> c",
            "seq : (a, b) -> b",
        ])
    );
    assert_eq!(d.check.unsound, 0, "{:?}", d.check.violations);
    let lets: Vec<Policy> = d.generalisation.policies.values().map(|p| p.0).collect();
    assert_eq!(lets, vec![Policy::IfValue]);
    let always = d
        .generalisation
        .trials
        .iter()
        .find(|t| t.1 == Policy::Always)
        .unwrap();
    assert!(always.3.is_some(), "generalising always should be refuted");

    // The textbook counterexample, built by hand, is refuted too:
    // `let c = (x) => x in (p) => { let old = c; c = p; old }`, whose type
    // `((a) => a) => (a) => a` has a free variable, but whose value hands
    // back at one instance what it stored at another; while the identity
    // is in every instance of its type.
    let c = |n: &str| m.con(n);
    let var = |i: i64| Term::leaf(c("var"), Atom::Int(i));
    let node = |n: &str, kids: Vec<Term>| Term::new(c(n), kids);
    let store = Term {
        con: c("assign"),
        atom: Atom::Int(3),
        kids: vec![var(1)],
    };
    let swap = node(
        "let",
        vec![
            node("func1", vec![var(0)]),
            node(
                "func1",
                vec![node("let", vec![var(2), node("seq", vec![store, var(0)])])],
            ),
        ],
    );
    assert_eq!(generalisable(&m, &cfg, &d, &swap), Some(false));
    assert_eq!(
        generalisable(&m, &cfg, &d, &node("func1", vec![var(0)])),
        Some(true)
    );
}

// The suite: languages whose type systems differ in kind from inty's, so
// the search is judged on all of them and can't fit itself to one.

/// Nothing gets stuck, so there is one sort, and every safe term is typed.
#[test]
fn unityped_has_one_sort() {
    let d = discover(
        &tysearch::langs::unityped::Unityped::default(),
        &Config::default(),
    );
    assert_eq!(d.sort_names.len(), 1);
    assert_eq!(d.check.unsound, 0);
    assert_eq!(d.check.untyped_safe, 0);
}

/// Products: a pair's sort is refined by both its eliminators, and the
/// type found is `a × b`.
#[test]
fn pairs_find_products() {
    let d = discover(
        &tysearch::langs::pairs::Pairs::default(),
        &Config::default(),
    );
    assert_eq!(
        rules(&d),
        sorted(&[
            "num : T0",
            "true : T1",
            "false : T1",
            "pair : (a, b) -> T2{fst: -> a, snd: -> b}",
            "fst : (T2{fst: -> a, snd: -> b}) -> a",
            "snd : (T2{fst: -> a, snd: -> b}) -> b",
            "+ : (T0, T0) -> T0",
            "not : (T1) -> T1",
            "if : (T1, a, a) -> a",
        ])
    );
    assert_eq!(d.check.unsound, 0);
}

/// Integers are accepted wherever floats are, and as a repeat count: the
/// fingerprints' order gives `Int <: Float` (T0 <: T1), which makes the
/// system half the size of the one with overloads alone, and `+` keeps
/// its more precise integer rule.
#[test]
fn subtyping_finds_int_below_float() {
    let d = discover(
        &tysearch::langs::subtyping::Subtyping::default(),
        &Config::default(),
    );
    assert_eq!(d.subtypes, vec![(0, 1)]);
    assert_eq!(
        rules(&d),
        sorted(&[
            "int : T0",
            "float : T1",
            "str : T2",
            "true : T3",
            "+ : (T1, T1) -> T1",
            "+ : (T0, T0) -> T0",
            "floor : (T1) -> T0",
            "< : (T1, T1) -> T3",
            "repeat : (T2, T0) -> T2",
            "len : (T2) -> T0",
            "if : (T3, a, a) -> a",
        ])
    );
    assert_eq!(d.check.unsound, 0);
}

/// JavaScript's coercions: `+` takes anything, and a string on either side
/// makes a string; only `length` and `toFixed` are particular. Booleans and
/// `null` are accepted only where everything is, so their sort is the top
/// of the order, and `+` of two values is at most their join.
#[test]
fn coerce_finds_a_type_system_unlike_intys() {
    let d = discover(
        &tysearch::langs::coerce::Coerce::default(),
        &Config::default(),
    );
    let r = rules(&d);
    for want in [
        "+ : (a, a) -> a",
        "+ : (a, T1) -> T1",
        "+ : (T1, a) -> T1",
        "- : (a, b) -> T0",
        "length : (T1) -> T0",
        "toFixed : (T0) -> T1",
        "if : (a, b, b) -> b",
    ] {
        assert!(r.contains(&want.to_string()), "missing {want} in {r:?}");
    }
    assert_eq!(d.subtypes, vec![(0, 2), (1, 2)]);
    assert_eq!(d.check.unsound, 0);
}

/// ML's references: a cell's type is invariant (`set` stores what the
/// cell holds), and `let` generalises only syntactic values: Wright's
/// value restriction, found because `ref((x) => x)`, typed with a free
/// variable, is not in all instances of its type at once.
#[test]
fn refs_find_the_value_restriction() {
    let d = discover(&tysearch::langs::refs::Refs::default(), &Config::default());
    assert_eq!(
        rules(&d),
        sorted(&[
            "num : T0",
            "true : T1",
            "false : T1",
            "+ : (T0, T0) -> T0",
            "not : (T1) -> T1",
            "if : (T1, a, a) -> a",
            "let : (a, [x0: a] b) -> b",
            "func : ([x0: a, x1: T2<a -> b>] b) -> T2<a -> b>",
            "app : (T2<a -> b>, a) -> b",
            "ref : (a) -> T3< -> a>",
            "get : (T3< -> a>) -> a",
            "set : (T3< -> a>, a) -> a",
            "seq : (a, b) -> b",
        ])
    );
    let lets: Vec<Policy> = d.generalisation.policies.values().map(|p| p.0).collect();
    assert_eq!(lets, vec![Policy::IfValue]);
    let always = d
        .generalisation
        .trials
        .iter()
        .find(|t| t.1 == Policy::Always)
        .unwrap();
    assert!(
        always.3.as_ref().is_some_and(|w| w.contains("ref(")),
        "{:?}",
        always.3
    );
    assert_eq!(d.check.unsound, 0, "{:?}", d.check.violations);
}
