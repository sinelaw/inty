//! Each language's discovered type system, pinned. The sorts are named in
//! the order their first members turn up, so the names are stable.

use tysearch::discover::{discover, Config, Discovery};
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

/// Iteration 1: functions, calls and `const`. The rules are the Lean
/// model's (`lean/Inty/Typing.lean`), found from its semantics alone: T3
/// and T4 are the functions of one and two parameters, refined by what a
/// call gives (`T3<a -> b>` is `(a) => b`). Where they differ, the
/// semantics allows more than inty's rules do, soundly:
///
/// - T2 is booleans with `undefined` and `null`: nothing in this fragment
///   gets stuck on one and not the other.
/// - A conditional on a function takes its first branch: functions are
///   truthy.
/// - A one-parameter function may be called with two arguments: the extra
///   one is ignored.
#[test]
fn model_finds_functions() {
    let cfg = Config {
        corpus_size: 4,
        ..Config::default()
    };
    let expected = sorted(&[
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
        "const : (a, [x0: a] b) -> b",
        "func1 : ([x0: a, x1: T3<a -> b>] b) -> T3<a -> b>",
        "func2 : ([x0: a, x1: b, x2: T4<a, b -> c>] c) -> T4<a, b -> c>",
        "app1 : (T3<a -> b>, a) -> b",
        "app2 : (T3<a -> b>, a, c) -> b",
        "app2 : (T4<a, b -> c>, a, b) -> c",
    ]);
    for seed in 1..=3 {
        let d = discover(&Model::default(), &Config { seed, ..cfg.clone() });
        assert_eq!(rules(&d), expected, "seed {seed}");
        assert_eq!(d.check.unsound, 0, "seed {seed}: {:?}", d.check.violations);
    }
}
