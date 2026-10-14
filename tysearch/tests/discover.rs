use tysearch::discover::{discover, Config};
use tysearch::langs::{arith::Arith, core::Core};

/// TAPL chapter 8's typing rules for the arithmetic language, up to the
/// names of the sorts: T0 is Bool, T1 is Nat.
#[test]
fn arith_finds_bool_and_nat() {
    let d = discover(&Arith::default(), &Config::default());
    assert_eq!(d.sort_names.len(), 2);
    assert_eq!(
        d.rule_strings(),
        [
            "true : T0",
            "false : T0",
            "zero : T1",
            "succ : (T1) -> T1",
            "pred : (T1) -> T1",
            "iszero : (T1) -> T0",
            "if : (T0, a, a) -> a",
        ]
    );
    assert_eq!(d.check.unsound, 0);
    // The price of compositional types: a conditional whose branches
    // differ is safe and untyped.
    assert!(d
        .check
        .untyped_safe_examples
        .contains(&"if(true, true, zero)".to_string()));
}

/// `+` is overloaded on numbers and strings: two rules, which fold into
/// one schema over a class, inty's `Plus`.
#[test]
fn core_finds_the_plus_class() {
    let d = discover(&Core::default(), &Config::default());
    assert_eq!(d.sort_names.len(), 3);
    let rules = d.rule_strings();
    for r in [
        "+ : (T1, T1) -> T1",
        "+ : (T0, T0) -> T0",
        "=== : (a, b) -> T2",
        "typeof : (a) -> T1",
        "if : (T2, a, a) -> a",
    ] {
        assert!(rules.contains(&r.to_string()), "missing {r} in {rules:?}");
    }
    let plus = d.searches.iter().find(|s| s.con == "+").unwrap();
    let (schema, instances) = plus.class.as_ref().unwrap();
    assert_eq!(d.show(schema).to_string(), "+ : (a, a) -> a");
    assert_eq!(instances, &[vec![0], vec![1]]);
    assert_eq!(d.check.unsound, 0);
}

/// With terms of size 2 nothing shows `+` or `if` running, so observation
/// refutes no rule of theirs: compatibility testing alone must reject the
/// unsound ones, and the result must still check on bigger terms.
#[test]
fn compatibility_testing_alone_keeps_it_sound() {
    let cfg = Config {
        learn_size: 2,
        check_size: 5,
        ..Config::default()
    };
    let d = discover(&Core::default(), &cfg);
    for s in d.searches.iter().filter(|s| s.con == "+" || s.con == "if") {
        assert_eq!(s.refuted_by_observation, 0);
        assert!(s.refuted_by_compatibility > 0);
    }
    assert_eq!(d.check.unsound, 0);
    assert!(d
        .rule_strings()
        .contains(&"if : (T2, a, a) -> a".to_string()));
}
