//! Each language's discovered type system, pinned. The sorts are named in
//! the order their first members turn up, so the names are stable.

use tysearch::discover::{climb, discover, generalisable, Config, Discovery};
use tysearch::infer::Policy;
use tysearch::lang::{Atom, Language, Term};
use tysearch::langs::{arith::Arith, core::Core, model::Model};
use tysearch::search::Features;

fn rules(d: &Discovery) -> Vec<String> {
    let mut r = d.rule_strings();
    r.sort();
    r
}

/// The rules with variables that may not stand for unions, and those.
fn no_unions(d: &Discovery) -> Vec<String> {
    let mut out: Vec<String> = d
        .generalisation
        .no_unions
        .iter()
        .map(|(r, vs)| {
            let vs: Vec<String> = vs.iter().map(|v| tysearch::types::var_name(*v)).collect();
            format!("{}: {}", d.names().schema(r), vs.join(", "))
        })
        .collect();
    out.sort();
    out
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
    // differ is typed by their union, but not where a union won't do
    // (`succ(if(true, succ(zero), true))`), safe as it is.
    assert!(d.check.untyped_safe > 0);
    assert!(no_unions(&d).is_empty());
}

/// `+` is overloaded on numbers and strings: two rules, whose lgg is one
/// schema over a class, inty's `Plus`. `==` compares two values of one
/// type, which can't be a union: `1 == "a"` is stuck.
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
            "== : (a, a) -> T2",
        ])
    );
    assert_eq!(no_unions(&d), vec!["== : (a, a) -> T2: a"]);
    let plus = d.search("+");
    let (schema, _) = tysearch::types::lgg(&plus.chosen).unwrap();
    assert_eq!(d.names().schema(&schema.normalize()), "+ : (a, a) -> a");
    assert_eq!(d.check.unsound, 0);
}

/// Iterations 1, 3 to 8: functions, calls, `let`, assignment,
/// `e₁; e₂`, objects, arrays and statements. The rules are the Lean model's (`lean/Inty/Typing.lean`),
/// found from its semantics alone: T3 and T4 are the functions of one and
/// two parameters, refined by what a call gives (`T3<a -> b>` is
/// `(a) => b`). Where they differ, the semantics allows more than inty's
/// rules do, soundly:
///
/// - T2 is booleans with `undefined` and `null`: nothing in this fragment
///   gets stuck on one and not the other.
/// - A conditional on a function or an object takes its first branch:
///   they are truthy.
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
            // A function's body returns its result (iteration 8).
            "func1 : ([x0: a, x1: T3<a -> b>] b (return b)) -> T3<a -> b>",
            "func2 : ([x0: a, x1: b, x2: T4<a, b -> c>] c (return c)) -> T4<a, b -> c>",
            "app1 : (T3<a -> b>, a) -> b",
            "app2 : (T3<a -> b>, a, c) -> b",
            "app2 : (T4<a, b -> c>, a, b) -> c",
            "seq : (a, b) -> b",
            // Objects (iteration 5): T5, T6 and T8 are `{x: a}`, `{y: a}`
            // and `{x: a, y: b}`, refined by their reads. A read is
            // overloaded on the objects that have the property (inty's
            // `HasProp`); a store keeps the property's type.
            "cond : (T5< -> a>, b, c) -> b",
            "cond : (T6< -> a>, b, c) -> b",
            "cond : (T8{.x: -> a, .y: -> b}, c, d) -> c",
            "{x} : (a) -> T5< -> a>",
            "{y} : (a) -> T6< -> a>",
            "{x,y} : (a, b) -> T8{.x: -> a, .y: -> b}",
            ".x : (T5< -> a>) -> a",
            ".x : (T8{.x: -> a, .y: -> b}) -> a",
            ".y : (T6< -> a>) -> a",
            ".y : (T8{.x: -> a, .y: -> b}) -> b",
            ".x= : (T5< -> a>, a) -> a",
            ".x= : (T8{.x: -> a, .y: -> b}, a) -> a",
            ".y= : (T6< -> a>, a) -> a",
            ".y= : (T8{.x: -> a, .y: -> b}, b) -> b",
            // Arrays (iteration 6): T7 is `a[]`, refined by `idx`, whose
            // elements share a type. Indexing an object gives `undefined`,
            // since no term builds the string "x" or "y".
            "cond : (T7<a -> b>, c, d) -> c",
            "[a] : (a) -> T7<T0 -> a>",
            "[a,b] : (a, a) -> T7<T0 -> a>",
            "idx : (T7<a -> b>, a) -> b",
            "idx : (T1, T0) -> T1",
            "idx : (T5< -> a>, T0) -> T2",
            "idx : (T5< -> a>, T1) -> T2",
            "idx : (T6< -> a>, T0) -> T2",
            "idx : (T6< -> a>, T1) -> T2",
            "idx : (T8{.x: -> a, .y: -> b}, T0) -> T2",
            "idx : (T8{.x: -> a, .y: -> b}, T1) -> T2",
            "idx= : (T7<a -> b>, a, b) -> b",
            // Statements (iteration 7): what doesn't complete is of every
            // type, and a `catch` binds `unknown`, as in the Lean model.
            "throw : (a) -> b",
            "try : (a, [x0: unknown] a) -> a",
            "while : (a, b) -> T2",
            "break : a",
            "continue : a",
            // `return` (iteration 8): its exit type is its value's.
            "return : (a) -> b (return a)",
            // `typeof` tests (iteration 10): plain rules; the narrowing is
            // the binder flow's (checked below).
            "typeof=number : (a, [x0: a] b, [x0: a] b) -> b",
            "typeof=string : (a, [x0: a] b, [x0: a] b) -> b",
        ])
    );
    assert_eq!(d.check.unsound, 0, "{:?}", d.check.violations);
    // Unions (iteration 9): any variable may stand for one, as in inty:
    // a conditional's branches, an array's elements, a `try`'s body and
    // handler may differ.
    assert!(no_unions(&d).is_empty());
    let lets: Vec<Policy> = d.generalisation.policies.values().map(|p| p.0).collect();
    // `let`'s, and the `typeof` tests' branches', which bind a value too.
    assert_eq!(lets.len(), 5);
    assert!(lets.iter().all(|p| *p == Policy::IfValue));
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

    // Narrowing (iteration 10): with `x` a number or a string,
    // `typeof x === "number" ? -x : x[0]` is typed, each branch seeing `x`
    // as only the sorts that reach it: the probes find that only numbers
    // reach the one, and all but numbers the other.
    let lit = |n: &str, a: Atom| Term::leaf(c(n), a);
    let x = node(
        "cond",
        vec![
            node("true", vec![]),
            lit("num", Atom::Int(0)),
            lit("str", Atom::Str("a".into())),
        ],
    );
    let test = node(
        "typeof=number",
        vec![
            var(0),
            node("idx", vec![var(0), lit("num", Atom::Int(0))]),
            node("neg", vec![var(0)]),
        ],
    );
    let narrowed = node("let", vec![x, test]);
    let names = d.names();
    let types: Vec<String> = d
        .checker
        .types(&narrowed)
        .iter()
        .map(|t| names.ty(t))
        .collect();
    assert_eq!(types, vec!["T0 | T1"]);
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

/// The climb, from ground rules: it keeps a capability that types more
/// programs or as many with a smaller system, stops when none does, then
/// drops what the result can do without. TAPL's arithmetic and `core` need
/// type variables (fewer rules for the same programs) and unions (a
/// conditional's branches may differ): nothing else, with nothing set.
#[test]
fn the_climb_finds_what_each_language_needs() {
    let need = Features {
        vars: true,
        unions: true,
        ..Features::NONE
    };
    for c in [
        climb(&Arith::default(), &Config::default()),
        climb(&Core::default(), &Config::default()),
    ] {
        assert_eq!(c.steps[c.last].features, need);
        // Every kept step types at least as many programs as the one
        // before (on a pool that only grows).
        let kept: Vec<usize> = c
            .steps
            .iter()
            .filter(|s| s.kept)
            .map(|s| s.score.typed)
            .collect();
        assert!(kept.windows(2).all(|w| w[1] >= w[0]), "{kept:?}");
        assert!(c.steps.iter().all(|s| !s.kept || s.score.unsound == 0));
    }
}

// Languages unlike any the search was built for: what it finds, what it
// can't, and that it never claims more than holds.

/// Typestate: a closed file is a sort of its own (`read` gets stuck on
/// it), but `close` changes its argument's sort, and a rule types each
/// value once, so `close` has no rule. Refused, not wrong.
#[test]
fn files_close_is_out_of_reach() {
    let d = discover(
        &tysearch::langs::files::Files::default(),
        &Config::default(),
    );
    let r = rules(&d);
    assert!(r.contains(&"read : (T0) -> T1".to_string()), "{r:?}");
    assert!(!r.iter().any(|s| s.starts_with("close")), "{r:?}");
    assert_eq!(d.check.unsound, 0);
}

/// An effect: `ask`'s type is its handler's, a context carried down the
/// program. The search carries one for `return` only, so `ask` has none.
#[test]
fn effects_ask_is_out_of_reach() {
    let d = discover(
        &tysearch::langs::effects::Effects::default(),
        &Config::default(),
    );
    let r = rules(&d);
    assert!(r.contains(&"with : (a, b) -> b".to_string()), "{r:?}");
    assert!(!r.iter().any(|s| s.starts_with("ask")), "{r:?}");
    assert_eq!(d.check.unsound, 0);
}

/// Information flow, where a leak gets stuck: public below secret, found
/// from the fingerprints (a public number goes everywhere a secret does,
/// and to `print`), and `print` takes public numbers only. Implicit flows
/// run fine, so nothing rules them out.
#[test]
fn secrets_find_an_information_flow_type_system() {
    let d = discover(
        &tysearch::langs::secrets::Secrets::default(),
        &Config::default(),
    );
    let r = rules(&d);
    assert_eq!(d.subtypes, vec![(0, 1)]);
    for want in [
        "print : (T0) -> T0",
        "declassify : (T1) -> T0",
        "secret : T1",
    ] {
        assert!(r.contains(&want.to_string()), "missing {want} in {r:?}");
    }
    assert_eq!(d.check.unsound, 0);
}

/// printf: a string's type records what `fmt` makes of it, and a
/// formatter's what `arg` does, but the literal `str` has no rule: "%" and
/// "%%" would need types of their own (literal types).
#[test]
fn printf_needs_literal_types() {
    let d = discover(
        &tysearch::langs::printf::Printf::default(),
        &Config::default(),
    );
    let r = rules(&d);
    for want in ["fmt : (T0< -> a>) -> a", "arg : (T3<a -> b>, a) -> b"] {
        assert!(r.contains(&want.to_string()), "missing {want} in {r:?}");
    }
    assert!(!r.iter().any(|s| s.starts_with("str")), "{r:?}");
    assert_eq!(d.check.unsound, 0);
}

/// Units of measure: each unit is a sort, but `*`'s result is computed
/// from its arguments' units (`U·V`), which no rule with variables says.
/// So `*` and `/` come out as a table of ground overloads.
#[test]
fn units_become_sorts_and_a_table() {
    let d = discover(
        &tysearch::langs::units::Units::default(),
        &Config::default(),
    );
    let r = rules(&d);
    assert_eq!(d.sort_names.len(), 9);
    assert!(r.contains(&"* : (T0, T1) -> T3".to_string()), "{r:?}");
    let times = r.iter().filter(|s| s.starts_with("* :")).count();
    assert!(times > 30, "{times} rules for *");
    assert!(
        !r.iter().any(|s| s.starts_with("* :") && s.contains('a')),
        "{r:?}"
    );
    assert_eq!(d.check.unsound, 0);
}
