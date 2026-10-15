//! The climb on the model of inty's language, with a few programs checked
//! by each step's type system: what each capability lets the checker
//! accept. `cargo run --release --example climb_walkthrough`.

use tysearch::discover::{climb_with, step_report, Config};
use tysearch::enumerate::Enumerator;
use tysearch::lang::{Atom, Language, Outcome, Term};
use tysearch::langs::model::Model;

fn main() {
    let m = Model::default();
    let c = |n: &str| m.con(n);
    let node = |n: &str, kids: Vec<Term>| Term::new(c(n), kids);
    let leaf = |n: &str| Term::new(c(n), vec![]);
    let num = |n: i64| Term::leaf(c("num"), Atom::Int(n));
    let s = |x: &str| Term::leaf(c("str"), Atom::Str(x.into()));
    let var = |i: i64| Term::leaf(c("var"), Atom::Int(i));
    let one_or_a = || node("cond", vec![leaf("true"), num(1), s("a")]);
    let examples: Vec<(&str, Term)> = vec![
        ("1 + 1", node("+", vec![num(1), num(1)])),
        ("1 + \"a\"", node("+", vec![num(1), s("a")])),
        ("({x: 1}).y", node(".y", vec![node("{x}", vec![num(1)])])),
        (
            "typeof (true ? 1 : \"a\")",
            node("typeof", vec![one_or_a()]),
        ),
        (
            "(true ? 1 : \"a\") + 1",
            node("+", vec![one_or_a(), num(1)]),
        ),
        (
            "((x) => x + 1)(1)",
            node(
                "app1",
                vec![node("func1", vec![node("+", vec![var(0), num(1)])]), num(1)],
            ),
        ),
        (
            "({x: 1}).x + 1",
            node(
                "+",
                vec![node(".x", vec![node("{x}", vec![num(1)])]), num(1)],
            ),
        ),
        (
            "[1, 1][0] + 1",
            node(
                "+",
                vec![
                    node("idx", vec![node("[a,b]", vec![num(1), num(1)]), num(0)]),
                    num(1),
                ],
            ),
        ),
        (
            "let id = (x) => x; id(1); id(\"a\")",
            node(
                "let",
                vec![
                    node("func1", vec![var(0)]),
                    node(
                        "seq",
                        vec![
                            node("app1", vec![var(0), num(1)]),
                            node("app1", vec![var(0), s("a")]),
                        ],
                    ),
                ],
            ),
        ),
        (
            "try { throw 1 } catch (e) { typeof e }",
            node(
                "try",
                vec![node("throw", vec![num(1)]), node("typeof", vec![var(0)])],
            ),
        ),
        (
            "((x) => { return x + 1 })(1)",
            node(
                "app1",
                vec![
                    node(
                        "func1",
                        vec![node("return", vec![node("+", vec![var(0), num(1)])])],
                    ),
                    num(1),
                ],
            ),
        ),
        (
            "let x = true ? 1 : \"a\"; typeof x === \"number\" ? -x : x[0]",
            node(
                "let",
                vec![
                    one_or_a(),
                    node(
                        "typeof=number",
                        vec![
                            var(0),
                            node("idx", vec![var(0), num(0)]),
                            node("neg", vec![var(0)]),
                        ],
                    ),
                ],
            ),
        ),
    ];

    // Each step as it finishes.
    let mut prev: Vec<String> = Vec::new();
    let cl = climb_with(&m, &Config::default(), |i, s| {
        print!("{}", step_report(i, s, &prev));
        if s.kept {
            prev = s.discovery.rule_strings();
        }
        use std::io::Write;
        std::io::stdout().flush().ok();
    });
    print!("{}", cl.summary());
    println!("\nexamples (what each kept step's checker says):");
    for (label, t) in &examples {
        let run = match m.eval_in(t, &[]) {
            Outcome::Value(v) => format!("runs to {}", m.show_value(&v)),
            Outcome::Stuck { reason, .. } => format!("CRASHES ({reason})"),
            o => format!("{o:?}"),
        };
        println!("\nEXAMPLE {label}   [{run}]");
        for (i, st) in cl.steps.iter().enumerate().filter(|(_, s)| s.kept) {
            let d = &st.discovery;
            let names = d.names();
            let tys: Vec<String> = d.checker.types(t).iter().map(|ty| names.ty(ty)).collect();
            println!(
                "  step {i} ({}): {}",
                st.change,
                if tys.is_empty() {
                    "rejected".to_string()
                } else {
                    format!("accepted as {}", tys.join(" or "))
                }
            );
        }
    }
    // Per kept step, the smallest safe programs its rules still reject:
    // those the next kept step accepts first (what that step fixes).
    println!("\nwrongly rejected (safe programs each kept step rejects, smallest first):");
    let mut en = Enumerator::new(m.signature(), 5);
    en.cap = 400_000;
    // Closed ones only: `(x) => y` runs to a function, but only because
    // its body never runs.
    let checker = &cl.steps[0].discovery.checker;
    let mut safe: Vec<Term> = en
        .up_to(5, 0)
        .into_iter()
        .filter(|t| checker.closed(t, 0) && matches!(m.eval_in(t, &[]), Outcome::Value(_)))
        .collect();
    fn size(t: &Term) -> usize {
        1 + t.kids.iter().map(size).sum::<usize>()
    }
    safe.sort_by_key(size);
    let kept: Vec<usize> = (0..cl.steps.len()).filter(|&i| cl.steps[i].kept).collect();
    for (n, &i) in kept.iter().enumerate() {
        let d = &cl.steps[i].discovery;
        let next = kept.get(n + 1).map(|&j| &cl.steps[j].discovery);
        let rejected: Vec<&Term> = safe
            .iter()
            .filter(|t| d.checker.types(t).is_empty())
            .collect();
        let (fixed, rest): (Vec<&Term>, Vec<&Term>) = rejected
            .iter()
            .partition(|t| next.is_some_and(|nd| !nd.checker.types(t).is_empty()));
        println!(
            "  step {i} ({}): {} safe programs rejected",
            cl.steps[i].change,
            rejected.len()
        );
        for t in fixed.iter().take(4) {
            println!("    fixed next: {}", m.show_term(t));
        }
        for t in rest.iter().take(4) {
            println!("    still out:  {}", m.show_term(t));
        }
    }

    let d = cl.result();
    println!("\nsorts of the result:");
    for (i, ex) in d.sort_examples.iter().enumerate() {
        println!("  T{i} = {}", ex.join(", "));
    }
    println!(
        "\nchecked programs: {} ({} safe), typed and safe: {}, typed but crashing: {}",
        d.check.terms,
        d.check.safe,
        d.check.typed - d.check.unsound,
        d.check.unsound
    );
    println!("\nthe system found:\n");
    print!("{d}");
}
