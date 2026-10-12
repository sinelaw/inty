//! The Lean model on inty's own programs (ground rule 4 of
//! `lean/ROADMAP.md`): every program inty's unit tests check that lies in
//! the model's fragment, written in the wire format by `inty::model_wire`,
//! is checked and run by both, and by a JavaScript engine, and:
//!
//! - inty and the model must agree on accepting it, but for the
//!   disagreements `tests/model_corpus/known.txt` lists: each a program's
//!   wire line, after `#` lines giving the reason;
//! - where both accept it, at the same type (its head, as the model prints
//!   it);
//! - neither interpreter (the model's, inty's `dynamics`) gets stuck on a
//!   program its checker accepts, and the engine raises no error of its
//!   own (a `TypeError`, say) on one the model accepts;
//! - where the model accepts it at a type other than `undefined`, the
//!   model's interpreter, `dynamics` and the engine agree on its value where
//!   they finish.
//!
//! The corpus, `tests/model_corpus/programs.txt`, holds the programs in the
//! fragment, one record per program (records end in a line holding `\x1e`).
//! To regenerate it from the unit tests:
//!
//! ```text
//! INTY_CORPUS_OUT=/tmp/raw.txt cargo test -p inty --lib
//! INTY_CORPUS_RAW=/tmp/raw.txt cargo test -p inty --test model_corpus
//! ```
//!
//! The model is `lean/.lake/build/bin/inty-model` (`cd lean && lake build`),
//! or `INTY_LEAN_MODEL`; without it the test is skipped, unless
//! `INTY_REQUIRE_MODEL` is set (as CI does), which fails it instead. The
//! engine is `node` (or `INTY_NODE`), as in `tests/differential.rs`.

use inty::builtins::initial_env;
use inty::infer::InferState;
use inty::types::Type;
use std::path::PathBuf;
use std::process::Command;

mod oracle;
use oracle::*;

const SEPARATOR: &str = "\n\x1e\n";

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/model_corpus")
}

fn records(text: &str) -> Vec<String> {
    text.split(SEPARATOR)
        .map(|s| s.trim_end_matches('\n').to_string())
        .filter(|s| !s.trim().is_empty())
        .collect()
}

/// The program in the wire format, if it parses and is in the fragment.
fn lower(source: &str) -> Result<String, String> {
    let program = inty::frontends::javascript::parse_source(source).map_err(|e| e.to_string())?;
    inty::model_wire::lower_program(&program)
}

/// inty's verdict on a program: whether it accepts it, as the CLI checks it,
/// at what type (the head of the type of its completion value, as the model
/// prints it), and what its interpreter (`dynamics`) makes of it.
fn inty_verdict(source: &str) -> (Typing, Run) {
    let source = source.to_string();
    inty::worker::run_with_inference_stack("inty-corpus", move || {
        let Ok(program) = inty::frontends::javascript::parse_source(&source) else {
            return (Typing::Reject, Run::Unsupported);
        };
        let mut state = InferState::new();
        let typing = match state.infer_program(&initial_env(), &program) {
            Ok(ty) if state.take_errors().is_empty() && state.resolve_constraints().is_ok() => {
                // A recursive type, by its unfolding, as the model prints it.
                let mut ty = state.apply_subst(&ty);
                if let Type::Named(id, args) = &ty {
                    if let Some(unrolled) = state.unroll_named(*id, args) {
                        ty = unrolled;
                    }
                }
                Typing::Type(core_type(&ty))
            }
            _ => Typing::Reject,
        };
        (typing, inty_run(&program))
    })
}

/// The model's verdicts (its inference's and its interpreter's), in one
/// process.
fn model_verdicts(model: &PathBuf, wires: &[String]) -> Vec<(Typing, Run)> {
    let input: String = wires.iter().map(|w| format!("{w}\n")).collect();
    run_lines(Command::new(model), "inty-model", input, wires.len())
        .iter()
        .map(|l| parse_model_line(l))
        .collect()
}

/// What fails the test beside a disagreement on accepting a program: the
/// soundness of each interpreter on what its checker accepts, the types,
/// and the values where they are compared.
const FAILING: [&str; 7] = [
    "type differs",
    "model accepts, its interpreter gets stuck",
    "inty accepts, dynamics gets stuck",
    "model accepts, the engine raises an error",
    "value differs from dynamics",
    "value differs from the engine",
    "an interpreter disagrees on getting stuck",
];

#[test]
fn the_model_agrees_with_inty_on_its_own_programs() {
    let path = corpus_dir().join("programs.txt");
    if let Some(raw) = std::env::var_os("INTY_CORPUS_RAW") {
        let mut seen = std::collections::BTreeSet::new();
        let mut why_not: std::collections::BTreeMap<String, usize> = Default::default();
        // The corpus so far, then what the unit tests check now: some of
        // them generate their programs at random, so a program once in
        // the corpus stays (while it's in the fragment).
        let old = std::fs::read_to_string(&path).unwrap_or_default();
        let kept: Vec<String> = records(&old)
            .into_iter()
            .chain(records(&std::fs::read_to_string(raw).unwrap()))
            .filter(|s| seen.insert(s.clone()))
            .filter(|s| match lower(s) {
                Ok(_) => true,
                Err(why) => {
                    // (Names and labels apart.)
                    let why = why.split('`').step_by(2).collect::<Vec<_>>().join("`…`");
                    *why_not.entry(why).or_default() += 1;
                    false
                }
            })
            .collect();
        let mut why_not: Vec<_> = why_not.into_iter().collect();
        why_not.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        eprintln!("left out of the fragment:");
        for (why, n) in why_not.iter().take(25) {
            eprintln!("  {n:5}  {why}");
        }
        let text: String = kept.iter().map(|s| format!("{s}{SEPARATOR}")).collect();
        std::fs::write(&path, text).unwrap();
    }
    let Some(model) = model_path() else {
        assert!(
            std::env::var_os("INTY_REQUIRE_MODEL").is_none(),
            "no inty-model, and INTY_REQUIRE_MODEL is set"
        );
        eprintln!("skipping: no inty-model (cd lean && lake build)");
        return;
    };
    let programs = records(&std::fs::read_to_string(&path).unwrap());
    let known_text = std::fs::read_to_string(corpus_dir().join("known.txt")).unwrap_or_default();
    let known: Vec<&str> = known_text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .collect();
    let wires: Vec<String> = programs
        .iter()
        .map(|s| lower(s).unwrap_or_else(|why| panic!("{why}, in the corpus:\n{s}")))
        .collect();
    let model = model_verdicts(&model, &wires);
    let inty: Vec<(Typing, Run)> = programs.iter().map(|s| inty_verdict(s)).collect();
    let engine = run_engine(&programs);
    let mut agree = 0;
    let mut excused = 0;
    let mut failures = Vec::new();
    let mut counts: std::collections::BTreeMap<&str, usize> = Default::default();
    let mut mismatches = Vec::new();
    // A known disagreement must still be one.
    let mut stale: Vec<&str> = known.clone();
    for (n, ((source, wire), (mt, mr))) in programs.iter().zip(&wires).zip(&model).enumerate() {
        let (it, ir) = &inty[n];
        let i = *it != Typing::Reject;
        let m = *mt != Typing::Reject;
        let er = engine.as_ref().map(|e| &e[n]);
        let mut note = |what: &'static str| {
            *counts.entry(what).or_default() += 1;
            if FAILING.iter().any(|f| what == *f) {
                mismatches.push(format!(
                    "{what}: the model {mt:?}, {mr:?}; inty {it:?}, {ir:?}; the engine {er:?}\n  js:   {source}\n  wire: {wire}"
                ));
            }
        };
        if let (Typing::Type(a), Typing::Type(b)) = (it, mt) {
            note(if a == b { "same type" } else { "type differs" });
        }
        if m && matches!(mr, Run::Stuck(_)) {
            note("model accepts, its interpreter gets stuck");
        }
        if i && matches!(ir, Run::Stuck(_)) {
            note("inty accepts, dynamics gets stuck");
        }
        // The values are compared where the program has a type other than
        // `undefined`: the front end writes a program that ends in a
        // statement as the statement then `undefined`, where JavaScript's
        // completion value is the statement's.
        let valued = matches!(mt, Typing::Type(t) if t != "undefined");
        match (mr, ir) {
            (Run::Value(a), Run::Value(b)) if valued => note(if a == b {
                "same value as dynamics"
            } else {
                "value differs from dynamics"
            }),
            (Run::Stuck(_), Run::Stuck(_)) => note("both stuck"),
            (Run::Stuck(_), Run::Value(_)) | (Run::Value(_), Run::Stuck(_)) if valued => {
                note("an interpreter disagrees on getting stuck")
            }
            _ => note("runs not compared with dynamics"),
        }
        if let Some(er) = er {
            if m && matches!(er, Run::NativeError(_)) {
                note("model accepts, the engine raises an error");
            }
            match (mr, er) {
                (Run::Value(a), Run::Value(b)) if valued => note(if a == b {
                    "same value as the engine"
                } else {
                    "value differs from the engine"
                }),
                _ => note("runs not compared with the engine"),
            }
        }
        if i == m {
            agree += 1;
        } else if known.contains(&wire.as_str()) {
            stale.retain(|k| *k != wire.as_str());
            excused += 1;
        } else {
            failures.push(format!(
                "inty {}, the model {}:\n  js:   {source}\n  wire: {wire}",
                if i { "accepts" } else { "rejects" },
                if m { "accepts" } else { "rejects" },
            ));
        }
    }
    eprintln!(
        "{} programs: {agree} agree, {excused} known disagreements, {} new",
        programs.len(),
        failures.len()
    );
    for (what, n) in &counts {
        eprintln!("  {n:5}  {what}");
    }
    failures.extend(mismatches);
    for k in stale {
        failures.push(format!(
            "known.txt lists a program inty and the model now agree on, or not in the corpus:\n  wire: {k}"
        ));
    }
    assert!(
        failures.is_empty(),
        "{} disagreements:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
