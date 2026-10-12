//! The Lean model on inty's own programs (ground rule 4 of
//! `lean/ROADMAP.md`): every program inty's unit tests check that lies in
//! the model's fragment, written in the wire format by `inty::model_wire`,
//! is checked by both, and they must agree on accepting it, but for the
//! disagreements `tests/model_corpus/known.txt` lists: each a program's
//! wire line, after `#` lines giving the reason.
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
//! or `INTY_LEAN_MODEL`; without it the test is skipped.

use inty::builtins::initial_env;
use inty::infer::InferState;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

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

/// Whether inty accepts the program, as the CLI checks it.
fn inty_accepts(source: &str) -> bool {
    let source = source.to_string();
    inty::worker::run_with_inference_stack("inty-corpus", move || {
        let Ok(program) = inty::frontends::javascript::parse_source(&source) else {
            return false;
        };
        let mut state = InferState::new();
        match state.infer_program(&initial_env(), &program) {
            Ok(_) => state.take_errors().is_empty() && state.resolve_constraints().is_ok(),
            Err(_) => false,
        }
    })
}

/// The model's verdicts, `true` for a type, in one process.
fn model_accepts(model: &PathBuf, wires: &[String]) -> Vec<bool> {
    let mut child = Command::new(model)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("start inty-model");
    let mut stdin = child.stdin.take().unwrap();
    let input: String = wires.iter().map(|w| format!("{w}\n")).collect();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()).unwrap());
    let out: Vec<bool> = BufReader::new(child.stdout.take().unwrap())
        .lines()
        .map(|l| {
            let l = l.unwrap();
            assert!(
                l.starts_with("type ") || l.starts_with("reject"),
                "the model can't read a line: {l}"
            );
            l.starts_with("type ")
        })
        .collect();
    writer.join().unwrap();
    assert!(child.wait().unwrap().success());
    assert_eq!(out.len(), wires.len(), "the model answered too few lines");
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
    let model = model_accepts(&model, &wires);
    let mut agree = 0;
    let mut excused = 0;
    let mut failures = Vec::new();
    // A known disagreement must still be one.
    let mut stale: Vec<&str> = known.clone();
    for ((source, wire), m) in programs.iter().zip(&wires).zip(model) {
        let i = inty_accepts(source);
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
