//! Accepted means it runs: inty on every program of the corpus
//! (`tests/corpus/mod.rs`: the repository's example and test programs, and
//! the probes in `tests/soundness/`), and, for each program it accepts, the
//! program under Node (`tests/soundness/run.mjs`, strict mode). The test
//! fails when Node exits non-zero on a program inty accepts, a TypeError or
//! ReferenceError say: a hole in the checker.
//!
//! What a program expects is said by its directives: lines `// inty:
//! DIRECTIVE` in the program (how the probes say it), or lines `PATH
//! DIRECTIVE` in `tests/soundness/corpus.txt` (for the other programs, so
//! they stay as they are). The directives:
//!
//! - `reject`: inty must reject it (a probe of a hole: it would fail
//!   under Node);
//! - `accept`: inty must accept it (and Node run it);
//! - `no-run: REASON`: don't run it, e.g. it needs a browser's DOM or
//!   command-line arguments;
//! - `throws: REASON`: it ends in an error of its own on purpose (`throw`,
//!   a rejected promise), so a non-zero exit is fine, but not a native
//!   error (`TypeError`, `ReferenceError`, `RangeError`, `SyntaxError`);
//! - `known-failing: REASON`: the check fails today, for the bug REASON
//!   names. The program is still checked and its failure reported, but it
//!   doesn't fail the test; one that passes does, so that the marker goes
//!   when the bug is fixed.
//!
//! A program with none of these must run under Node if inty accepts it.
//!
//! Node is `node` or `INTY_NODE`. Without it the runs are skipped (the
//! `reject`/`accept` verdicts are still checked), except on CI (`CI` set),
//! where the test fails instead. `INTY_SOUNDNESS_FILTER=TEXT` checks only
//! the programs whose path contains TEXT.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

mod corpus;

/// How long a program may run under Node.
const TIMEOUT: Duration = Duration::from_secs(60);

#[derive(Default, Debug)]
struct Directives {
    reject: bool,
    accept: bool,
    no_run: Option<String>,
    throws: Option<String>,
    known_failing: Option<String>,
}

impl Directives {
    fn add(&mut self, text: &str, whence: &str) -> Result<(), String> {
        let (name, reason) = match text.split_once(':') {
            Some((name, reason)) => (name.trim(), Some(reason.trim().to_string())),
            None => (text.trim(), None),
        };
        let reason = || match &reason {
            Some(r) if !r.is_empty() => Ok(r.clone()),
            _ => Err(format!("{whence}: `{name}` needs a reason (`{name}: WHY`)")),
        };
        match name {
            "reject" => self.reject = true,
            "accept" => self.accept = true,
            "no-run" => self.no_run = Some(reason()?),
            "throws" => self.throws = Some(reason()?),
            "known-failing" => self.known_failing = Some(reason()?),
            _ => return Err(format!("{whence}: unknown directive `{name}`")),
        }
        if self.reject && self.accept {
            return Err(format!("{whence}: both `reject` and `accept`"));
        }
        Ok(())
    }
}

fn soundness_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/soundness")
}

/// `tests/soundness/corpus.txt`: `PATH DIRECTIVE` per line, `#` comments.
fn manifest() -> Result<BTreeMap<String, Directives>, String> {
    let path = soundness_dir().join("corpus.txt");
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut out: BTreeMap<String, Directives> = BTreeMap::new();
    for (n, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let whence = format!("tests/soundness/corpus.txt:{}", n + 1);
        let (program, directive) = line
            .split_once(char::is_whitespace)
            .ok_or_else(|| format!("{whence}: expected `PATH DIRECTIVE`"))?;
        out.entry(program.to_string())
            .or_default()
            .add(directive, &whence)?;
    }
    Ok(out)
}

fn node() -> Option<std::ffi::OsString> {
    let node = std::env::var_os("INTY_NODE").unwrap_or_else(|| "node".into());
    let found = Command::new(&node)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    found.then_some(node)
}

/// The first line of `text` that names an error (`TypeError: ...`), or
/// else its last non-empty line.
fn error_line(text: &str) -> String {
    let named = text.lines().find(|l| {
        let head = l.trim_start().split([':', ' ']).next().unwrap_or("");
        head.ends_with("Error") || head.ends_with("Rejection")
    });
    named
        .or_else(|| text.lines().rev().find(|l| !l.trim().is_empty()))
        .unwrap_or("")
        .trim()
        .chars()
        .take(200)
        .collect()
}

/// A native error the engine raised (not one the program threw).
fn native_error(stderr: &str) -> bool {
    const NATIVE: &[&str] = &["TypeError", "ReferenceError", "RangeError", "SyntaxError"];
    stderr.lines().any(|l| {
        let head = l.trim_start().split([':', ' ']).next().unwrap_or("");
        NATIVE.contains(&head)
    })
}

/// Run `program` under Node: `Ok` if it completes, else what went wrong.
fn run_node(node: &std::ffi::OsStr, program: &str) -> Result<(), (bool, String)> {
    let path = corpus::root().join(program);
    let mut child = Command::new(node)
        .current_dir(path.parent().unwrap())
        .arg(soundness_dir().join("run.mjs"))
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| (false, format!("couldn't run node: {e}")))?;
    let mut stderr = child.stderr.take().unwrap();
    let reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr.read_to_string(&mut s);
        s
    });
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("wait for node") {
            break Some(status);
        }
        if started.elapsed() > TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let stderr = reader.join().unwrap_or_default();
    match status {
        None => Err((
            false,
            format!("timed out after {}s under node", TIMEOUT.as_secs()),
        )),
        Some(s) if s.success() => Ok(()),
        Some(s) => Err((
            native_error(&stderr),
            format!("node exited with {s}: {}", error_line(&stderr)),
        )),
    }
}

enum Outcome {
    Pass(&'static str),
    Fail(String),
}

fn check(program: &str, d: &Directives, node: Option<&std::ffi::OsStr>) -> Outcome {
    let out = corpus::inty(&[program]);
    let accepted = match out.status.code() {
        Some(0) => true,
        Some(1) => false,
        _ => {
            return Outcome::Fail(format!(
                "inty crashed ({}): {}",
                out.status,
                error_line(&String::from_utf8_lossy(&out.stderr))
            ))
        }
    };
    if !accepted {
        return if d.accept {
            let stderr = String::from_utf8_lossy(&out.stderr);
            Outcome::Fail(format!("inty rejects it: {}", error_line(&stderr)))
        } else {
            Outcome::Pass("rejected")
        };
    }
    if d.reject {
        let ran = node.map(|node| match run_node(node, program) {
            Ok(()) => "and node runs it".to_string(),
            Err((_, e)) => format!("({e})"),
        });
        return Outcome::Fail(format!(
            "inty accepts it, which should reject it {}",
            ran.unwrap_or_default()
        ));
    }
    if d.no_run.is_some() {
        return Outcome::Pass("accepted, not run");
    }
    let Some(node) = node else {
        return Outcome::Pass("accepted, not run (no node)");
    };
    match run_node(node, program) {
        Ok(()) => Outcome::Pass("accepted and ran"),
        Err((false, _)) if d.throws.is_some() => Outcome::Pass("accepted, threw as it should"),
        Err((_, e)) => Outcome::Fail(format!("inty accepts it, but {e}")),
    }
}

#[test]
fn accepted_programs_run_under_node() {
    let mut manifest = manifest().unwrap_or_else(|e| panic!("{e}"));
    let filter = std::env::var("INTY_SOUNDNESS_FILTER").unwrap_or_default();
    let all = corpus::programs();
    let stale: Vec<&String> = manifest.keys().filter(|p| !all.contains(p)).collect();
    assert!(
        stale.is_empty(),
        "tests/soundness/corpus.txt names programs that aren't in the corpus: {stale:?}"
    );

    let mut programs = Vec::new();
    for program in all.into_iter().filter(|p| p.contains(&filter)) {
        let mut d = manifest.remove(&program).unwrap_or_default();
        let source = std::fs::read_to_string(corpus::root().join(&program)).unwrap();
        for (n, line) in source.lines().enumerate() {
            if let Some(text) = line.trim().strip_prefix("// inty:") {
                let whence = format!("{program}:{}", n + 1);
                d.add(text, &whence).unwrap_or_else(|e| panic!("{e}"));
            }
        }
        programs.push((program, d));
    }

    let node = node();
    if node.is_none() {
        assert!(
            std::env::var_os("CI").is_none(),
            "no node (or INTY_NODE) on CI: the soundness check needs it"
        );
        eprintln!("note: no node on PATH (or INTY_NODE): checking inty's verdicts only");
    }
    let outcomes = corpus::par_map(&programs, |(program, d)| check(program, d, node.as_deref()));

    let mut failures = Vec::new();
    let mut known = Vec::new();
    let mut fixed = Vec::new();
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for ((program, d), outcome) in programs.iter().zip(outcomes) {
        match (outcome, &d.known_failing) {
            (Outcome::Pass(what), None) => *counts.entry(what).or_default() += 1,
            (Outcome::Pass(_), Some(bug)) => fixed.push(format!(
                "{program}: passes now; remove its `known-failing: {bug}`"
            )),
            (Outcome::Fail(e), None) => failures.push(format!("{program}: {e}")),
            (Outcome::Fail(e), Some(bug)) => known.push(format!("{program}: {e}\n    ({bug})")),
        }
    }
    println!("soundness: {} programs: {counts:?}", programs.len());
    for (program, d) in &programs {
        if let Some(why) = &d.no_run {
            println!("not run: {program}: {why}");
        }
    }
    if !known.is_empty() {
        println!("\nknown failures ({}):\n{}", known.len(), known.join("\n"));
    }
    let mut unexpected = failures;
    unexpected.extend(fixed);
    assert!(
        unexpected.is_empty(),
        "\n{} program(s) failed the soundness check:\n{}\n\n\
         A program inty accepts must run under node. If one doesn't for a\n\
         reason of its own (it needs a DOM, arguments, ...), say so in\n\
         crates/inty-cli/tests/soundness/corpus.txt (see tests/soundness.rs).",
        unexpected.len(),
        unexpected.join("\n")
    );
}
