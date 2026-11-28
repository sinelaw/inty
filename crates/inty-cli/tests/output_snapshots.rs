//! What inty prints for every program of the corpus (`tests/corpus/mod.rs`:
//! the repository's example and test programs, and the soundness probes),
//! pinned by a committed snapshot: `tests/snapshots/PATH.out` holds, for the
//! program at PATH,
//!
//! - `inty PATH`: its exit status, stdout (the program printed back with
//!   the types inty inferred, as annotations) and stderr (its diagnostics);
//! - for a module that exports something, `inty declarations PATH` too.
//!
//! The run time in the summary line is left out, and the workspace's path
//! is written `<root>`. The test fails on any
//! difference, on a program with no snapshot and on a snapshot with no
//! program, so a change to what inty infers or reports for any of them
//! shows up in review as a diff of the snapshots: an intended change is
//! committed with them updated,
//!
//! ```text
//! INTY_BLESS=1 cargo test -p inty-cli --test output_snapshots
//! git diff crates/inty-cli/tests/snapshots
//! ```
//!
//! and one nobody meant fails CI. `INTY_BLESS` writes every snapshot anew
//! (adding and removing files), as in `tests/diagnostics_golden.rs`.

use std::path::{Path, PathBuf};

mod corpus;

fn snapshot_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots")
}

/// The summary line's run time (`... in 12ms`, `... in 1.30s`), which
/// differs from run to run.
fn without_time(stdout: &str) -> String {
    stdout
        .lines()
        .map(|line| match line.rfind(" in ") {
            Some(i)
                if line.starts_with("All checks passed: ")
                    && line[i + 4..].ends_with('s')
                    && line[i + 4..]
                        .trim_end_matches(['m', 's'])
                        .parse::<f64>()
                        .is_ok() =>
            {
                format!("{} in <time>", &line[..i])
            }
            _ => line.to_string(),
        })
        .map(|l| l + "\n")
        .collect()
}

/// `text` with the workspace's path (inty names a module by its absolute
/// path) as `<root>`.
fn without_root(text: &str) -> String {
    let root = corpus::root();
    let mut roots = vec![root.display().to_string()];
    if let Ok(real) = root.canonicalize() {
        roots.push(real.display().to_string());
    }
    roots.sort_by_key(|r| std::cmp::Reverse(r.len()));
    roots
        .iter()
        .fold(text.to_string(), |t, r| t.replace(r.as_str(), "<root>"))
}

fn section(out: &mut String, args: &[&str]) {
    let output = corpus::inty(args);
    let status = match output.status.code() {
        Some(code) => code.to_string(),
        None => output.status.to_string(),
    };
    out.push_str(&format!("$ inty {}\n", args.join(" ")));
    out.push_str(&format!("exit: {status}\n"));
    out.push_str("--- stdout\n");
    let stdout = without_time(&String::from_utf8_lossy(&output.stdout));
    out.push_str(&without_root(&stdout));
    out.push_str("--- stderr\n");
    out.push_str(&without_root(&String::from_utf8_lossy(&output.stderr)));
    if !out.ends_with('\n') {
        out.push('\n');
    }
}

fn exports_something(source: &str) -> bool {
    source
        .lines()
        .any(|l| l.trim_start().starts_with("export "))
}

/// What the snapshot of `program` holds.
fn render(program: &str) -> String {
    let source = std::fs::read_to_string(corpus::root().join(program)).unwrap();
    let mut out = String::new();
    section(&mut out, &[program]);
    if exports_something(&source) {
        out.push('\n');
        section(&mut out, &["declarations", program]);
    }
    out
}

fn snapshot_path(program: &str) -> PathBuf {
    snapshot_dir().join(format!("{program}.out"))
}

/// The lines where `expected` and `actual` differ, between the lines they
/// begin and end with in common, with a few lines of context.
fn difference(expected: &str, actual: &str) -> String {
    let e: Vec<&str> = expected.lines().collect();
    let a: Vec<&str> = actual.lines().collect();
    let prefix = e.iter().zip(&a).take_while(|(x, y)| x == y).count();
    let suffix = e[prefix..]
        .iter()
        .rev()
        .zip(a[prefix..].iter().rev())
        .take_while(|(x, y)| x == y)
        .count();
    const CONTEXT: usize = 3;
    const MAX: usize = 40;
    let mut out = format!("@@ line {} @@\n", prefix + 1);
    for line in &e[prefix.saturating_sub(CONTEXT)..prefix] {
        out.push_str(&format!(" {line}\n"));
    }
    let removed = &e[prefix..e.len() - suffix];
    let added = &a[prefix..a.len() - suffix];
    for line in removed.iter().take(MAX) {
        out.push_str(&format!("-{line}\n"));
    }
    if removed.len() > MAX {
        out.push_str(&format!("-... ({} more)\n", removed.len() - MAX));
    }
    for line in added.iter().take(MAX) {
        out.push_str(&format!("+{line}\n"));
    }
    if added.len() > MAX {
        out.push_str(&format!("+... ({} more)\n", added.len() - MAX));
    }
    for line in e[e.len() - suffix..].iter().take(CONTEXT) {
        out.push_str(&format!(" {line}\n"));
    }
    out
}

fn snapshot_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            snapshot_files(&path, out);
        } else {
            out.push(path);
        }
    }
}

#[test]
fn output_matches_snapshots() {
    let programs = corpus::programs();
    let bless = std::env::var_os("INTY_BLESS").is_some();
    let rendered = corpus::par_map(&programs, |p| render(p));

    let mut problems = Vec::new();
    for (program, actual) in programs.iter().zip(&rendered) {
        let path = snapshot_path(program);
        if bless {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            if std::fs::read_to_string(&path).ok().as_ref() != Some(actual) {
                std::fs::write(&path, actual).unwrap();
            }
            continue;
        }
        match std::fs::read_to_string(&path) {
            Err(_) => problems.push(format!("== {program}: no snapshot ({})", path.display())),
            Ok(expected) if &expected != actual => problems.push(format!(
                "== {program}: differs from its snapshot\n{}",
                difference(&expected, actual)
            )),
            Ok(_) => {}
        }
    }

    // Snapshots of programs that are gone.
    let mut files = Vec::new();
    snapshot_files(&snapshot_dir(), &mut files);
    for file in files {
        let rel = file.strip_prefix(snapshot_dir()).unwrap();
        let rel = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let known = rel
            .strip_suffix(".out")
            .is_some_and(|p| programs.iter().any(|q| q == p));
        if known {
            continue;
        }
        if bless {
            std::fs::remove_file(&file).unwrap();
        } else {
            problems.push(format!("== {rel}: a snapshot of no program"));
        }
    }

    assert!(
        problems.is_empty(),
        "\n{}\n\n{} snapshot(s) out of date. If the change is intended, update them with\n\
         \n    INTY_BLESS=1 cargo test -p inty-cli --test output_snapshots\n\n\
         and commit them, so that the change shows in review \
         (docs/regression-checks.md).",
        problems.join("\n\n"),
        problems.len()
    );
}
