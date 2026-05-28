//! Verifies every example in `examples/playground/` against the
//! manifest-declared expectation and (when present) against its
//! marker-driven "error variant".
//!
//! Marker convention used inside each example:
//!
//! * **Single line.** A commented-out line ending with `// error!` is
//!   a trigger: when the test enables it, the leading `// ` is
//!   stripped so the statement becomes live code.
//!
//! * **Multi-line block.** Lines wrapped in `// error-begin` /
//!   `// error-end` get the same treatment, line by line. The
//!   delimiters themselves are dropped.
//!
//! Files with `expect: "ok"` must type-check as-written. Files with
//! `expect: "error"` must fail as-written (parse or type error).
//! Any file that contains markers must also fail once the markers
//! are enabled — proving the playground's "uncomment to see the
//! error" hint actually does what it claims.

use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

#[derive(Debug, Deserialize)]
struct Manifest {
    sections: Vec<Section>,
}

#[derive(Debug, Deserialize)]
struct Section {
    id: String,
    items: Vec<Item>,
}

#[derive(Debug, Deserialize)]
struct Item {
    id: String,
    expect: Expect,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Expect {
    Ok,
    Error,
}

/// Run the same pipeline the CLI uses, collapsing parse and type
/// errors into a single `Err` (we only care whether it accepts).
fn check(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    let (_ty, _) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    Ok(())
}

/// Strip the leading `// ` (with optional space) from a line so a
/// commented-out trigger line becomes live code.
fn uncomment(line: &str) -> String {
    let trimmed = line.trim_start();
    let indent_len = line.len() - trimmed.len();
    let indent = &line[..indent_len];
    let rest = trimmed
        .strip_prefix("// ")
        .or_else(|| trimmed.strip_prefix("//"))
        .unwrap_or(trimmed);
    format!("{indent}{rest}")
}

/// Returns `Some(src')` if the file contains any markers; otherwise
/// `None`. The returned source is the input with every trigger line
/// uncommented and the block delimiters removed.
fn enable_markers(src: &str) -> Option<String> {
    let mut out = String::with_capacity(src.len());
    let mut in_block = false;
    let mut found_any = false;

    for raw_line in src.split_inclusive('\n') {
        let line = raw_line.strip_suffix('\n').unwrap_or(raw_line);
        let body = line.trim();

        if body.starts_with("//") && body.contains("error-begin") {
            in_block = true;
            found_any = true;
            continue;
        }
        if body.starts_with("//") && body.contains("error-end") {
            in_block = false;
            continue;
        }
        if in_block {
            out.push_str(&uncomment(line));
            if raw_line.ends_with('\n') {
                out.push('\n');
            }
            continue;
        }
        // Single-line trigger: a comment line ending with `// error!`.
        if body.starts_with("//") && body.trim_end().ends_with("// error!") {
            found_any = true;
            out.push_str(&uncomment(line));
            if raw_line.ends_with('\n') {
                out.push('\n');
            }
            continue;
        }
        out.push_str(raw_line);
    }

    if found_any {
        Some(out)
    } else {
        None
    }
}

fn workspace_root() -> PathBuf {
    // `CARGO_MANIFEST_DIR` is `<root>/crates/inty`.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn read_manifest() -> (PathBuf, Manifest) {
    let root = workspace_root();
    let dir = root.join("examples").join("playground");
    let manifest_path = dir.join("manifest.json");
    let raw = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", manifest_path.display()));
    let manifest: Manifest =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse manifest: {e}"));
    (dir, manifest)
}

fn read_example(dir: &Path, section: &str, item: &str) -> String {
    let path = dir.join(section).join(format!("{item}.js"));
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

#[test]
fn every_example_matches_manifest_expectation() {
    let (dir, manifest) = read_manifest();
    let mut failures: Vec<String> = Vec::new();

    for section in &manifest.sections {
        for item in &section.items {
            let src = read_example(&dir, &section.id, &item.id);
            let result = check(&src);
            let qualified = format!("{}/{}", section.id, item.id);
            match (&item.expect, &result) {
                (Expect::Ok, Err(e)) => {
                    failures.push(format!("{qualified}: expected to type-check, got: {e}"));
                }
                (Expect::Error, Ok(())) => {
                    failures.push(format!(
                        "{qualified}: expected an error, but it type-checked"
                    ));
                }
                _ => {}
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} example(s) disagreed with manifest:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}

#[test]
fn marker_lines_actually_trigger_errors() {
    let (dir, manifest) = read_manifest();
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0usize;

    for section in &manifest.sections {
        for item in &section.items {
            let src = read_example(&dir, &section.id, &item.id);
            let Some(enabled) = enable_markers(&src) else {
                continue;
            };
            covered += 1;
            let qualified = format!("{}/{}", section.id, item.id);
            if check(&enabled).is_ok() {
                failures.push(format!(
                    "{qualified}: enabling the `// error!` marker(s) did not produce an error"
                ));
            }
        }
    }

    assert!(
        covered > 0,
        "no marker-bearing examples found — did the convention change?"
    );
    assert!(
        failures.is_empty(),
        "{} example(s) failed marker check:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}
