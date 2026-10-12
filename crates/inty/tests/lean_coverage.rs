//! `lean/COVERAGE.md` against the Lean model and inty (ground rule 3 of
//! `lean/ROADMAP.md`): every rule of `HasTypeS` is in its table of rules,
//! every inty function it names exists, and every inference function of
//! inty's is named in one of its tables.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The backticked names in `text`.
fn ticked(text: &str) -> Vec<String> {
    text.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_string)
        .collect()
}

/// The constructors of the inductive `name` in a Lean source: the lines
/// `  | c …` from its declaration to the next declaration at column 0.
fn constructors(lean: &str, name: &str) -> Vec<String> {
    let start = lean
        .find(&format!("inductive {name} "))
        .unwrap_or_else(|| panic!("no inductive {name}"));
    let mut out = Vec::new();
    for line in lean[start..].lines().skip(1) {
        // (A rule may start at column 0: `| c …`.)
        if !line.is_empty()
            && !line.starts_with(' ')
            && !line.starts_with("--")
            && !line.starts_with('|')
        {
            break;
        }
        if let Some(rest) = line.trim_start().strip_prefix("| ") {
            let c: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            out.push(c);
        }
    }
    out
}

/// Every `fn` name in the Rust sources under `dir`.
fn rust_fns(dir: &Path, out: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_fns(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            for piece in read(&path).split("fn ").skip(1) {
                let name: String = piece
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !name.is_empty() {
                    out.insert(name);
                }
            }
        }
    }
}

/// inty's inference functions: `infer_…` and `check_…` in these files.
fn inference_fns(files: &[PathBuf]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for f in files {
        for piece in read(f).split("fn ").skip(1) {
            let name: String = piece
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if name.starts_with("infer_") || name.starts_with("check_") {
                out.insert(name);
            }
        }
    }
    out
}

#[test]
fn the_coverage_table_matches_the_model_and_inty() {
    let root = root();
    let table = read(&root.join("lean/COVERAGE.md"));
    let (rules_part, rest) = table
        .split_once("## inty's functions the model doesn't have")
        .expect("COVERAGE.md has its two tables");
    let rows = |part: &str| -> Vec<(Vec<String>, Vec<String>)> {
        part.lines()
            .filter(|l| l.starts_with("| `"))
            .map(|l| {
                let cells: Vec<&str> = l.split(" | ").collect();
                (
                    ticked(cells[0]),
                    cells.get(1).map(|c| ticked(c)).unwrap_or_default(),
                )
            })
            .collect()
    };
    let rule_rows = rows(rules_part);
    let missing_rows = rows(rest);
    let mut failures = Vec::new();

    // Every rule is in the table of rules, and only rules are.
    let typing = read(&root.join("lean/Inty/Typing.lean"));
    let rules: Vec<String> = constructors(&typing, "HasTypeS")
        .into_iter()
        .map(|c| format!("HasTypeS.{c}"))
        .collect();
    let listed: Vec<String> = rule_rows.iter().flat_map(|(r, _)| r.clone()).collect();
    for r in &rules {
        if !listed.contains(r) {
            failures.push(format!("the rule `{r}` isn't in lean/COVERAGE.md"));
        }
    }
    for r in &listed {
        if !rules.contains(r) {
            failures.push(format!("lean/COVERAGE.md lists `{r}`, which isn't a rule"));
        }
    }

    // Every inty function named exists.
    let mut fns = BTreeSet::new();
    rust_fns(&root.join("crates/inty/src"), &mut fns);
    // The inty column of each table: every name there is a function.
    let named: BTreeSet<String> = rule_rows
        .iter()
        .flat_map(|(_, inty)| inty.clone())
        .chain(missing_rows.iter().flat_map(|(n, _)| n.clone()))
        .chain(
            ticked(&table)
                .into_iter()
                .filter(|n| n.starts_with("infer_") || n.starts_with("check_")),
        )
        .filter(|n| n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
        .collect();
    for n in &named {
        if !fns.contains(n) {
            failures.push(format!("lean/COVERAGE.md names `{n}`, which inty hasn't"));
        }
    }

    // Every inference function is named, as modelled or not.
    let src = root.join("crates/inty/src/infer");
    let mut files: Vec<PathBuf> = std::fs::read_dir(src.join("features"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .collect();
    files.push(src.join("mod.rs"));
    files.push(src.join("state.rs"));
    let covered: BTreeSet<String> = named
        .iter()
        .cloned()
        .chain(missing_rows.iter().flat_map(|(n, _)| n.clone()))
        .collect();
    for f in inference_fns(&files) {
        if !covered.contains(&f) {
            failures.push(format!(
                "inty's `{f}` is in neither table of lean/COVERAGE.md"
            ));
        }
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
