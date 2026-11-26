//! Inference records the type of every expression it checks
//! (`InferState::expr_types`): what the language server's hover answers
//! from, and what the Go backend generates code from. A path that types an
//! expression without recording it is a hover that shows nothing.
//!
//! Every expression of every example program that checks cleanly must
//! have a recorded type.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use inty::ast::visit::each_expr;
use inty::ast::Expr;
use inty::frontends::{self, Language};

fn js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|n| n != "node_modules") {
                js_files(&path, out);
            }
        } else if path.extension().is_some_and(|e| e == "js") {
            out.push(path);
        }
    }
}

/// The variant's name, for grouping what's missing.
fn kind(e: &Expr) -> String {
    let debug = format!("{e:?}");
    debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or_default()
        .to_string()
}

/// The expressions of the program at `path` inference checked without
/// recording a type, as `(kind, site)`; `None` when it doesn't check
/// cleanly (a failing statement's expressions may not all be checked).
fn unrecorded(root: &Path, path: &Path) -> Option<Vec<(String, String)>> {
    let source = std::fs::read_to_string(path).unwrap();
    let program = frontends::parse(Language::JavaScript, &source).ok()?;
    let (base, mut state) = inty::stdlib::initial_env_with_stdlib().unwrap();
    let env = frontends::program_env(&mut state, base, &program, Language::JavaScript, Some(path))
        .ok()?;
    // Only the program's own expressions: its imports are checked.
    state.expr_types = Some(Default::default());
    state.infer_program_with_env(&env, &program).ok()?;
    let recorded = state.expr_types.take().unwrap();
    let mut missing = Vec::new();
    each_expr(&program.statements, &mut |e| {
        let span = e.span();
        if !recorded.contains_key(&(span.start, span.end)) {
            let text = source.get(span.start..span.end).unwrap_or("<made up>");
            let line = source[..span.start.min(source.len())].matches('\n').count() + 1;
            missing.push((
                kind(e),
                format!(
                    "{}:{line}: {}",
                    path.strip_prefix(root).unwrap_or(path).display(),
                    text.chars().take(60).collect::<String>().replace('\n', " ")
                ),
            ));
        }
    });
    Some(missing)
}

#[test]
fn every_checked_expression_has_a_recorded_type() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for dir in ["examples", "web", "crates/inty/tests"] {
        js_files(&root.join(dir), &mut files);
    }
    files.sort();

    // Each file on its own thread (its own state; inference wants a
    // deep stack): loading the stdlib dominates, once per file.
    let results: Vec<Option<Vec<(String, String)>>> = std::thread::scope(|scope| {
        let handles: Vec<_> = files
            .iter()
            .map(|path| {
                let root = &root;
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(scope, move || unrecorded(root, path))
                    .unwrap()
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let checked = results.iter().filter(|r| r.is_some()).count();
    let mut missing: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (kind, site) in results.into_iter().flatten().flatten() {
        missing.entry(kind).or_default().push(site);
    }
    assert!(checked > 40, "only {checked} example programs checked");
    let report: Vec<String> = missing
        .iter()
        .map(|(kind, sites)| {
            format!(
                "{kind}: {} unrecorded, e.g.\n    {}",
                sites.len(),
                sites
                    .iter()
                    .take(4)
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("\n    ")
            )
        })
        .collect();
    assert!(
        missing.is_empty(),
        "expressions inference checked without recording a type:\n{}",
        report.join("\n")
    );
}
