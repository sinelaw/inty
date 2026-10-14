//! How much of inty's examples the Lean model covers (ground rule 4 of
//! `lean/ROADMAP.md`).
//!
//! Each JavaScript file under `examples/` is written in the model's wire
//! format by `inty::model_wire`, if it lies in the model's fragment. The test
//! prints how many do, and, for the others, the first construct the model
//! lacks, counted over the files: a measure of what the model covers, and a
//! list of what to model next. A file in the fragment is checked by both
//! inty and the model, which must agree on accepting it.

use inty::builtins::initial_env;
use inty::infer::InferState;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

mod oracle;
use oracle::*;

/// Whether inty accepts the program whose entry module is `path`, as the
/// CLI checks it (with the modules it imports).
fn inty_accepts(path: &Path) -> bool {
    let path = path.to_path_buf();
    inty::worker::run_with_inference_stack("inty-examples", move || {
        let mut state = InferState::new();
        inty::modules::check_module(&mut state, initial_env(), &path).is_ok()
            && state.take_errors().is_empty()
            && state.resolve_constraints().is_ok()
    })
}

fn js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            if p.file_name()
                .is_some_and(|n| n == "node_modules" || n == "dist")
            {
                continue;
            }
            js_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "js")
            && !p.to_string_lossy().ends_with(".d.js")
        {
            out.push(p);
        }
    }
}

/// What the first construct outside the fragment is, without the details
/// (a name, a label) that would split one kind into many.
fn kind(reason: &str) -> String {
    let r = reason.split(':').next().unwrap_or(reason);
    let mut out = String::new();
    let mut quoted = false;
    for c in r.chars() {
        if c == '\'' {
            quoted = !quoted;
            out.push_str(if quoted { "'…" } else { "'" });
        } else if !quoted {
            out.push(c);
        }
    }
    out.trim().to_string()
}

#[test]
fn the_model_on_inty_examples() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut files = Vec::new();
    js_files(&root, &mut files);
    assert!(!files.is_empty(), "no examples under {}", root.display());
    let mut lowered = Vec::new();
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    let mut lines = (0, 0);
    for f in &files {
        let source = std::fs::read_to_string(f).unwrap();
        let n = source.lines().count();
        lines.1 += n;
        let wire = inty::model_wire::lower_entry(f);
        match wire {
            Ok(w) => {
                lines.0 += n;
                lowered.push((f.clone(), w));
            }
            Err(e) => {
                if std::env::var_os("INTY_EXAMPLES_WHY").is_some() {
                    eprintln!("{}: {e}", f.display());
                }
                *reasons.entry(kind(&e)).or_default() += 1
            }
        }
    }
    eprintln!(
        "{} of {} example files ({} of {} lines) are in the model's fragment",
        lowered.len(),
        files.len(),
        lines.0,
        lines.1
    );
    let mut reasons: Vec<_> = reasons.into_iter().collect();
    reasons.sort_by_key(|r| std::cmp::Reverse(r.1));
    for (r, n) in &reasons {
        eprintln!("  {n:4}  {r}");
    }
    for (f, _) in &lowered {
        eprintln!(
            "  in the fragment: {}",
            f.strip_prefix(&root).unwrap_or(f).display()
        );
    }
    let Some(model) = model_path() else {
        assert!(
            std::env::var_os("INTY_REQUIRE_MODEL").is_none(),
            "no inty-model, and INTY_REQUIRE_MODEL is set"
        );
        eprintln!("skipping the comparison: no inty-model (cd lean && lake build)");
        return;
    };
    // The model and inty agree on accepting each file in the fragment.
    let input: String = lowered.iter().map(|(_, w)| format!("{w}\n")).collect();
    let verdicts = run_lines(Command::new(model), "inty-model", input, lowered.len());
    let disagreements: Vec<String> = lowered
        .iter()
        .zip(&verdicts)
        .filter_map(|((f, w), line)| {
            let (typing, _) = parse_model_line(line);
            let model = typing != Typing::Reject;
            let inty = inty_accepts(f);
            (model != inty).then(|| {
                format!(
                    "{}: inty {}, the model {}\n  wire: {w}",
                    f.display(),
                    if inty { "accepts" } else { "rejects" },
                    if model { "accepts" } else { "rejects" },
                )
            })
        })
        .collect();
    assert!(
        disagreements.is_empty(),
        "inty and the model disagree on examples:\n{}",
        disagreements.join("\n")
    );
}
