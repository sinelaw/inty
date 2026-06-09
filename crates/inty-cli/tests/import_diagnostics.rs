//! Diagnostic-location tests for multi-file programs.
//!
//! Every other test in the workspace stops at "an error was raised"
//! (`is_err()` / non-empty `state.errors`). None check *where* the error
//! is reported. This is the missing layer: when the entry file imports a
//! module that itself contains an error, the diagnostic must point at the
//! *imported* file and the offending line — not at the importer.
//!
//! These drive the real `inty` binary so they exercise the same
//! diagnostic-rendering path a user sees.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(0);

fn tmp_dir() -> PathBuf {
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("inty_cli_diag_{}_{}", std::process::id(), n));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn write(dir: &Path, rel: &str, contents: &str) {
    std::fs::write(dir.join(rel), contents).expect("write fixture");
}

/// Run the `inty` binary on `entry` (with colour disabled) and return the
/// combined stdout+stderr.
fn run_inty(entry: &Path) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_inty"))
        .arg("--no-color")
        .arg(entry)
        .output()
        .expect("spawn inty");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    combined
}

#[test]
fn type_error_in_imported_module_points_at_that_module() {
    // `helpers.py` has a type error on line 3 (`oops = 1 + "x"`). The
    // entry only imports the healthy `double`. The diagnostic must name
    // the imported file and its line — not blame the importer.
    let dir = tmp_dir();
    write(
        &dir,
        "helpers.py",
        "def double(x):\n    return x + x\noops = 1 + \"x\"\n",
    );
    write(
        &dir,
        "main.py",
        "from helpers import double\nr = double(21)\nr\n",
    );

    let output = run_inty(&dir.join("main.py"));
    assert!(
        output.contains("helpers.py:3"),
        "diagnostic for a type error inside helpers.py must point at that file/line, got:\n{output}"
    );
    assert!(
        !output.contains("main.py"),
        "the type error lives in helpers.py, so the importer must not be blamed, got:\n{output}"
    );
}

#[test]
fn parse_error_in_imported_module_points_at_that_module() {
    // A parse error inside the imported module must likewise be located
    // in that file, not at the importer's `import` statement.
    let dir = tmp_dir();
    write(&dir, "helpers.py", "class Dog(Animal):\n    pass\n");
    write(&dir, "main.py", "from helpers import Dog\n");

    let output = run_inty(&dir.join("main.py"));
    assert!(
        output.contains("helpers.py:1"),
        "diagnostic for a parse error inside helpers.py must point at that file/line, got:\n{output}"
    );
    assert!(
        !output.contains("main.py"),
        "the parse error lives in helpers.py, so the importer must not be blamed, got:\n{output}"
    );
}
