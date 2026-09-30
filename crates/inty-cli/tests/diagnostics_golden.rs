//! Golden tests of rendered diagnostics.
//!
//! Each directory under `tests/golden/` is a small program: `main.js`
//! (and whatever it imports), optionally an `args` file with the
//! command-line arguments (default: `main.js`). The test runs the `inty`
//! binary there with colour off and compares its stderr with
//! `expected.txt`. Run with `INTY_BLESS=1` to rewrite the expectations
//! after an intended change, and review the diff.

use std::path::Path;
use std::process::Command;

fn run_case(dir: &Path) -> Result<(), String> {
    let args = std::fs::read_to_string(dir.join("args")).unwrap_or_else(|_| "main.js".into());
    let out = Command::new(env!("CARGO_BIN_EXE_inty"))
        .current_dir(dir)
        .arg("--no-color")
        .args(args.split_whitespace())
        .output()
        .map_err(|e| e.to_string())?;
    let actual = String::from_utf8_lossy(&out.stderr).into_owned();
    let expected_path = dir.join("expected.txt");
    if std::env::var_os("INTY_BLESS").is_some() {
        std::fs::write(&expected_path, &actual).map_err(|e| e.to_string())?;
        return Ok(());
    }
    let expected = std::fs::read_to_string(&expected_path)
        .map_err(|e| format!("{}: {}", expected_path.display(), e))?;
    if actual != expected {
        return Err(format!(
            "--- expected ({})\n{expected}\n--- actual\n{actual}",
            expected_path.display()
        ));
    }
    Ok(())
}

#[test]
fn golden_diagnostics() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let mut cases: Vec<_> = std::fs::read_dir(&root)
        .expect("tests/golden")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    cases.sort();
    assert!(!cases.is_empty());
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|dir| {
            run_case(dir)
                .err()
                .map(|e| format!("== {}\n{e}", dir.file_name().unwrap().to_string_lossy()))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
