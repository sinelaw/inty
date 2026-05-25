//! End-to-end checks for the Lua and Python frontends against the
//! example files in `examples/lua` and `examples/python`.
//!
//! Convention: a file named `ok_*.{lua,py}` must parse and type-check;
//! a file named `err_*.{lua,py}` must fail (parse or type error). This
//! keeps the shipped examples honest and exercises each frontend through
//! the same pipeline the CLI uses.

use std::fs;
use std::path::{Path, PathBuf};

use inty::frontends::{parse, Language};
use inty::stdlib::initial_env_with_stdlib;

/// Parse `src` with `lang`, then infer and resolve constraints. Collapses
/// parse and type errors into a single `Err`.
fn check(lang: Language, src: &str) -> Result<(), String> {
    let program = parse(lang, src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    let collected = state.take_errors();
    if !collected.is_empty() {
        return Err(format!("type errors: {:?}", collected));
    }
    Ok(())
}

fn workspace_root() -> PathBuf {
    // `CARGO_MANIFEST_DIR` is `<root>/crates/inty`.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn run_dir(lang: Language, dir: &Path, ext: &str, failures: &mut Vec<String>) {
    let mut count = 0usize;
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read dir {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == ext).unwrap_or(false))
        .collect();
    entries.sort();

    for path in entries {
        count += 1;
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let src = fs::read_to_string(&path).unwrap();
        let result = check(lang, &src);
        let expect_ok = name.starts_with("ok_");
        let expect_err = name.starts_with("err_");
        assert!(
            expect_ok || expect_err,
            "example {} must be named ok_* or err_*",
            name
        );
        match (expect_ok, &result) {
            (true, Err(e)) => failures.push(format!("{name}: expected to type-check, got: {e}")),
            (false, Ok(())) => {
                failures.push(format!("{name}: expected an error, but it type-checked"))
            }
            _ => {}
        }
    }

    assert!(count > 0, "no .{ext} examples found in {}", dir.display());
}

#[test]
fn lua_examples_match_expectation() {
    let dir = workspace_root().join("examples").join("lua");
    let mut failures = Vec::new();
    run_dir(Language::Lua, &dir, "lua", &mut failures);
    assert!(
        failures.is_empty(),
        "{} Lua example(s) disagreed:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}

#[test]
fn python_examples_match_expectation() {
    let dir = workspace_root().join("examples").join("python");
    let mut failures = Vec::new();
    run_dir(Language::Python, &dir, "py", &mut failures);
    assert!(
        failures.is_empty(),
        "{} Python example(s) disagreed:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}
