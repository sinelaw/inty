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

/// Run the `inty` binary with `args` (colour disabled) in `dir`; returns
/// (success, stdout, stderr).
fn run_inty_args(dir: &Path, args: &[&str]) -> (bool, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_inty"))
        .current_dir(dir)
        .arg("--no-color")
        .args(args)
        .output()
        .expect("spawn inty");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn several_files_share_the_modules_they_import() {
    let dir = tmp_dir();
    write(&dir, "store.js", "export const state = { n: 0 };\n");
    write(
        &dir,
        "a.js",
        "import { state } from \"./store.js\";\nexport function a() { state.n = state.n + 1; }\n",
    );
    write(
        &dir,
        "b.js",
        "import { state } from \"./store.js\";\nimport { a } from \"./a.js\";\nexport function b() { a(); return state.n; }\n",
    );
    let (ok, stdout, stderr) = run_inty_args(&dir, &["store.js", "a.js", "b.js"]);
    assert!(ok, "{stdout}{stderr}");
    assert!(
        stdout.contains("All checks passed: 3 files (3 modules checked"),
        "{stdout}"
    );
    // A conflicting use in another file is reported in that file.
    write(
        &dir,
        "c.js",
        "import { state } from \"./store.js\";\nstate.n = \"many\";\n",
    );
    let (ok, stdout, stderr) = run_inty_args(&dir, &["a.js", "b.js", "c.js"]);
    assert!(!ok, "{stdout}{stderr}");
    assert!(stderr.contains("c.js:2"), "{stderr}");
}

#[test]
fn timings_report_modules_and_declarations() {
    let dir = tmp_dir();
    write(
        &dir,
        "lib.js",
        "export function double(x) { return x * 2; }\n",
    );
    write(
        &dir,
        "main.js",
        "import { double } from \"./lib.js\";\nfunction twice(n) { return double(double(n)); }\nconst r = twice(3);\n",
    );
    let (ok, _stdout, stderr) = run_inty_args(&dir, &["--timings", "main.js"]);
    assert!(ok, "{stderr}");
    assert!(stderr.contains("Timings"), "{stderr}");
    assert!(stderr.contains("lib.js"), "{stderr}");
    assert!(stderr.contains("function twice  (main.js:2)"), "{stderr}");
    assert!(stderr.contains("const r  (main.js:3)"), "{stderr}");
}

/// A project's `inty.json` is found from the file however it is named: a
/// path relative to the working directory (`inty js/a.js`, run in a
/// directory below the project's root) reaches the config above it.
#[test]
fn a_relative_entry_path_finds_the_project_config_above_it() {
    let dir = tmp_dir();
    std::fs::create_dir_all(dir.join("types")).unwrap();
    std::fs::create_dir_all(dir.join("web/js")).unwrap();
    write(
        &dir,
        "types/app.d.js",
        "/** type Op = {t: String, pos: Number} */\n",
    );
    write(&dir, "inty.json", r#"{ "libs": ["./types/app.d.js"] }"#);
    write(
        &dir,
        "web/js/a.js",
        "/** function at(pos: Number) => Op */\nfunction at(pos) { return { t: \"ins\", pos }; }\n",
    );
    for args in [&["js/a.js"][..], &["js/a.js", "js/a.js"][..]] {
        let out = Command::new(env!("CARGO_BIN_EXE_inty"))
            .arg("--no-color")
            .args(args)
            .current_dir(dir.join("web"))
            .output()
            .expect("spawn inty");
        let text = String::from_utf8_lossy(&out.stdout).into_owned()
            + &String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "inty {args:?}:\n{text}");
    }
}

/// A class that fails to check (an error in a method) is unknown to the
/// modules checked after it, not a type that fits nothing: an annotation
/// naming it there gives no error of its own.
#[test]
fn a_class_that_failed_to_check_is_unknown_elsewhere() {
    let dir = tmp_dir();
    write(
        &dir,
        "h.js",
        "/** type M = {kind: \"a\"} | {kind: \"b\"} */\n\
         /** function send(m: M) => Undefined */\nfunction send(m) {}\n\
         export class H {\n  constructor() { this.g = [1]; }\n  \
         bad() { send({ kind: \"c\" }); return this.g.length; }\n}\n",
    );
    write(
        &dir,
        "g.js",
        "export class G {\n  constructor(h) {\n    /** this.h: Promise<H> */\n    this.h = h;\n  }\n  \
         go() { return this.h.then((x) => x.g.length + x.bad()); }\n}\n",
    );
    let (ok, stdout, stderr) = run_inty_args(&dir, &["h.js", "g.js"]);
    assert!(!ok, "{stdout}{stderr}");
    let all = format!("{stdout}{stderr}");
    assert!(all.contains("h.js:6:"), "{all}");
    assert!(!all.contains("g.js:"), "no error in g.js:\n{all}");
}
