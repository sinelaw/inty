//! `inty fmt`: long annotations laid out across lines, in place.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn tmp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("inty_fmt_{}_{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sub")).expect("create temp dir");
    dir
}

fn inty(args: &[&str], dir: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_inty"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn inty")
}

const LONG: &str = "/** type ScoreView = { id: String, scope: String, size: Number, zoom: Number, width: Number, height: Number, fitWidth: Number } */
/** type P = { x: Number } */
/** const v: ScoreView */
const v = { id: \"a\", scope: \"\", size: 1, zoom: 2, width: 3, height: 4, fitWidth: 5 };
";

const WRAPPED: &str = "/** type ScoreView = {
 *   id: String,
 *   scope: String,
 *   size: Number,
 *   zoom: Number,
 *   width: Number,
 *   height: Number,
 *   fitWidth: Number,
 * } */
/** type P = { x: Number } */
/** const v: ScoreView */
const v = { id: \"a\", scope: \"\", size: 1, zoom: 2, width: 3, height: 4, fitWidth: 5 };
";

#[test]
fn check_lists_what_would_change_and_rewrites_nothing() {
    let dir = tmp_dir("check");
    std::fs::write(dir.join("sub/a.js"), LONG).unwrap();
    std::fs::write(dir.join("b.js"), WRAPPED).unwrap();
    let out = inty(&["fmt", "--check", "."], &dir);
    assert_eq!(out.status.code(), Some(1));
    let listed = String::from_utf8_lossy(&out.stdout);
    assert!(
        listed.contains("a.js") && !listed.contains("b.js"),
        "{listed}"
    );
    assert_eq!(std::fs::read_to_string(dir.join("sub/a.js")).unwrap(), LONG);
}

#[test]
fn fmt_rewrites_in_place_and_is_idempotent() {
    let dir = tmp_dir("write");
    std::fs::write(dir.join("a.js"), LONG).unwrap();
    let out = inty(&["fmt", "a.js"], &dir);
    assert!(out.status.success(), "{out:?}");
    assert_eq!(std::fs::read_to_string(dir.join("a.js")).unwrap(), WRAPPED);
    // Nothing more to do.
    let again = inty(&["fmt", "--check", "a.js"], &dir);
    assert_eq!(again.status.code(), Some(0), "{again:?}");
    // And the program still checks.
    let checked = inty(&["--no-color", "a.js"], &dir);
    assert!(checked.status.success(), "{checked:?}");
}

#[test]
fn the_width_is_configurable() {
    let dir = tmp_dir("width");
    std::fs::write(dir.join("a.js"), LONG).unwrap();
    let out = inty(&["fmt", "--check", "--width=200", "a.js"], &dir);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let out = inty(&["fmt", "--width", "20", "a.js"], &dir);
    assert!(out.status.success(), "{out:?}");
    let text = std::fs::read_to_string(dir.join("a.js")).unwrap();
    // `type P = { x: Number }` is longer than 20 columns now.
    assert!(
        text.contains("/** type P = {\n *   x: Number,\n * } */"),
        "{text}"
    );
}
