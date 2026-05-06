//! End-to-end bundler tests. Most tests build a small fixture in a
//! tempdir, bundle it, and assert structural properties of the
//! emitted JS plus the source map. The `quickjs_round_trip` test
//! actually executes the bundle through rquickjs to verify it
//! evaluates without errors.

use std::io::Write;
use std::path::{Path, PathBuf};

fn make_tempdir(tag: &str) -> PathBuf {
    let base = std::env::temp_dir();
    let pid = std::process::id();
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = base.join(format!("inty-bundle-{}-{}-{}", tag, pid, nonce));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(dir: &Path, name: &str, contents: &str) -> PathBuf {
    let path = dir.join(name);
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(contents.as_bytes()).unwrap();
    path
}

#[test]
fn bundles_named_imports() {
    let dir = make_tempdir("named");
    write(
        &dir,
        "lib.js",
        "export var answer = 42;\nexport function id(x) { return x; }\n",
    );
    let entry = write(
        &dir,
        "app.js",
        "import { answer, id } from \"./lib.js\";\n\
         var v = id(answer);\n",
    );

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    assert!(out.code.contains("__mods["), "missing __mods registry");
    assert!(out.code.contains("__exports.answer"), "lib must export answer");
    assert!(out.code.contains("__exports.id"), "lib must export id");
    assert!(
        out.code.contains("var answer = __mods["),
        "named import should rewrite to __mods lookup"
    );
    assert!(
        out.code.contains("var id = __mods["),
        "named import should rewrite to __mods lookup"
    );
    // Source map should be valid JSON containing "version":3.
    assert!(
        out.source_map.contains("\"version\":3"),
        "source map should be v3 JSON; got: {}",
        out.source_map
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn bundles_namespace_import() {
    let dir = make_tempdir("ns");
    write(
        &dir,
        "lib.js",
        "export var answer = 42;\nexport var name = \"x\";\n",
    );
    let entry = write(
        &dir,
        "app.js",
        "import * as L from \"./lib.js\";\nvar a = L.answer;\n",
    );

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    assert!(
        out.code.contains("var L = __mods["),
        "namespace import should bind to the whole module: {}",
        out.code
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn bundles_default_import() {
    let dir = make_tempdir("default");
    write(
        &dir,
        "lib.js",
        "export default 42;\n",
    );
    let entry = write(
        &dir,
        "app.js",
        "import answer from \"./lib.js\";\n",
    );

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    assert!(
        out.code.contains("__exports.default = 42"),
        "default export must write `__exports.default`: {}",
        out.code
    );
    assert!(
        out.code.contains("var answer = __mods[")
            && out.code.contains("].default"),
        "default import should read .default: {}",
        out.code
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn bundles_reexports() {
    let dir = make_tempdir("reexport");
    write(&dir, "a.js", "export var x = 1;\nexport var y = 2;\n");
    write(&dir, "b.js", "export { x, y as z } from \"./a.js\";\n");
    let entry = write(
        &dir,
        "app.js",
        "import { x, z } from \"./b.js\";\n",
    );

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    assert!(out.code.contains("__exports.x = __mods["));
    assert!(out.code.contains("__exports.z = __mods["));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn bundles_side_effect_import() {
    let dir = make_tempdir("sideeffect");
    write(&dir, "init.js", "var x = 1;\n");
    let entry = write(&dir, "app.js", "import \"./init.js\";\nvar y = 2;\n");

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    // Side-effect import doesn't introduce bindings but the dep
    // still appears in the module table so its body runs.
    assert!(
        out.code.contains("__mods[") && out.code.contains("init.js\"]"),
        "side-effect import should still register the dep: {}",
        out.code
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rejects_import_cycle() {
    let dir = make_tempdir("cycle");
    write(&dir, "a.js", "import \"./b.js\";\nexport var x = 1;\n");
    write(&dir, "b.js", "import \"./a.js\";\nexport var y = 2;\n");
    let entry = write(&dir, "app.js", "import \"./a.js\";\n");

    let err = inty_bundle::bundle(&entry).expect_err("cycle should reject");
    let msg = format!("{}", err);
    assert!(
        msg.contains("cycle"),
        "diagnostic should mention 'cycle': {}",
        msg
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn quickjs_round_trip() {
    use rquickjs::{Context, Function, Runtime};

    let dir = make_tempdir("qjs");
    write(&dir, "lib.js", "export var answer = 42;\n");
    let entry = write(
        &dir,
        "app.js",
        // The bundle's wrapping IIFE captures any side effects;
        // here we set a global so the host can read it back.
        "import { answer } from \"./lib.js\";\nglobalThis.__test = answer;\n",
    );

    let out = inty_bundle::bundle(&entry).expect("bundle ok");
    let _ = std::fs::remove_dir_all(&dir);

    let runtime = Runtime::new().expect("rquickjs runtime");
    let ctx = Context::full(&runtime).expect("context");
    ctx.with(|ctx| {
        ctx.eval::<(), _>(out.code.as_bytes()).expect("eval bundle");
        let global = ctx.globals();
        let probe: Function = global
            .get::<_, Function>("eval")
            .expect("eval is available");
        let _ = probe;
        let answer: i32 = ctx
            .eval::<i32, _>(b"globalThis.__test".as_slice())
            .expect("read __test back");
        assert_eq!(answer, 42);
    });
}
