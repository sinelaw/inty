//! Tests for the Starlark dialect: rejections, static rules, lowerings and `load`.

use std::path::{Path, PathBuf};

use super::*;
use crate::infer::InferState;

/// Parse and infer a single Starlark program with the Starlark prelude
/// (Bazel's globals included), returning every error.
fn check(src: &str) -> Vec<String> {
    let program = match parse_source(src) {
        Ok(p) => p,
        Err(e) => return vec![format!("{e:?}")],
    };
    let mut state = InferState::new();
    let env = prelude::load(&mut state, crate::builtins::initial_env(), true).expect("prelude");
    let env = bind_loads_opaquely(&mut state, env, &program).expect("loads");
    if let Err(e) = state.infer_program_with_env(&env, &program) {
        return vec![format!("{e:?}")];
    }
    state.errors.iter().map(|e| format!("{e:?}")).collect()
}

fn accepts(src: &str) {
    let errs = check(src);
    assert!(errs.is_empty(), "rejected:\n{src}\n{errs:?}");
}

fn rejects(src: &str, needle: &str) {
    let errs = check(src);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "expected an error containing {needle:?} for:\n{src}\ngot {errs:?}"
    );
}

#[test]
fn python_constructs_outside_starlark_are_rejected() {
    let cases = [
        ("class C:\n    pass\n", "'class' is not part of Starlark"),
        (
            "def f():\n    while True:\n        pass\n",
            "'while' is not part of Starlark",
        ),
        (
            "def f():\n    try:\n        pass\n    except Exception:\n        pass\n",
            "'try' is not part of Starlark",
        ),
        (
            "def f():\n    raise ValueError(\"x\")\n",
            "'raise' is not part of Starlark",
        ),
        ("import os\n", "'import' is not part of Starlark"),
        ("from os import path\n", "'import' is not part of Starlark"),
        (
            "def f(x):\n    return x is None\n",
            "'is' is not part of Starlark",
        ),
        ("x = 2 ** 3\n", "'**' operator is not part of Starlark"),
        ("x = 1\ns = f\"{x}\"\n", "f-string is not part of Starlark"),
        (
            "def f():\n    global x\n",
            "'global' is not part of Starlark",
        ),
        (
            "@foo\ndef f():\n    pass\n",
            "decorator is not part of Starlark",
        ),
        (
            "def f():\n    with g() as h:\n        pass\n",
            "'with' is not part of Starlark",
        ),
        ("def f(x):\n    del x\n", "'del' is not part of Starlark"),
    ];
    for (src, needle) in cases {
        rejects(src, needle);
    }
}

#[test]
fn python_only_builtins_are_not_bound() {
    rejects("x = open(\"f\")\n", "open");
    rejects("x = input()\n", "input");
}

#[test]
fn top_level_if_and_for_are_rejected() {
    rejects(
        "if True:\n    x = 1\n",
        "'if' is not allowed at the top level",
    );
    rejects(
        "for x in [1]:\n    pass\n",
        "'for' is not allowed at the top level",
    );
    // Inside a function they are fine, as is a comprehension anywhere.
    accepts(
        "def f(xs):\n\
         \x20   t = 0\n\
         \x20   for x in xs:\n\
         \x20       if x > 0:\n\
         \x20           t += x\n\
         \x20   return t\n\
         ys = [x for x in [1, 2] if x > 1]\n",
    );
}

#[test]
fn globals_are_bound_once() {
    let needle = "a Starlark global is bound once";
    rejects("x = 1\nx = 2\n", needle);
    rejects("x = [1]\nx += [2]\n", needle);
    rejects("def f():\n    return 1\ndef f():\n    return 2\n", needle);
    rejects("x = 1\ndef x():\n    return 1\n", needle);
    rejects("load(\":a.bzl\", \"x\")\nx = 1\n", needle);
    // A function's locals may be reassigned.
    accepts("def f(x):\n    y = 1\n    y = 2\n    y += x\n    return y\n");
}

#[test]
fn recursion_is_rejected() {
    rejects(
        "def f(n):\n    return f(n - 1)\n",
        "recursion is not allowed in Starlark (f → f)",
    );
    rejects(
        "def a(n):\n    return b(n)\ndef b(n):\n    return a(n)\n",
        "recursion is not allowed in Starlark (a → b → a)",
    );
    // A call through a parameter that shadows a top-level `def` is not
    // a call of that `def`; and a function passed as a value isn't
    // followed.
    accepts("def f(g):\n    return g(1)\ndef g(x):\n    return f(g)\n");
}

#[test]
fn fail_is_a_throw() {
    // After `fail`, the `None` case is gone.
    accepts(
        "def f(x = None):\n\
         \x20   if x == None:\n\
         \x20       fail(\"need x\")\n\
         \x20   return x + 1\n",
    );
    match &parse_source("fail(\"no\")\n").unwrap().statements[0] {
        Stmt::Throw { .. } => {}
        other => panic!("expected a throw, got {other:?}"),
    }
    // In an expression, `fail(…)` can stand for any value.
    accepts("def f(c):\n    return 1 if c else fail(\"no\")\n");
    // A `fail` the file binds itself is an ordinary call.
    match &parse_source("def fail(m):\n    return m\nfail(\"no\")\n")
        .unwrap()
        .statements[1]
    {
        Stmt::Expr { .. } => {}
        other => panic!("expected a call, got {other:?}"),
    }
}

#[test]
fn struct_is_a_record() {
    accepts("s = struct(name = \"a\", n = 1)\nt = s.name + \"!\"\nu = s.n + 1\n");
    rejects("s = struct(name = \"a\")\nt = s.nme\n", "nme");
    rejects("s = struct(n = 1)\nt = s.n + \"a\"\n", "UnificationError");
}

#[test]
fn starlark_reuses_python_lowerings() {
    accepts(
        "def obj_files(srcs):\n\
         \x20   return [s[:-2] + \".o\" for s in srcs if s[-2:] == \".c\"]\n\
         def f(a, *, b = 1):\n\
         \x20   return a + b\n\
         names = []  # type: list[str]\n\
         def g():\n\
         \x20   names.append(obj_files([\"a.c\"])[0])\n\
         \x20   return f(1, b = 2)\n",
    );
    rejects(
        "names = []  # type: list[str]\ndef g():\n    names.append(1)\n",
        "UnificationError",
    );
}

#[test]
fn load_statement_lowers_to_an_import() {
    let program = parse_source("load(\"//lib:a.bzl\", \"x\", y = \"z\",)\n").unwrap();
    match &program.statements[0] {
        Stmt::Import {
            specifiers, source, ..
        } => {
            assert_eq!(source, "//lib:a.bzl");
            let names: Vec<(&str, &str)> = specifiers
                .iter()
                .map(|s| match s {
                    ImportSpecifier::Named {
                        imported, local, ..
                    } => (imported.as_str(), local.as_str()),
                    other => panic!("unexpected specifier {other:?}"),
                })
                .collect();
            assert_eq!(names, [("x", "x"), ("z", "y")]);
        }
        other => panic!("expected an import, got {other:?}"),
    }
    rejects("load(\":a.bzl\", \"_p\")\n", "private");
    rejects(
        "def f():\n    load(\":a.bzl\", \"p\")\n",
        "only allowed at the top level",
    );
    assert!(parse_source("load(\":a.bzl\")\n").is_err());
}

/// A fresh, empty directory under the system temp dir.
fn temp_dir(tag: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!(
        "inty-starlark-{tag}-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir.canonicalize().unwrap()
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// Check the file at `path` as the CLI does: prelude, resolved loads, then
/// inference. Returns every error.
fn check_file(path: &Path) -> Vec<String> {
    let text = std::fs::read_to_string(path).unwrap();
    let program = match parse_source(&text) {
        Ok(p) => p,
        Err(e) => return vec![format!("{e:?}")],
    };
    let mut state = InferState::new();
    let base = prelude::load(
        &mut state,
        crate::builtins::initial_env(),
        is_bazel_file(path),
    )
    .unwrap();
    let mut loader = Loader::new();
    let env = match resolve_loads(&mut state, &base, base.clone(), &program, path, &mut loader) {
        Ok(env) => env,
        Err(e) => return vec![format!("{e:?}")],
    };
    if let Err(e) = state.infer_program_with_env(&env, &program) {
        return vec![format!("{e:?}")];
    }
    state.errors.iter().map(|e| format!("{e:?}")).collect()
}

#[test]
fn labels_resolve_against_workspace_and_package() {
    let root = temp_dir("labels");
    write(&root.join("MODULE.bazel"), "");
    write(&root.join("lib/BUILD"), "");
    let from = root.join("lib/sub/x.bzl");
    write(&from, "");
    let file = |p: &str| Some(LoadTarget::File(root.join(p)));
    assert_eq!(resolve_label("//lib:a.bzl", &from), file("lib/a.bzl"));
    assert_eq!(resolve_label("@//lib:a.bzl", &from), file("lib/a.bzl"));
    assert_eq!(resolve_label("//lib/a.bzl", &from), file("lib/a.bzl/a.bzl"));
    // A relative label is in the file's package (`lib`, the nearest
    // directory up with a BUILD file), not its directory.
    assert_eq!(resolve_label(":a.bzl", &from), file("lib/a.bzl"));
    assert_eq!(resolve_label("sub/x.bzl", &from), file("lib/sub/x.bzl"));
    assert_eq!(
        resolve_label("@rules_cc//cc:defs.bzl", &from),
        Some(LoadTarget::External)
    );
    assert_eq!(
        resolve_label("@@rules_cc//cc:defs.bzl", &from),
        Some(LoadTarget::External)
    );
    // Without a workspace root, `//` labels can't be resolved.
    let bare = temp_dir("noroot");
    assert_eq!(resolve_label("//lib:a.bzl", &bare.join("x.star")), None);
    let _ = std::fs::remove_dir_all(&root);
    let _ = std::fs::remove_dir_all(&bare);
}

#[test]
fn loads_bring_in_typed_names() {
    let root = temp_dir("loads");
    write(&root.join("MODULE.bazel"), "");
    write(&root.join("lib/BUILD"), "");
    write(
        &root.join("lib/strings.bzl"),
        "_SEP = \"_\"\n\
         def join_name(parts):\n\
         \x20   return _SEP.join([p.lower() for p in parts if p != \"\"])\n\
         INFO = struct(version = 2, label = \"lib\")\n",
    );
    write(
        &root.join("lib/paths.bzl"),
        "load(\":strings.bzl\", \"join_name\")\n\
         def obj_name(src):\n\
         \x20   return join_name([src[:-2], \"o\"])\n",
    );
    let app = root.join("app/defs.bzl");
    write(
        &app,
        "load(\"//lib:strings.bzl\", \"join_name\", my_info = \"INFO\")\n\
         load(\"//lib:paths.bzl\", \"obj_name\")\n\
         load(\"@bazel_skylib//lib:paths.bzl\", \"paths\")\n\
         def _impl(ctx):\n\
         \x20   return [DefaultInfo(files = depset([obj_name(\"a.c\")]))]\n\
         my_rule = rule(implementation = _impl, attrs = {\"srcs\": attr.label_list()})\n\
         def app_name(prefix):\n\
         \x20   v = my_info.version + 1\n\
         \x20   return join_name([prefix, paths.basename(\"x\"), str(v)])\n",
    );
    let errs = check_file(&app);
    assert!(errs.is_empty(), "{errs:?}");

    // A loaded name keeps its type.
    let bad = root.join("app/bad.bzl");
    write(
        &bad,
        "load(\"//lib:strings.bzl\", my_info = \"INFO\")\n\
         def bad():\n\
         \x20   return my_info.version + \"x\"\n",
    );
    let errs = check_file(&bad);
    assert!(
        errs.iter().any(|e| e.contains("UnificationError")),
        "{errs:?}"
    );

    // A private or missing symbol, or a missing file, is an error.
    let missing = root.join("app/missing.bzl");
    write(&missing, "load(\"//lib:strings.bzl\", \"nope\")\n");
    let errs = check_file(&missing);
    assert!(errs.iter().any(|e| e.contains("no symbol")), "{errs:?}");
    write(&missing, "load(\"//lib:nope.bzl\", \"x\")\n");
    let errs = check_file(&missing);
    assert!(errs.iter().any(|e| e.contains("no file")), "{errs:?}");

    // A load cycle is reported, not followed forever.
    write(&root.join("c/a.star"), "load(\":b.star\", \"b\")\na = 1\n");
    write(&root.join("c/b.star"), "load(\":a.star\", \"a\")\nb = 1\n");
    let errs = check_file(&root.join("c/a.star"));
    assert!(errs.iter().any(|e| e.contains("load cycle")), "{errs:?}");

    // Bazel's globals are only in a `.bzl` file's prelude.
    let star = root.join("plain.star");
    write(&star, "r = rule()\n");
    let errs = check_file(&star);
    assert!(errs.iter().any(|e| e.contains("rule")), "{errs:?}");

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn strings_are_not_iterable() {
    rejects(
        "def f(s):\n    for c in s:\n        print(c)\nf(\"abc\")\n",
        "a Starlark string isn't iterable",
    );
    rejects(
        "def f():\n    return [c for c in \"abc\"]\n",
        "a Starlark string isn't iterable",
    );
    accepts("def f(s):\n    return [c.upper() for c in s.elems()]\nr = f(\"ab\")\n");
    // `in` on a string is a substring test, not iteration.
    accepts("b = \"a\" in \"abc\"\n");
}

#[test]
fn methods_are_starlarks_not_pythons() {
    // Python-only `str`, `list` and `dict` methods don't exist here.
    rejects("x = \"1\".zfill(3)\n", "zfill");
    rejects("x = \"a\".casefold()\n", "casefold");
    rejects(
        "def f():\n    xs = [2, 1]\n    xs.sort()\n    return xs\n",
        "sort",
    );
    rejects(
        "def f(d):\n    # type: (dict[str, int]) -> int\n    c = d.copy()\n    return 0\n",
        "copy",
    );
    // Starlark's own, and the shared ones, do.
    accepts(
        "def f(d, xs):\n\
         \x20   # type: (dict[str, int], list[str]) -> int\n\
         \x20   a, sep, b = \"k=v\".partition(\"=\")\n\
         \x20   xs.append(a.removeprefix(\"k\") + b)\n\
         \x20   t = 0\n\
         \x20   for k, v in d.items():\n\
         \x20       t += v + d.get(k, 0)\n\
         \x20   for k in d:\n\
         \x20       t += len(k)\n\
         \x20   return t + xs.index(\"x\")\n",
    );
}

#[test]
fn starlark_programs_carry_their_language() {
    assert_eq!(
        parse_source("x = 1\n").unwrap().language,
        crate::ast::SourceLanguage::Starlark
    );
    assert_eq!(
        crate::frontends::python::parse_source("x = 1\n")
            .unwrap()
            .language,
        crate::ast::SourceLanguage::Python
    );
}
