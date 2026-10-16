//! A binding with a type annotation has that type even where a function
//! reads it before its declaration has been checked.
//!
//! A call checks the function it calls, and everything that function
//! reaches, at that point: here `f`, from the callback `arm` registers,
//! before the `let` below the call. (`f` runs later, so this is no use
//! before initialisation.) `f` must read `cont` at its annotated type; a
//! fresh variable would be pinned by the first use (`o.f`, a record) and
//! then fail to meet `{f: Boolean} | Null`.
//!
//! Drives the real `inty` binary: the program goes through the same module
//! check a user's file does.

use std::process::Command;

fn check(name: &str, src: &str) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("inty_cli_fwd_{}_{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("main.js");
    std::fs::write(&file, src).expect("write fixture");
    let out = Command::new(env!("CARGO_BIN_EXE_inty"))
        .arg("--no-color")
        .arg(&file)
        .output()
        .expect("spawn inty");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

#[test]
fn annotated_binding_read_before_its_declaration_is_checked() {
    let (ok, text) = check(
        "top",
        "function arm() { setTimeout(() => f(), 0); }\n\
         arm();\n\
         /** let cont: {f: Boolean} | Null */\n\
         let cont = null;\n\
         function f() { const o = cont; if (o && o.f) return; }\n",
    );
    assert!(ok, "expected a clean check, got:\n{text}");
}

#[test]
fn annotated_binding_in_a_function_body_read_before_its_declaration() {
    let (ok, text) = check(
        "fn",
        "function outer() {\n\
         function arm() { setTimeout(() => f(), 0); }\n\
         arm();\n\
         /** let cont: {f: Boolean} | Null */\n\
         let cont = null;\n\
         function f() { const o = cont; if (o && o.f) return; }\n\
         }\n\
         outer();\n",
    );
    assert!(ok, "expected a clean check, got:\n{text}");
}

#[test]
fn annotated_declaration_without_initialiser_read_early() {
    let (ok, text) = check(
        "decl",
        "function arm() { setTimeout(() => f(), 0); }\n\
         arm();\n\
         /** const cont: {f: Boolean, g?: String} | Null */\n\
         const cont;\n\
         function f() { const o = cont; if (o && o.f) return; }\n",
    );
    assert!(ok, "expected a clean check, got:\n{text}");
}

#[test]
fn annotated_binding_still_checks_its_uses() {
    // The early-read type is the annotation itself: a use it forbids is an
    // error, wherever it is checked.
    let (ok, text) = check(
        "bad",
        "function arm() { setTimeout(() => f(), 0); }\n\
         arm();\n\
         /** let cont: {f: Boolean} | Null */\n\
         let cont = null;\n\
         function f() { const o = cont; if (o) return o.f + 1; return 0; }\n",
    );
    assert!(!ok, "expected an error, got a clean check:\n{text}");
}
