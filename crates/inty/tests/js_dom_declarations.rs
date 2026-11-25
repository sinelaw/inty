//! DOM declarations: the node tree, ranges and selections, caret hit
//! testing, computed and inline styles.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src`; return Ok(()) if it checks, or the formatted error.
fn check(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    let errs = state.take_errors();
    if errs.is_empty() {
        Ok(())
    } else {
        Err(format!("{:?}", errs))
    }
}

fn ok(src: &str) {
    let r = check(src);
    assert!(r.is_ok(), "should check: {:?}\n{}", r, src);
}

#[test]
fn node_tree() {
    ok("const box = document.createElement(\"div\");\n\
        box.replaceChildren(...[document.createTextNode(\"a\"), document.createElement(\"span\")]);\n\
        const first = box.firstChild;\n\
        const isText = first !== null && first.nodeType === 3;\n\
        const n = box.childNodes.length + (box.isConnected ? 1 : 0);\n\
        const next = first ? first.nextSibling : null;\n");
}

#[test]
fn ranges_and_caret_hit_testing() {
    ok("const box = document.createElement(\"div\");\n\
        const r = document.createRange();\n\
        const first = box.firstChild;\n\
        if (first) { r.setStart(first, 0); r.collapse(true); }\n\
        const rects = r.getClientRects();\n\
        const w = rects.length ? rects[0].width : r.getBoundingClientRect().width;\n\
        const pos = document.caretPositionFromPoint(10, 20);\n\
        const off = pos ? pos.offset : 0;\n\
        const hit = document.caretRangeFromPoint(10, 20);\n\
        const node = hit ? hit.startContainer : null;\n\
        const sel = document.getSelection();\n\
        if (sel) { sel.removeAllRanges(); sel.addRange(r); }\n");
}

#[test]
fn styles() {
    ok("const box = document.createElement(\"div\");\n\
        box.style.display = \"none\";\n\
        box.style.left = `${4}px`;\n\
        const cs = getComputedStyle(box);\n\
        const size = parseFloat(cs.fontSize) + parseFloat(cs.lineHeight);\n\
        const family = cs.fontFamily + window.getComputedStyle(box).getPropertyValue(\"--x\");\n");
}

#[test]
fn document_state() {
    ok(
        "const away = document.hidden || document.visibilityState === \"hidden\";\n\
        document.fonts.ready.then(() => { const el = document.elementFromPoint(1, 2); });\n",
    );
}

/// `addEventListener`'s options: an object with any of `capture`,
/// `once`, `passive`, or a Boolean, and none, on the same element.
#[test]
fn add_event_listener_options() {
    let src = "const el = document.createElement(\"div\");\n\
               el.addEventListener(\"wheel\", (e) => {}, { passive: false });\n\
               el.addEventListener(\"x\", (e) => {}, true);\n\
               el.addEventListener(\"z\", (e) => {});\n\
               el.addEventListener(\"y\", (e) => {}, { once: true, capture: false });\n\
               window.addEventListener(\"resize\", (e) => {}, { passive: true });\n";
    let r = check(src);
    assert!(r.is_ok(), "{:?}", r);
    let typo = "const el = document.createElement(\"div\");\n\
                el.addEventListener(\"wheel\", (e) => {}, { pasive: false });\n";
    assert!(check(typo).is_err(), "an unknown option is rejected");
}

/// Host methods that throw when called detached say their `this`; a
/// computed style is read-only; `replaceChildren()` clears (review of
/// #114).
#[test]
fn ranges_selections_and_styles_keep_their_receiver() {
    let ok = "const r = document.createRange(); r.setStart(document.body, 0); r.collapse(true);\n\
              const s = document.getSelection();\n\
              if (s) { s.removeAllRanges(); s.addRange(r); s.getRangeAt(0).cloneRange().toString(); }\n\
              const el = document.createElement(\"div\"); el.style.setProperty(\"color\", \"red\");\n\
              const d = getComputedStyle(el).display; el.replaceChildren();\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    for bad in [
        "const r = document.createRange(); const f = r.setStart; f(document.body, 0);\n",
        "const sp = document.createElement(\"div\").style.setProperty; sp(\"a\", \"b\");\n",
        "getComputedStyle(document.createElement(\"div\")).display = \"none\";\n",
    ] {
        assert!(check(bad).is_err(), "{bad}");
    }
}
