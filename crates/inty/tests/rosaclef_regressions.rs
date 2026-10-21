//! Regression tests for the bugs found while type-checking Rosaclef, a
//! ~6k-line vanilla-JS DAW frontend built on inty (see
//! `docs/patterns.md`). Each test is the minimal repro from the bug
//! report; the numbers refer to that report.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src` against the stdlib; `Err` carries every diagnostic.
fn check(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {}", e))?;
    let (env, mut state) = initial_env_with_stdlib().map_err(|e| format!("stdlib: {}", e))?;
    let result = state.infer_program_with_env(&env, &program);
    let errors = state.take_errors();
    if !errors.is_empty() {
        let msgs: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
        return Err(msgs.join("\n"));
    }
    result.map_err(|e| e.to_string())?;
    state.resolve_constraints().map_err(|e| e.to_string())
}

#[track_caller]
fn ok(src: &str) {
    if let Err(e) = check(src) {
        panic!(
            "expected to type-check, got:\n{}\n--- source ---\n{}",
            e, src
        );
    }
}

#[track_caller]
fn err(src: &str) -> String {
    match check(src) {
        Ok(()) => panic!("expected a type error\n--- source ---\n{}", src),
        Err(e) => e,
    }
}

// `new Date()` with no argument: the stdlib declared a required
// milliseconds argument, so every module using it failed.
#[test]
fn new_date_without_argument() {
    ok("const at = new Date().toISOString();");
    ok("const d = new Date(0); const t = d.getTime();");
}

// 1. A comparison of property reads on a module-level binding, inside a
// function declaration.
#[test]
fn b1_compare_outer_property_reads() {
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function fix() { if (state.insert >= state.xs.length) state.insert = 0; }
        fix();
    ");
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function fix() { if (state.insert === state.xs.length) state.insert = 0; }
        fix();
    ");
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function f() { return state.insert + state.xs.length; }
        function g() { return state.insert < state.xs.length && state.xs.length <= state.insert; }
    ");
}

// 1. The function reads a binding declared after it.
#[test]
fn b1_function_before_declaration() {
    ok("
        function fix() { if (state.insert >= state.xs.length) state.insert = 0; }
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        fix();
    ");
}

// 2. Narrowing a local whose type comes from a module-level binding.
#[test]
fn b2_narrowing_outer_find() {
    ok(r#"
        /** const XS: { name: String, v: String }[] */
        const XS = [{ name: "a", v: "x" }];
        /** function g(n: String) => String */
        function g(n) { const found = XS.find((i) => i.name === n); return found ? found.v : ""; }
    "#);
    ok(r#"
        /** const XS: String[][] */
        const XS = [["a", "x"]];
        /** function g(n: String) => String */
        function g(n) { const found = XS.find((i) => i[0] === n); return found !== undefined ? found[1] : ""; }
    "#);
}

#[test]
fn b2_narrowing_forms_on_outer_bindings() {
    let decls = r#"
        /** const XS: { name: String, v: String }[] */
        const XS = [{ name: "a", v: "x" }];
    "#;
    for body in [
        r#"const f = XS.find((i) => i.name === n); if (f === undefined) return ""; return f.v;"#,
        r#"const f = XS.find((i) => i.name === n); if (!f) return ""; return f.v;"#,
        r#"const f = XS.find((i) => i.name === n); if (f != null) return f.v; return "";"#,
        r#"const f = XS.find((i) => i.name === n); return f !== undefined ? f.v : "";"#,
    ] {
        ok(&format!(
            "{decls}\n/** function g(n: String) => String */\nfunction g(n) {{ {body} }}"
        ));
    }
}

/// Like [`check`], with `lib` loaded first as a `--lib` declaration file.
fn check_with_lib(lib: &str, src: &str) -> Result<(), String> {
    let (env, mut state) = initial_env_with_stdlib().map_err(|e| format!("stdlib: {}", e))?;
    let env = inty::stdlib::load_lib(&mut state, env, lib).map_err(|e| format!("lib: {}", e))?;
    let program = parse(src).map_err(|e| format!("parse error: {}", e))?;
    let result = state.infer_program_with_env(&env, &program);
    let errors = state.take_errors();
    if !errors.is_empty() {
        let msgs: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
        return Err(msgs.join("\n"));
    }
    result.map_err(|e| e.to_string())?;
    state.resolve_constraints().map_err(|e| e.to_string())
}

// 3. An alias may refer to one declared after it.
#[test]
fn b3_alias_forward_reference() {
    ok("
        /** type R = { a: Number, xs: R2[] } */
        /** type R2 = { b: Number } */
        /** function f() => R */
        function f() { return { a: 1, xs: [{ b: 0 }] }; }
    ");
    ok("
        /** type Pair<T> = { l: Side<T>, r: Side<T> } */
        /** type Side<T> = { v: T } */
        /** const p: Pair<String> */
        const p = { l: { v: \"a\" }, r: { v: \"b\" } };
    ");
    err("
        /** type R = { xs: R2[] } */
        /** type R2 = { b: Number } */
        /** const r: R */
        const r = { xs: [{ b: \"no\" }] };
    ");
}

// 3. Recursive aliases are equi-recursive types; one that is defined as
// itself is an error that says so.
#[test]
fn b3_recursive_aliases() {
    ok("
        /** type Tree = { label: String, kids: Tree[] } */
        /** function size(t: Tree) => Number */
        function size(t) { let n = 1; for (const k of t.kids) n = n + size(k); return n; }
        const s = size({ label: \"a\", kids: [{ label: \"b\", kids: [] }] });
    ");
    ok("
        /** type A = { b: B | Null } */
        /** type B = { a: A } */
        /** const x: A */
        const x = { b: null };
        /** const y: A */
        const y = { b: { a: { b: null } } };
    ");
    ok("
        /** type List<T> = { head: T, tail: List<T> | Null } */
        /** const l: List<Number> */
        const l = { head: 1, tail: { head: 2, tail: null } };
    ");
    err("
        /** type Tree = { label: String, kids: Tree[] } */
        /** const t: Tree */
        const t = { label: \"a\", kids: [{ label: 1, kids: [] }] };
    ");
    let e = err("/** type Bad = Bad */ const x = 1;");
    assert!(e.contains("'Bad' is defined as itself"), "{e}");
}

// 4. A class in a --lib file is a type for the aliases of the same file.
#[test]
fn b4_lib_class_visible_to_aliases() {
    let lib = "
        class InsertIx {}
        /** type Channel = { name: String, mixer: InsertIx } */
    ";
    check_with_lib(
        lib,
        "/** const c: Channel */ const c = { name: \"a\", mixer: new InsertIx() };",
    )
    .unwrap();
    // Still nominal: a different class is rejected.
    let e = check_with_lib(
        &format!("{lib}\nclass TrackIx {{}}"),
        "/** const c: Channel */ const c = { name: \"a\", mixer: new TrackIx() };",
    );
    assert!(e.is_err());
    // In an ordinary module too, whichever comes first.
    ok("
        /** type Channel = { mixer: InsertIx } */
        class InsertIx {}
        /** const c: Channel */
        const c = { mixer: new InsertIx() };
    ");
}

// 5. A length flows into a `Number` field of a returned
// record: the annotation is pushed into the function literal.
#[test]
fn b5_int_into_number_positions() {
    ok("
        /** type S = { elements: Number } */
        /** const f: () => S */
        const f = () => ({ elements: [1, 2].length });
    ");
    ok("
        /** type S = { elements: Number, xs: Number[] } */
        /** function f(x: Number) => S */
        function f(x) { return { elements: Math.round(x), xs: [Math.round(x), 0.5] }; }
    ");
    ok("
        /** const p: Promise<{ n: Number }> */
        const p = Promise.resolve({ n: 1 });
        /** const g: (Number) => { n: Number } */
        const g = (i) => ({ n: i });
    ");
    // The fresh object's slot is a Number: it may later hold a fraction.
    ok("
        /** type S = { n: Number } */
        /** const f: () => S */
        const f = () => ({ n: [1].length });
        const s = f();
        s.n = 0.5;
    ");
    // An existing record of a length is a record of a number: there is
    // one number type.
    ok("
        const r = { n: [1].length };
        /** const s: { n: Number } */
        const s = r;
    ");
}

// 5. A mutable field initialised with an integer literal holds fractions.
#[test]
fn b5_literal_initialised_field() {
    ok("const s = { volume: 1 }; s.volume = 0.5;");
    ok("const state = { volume: 1 }; function set() { state.volume = 0.25; } set();");
}

// 6. A callback may take fewer parameters than it is passed.
#[test]
fn b6_fewer_callback_parameters() {
    ok("const ys = [1, 2].map(() => \"a\");");
    ok("
        /** function each(f: (Number, String) => Undefined) => Undefined */
        function each(f) { f(1, \"a\"); return undefined; }
        each(() => undefined);
        each((i) => undefined);
    ");
    // Not more than it is passed.
    err("
        /** function each(f: (Number) => Undefined) => Undefined */
        function each(f) { f(1); return undefined; }
        each((i, j) => undefined);
    ");
}

// 7. Iteration callbacks are passed the index (and the array).
#[test]
fn b7_index_callbacks() {
    ok(r#"
        const xs = ["a", "b"];
        const a = xs.map((x, i) => x + String(i));
        const b = xs.filter((x, i) => i > 0);
        xs.forEach((x, i) => { console.log(i); });
        const c = xs.some((x, i) => i > 0);
        const d = xs.every((x, i, all) => i < all.length);
        const e = xs.findIndex((x, i) => i > 0);
        const f = xs.find((x, i) => i > 0);
        const g = xs.reduce((acc, x, i) => acc + i, 0);
    "#);
    // A function taking only the element still fits.
    ok(r#"
        /** function up(s: String) => String */
        function up(s) { return s.toUpperCase(); }
        const k = ["a"].map(up);
        const n = ["1"].map(Number);
    "#);
    // The index is a number.
    err(r#"const xs = ["a"].map((x, i) => i.length);"#);
    ok("const s = [3, 1, 2].sort((a, b) => a - b); const t = [0.5].sort();");
}

// 8. `&&` / `||` with known operand types give what can come out.
#[test]
fn b8_logical_operators() {
    ok(r#"
        /** const maybe: Undefined | { v: Number } */
        const maybe = undefined;
        const cond = true;
        const r = cond && maybe ? 1 : 2;
        const w = maybe && maybe.v;
    "#);
    ok(r#"
        /** function greet(name: String) => String */
        function greet(name) { return name || "Guest"; }
    "#);
    ok(r#"
        /** const XS: { name: String, v: String }[] */
        const XS = [{ name: "a", v: "x" }];
        /** function g(n: String) => String */
        function g(n) { const f = XS.find((i) => i.name === n); return (f && f.v) || ""; }
    "#);
    // What comes out is still checked.
    err(r#"
        /** const maybe: Undefined | { v: Number } */
        const maybe = undefined;
        /** const n: Number */
        const n = maybe && maybe.v;
    "#);
}

// 9. `then` / `catch` callbacks may return a value or a promise.
#[test]
fn b9_promise_callbacks_return_values() {
    ok(r#"
        /** const p: Promise<Boolean> */
        const p = Promise.resolve(true);
        /** const q: Promise<Boolean> */
        const q = p.catch((e) => false);
        /** const r: Promise<Number> */
        const r = p.then((x) => Promise.resolve(x ? 1 : 2));
        /** const s: Promise<String> */
        const s = p.then((x) => x ? "a" : "b").then((y) => y + "!");
        const t = p.catch((e) => Promise.resolve(false));
    "#);
    ok(r#"
        function after(p) { return p.then((x) => x + 1); }
        /** const q: Promise<Number> */
        const q = after(Promise.resolve(1));
    "#);
    err(r#"
        /** const p: Promise<Boolean> */
        const p = Promise.resolve(true);
        const q = p.catch((e) => "no");
    "#);
}

// 10. Tuples: `[A, B]` annotations; an unannotated heterogeneous array
// says how to write one.
#[test]
fn b10_tuples() {
    ok(r#"
        /** const pairs: [String, Number][] */
        const pairs = [["l", 0.5], ["r", 0.25]];
        const name = pairs[0][0].toUpperCase();
        const gain = pairs[0][1] * 2;
        const [a, b] = pairs[1];
        const c = a + "!";
        const d = b / 2;
        /** function mk(s: String) => [String, Number] */
        function mk(s) { return [s, s.length]; }
    "#);
    err(r#"/** const p: [String, Number] */ const p = [1, "a"];"#);
    let e = err(r#"const pairs = [["l", 0.5], ["r", 0.25]];"#);
    assert!(e.contains("Array elements have different types"), "{e}");
}

// 12. A concise arrow passed where the result is `Undefined` runs for its
// effect.
#[test]
fn b12_undefined_callbacks() {
    ok(r#"
        /** function hint(s: String) => Undefined */
        function hint(s) { return undefined; }
        /** function on(f: (Number) => Undefined) => Undefined */
        function on(f) { return undefined; }
        on((e) => hint("x"));
        on((e) => { hint("x"); });
        on((e) => { if (e > 1) return; hint("y"); });
        const arr = [1];
        on((e) => arr.push(e));
    "#);
    // A block body still returns what it says.
    err(r#"
        /** function on(f: (Number) => Undefined) => Undefined */
        function on(f) { return undefined; }
        on((e) => { return 5; });
    "#);
}

// 21. `class … extends Base` is rejected: inty has no inheritance. A
// base method is checked with the base's instance as `this`, whose type
// says which fields it lacks, so running it on a subclass instance isn't
// safe (here `{label: 5, ...this}.label` would be the subclass's string).
#[test]
fn b21_class_extends_rejected() {
    let e = err("
        class Base { constructor() { this.n = 1; } m() { return {label: 5, ...this}.label - 1; } }
        class Sub extends Base { constructor() { super(); this.label = \"x\"; } }
        const r = new Sub().m();
    ");
    assert!(e.contains("class inheritance is not supported"), "{e}");
}

// 19/20. Typed DOM events and the web platform declarations a real app
// uses (canvas, WebSocket, ResizeObserver, fetch, Blob URLs, media
// devices, Web Audio, storage, animation frames).
#[test]
fn b19_b20_web_platform() {
    ok(r##"const el = document.createElement("canvas");
el.addEventListener("pointerdown", (e) => { el.setPointerCapture(e.pointerId); console.log(e.clientX + 1); });
el.addEventListener("keydown", (e) => { if (e.key === "Enter" && e.shiftKey) e.preventDefault(); });
el.addEventListener("wheel", (e) => { console.log(e.deltaY); });
el.addEventListener("drop", (e) => { const dt = e.dataTransfer; if (dt) console.log(dt.files.length); });
window.addEventListener("resize", (e) => { console.log(window.innerWidth * window.devicePixelRatio); });
document.addEventListener("keyup", (e) => console.log(e.code));
const n = window.prompt("name?", "x");
const g = el.getContext("2d");
if (g === null) throw new Error("no 2d context");
g.fillStyle = "#fff";
g.fillRect(0, 0, el.width, el.height);
const w = g.measureText("hi").width;
const grad = g.createLinearGradient(0, 0, 1, 1);
grad.addColorStop(0, "red");
g.fillStyle = grad;
const ws = new WebSocket("ws://x");
ws.binaryType = "arraybuffer";
ws.onmessage = (m) => { const d = m.data; if (typeof d === "string") console.log(d.length); };
ws.send("hello");
const ro = new ResizeObserver((entries) => { for (const en of entries) console.log(en.contentRect.width); });
ro.observe(el);
const id = requestAnimationFrame((t) => { console.log(t); });
const t0 = performance.now();
const v = localStorage.getItem("k") ?? "";
fetch("/api", { method: "POST", headers: { "Content-Type": "application/json" }, body: "{}" })
  .then((r) => r.ok ? r.arrayBuffer() : Promise.resolve(new ArrayBuffer(0)))
  .then((b) => console.log(b.byteLength));
const url = URL.createObjectURL(new Blob(["x"], { type: "text/plain" }));
navigator.mediaDevices.getUserMedia({ audio: true }).then((s) => { s.getTracks().forEach((tr) => tr.stop()); });
const ctx = new AudioContext();
const gain = ctx.createGain();
gain.gain.value = 0.5;
gain.connect(ctx.destination);
const node = new AudioWorkletNode(ctx, "proc", { numberOfOutputs: 1 });
node.port.postMessage({ t: "note", key: 60 });
node.port.onmessage = (m) => { console.log(m.data.key); };
node.connect(ctx.destination);
ctx.decodeAudioData(new ArrayBuffer(4)).then((buf) => console.log(buf.getChannelData(0).length));
"##);
    // An event is one shape: the fields the listener reads are checked.
    err(r##"document.addEventListener("keydown", (e) => { const n = e.key * 2; });"##);
    // A missing storage key reads as null.
    err(r##"const v = localStorage.getItem("k"); const n = v.length;"##);
}

// 20. Core additions: console with several values, typed arrays
// (Float32Array, subarray/set), ArrayBuffer, Map/Set types, String
// match/matchAll, Array.from with a map function, structuredClone.
#[test]
fn b20_core_additions() {
    ok(r##"console.log("a", 1, [2]);
const buf = new ArrayBuffer(16);
const f = new Float32Array(4);
f[0] = 0.5;
const u = new Uint8Array(8);
u.set(u.subarray(0, 2), 4);
const n = f.length + u.byteLength;
/** const m: Map<String, Number> */
const m = new Map();
m.set("a", 1);
/** const st: Set<String> */
const st = new Set();
const r = "a1b2".match(/\d/g);
const k = r ? r.length : 0;
const all = "a1".matchAll(/\d/g);
const xs = Array.from([1, 2], (x, i) => x * i);
const c = structuredClone({ a: 1 });
"##);
    err(r##"const r = "a1".match(/\d/); const n = r.length;"##);
}

// 20. The AudioWorklet global scope. A processor class would `extends
// AudioWorkletProcessor`, which only an external class's declaration
// may: a class with a body can't extend another.
#[test]
fn b20_audio_worklet() {
    let e = check_with_lib(
        inty::stdlib::AUDIO_WORKLET,
        r##"class Gain extends AudioWorkletProcessor {
  process(inputs, outputs, parameters) { return true; }
}
registerProcessor("gain", Gain);
"##,
    )
    .unwrap_err();
    assert!(e.contains("class inheritance is not supported"), "{e}");
    check_with_lib(
        inty::stdlib::AUDIO_WORKLET,
        r##"/** class Gain extends AudioWorkletProcessor { gain: Number } */
class Gain;
const g = new Gain();
g.port.postMessage({ t: "second", at: currentTime });
const half = g.gain / 2;
registerProcessor("gain", Gain);
"##,
    )
    .unwrap();
}

// 22. `Dict<V>` / `{ [String]: V }`: plain objects used as maps.
#[test]
fn b22_dict() {
    ok(r##"/** const params: Dict<Number> */
const params = { cutoff: 1200, resonance: 0.3 };
const c = params.cutoff ?? 0;
const r = params["resonance"];
params["gain"] = 1;
let total = 0;
for (const [k, v] of Object.entries(params)) total = total + v;
const names = Object.keys(params);
/** type Device = { name: String, params: { [String]: Number } } */
/** const d: Device */
const d = { name: "filter", params: { cutoff: 100 } };
/** function decode(text: String) => Dict<Number> */
function decode(text) { return JSON.parse(text); }
const back = Object.fromEntries(Object.entries(params));
"##);
    err(r##"/** const bad: Dict<Number> */ const bad = { a: "x" };"##);
    // A read may miss.
    err(r##"/** const d: Dict<Number> */ const d = { a: 1 }; const n = d.b + 1;"##);
    ok(r##"/** const d: Dict<Number> */ const d = { a: 1 }; const n = (d.b ?? 0) + 1;"##);
}

// "Gaps found moving to inty cb4bfca" (Rosaclef's docs/inty-notes.md),
// lettered as there. A (checking time) is `tests/checking_time.rs`.

// B. A record field holds a callback (a function that uses no `this`):
// stored, read back, called and passed on. A function that reads `this`
// can't be stored there.
#[test]
fn gap_b_a_record_field_holds_a_callback() {
    ok("
        /** const s: { stop: () => Undefined } */
        const s = { stop: () => undefined };
        /** function set(stop: () => Undefined) => Undefined */
        function set(stop) { s.stop = stop; }
        const end = s.stop;
        end();
        /** function call(f: () => Undefined) => Undefined */
        function call(f) { f(); }
        call(s.stop);
    ");
    err("
        /** const s: { x: Number, stop: () => Number } */
        const s = { x: 1, stop: () => 1 };
        s.stop = function () { return this.x; };
    ");
}

// C. Calling a method detached says it is about `this`.
#[test]
fn gap_c_a_detached_method_call_says_this() {
    let e = err("
        const s = { x: 1, stop() { return this.x; } };
        const end = s.stop;
        end();
    ");
    assert!(e.contains("`this`"), "{e}");
}

// D (not changed): `{}` is a closed empty record, so a field read of
// `(x ?? {})` is rejected; telling the absent case apart first works.
#[test]
fn gap_d_a_field_of_an_empty_default() {
    let e = err("
        function f(raw) { return ((raw.c ?? {}).off ?? []).map((x) => String(x)); }
    ");
    assert!(e.contains("'off' not found"), "{e}");
    ok("
        /** type Opts = {off: Number[]?} */
        /** function decode(c: Opts?) => String[] */
        function decode(c) {
          if (!c) return [];
          return (c.off ?? []).map((x) => String(x));
        }
        /** function f(raw: {c: Opts?}) => String[] */
        function f(raw) { return decode(raw.c); }
    ");
}

// E. `arr.length = 0` clears an array.
#[test]
fn gap_e_array_length_store() {
    ok("
        /** const xs: String[] */
        const xs = [];
        xs.length = 0;
    ");
    err("const xs = [1]; xs.length = \"0\";");
}

// F. `c ? x : undefined` (or `null`) is `T | Undefined` (`T | Null`).
#[test]
fn gap_f_conditional_with_nothing() {
    ok("
        /** const xs: Number[] */
        const xs = [];
        const last = xs.length > 0 ? xs[xs.length - 1] : undefined;
        const first = xs.length > 0 ? xs[0] : null;
        /** const n: Number */
        const n = (last ?? 0) + (first ?? 0);
    ");
    err("
        /** const xs: Number[] */
        const xs = [];
        const last = xs.length > 0 ? xs[xs.length - 1] : undefined;
        const n = last + 1;
    ");
}

// G. `Array.prototype.at`.
#[test]
fn gap_g_array_at() {
    ok("
        /** const xs: Number[] */
        const xs = [1, 2];
        /** const n: Number */
        const n = xs.at(-1) ?? 0;
    ");
    err("const xs = [1, 2]; const n = xs.at(-1) + 1;");
}

// Lookups that may find nothing say so, as `find` and `at` do: `Map` and
// `WeakMap` `get` and an empty array's `pop`/`shift` give `undefined`;
// `exec` without a match, a DOM lookup without an element and a query
// string's `get` without the key give `null`.
#[test]
fn lookups_that_may_find_nothing() {
    ok("
        const m = new Map([[\"a\", 1]]);
        /** const n: Number */
        const n = m.get(\"a\") ?? 0;
        const w = new WeakMap(); const k = {a: 1}; w.set(k, 1);
        const wv = w.get(k);
        if (wv !== undefined) { wv.toFixed(); }
        /** const xs: Number[] */
        const xs = [1, 2];
        const last = xs.pop();
        if (last !== undefined) { last.toFixed(); }
        const first = xs.shift() ?? 0;
        const r = /a(b)/.exec(\"ab\");
        if (r !== null) { r[1].length; }
        const el = document.getElementById(\"go\");
        if (el !== null) { el.textContent = \"ok\"; }
        const q = document.querySelector(\"p\");
        if (q) { q.textContent = \"ok\"; }
        const p = new URLSearchParams().get(\"a\") ?? \"\";
    ");
    err("const m = new Map([[\"a\", 1]]); const n = m.get(\"b\") + 1;");
    err("const w = new WeakMap(); const k = {a: 1}; w.set(k, 1); w.get(k).toFixed();");
    err("/** const xs: Number[] */ const xs = []; xs.pop().toFixed();");
    err("/** const xs: Number[] */ const xs = []; xs.shift().toFixed();");
    err("const r = /a/.exec(\"b\"); r.length;");
    err("document.getElementById(\"x\").textContent = \"hi\";");
    err("document.querySelector(\"p\").textContent = \"hi\";");
    err("const el = document.createElement(\"div\"); el.closest(\"p\").textContent = \"hi\";");
    err("new URLSearchParams().get(\"a\").length;");
    err("new FormData(document.createElement(\"form\")).get(\"a\").length;");
}

// The DOM's links between elements and its attribute reads may find
// nothing: a root has no parent, a last child no next sibling, a missing
// attribute reads `null`, as does an input outside a form, an unsupported
// canvas context, a storage key past the end and the active element of an
// unfocused document.
#[test]
fn dom_reads_that_may_find_nothing() {
    ok("
        const el = document.createElement(\"div\");
        const p = el.parentElement;
        if (p !== null) { p.textContent = \"ok\"; }
        const next = el.nextElementSibling;
        if (next) { next.remove(); }
        const id = el.getAttribute(\"data-id\") ?? \"\";
        const ctx = el.getContext(\"2d\");
        if (ctx !== null) { ctx.fillRect(0, 0, 1, 1); }
        const k = localStorage.key(0) ?? \"\";
    ");
    err("document.createElement(\"div\").parentElement.remove();");
    err("document.createElement(\"div\").firstElementChild.remove();");
    err("document.createElement(\"div\").lastElementChild.remove();");
    err("document.createElement(\"div\").nextElementSibling.remove();");
    err("document.createElement(\"div\").previousElementSibling.remove();");
    err("const n = document.createElement(\"div\").getAttribute(\"x\").length;");
    err("document.createElement(\"input\").form.submit();");
    err("document.createElement(\"canvas\").getContext(\"2d\").fillRect(0, 0, 1, 1);");
    err("const n = localStorage.key(0).length;");
    err("document.activeElement.focus();");
}

// A promise is always truthy: testing one, negating it or putting it on
// the left of `&&` / `||` is a forgotten `await` (`Testable`).
#[test]
fn a_promise_is_not_a_condition() {
    ok("
        async function isAdmin() { return false; }
        async function main() {
            if (await isAdmin()) { console.log(1); }
            const p = isAdmin();
            p.then(function (b) { return b ? 1 : 0; });
        }
    ");
    let decl = "async function isAdmin() { return false; }";
    for test in [
        "if (isAdmin()) { console.log(1); }",
        "if (!isAdmin()) { console.log(1); }",
        "while (isAdmin()) { console.log(1); }",
        "const n = isAdmin() ? 1 : 2;",
        "const b = isAdmin() && true;",
        "const b = isAdmin() || true;",
    ] {
        let e = err(&format!("{decl} {test}"));
        assert!(e.contains("a promise is always truthy"), "{test}: {e}");
    }
}

// A function is always truthy: testing one (`if`, `while`, `?:`, `!`, the
// left of `&&` / `||`) is a forgotten call (`Testable`, as the Lean model
// has it). A function that tests its parameter says so in its type, and
// is called with no function; a value that may be missing is tested as
// usual.
#[test]
fn a_function_is_not_a_condition() {
    ok("
        function isReady() { return true; }
        if (isReady()) { console.log(1); }
        function pick(x) { return x ? 1 : 2; }
        const n = pick(5) + pick(\"\");
        /** let cb: (() => Number) | Undefined */
        let cb = undefined;
        if (cb) { cb(); }
        try { JSON.parse(\"x\"); } catch (e) { if (e) { console.log(1); } }
    ");
    for src in [
        "function isReady() { return true; } if (isReady) { console.log(1); }",
        "function isReady() { return true; } while (isReady) { break; }",
        "function isReady() { return true; } const n = isReady ? 1 : 2;",
        "function isReady() { return true; } const b = !isReady;",
        "function isReady() { return true; } const b = isReady && true;",
        "function isReady() { return true; } const b = isReady || null;",
        "function isReady() { return true; } if (isReady) { isReady(); }",
        "const user = { isAdmin() { return false; } }; if (user.isAdmin) { console.log(1); }",
        "class C { m() { return 1; } } if (C) { new C(); }",
        "function pick(x) { return x ? 1 : 2; } pick(function () { return 1; });",
        "function g(f) { if (f) {} return f(); }",
        "/** const id: <T>(T) => T */ const id = function (x) { if (x) {} return x; };",
    ] {
        let e = err(src);
        assert!(
            e.contains("Testable") && (e.contains("always truthy") || e.contains("type parameter")),
            "{src}: {e}"
        );
    }
}

// A `function` declaration's annotation with type parameters is its type,
// as a `const`'s is: the body is checked with them rigid, so it must have
// every instance, and each call instantiates the declared scheme (it used
// to instantiate the parameters by the body: `<T>(x: T) => T` returning
// `1` was `(1) => 1`).
#[test]
fn a_function_annotations_type_parameters_are_rigid() {
    ok("
        /** function id<T>(x: T) => T */
        function id(x) { return x; }
        const n = id(1) + 1;
        const s = id(\"a\").length;
        /** function first<T>(xs: T[]) => T? */
        function first(xs) { return xs.length > 0 ? xs[0] : undefined; }
        const a = (first([1]) ?? 0) + 1;
        /** function len<T>(xs: T[]) => Number */
        function len(xs) { return xs.length === 0 ? 0 : 1 + len(xs.slice(1)); }
        const k = len([1]) + len([\"a\"]);
        /** function decode<T>(text: String) => T */
        function decode(text) { return JSON.parse(text); }
    ");
    for body in [
        "return 1;",
        "return x + x;",
        "if (x) {} return x;",
        "return x.length;",
    ] {
        err(&format!(
            "/** function f<T>(x: T) => T */ function f(x) {{ {body} }}"
        ));
    }
    let e = err("let g = 0; /** function f<T>(x: T) => T */ function f(x) { g = x; return x; }");
    assert!(e.contains("'"), "{e}");
}

// The standard library's host methods that throw when called detached
// ("Illegal invocation") say their `this`: called on their object, not
// taken off it or passed as a callback.
#[test]
fn stdlib_host_methods_are_called_on_their_object() {
    ok("
        localStorage.setItem(\"k\", \"v\");
        const v = localStorage.getItem(\"k\");
        const m = Map(); m.set(\"a\", 1);
        const n = (m.get(\"a\") ?? 0) + m.size;
        history.pushState(1, \"\", \"/a\");
        const r = [1.5].map(Math.round);
    ");
    err("const g = localStorage.getItem; const v = g(\"k\");");
    err("const m = Map(); const g = m.get; const v = g(\"a\");");
    err("const r = [\"k\"].map(localStorage.getItem);");
}

// The canvas context's and a gradient's methods say their `this`: called on
// them, as painters do, but not taken off them. A type naming the
// context (`type Ctx = CanvasRenderingContext2D<…>`) types a painter.
#[test]
fn canvas_methods_are_called_on_their_context() {
    ok("
        const g = document.createElement(\"canvas\").getContext(\"2d\");
        if (g === null) throw new Error(\"no 2d context\");
        g.beginPath(); g.moveTo(0, 0); g.lineTo(1, 1); g.stroke();
        const grad = g.createLinearGradient(0, 0, 1, 0);
        grad.addColorStop(0, \"red\");
        g.fillStyle = grad;
        const w = g.measureText(\"hi\").width;
        /** type Ctx = CanvasRenderingContext2D<{}> */
        /** type Painter = (Ctx, Number, Number) => Undefined */
        /** function run(p: Painter) => Undefined */
        function run(p) {}
        run((c, w, h) => { c.fillStyle = \"red\"; c.fillRect(0, 0, w, h); });
    ");
    let ctx = "const g = document.createElement(\"canvas\").getContext(\"2d\"); \
               if (g === null) throw new Error(\"no 2d context\");";
    let e = err(&format!("{ctx} const f = g.fillRect; f(0, 0, 1, 1);"));
    assert!(e.contains("detached"), "{e}");
    let e = err(&format!(
        "{ctx} const a = g.createLinearGradient(0, 0, 1, 0).addColorStop; a(0, \"red\");"
    ));
    assert!(e.contains("detached"), "{e}");
}
