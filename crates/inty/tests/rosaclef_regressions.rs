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
        panic!("expected to type-check, got:\n{}\n--- source ---\n{}", e, src);
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
// function declaration: `Number >= Int`.
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
        /** function size(t: Tree) => Int */
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
        /** const l: List<Int> */
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

// 5. A non-literal `Int` flows into a `Number` field of a returned
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
        /** const g: (Int) => { n: Number } */
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
    // An existing Int record is not a Number record (it could be written
    // a fraction through the other view).
    err("
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
        /** function each(f: (Int, String) => Undefined) => Undefined */
        function each(f) { f(1, \"a\"); return undefined; }
        each(() => undefined);
        each((i) => undefined);
    ");
    // Not more than it is passed.
    err("
        /** function each(f: (Int) => Undefined) => Undefined */
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
    // The index is an Int.
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
        /** const r: Promise<Int> */
        const r = p.then((x) => Promise.resolve(x ? 1 : 2));
        /** const s: Promise<String> */
        const s = p.then((x) => x ? "a" : "b").then((y) => y + "!");
        const t = p.catch((e) => Promise.resolve(false));
    "#);
    ok(r#"
        function after(p) { return p.then((x) => x + 1); }
        /** const q: Promise<Int> */
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
        /** function mk(s: String) => [String, Int] */
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

// 21. `class … extends Base`: the base instance's fields and methods,
// from a class of the same program or a constructor a lib declares.
#[test]
fn b21_class_extends() {
    check_with_lib(
        "/** type MessagePort = { postMessage: (String) => Undefined } */\n\
         /** const AudioWorkletProcessor: () => { port: MessagePort } */\n\
         const AudioWorkletProcessor;",
        "class Gain extends AudioWorkletProcessor {
            constructor() { super(); this.gain = 0.5; }
            process(inputs) { this.port.postMessage(\"hi\"); return this.gain > 0; }
         }
         const ok = new Gain().process([]);",
    )
    .unwrap();
    ok("
        class Base { constructor(n) { this.n = n; } twice() { return this.n * 2; } }
        class Sub extends Base {
            constructor() { super(21); this.label = \"x\"; }
            show() { return this.label + String(this.twice()); }
        }
        const s = new Sub();
        const t = s.show() + String(s.n + 1);
    ");
    // A base field keeps its type.
    err("
        class Base { constructor(n) { this.n = n; } twice() { return this.n * 2; } }
        class Bad extends Base { constructor() { super(1); this.n = \"x\"; } }
    ");
    // `super(…)` passes the base constructor's arguments.
    err("
        class Base { constructor(n) { this.n = n * 2; } }
        class Bad extends Base { constructor() { super(\"x\"); } }
    ");
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
/** const m: Map<String, Int> */
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

// 20. The AudioWorklet global scope, with `extends AudioWorkletProcessor`.
#[test]
fn b20_audio_worklet() {
    check_with_lib(inty::stdlib::AUDIO_WORKLET, r##"class Gain extends AudioWorkletProcessor {
  constructor() {
    super();
    this.gain = 1;
    this.frames = 0;
  }
  /** process(inputs, outputs, parameters) */
  process(inputs, outputs, parameters) {
    const out = outputs[0];
    for (const ch of out) for (let i = 0; i < ch.length; i++) ch[i] = ch[i] * this.gain;
    this.frames = this.frames + 128;
    if (this.frames > sampleRate) this.port.postMessage({ t: "second", at: currentTime });
    return true;
  }
}
registerProcessor("gain", Gain);
"##).unwrap();
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
