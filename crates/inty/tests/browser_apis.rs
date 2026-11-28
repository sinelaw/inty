//! Browser APIs the stdlib declares: typed arrays (every kind, and views
//! of an `ArrayBuffer`), `TextEncoder`/`TextDecoder`, WebAssembly, the
//! `Error` type, workers and message channels.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src` with the stdlib and `libs` (declaration files loaded
/// after it); return Ok(()) if it checks, or the formatted error.
fn check_with(libs: &[&str], src: &str) -> Result<(), String> {
    let (mut env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    for lib in libs {
        let program = parse(lib).map_err(|e| format!("lib parse error: {:?}", e))?;
        let (_, lib_env) = state
            .infer_program_with_env(&env, &program)
            .map_err(|e| format!("lib error: {:?}", e))?;
        env = lib_env;
    }
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {}", e))?;
    let errs = state.take_errors();
    match errs.first() {
        None => Ok(()),
        Some(e) => Err(e.to_string()),
    }
}

fn ok(src: &str) {
    let r = check_with(&[], src);
    assert!(r.is_ok(), "should check: {:?}\n{}", r, src);
}

/// `src` is rejected, with an error that mentions `needle`.
fn bad(src: &str, needle: &str) {
    match check_with(&[], src) {
        Ok(()) => panic!("should be rejected:\n{}", src),
        Err(e) => assert!(
            e.contains(needle),
            "expected {:?} in {:?}\n{}",
            needle,
            e,
            src
        ),
    }
}

#[test]
fn every_typed_array_kind() {
    for kind in [
        "Int8Array",
        "Uint8Array",
        "Uint8ClampedArray",
        "Int16Array",
        "Uint16Array",
        "Int32Array",
        "Uint32Array",
        "Float32Array",
        "Float64Array",
    ] {
        ok(&format!(
            "/** const a: {kind} */\n\
             const a = new {kind}(4);\n\
             a[0] = 1.5;\n\
             const x = a[1] + a.length + a.byteLength + a.byteOffset + a.BYTES_PER_ELEMENT + {kind}.BYTES_PER_ELEMENT;\n\
             /** const s: {kind} */\n\
             const s = a.subarray(1, 3);\n\
             /** const c: {kind} */\n\
             const c = a.slice(1).fill(2);\n\
             a.set(c, 1);\n\
             /** const f: {kind} */\n\
             const f = {kind}.from([1, 2]);\n\
             /** const b: ArrayBuffer */\n\
             const b = a.buffer;\n\
             let t = 0;\n\
             for (const v of a) t += v;\n"
        ));
        // Fixed length; a kind is its own type.
        bad(&format!("const a = new {kind}(1); a.push(1);"), "push");
        let other = if kind == "Uint8Array" {
            "Int8Array"
        } else {
            "Uint8Array"
        };
        bad(
            &format!("const a = new {kind}(1); a.set(new {other}(1));"),
            "Cannot unify",
        );
    }
}

#[test]
fn typed_array_views_of_a_buffer() {
    ok("const mem = new WebAssembly.Memory({ initial: 1 });\n\
        /** const bytes: Uint8Array */\n\
        const bytes = new Uint8Array(mem.buffer);\n\
        /** const words: Uint32Array */\n\
        const words = new Uint32Array(mem.buffer, 8, 2).slice();\n\
        /** const f: Float32Array */\n\
        const f = new Float32Array(new ArrayBuffer(16), 4);\n\
        const n = bytes.subarray(0, 4).length + words[1] + f[0];\n");
    // Copies of an array and of another typed array; an empty one.
    ok(
        "/** const a: Uint8Array */ const a = new Uint8Array([1, 2, 3]);\n\
        /** const b: Uint32Array */ const b = new Uint32Array(a);\n\
        /** const c: Int8Array */ const c = new Int8Array();\n",
    );
    // A buffer parameter, once annotated (an argument whose type isn't
    // known yet is a length), and one any call with an offset makes one.
    ok("/** function view(b: ArrayBuffer) => Uint8Array */\n\
        function view(b) { return new Uint8Array(b); }\n\
        function at(b, i) { return new Uint32Array(b, i, 1); }\n\
        const v = view(new ArrayBuffer(4));\n\
        const w = at(new ArrayBuffer(8), 4);\n");
    bad("const a = new Uint8Array(\"abc\");", "expected Number");
    bad("const a = new Uint8Array([\"a\"]);", "Number[]");
    bad("const a = new Uint32Array(4, 0);", "Cannot unify");
    bad(
        "const a = new Uint32Array(new ArrayBuffer(8), \"0\");",
        "expected Number",
    );
    bad(
        "function f(b) { return new Uint8Array(b); }\n\
         const v = f(new ArrayBuffer(1));",
        "Cannot unify",
    );
    // A program's own binding of the name is an ordinary constructor.
    ok("function Uint8Array(s) { return { s }; } const u = new Uint8Array(\"x\");");
}

#[test]
fn text_encoder_and_decoder() {
    ok("const enc = new TextEncoder();\n\
        /** const bytes: Uint8Array */\n\
        const bytes = enc.encode(\"héllo\");\n\
        const r = enc.encodeInto(\"hi\", new Uint8Array(8));\n\
        const n = r.read + r.written;\n\
        const dec = new TextDecoder(\"utf-8\", { fatal: true });\n\
        /** const s: String */\n\
        const s = dec.decode(bytes) + dec.decode(bytes.subarray(1), { stream: true }) + dec.decode();\n");
    bad(
        "const r = new TextEncoder().encodeInto(\"x\", new Uint32Array(2));",
        "Uint8Array",
    );
    bad(
        "const r = new TextEncoder().encodeInto(\"x\", new Uint8Array(2)); r.bytes;",
        "bytes",
    );
    bad(
        "const s = new TextDecoder().decode(\"abc\");",
        "Cannot unify",
    );
}

#[test]
fn webassembly_instantiate_by_bytes_and_by_module() {
    ok(
        "/** type Ex = {memory: WebAssemblyMemory, f: (Number) => Number} */\n\
        /** function load(bytes: ArrayBuffer) => Promise<Number> */\n\
        async function load(bytes) {\n\
          const { instance, module } = await WebAssembly.instantiate(bytes, {});\n\
          /** const ex: Ex */\n\
          const ex = instance.exports;\n\
          /** const m: WebAssemblyModule */\n\
          const m = module;\n\
          const again = await WebAssembly.instantiate(m, { env: {} });\n\
          /** const ex2: Ex */\n\
          const ex2 = again.exports;\n\
          /** const compiled: WebAssemblyModule */\n\
          const compiled = await WebAssembly.compile(new Uint8Array(bytes));\n\
          /** const i: WebAssemblyInstance<Ex> */\n\
          const i = new WebAssembly.Instance(new WebAssembly.Module(bytes), {});\n\
          return ex.f(1) + ex2.f(2) + i.exports.f(3) + (WebAssembly.validate(bytes) ? 1 : 0);\n\
        }\n",
    );
    // An annotated module parameter instantiates to the instance.
    ok(
        "/** function inst(m: WebAssemblyModule) => Promise<Number> */\n\
        async function inst(m) {\n\
          const instance = await WebAssembly.instantiate(m);\n\
          return instance.exports.f();\n\
        }\n",
    );
    // Bytes resolve to `{instance, module}`, not to an instance.
    bad(
        "const p = WebAssembly.instantiate(new ArrayBuffer(1)).then((r) => r.exports);",
        "exports",
    );
    // A module resolves to the instance alone.
    bad(
        "/** const m: WebAssemblyModule */ const m = new WebAssembly.Module(new ArrayBuffer(1));\n\
         const p = WebAssembly.instantiate(m).then((r) => r.instance);",
        "instance",
    );
    // A module is its own type, not any record.
    bad("const p = WebAssembly.instantiate({});", "Cannot unify");
    bad(
        "/** const m: WebAssemblyModule */ const m = {};",
        "Cannot unify",
    );
}

#[test]
fn error_is_a_type_name() {
    ok(
        "/** type Build = {resolve: (Uint8Array) => Undefined, reject: (Error) => Undefined} */\n\
        /** const b: Build */\n\
        const b = { resolve: (u) => {}, reject: (e) => { console.log(e.message + e.name); } };\n\
        b.reject(new Error(\"x\"));\n\
        b.reject(new TypeError());\n\
        /** function why(e: Error) => String */\n\
        function why(e) { return e.stack; }\n",
    );
    bad(
        "/** type B = {reject: (Error) => Undefined} */\n\
         /** const b: B */ const b = { reject: (e) => {} };\n\
         b.reject(\"x\");",
        "Cannot unify",
    );
}

#[test]
fn workers_and_message_channels() {
    ok("/** type ToW = {kind: \"build\", id: Number} */\n\
        /** type FromW = {kind: \"built\", id: Number, bytes: Uint8Array} */\n\
        /** const w: Worker<ToW, FromW> */\n\
        const w = new Worker(\"/js/w.js\", { type: \"module\" });\n\
        w.onmessage = (e) => { const n = e.data.bytes.length + e.data.id; };\n\
        w.onerror = (e) => { console.log(e.message); };\n\
        w.postMessage({ kind: \"build\", id: 1 });\n\
        w.terminate();\n\
        const ch = new MessageChannel();\n\
        ch.port1.onmessage = () => {};\n\
        ch.port2.postMessage(null);\n");
    bad(
        "/** const w: Worker<Number, String> */\n\
         const w = new Worker(\"/w.js\");\n\
         w.postMessage(\"x\");",
        "Cannot unify",
    );
}

#[test]
fn a_worker_scope() {
    let worker = inty::stdlib::builtin_lib("worker").expect("builtin:worker");
    let src = "/** type ToW = {id: Number} */\n\
               /** type FromW = {id: Number, bytes: Uint8Array} */\n\
               /** const scope: WorkerScope<ToW, FromW> */\n\
               const scope = self;\n\
               scope.onmessage = (e) => {\n\
                 const bytes = new Uint8Array(4);\n\
                 scope.postMessage({ id: e.data.id, bytes }, [bytes.buffer]);\n\
               };\n\
               self.postMessage(1);\n\
               postMessage(\"done\", []);\n";
    let r = check_with(&[worker], src);
    assert!(r.is_ok(), "{:?}", r);
    // Answers must be the scope's.
    let r = check_with(
        &[worker],
        "/** const scope: WorkerScope<Number, String> */ const scope = self;\n\
         scope.onmessage = (e) => { scope.postMessage(e.data); };",
    );
    assert!(r.is_err(), "should be rejected");
    // Not declared on a page's main thread.
    bad("self.postMessage(1);", "self");
}

/// The rules that make one of the standard library's types (a
/// generator's iterator, a typed array's buffer, a WebAssembly module)
/// make the library's, not a program's own alias of the same name.
#[test]
fn a_program_s_alias_does_not_stand_in_for_the_library_s_type() {
    // A generator is the library's iterator, which a program's own
    // `Iterator` doesn't describe.
    ok("/** type Iterator<T> = {current: T} */\n\
        function* g() { yield 1; }\n\
        const xs = [...g()];\n\
        const n = xs[0] + 1;");
    bad(
        "/** type Iterator<T> = {current: T} */\n\
         /** function g() => Iterator<Number> */ function* g() { yield 1; }",
        "Symbol.iterator",
    );
    // A typed array's `buffer` is the library's `ArrayBuffer`.
    ok("/** type ArrayBuffer = {mine: Number} */\n\
        const b = new Uint8Array(4).buffer;\n\
        const n = b.byteLength;");
    bad(
        "/** type ArrayBuffer = {mine: Number} */\n\
         const b = new Uint8Array(4).buffer;\n\
         const n = b.mine;",
        "mine",
    );
    // `instantiate` of a program's own `WebAssemblyModule` is of bytes.
    bad(
        "/** nominal type WebAssemblyModule = {} */\n\
         /** function own(m: WebAssemblyModule) => Undefined */\n\
         function own(m) { WebAssembly.instantiate(m); }",
        "BufferSource",
    );
}
