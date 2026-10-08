// The JavaScript engine oracle for crates/inty/tests/differential.rs.
//
// Reads one program per line on stdin, runs each as a strict-mode script in
// a fresh realm, and prints one verdict per line, in the model's value wire format
// (lean/Inty/Wire.lean):
//
//   value V    the script's completion value
//   thrown V   an uncaught `throw` of a value the program made
//   error N    a native error the engine raised (TypeError, ...)
//   limit      a resource limit: the stack, a string's length, the time
//
// where V is `num BITS` (the float64's bits, so NaN and -0 survive),
// `str s:TEXT`, `bool B`, `undef`, `null`, `fun` or `obj`.

"use strict";

const readline = require("node:readline");
const vm = require("node:vm");

const view = new DataView(new ArrayBuffer(8));

function wire(v) {
  switch (typeof v) {
    case "number":
      view.setFloat64(0, v);
      return `num ${view.getBigUint64(0)}`;
    case "string":
      return `str s:${v}`;
    case "boolean":
      return `bool ${v}`;
    case "undefined":
      return "undef";
    case "function":
      return "fun";
    case "object":
      return v === null ? "null" : "obj";
    default:
      return `other ${typeof v}`;
  }
}

// inty assumes strict mode throughout (docs/scc-inference.md). It matters
// here for `this`: in a call outside a receiver it is `undefined`, where
// sloppy mode makes it the global object.
function run(source) {
  try {
    const strict = `"use strict"; ${source}`;
    return `value ${wire(vm.runInNewContext(strict, {}, { timeout: 200 }))}`;
  } catch (e) {
    // The engine's own errors have a stack; the plain objects a program
    // makes don't (they come from the script's realm, where `instanceof
    // Error` doesn't hold).
    if (e === null || typeof e !== "object" || !("stack" in e)) return `thrown ${wire(e)}`;
    if (e.code === "ERR_SCRIPT_EXECUTION_TIMEOUT") return "limit";
    if (e.name === "RangeError") return "limit";
    return `error ${e.name}`;
  }
}

const out = [];
readline
  .createInterface({ input: process.stdin, crlfDelay: Infinity })
  .on("line", (line) => out.push(run(line)))
  .on("close", () => process.stdout.write(out.map((l) => l + "\n").join("")));
