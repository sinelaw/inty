// Re-export demo. Run with:
//
//     minfern examples/modules/app-reexport.js
//
// `lib.js` is a barrel: it re-exports a curated subset of
// `lib-internal.js`. We never touch the internal module directly — every
// binding here threads through the barrel's `export … from` clauses.

import describe, { double, triplicate, internals } from "./lib.js";

const a = double(21);          // -> 42
const b = triplicate(7);       // -> 21
const tag = internals.TAG;     // namespace member access through the barrel
const summary = describe();
console.log(a);
console.log(b);
console.log(tag);
console.log(summary);
