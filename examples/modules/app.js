// Entry point. Pulls the mutable `state` and its mutators from `./store`
// and the pretty-printers from `./format`. Run with:
//
//     inty examples/modules/app.js
//
// inty resolves the two relative imports from `app.js`'s directory,
// parses and infers each module, then merges the exported bindings into
// this file's environment. You'll see every call below type-check with
// no per-call annotations.
//
// To run this in a browser, every file needs to be served over HTTP
// (Chromium blocks `type="module"` imports from `file://`). The SPA
// example next door stays single-file for exactly that reason.

import { state, increment, reset, snapshot } from "./store.js";
import { formatCount, formatHistory } from "./format.js";

increment();
increment();
increment();

const summary = `count = ${state.count}, ${formatCount(state.count)}`;
const history = formatHistory(state.history);
const frozen = snapshot();

console.log(summary);
console.log(history);
console.log(frozen);

reset();
