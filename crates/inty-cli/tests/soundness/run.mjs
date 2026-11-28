// Runs one program for crates/inty-cli/tests/soundness.rs: `node run.mjs
// FILE`. inty assumes strict mode throughout (docs/scc-inference.md), so a
// script runs as strict-mode code in this realm (its globals: console,
// TextDecoder, ...); a file with `import` or `export` runs as an ES module
// (Node detects module syntax in a `.js` file). An uncaught error, or a
// promise rejected with no handler, exits non-zero with its stack on stderr.

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import vm from "node:vm";

const file = resolve(process.argv[2]);
const source = readFileSync(file, "utf8");
if (/^\s*(import|export)\b/m.test(source)) {
  await import(pathToFileURL(file).href);
} else {
  vm.runInThisContext(`"use strict"; ${source}`, { filename: file });
}
