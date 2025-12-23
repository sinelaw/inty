// Namespace-import demo. Run with:
//
//     inty examples/modules/app-namespace.js
//
// `import * as id from "./identity.js";` binds `id` to a *module* type
// — not an object literal. Each `id.id(...)` access re-instantiates the
// polymorphic export, so calling it at Number and String in the same
// program both type-check. A row would have shared the type variable
// across uses and rejected the second call.

import * as id from "./identity.js";

const n = id.id(42);
const s = id.id("hello");
const p = id.PI;
console.log(n);
console.log(s);
console.log(p);
