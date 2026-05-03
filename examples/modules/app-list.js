// Export-list demo. Run with:
//
//     minfern examples/modules/app-list.js
//
// `math.js` exports `square` under its own name and renames `cube` to
// `pow3`. The local name `cube` is intentionally not importable — try
// `import { cube } from "./math.js";` to see the resolver reject it.

import { square, pow3 } from "./math.js";

const a = square(4);
const b = pow3(3);
console.log(a);
console.log(b);
