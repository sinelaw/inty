/** function pair<A, B>(a: A, b: B) => { a: A, b: B } */
function pair(a, b) { return { a: a, b: b }; }
/** const p: { a: String, b: Number } */
const p = pair(1, 2);
/** function wrap<T>(x: T) => { v: T } */
function wrap(x) { return { v: x }; }
/** const w: String */
const w = wrap;
