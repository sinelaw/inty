// A mismatch in a function's parameter is the function's: the member
// named is `cb`, with its two function types (not `cb.x`).
/** function f(o: {cb: ({x: String}) => Number}) => Number */
function f(o) { return o.cb({x: "a"}); }
/** const v: {cb: ({x: Number}) => Number} */
const v = {cb: (p) => p.x * 2};
f(v);

// A member that would fit but for a record's invariance says why.
/** function g(o: {xs: (Number | String)[]}) => Number */
function g(o) { return o.xs.length; }
/** const ys: Number[] */
const ys = [1];
const w = {xs: ys};
g(w);
