// TypeScript treats arrays as covariant: a `number[]` may be passed where
// a `(number | string)[]` is expected. That's unsound as soon as the
// callee writes to the array: with full JSDoc types and `--strict`, tsc
// accepts this, and at runtime `scores[1].toFixed` is not a function.
//
// Inty: an array's element type is invariant. A `Number[]` is not a
// `(Number | String)[]`, so the call is rejected.

/** function addLabel(xs: (Number | String)[]) => Undefined */
function addLabel(xs) { xs.push("n/a"); }

/** const scores: Number[] */
const scores = [90];
addLabel(scores);
// Inty: expected '(Number | String)[]', found 'Number[]'.
console.log(scores[1].toFixed(1));
