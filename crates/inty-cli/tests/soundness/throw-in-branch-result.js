// inty: accept
// inty: known-failing: inty rejects it with `Property 'n' not found in type Null | {n: Number}` (review of claude/browser-apis, fix pending)
// A branch that throws doesn't contribute to the function's result:
// `check` returns its argument, which fits `{n: Number} | Null`.
function check(o) { if (o.n < 0) { throw new Error("x"); } return o; }
/** const c: {n: Number} | Null */
const c = check({n: 1});
