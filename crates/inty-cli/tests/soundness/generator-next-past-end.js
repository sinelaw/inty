// inty: reject
// inty: known-failing: a finished generator's `next()` is typed as yielding the element type; its `value` is the return value (`undefined`) (review of claude/browser-apis, fix pending)
// The second `next()` finishes the generator: its `value` is `undefined`
// (the function's return value), so `.toFixed` throws a TypeError.
function* g() { yield 1; }
const it = g();
it.next();
it.next().value.toFixed(1);
