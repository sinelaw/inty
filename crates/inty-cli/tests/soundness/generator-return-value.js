// inty: reject
// inty: known-failing: a generator's `return` value isn't part of what `next().value` can be (review of claude/browser-apis, fix pending)
// The second `next()` returns the generator's `return` value, a string,
// which has no `toFixed`.
function* g() { yield 1; return "s"; }
const it = g();
it.next();
it.next().value.toFixed(1);
