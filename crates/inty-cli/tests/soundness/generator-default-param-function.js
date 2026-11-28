// inty: accept
// inty: known-failing: inty rejects it with `Undefined variable: 'yield'` (review of claude/browser-apis, fix pending)
// A generator whose parameter defaults to a function expression.
function* g(cb = function () { return 1; }) { yield cb(); }
for (const x of g()) x.toFixed(1);
