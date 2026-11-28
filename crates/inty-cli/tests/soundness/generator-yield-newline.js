// inty: reject
// inty: known-failing: `yield` followed by a line break parses as `yield EXPR` instead of `yield;` (ASI) (review of claude/browser-apis, fix pending)
// A line break after `yield` ends the statement (ASI): this is `yield;`
// followed by `1;`, so the generator yields `undefined`.
function* g() { yield
1; }
for (const x of g()) x.toFixed(1);
