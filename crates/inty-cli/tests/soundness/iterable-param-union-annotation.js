// inty: accept
// inty: known-failing: inty rejects it with `Type mismatch: expected 'Number', found 'String'` (review of claude/browser-apis, fix pending)
// A function iterating its argument and returning it, used at an
// annotated union type.
function f(xs) { for (const x of xs) x.toFixed(1); return xs; }
/** const r: Number[] | Set<String> */
const r = f([1]);
