// inty: reject
// inty: known-failing: a user `type Iterator<T>` alias replaces the generator object's type (review of claude/browser-apis, fix pending)
// A user alias named `Iterator` must not become the type of a generator
// object: a generator has no `current` field.
/** type Iterator<T> = {current: T} */
function* g() { yield 1; }
const c = g().current.toFixed(1);
