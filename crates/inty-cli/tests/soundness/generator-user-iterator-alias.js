// inty: reject
// A user alias named `Iterator` must not become the type of a generator
// object: a generator has no `current` field.
/** type Iterator<T> = {current: T} */
function* g() { yield 1; }
const c = g().current.toFixed(1);
