// inty: reject
// inty: known-failing: a `static *g()` generator method is typed as an instance method (review of claude/browser-apis, fix pending)
// A static generator method lives on the class, not on its instances:
// `new C().g` is undefined.
class C { static *g() { yield 1; } }
const xs = [...new C().g()];
