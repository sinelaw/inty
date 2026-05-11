// `+` works on any addable type — Number or String.
// Inty infers `add<a> where Plus a => (a, a) => a`.

function add(x, y) { return x + y; }

var sum    = add(1, 2);
var concat = add("foo", "bar");

// The call site picks the instance. Mixing them is a type error:
// var bad = add(1, "two");   // error!
