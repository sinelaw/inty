// Functions are *rows* — a call signature plus optional named fields.
// So `String(42)` and `String.fromCharCode(65)` are the same value
// used two different ways.

var c = String.fromCharCode(65);   // "A"
var s = String(42);                // "42"

var arr = [1, 2, 3];
var stringified = arr.map(String); // String[]

// Passing `String` where `.map` expects a function is pure row
// polymorphism — no special "constructor type" rule.
