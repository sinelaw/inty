// Inty infers a type for every binding — no annotations needed.
// Hover anything to see the inferred type.

var n = 42;
var s = "hello";
var b = true;

function square(x) { return x * x; }
var nine = square(3);

function greet(name) { return "Hello, " + name; }
var hi = greet("world");
