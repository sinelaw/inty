function add(x, y) { return x + y; }

var sum    = add(1, 2);
var concat = add("foo", "bar");
var bad = add(1, "two");   // ← should error
