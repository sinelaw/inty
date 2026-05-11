// A function that doesn't constrain its inputs becomes polymorphic.
// Inty infers `id<a>(a) => a`.

function id(x) { return x; }

var n   = id(42);
var s   = id("hello");
var arr = id([1, 2, 3]);

// One function, three call sites — each instantiated at a fresh type.
