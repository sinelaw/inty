// Functions are first-class. Inty handles higher-order use directly.

function compose(f, g) {
    return function(x) { return f(g(x)); };
}

function double(x) { return x * 2; }
function inc(x)    { return x + 1; }

var f = compose(double, inc);
var n = f(3);                       // (3 + 1) * 2 = 8

// `compose` is fully polymorphic — works for any matching pair.
var g = compose(function(s) { return s + "!"; },
                function(s) { return s + s; });
var loud = g("yo");                 // "yoyo!"
