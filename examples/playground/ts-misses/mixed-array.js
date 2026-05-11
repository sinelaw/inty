// Without annotations, TypeScript widens this to `(string | number)[]`
// and lets you use any element as if it were either type.
// Inty types it as a closed union and forces a narrow before use.

var items = [1, "two", 3, "four"];

// In TS: items[0].toFixed(2) compiles (because of `number` in the union).
// At runtime: TypeError when the element is actually a string.
//
// Inty: `.toFixed` isn't on the union — you must narrow first.
function describe(x) {
    if (typeof x === "number") { return x.toFixed(2); }
    else                       { return x.toUpperCase(); }
}
var first = describe(items[0]);
