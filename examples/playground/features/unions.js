// Unions are declared, not guessed: branches that disagree on type
// are an error unless an annotation says they form a union. A branch
// that is `null` or `undefined` is no different: `T | Null` is said too.

/** function tag(Boolean) => Number | String */
function tag(c) { return c ? 42 : "err"; }
var t = tag(true);                  // Number | String

// Arrays:
/** var mixed: (Number | String)[] */
var mixed = [1, "two", 3];
var first = mixed[0];               // Number | String

// Object branches with disjoint shapes:
/** function pick(Boolean) => {x: Number, y: Number} | {x: Number, z: Number} */
function pick(b) {
    return b ? { x: 1, y: 2 } : { x: 3, z: 4 };
}
var pt = pick(true);
var x  = pt.x;                      // both arms expose `x: Number`

// Nullable: `T | Null` holds a `T` or `null`, and `??` or a test for
// null gets the `T` back out.
/** function find<a>(xs: a[], v: a) => a | Null */
function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }
var hit = find([1, 2], 2);          // Number | Null
var n = hit ?? 0;                   // Number

// Try this — remove an annotation above to see the branches rejected.
