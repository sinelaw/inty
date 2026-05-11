// Branches that disagree on type are *joined* into a closed union.

function tag(c) { return c ? 42 : "err"; }
var t = tag(true);                  // Number | String

// Arrays:
var mixed = [1, "two", 3];          // (Number | String)[]
var first = ["a", 2][0];            // Number | String

// Object branches with disjoint shapes:
function pick(b) {
    return b ? { x: 1, y: 2 } : { x: 3, z: 4 };
}
var pt = pick(true);
var x  = pt.x;                      // both branches expose `x: Number`
