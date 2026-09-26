// Array mutators: splice (every arity, negative / out-of-range / fractional
// arguments, result used or not), unshift, and push growth.
function show(xs) {
  return "[" + xs.join(",") + "]";
}

const a = [0, 1, 2, 3, 4, 5, 6, 7];
console.log(show(a.splice(2, 3)) + " " + show(a));
a.splice(1, 0, 10, 11);
console.log(show(a));
a.splice(-2, 1, 20);
console.log(show(a));
console.log(show(a.splice(3)) + " " + show(a));
console.log(show(a.splice(-100, 1, 30, 31, 32, 33)) + " " + show(a));
console.log(show(a.splice(100, 5, 40)) + " " + show(a));
console.log(show(a.splice(1.7, 1.9)) + " " + show(a));
console.log(show(a.splice(1, -3, 50)) + " " + show(a));
a.splice(0, a.length);
console.log(show(a) + " " + String(a.length));

// Objects are references: splice moves them, it doesn't copy them.
const recs = [{ id: 1 }, { id: 2 }, { id: 3 }];
const moved = recs.splice(0, 1);
recs.splice(1, 0, moved[0]);
moved[0].id = 9;
console.log(recs.map((r) => String(r.id)).join(","));

const s = ["b", "c"];
console.log(s.unshift("a"));
s.unshift("z");
console.log(s.join(""));

// Push growth: a large array built one element at a time.
const big = [];
for (let i = 0; i < 100000; i++) big.push(i % 7);
let sum = 0;
for (let i = 0; i < big.length; i++) sum += big[i];
console.log(String(big.length) + " " + String(sum));
const n = [];
console.log(n.push(5) + n.push(6));

// `new Array(n).fill(v)`: one allocation of the final size.
const filled = new Array(4).fill(-1);
filled[2] = 7;
console.log(filled.join(","));
console.log(Array(3).fill("ab").join("|"));
