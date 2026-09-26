// Array pipelines: chains the backend fuses into one loop (pure
// callbacks) and chains it must leave alone (effects whose order shows).
const xs = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3];

function square(x) {
  return x * x;
}

// Fused chains, one per kind of consumer.
console.log(xs.map((x) => x * 2).reduce((a, b) => a + b, 0));
console.log(xs.filter((x) => x % 2 === 1).map((x) => x + 1).join(","));
console.log(xs.map(square).filter((x) => x > 10).join(","));
console.log(xs.map((x) => x - 5).some((x) => x > 3));
console.log(xs.map((x) => x - 5).every((x) => x > -5));
console.log(xs.filter((x) => x > 3).findIndex((x) => x === 5));
console.log(xs.filter((x) => x > 100).findIndex((x) => x === 5));
console.log(xs.map((x) => x / 2).map((x) => x * 3).join(","));
console.log([].map((x) => x + 1).reduce((a, b) => a + b, 7));
let sum = 0;
xs.filter((x) => x > 2).forEach((x) => {
  sum += x;
});
console.log(sum);

// Intermediates in single-use consts, as a program would write them.
function stats(round) {
  const shifted = xs.map((x) => x + round);
  const big = shifted.filter((x) => x > 5);
  return big.reduce((acc, x) => acc + x / 10, 0);
}
console.log(stats(1));
console.log(stats(3));

// An intermediate used twice stays an array.
const doubled = xs.map((x) => x * 2);
const firstBig = doubled.findIndex((x) => x > 10);
console.log(firstBig + doubled.length);

// Effects: JS runs every map call before any filter call, and a fused
// loop would interleave them, so these chains must not fuse.
let trace = "";
const kept = xs
  .map((x) => {
    trace += "m" + String(x);
    return x;
  })
  .filter((x) => {
    trace += "f" + String(x);
    return x > 4;
  });
console.log(kept.join(","));
console.log(trace);
