// Higher-order array methods: map / filter / reduce with closures,
// rebuilt on every round.
function range(n) {
  const xs = [];
  for (let i = 0; i < n; i++) {
    xs.push(i);
  }
  return xs;
}

function main() {
  const lines = [];
  const xs = range(100000);
  let total = 0;
  for (let round = 0; round < 150; round++) {
    const squares = xs.map((x) => x * x + round);
    const odd = squares.filter((x) => x % 2 === 1);
    total += odd.reduce((acc, x) => acc + x / 1000, 0);
  }
  lines.push(total);
  return lines.join("\n");
}

// ---- benchmark protocol (see bench.mjs) ------------------------------
// Run the workload 4 times in one process. The first run includes JIT
// warm-up; bench.mjs reports the other three as steady-state samples.
let report = "";
for (let iteration = 0; iteration < 4; iteration++) {
  const t0 = performance.now();
  report = main();
  console.error(`inty-bench iteration ${iteration} ms ${performance.now() - t0}`);
}
console.log(report);
