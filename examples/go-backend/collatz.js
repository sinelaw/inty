// Longest Collatz chain below a bound: integer arithmetic done in
// doubles, dominated by `%` and division.
function chainLength(start) {
  let n = start;
  let steps = 1;
  while (n !== 1) {
    if (n % 2 === 0) {
      n = n / 2;
    } else {
      n = 3 * n + 1;
    }
    steps++;
  }
  return steps;
}

function main() {
  const lines = [];
  let best = 0;
  let bestStart = 0;
  for (let i = 1; i < 1000000; i++) {
    const len = chainLength(i);
    if (len > best) {
      best = len;
      bestStart = i;
    }
  }
  lines.push(`${bestStart} ${best}`);
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
