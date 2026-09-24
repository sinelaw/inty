// Sieve of Eratosthenes, repeated: array-of-booleans writes and reads
// with integer-valued indices.
function sieve(n) {
  const composite = [];
  for (let i = 0; i <= n; i++) {
    composite.push(false);
  }
  let count = 0;
  for (let i = 2; i <= n; i++) {
    if (!composite[i]) {
      count++;
      for (let j = i * i; j <= n; j += i) {
        composite[j] = true;
      }
    }
  }
  return count;
}

function main() {
  const lines = [];
  let total = 0;
  for (let round = 0; round < 10; round++) {
    total += sieve(2000000);
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
