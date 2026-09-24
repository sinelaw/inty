// Mandelbrot set: counts points that stay bounded. Pure double
// arithmetic in nested loops with an early exit.
function mandelbrot(size, maxIter) {
  let inside = 0;
  for (let py = 0; py < size; py++) {
    const ci = (2 * py) / size - 1;
    for (let px = 0; px < size; px++) {
      const cr = (2 * px) / size - 1.5;
      let zr = 0;
      let zi = 0;
      let i = 0;
      while (i < maxIter && zr * zr + zi * zi <= 4) {
        const t = zr * zr - zi * zi + cr;
        zi = 2 * zr * zi + ci;
        zr = t;
        i++;
      }
      if (i === maxIter) {
        inside++;
      }
    }
  }
  return inside;
}

function main() {
  return String(mandelbrot(2000, 200));
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
