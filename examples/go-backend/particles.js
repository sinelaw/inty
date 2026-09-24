// Allocation heavy: every step builds fresh small {x, y} objects, most
// of them short-lived. Stresses the allocator and GC rather than
// arithmetic.
function vec(x, y) {
  return { x: x, y: y };
}

function add(a, b) {
  return vec(a.x + b.x, a.y + b.y);
}

function scale(a, s) {
  return vec(a.x * s, a.y * s);
}

function simulate(n, steps) {
  const pos = [];
  const vel = [];
  for (let i = 0; i < n; i++) {
    pos.push(vec(i, -i));
    vel.push(vec(1 + i / n, 0.5 - i / n));
  }
  for (let s = 0; s < steps; s++) {
    for (let i = 0; i < n; i++) {
      pos[i] = add(pos[i], scale(vel[i], 0.01));
    }
  }
  let sum = 0;
  for (let i = 0; i < n; i++) {
    sum += pos[i].x + pos[i].y;
  }
  return sum;
}

function main() {
  return String(simulate(1000, 20000));
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
