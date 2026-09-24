// Conway's Game of Life on a 1024x1024 torus — the core loop of any
// cellular-automaton / image-kernel workload: dense boolean grids and
// neighbour lookups. Prints the live-cell count every 25 generations.
const W = 1024;
const H = 1024;

// Deterministic Park–Miller PRNG so JS and Go see the same board.
let seed = 42;
function random() {
  seed = (seed * 16807) % 2147483647;
  return seed / 2147483647;
}

function makeGrid() {
  const g = [];
  for (let i = 0; i < W * H; i++) {
    g.push(false);
  }
  return g;
}

function step(cur, next) {
  for (let y = 0; y < H; y++) {
    const up = y === 0 ? H - 1 : y - 1;
    const down = y === H - 1 ? 0 : y + 1;
    for (let x = 0; x < W; x++) {
      const left = x === 0 ? W - 1 : x - 1;
      const right = x === W - 1 ? 0 : x + 1;
      let n = 0;
      if (cur[up * W + left]) n++;
      if (cur[up * W + x]) n++;
      if (cur[up * W + right]) n++;
      if (cur[y * W + left]) n++;
      if (cur[y * W + right]) n++;
      if (cur[down * W + left]) n++;
      if (cur[down * W + x]) n++;
      if (cur[down * W + right]) n++;
      const alive = cur[y * W + x];
      next[y * W + x] = n === 3 || (alive && n === 2);
    }
  }
}

function population(g) {
  let count = 0;
  for (let i = 0; i < g.length; i++) {
    if (g[i]) count++;
  }
  return count;
}

function main() {
  seed = 42;
  const lines = [];
  let a = makeGrid();
  let b = makeGrid();
  for (let i = 0; i < W * H; i++) {
    a[i] = random() < 0.3;
  }
  for (let gen = 1; gen <= 50; gen++) {
    step(a, b);
    const t = a;
    a = b;
    b = t;
    if (gen % 25 === 0) {
      lines.push(`generation ${gen}: ${population(a)} alive`);
    }
  }
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
