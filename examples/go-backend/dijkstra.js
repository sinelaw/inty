// Route planning: single-source shortest paths with Dijkstra's
// algorithm on a 700x700 road grid (490k intersections, ~2M directed
// edges) with random travel times, using a hand-written binary heap.
// Adjacency is stored CSR-style in flat number arrays, as a routing
// engine would.
const N = 700;
const V = N * N;

let seed = 12345;
function rand() {
  seed = (seed * 16807) % 2147483647;
  return seed / 2147483647;
}

// Build CSR adjacency: offsets[v]..offsets[v+1] index into targets/weights.
const offsets = [];
const targets = [];
const weights = [];
for (let v = 0; v < V; v++) {
  offsets.push(targets.length);
  const x = v % N;
  const y = (v - x) / N;
  if (x > 0) {
    targets.push(v - 1);
    weights.push(1 + Math.floor(rand() * 9));
  }
  if (x < N - 1) {
    targets.push(v + 1);
    weights.push(1 + Math.floor(rand() * 9));
  }
  if (y > 0) {
    targets.push(v - N);
    weights.push(1 + Math.floor(rand() * 9));
  }
  if (y < N - 1) {
    targets.push(v + N);
    weights.push(1 + Math.floor(rand() * 9));
  }
}
offsets.push(targets.length);

// Binary min-heap of (priority, vertex) pairs in two parallel arrays.
/** function heapPush(Number[], Int[], Number, Int) => Undefined */
function heapPush(heapKey, heapVal, k, v) {
  heapKey.push(k);
  heapVal.push(v);
  let i = heapKey.length - 1;
  while (i > 0) {
    const parent = Math.floor((i - 1) / 2);
    if (heapKey[parent] <= heapKey[i]) {
      break;
    }
    const tk = heapKey[parent];
    heapKey[parent] = heapKey[i];
    heapKey[i] = tk;
    const tv = heapVal[parent];
    heapVal[parent] = heapVal[i];
    heapVal[i] = tv;
    i = parent;
  }
}

// Removes the minimum; its vertex is returned, its key left in popKey.
let popKey = 0;
/** function heapPop(Number[], Int[]) => Int */
function heapPop(heapKey, heapVal) {
  const top = heapVal[0];
  popKey = heapKey[0];
  const lastK = heapKey.pop();
  const lastV = heapVal.pop();
  const n = heapKey.length;
  if (n > 0) {
    heapKey[0] = lastK;
    heapVal[0] = lastV;
    let i = 0;
    while (true) {
      const l = 2 * i + 1;
      const r = l + 1;
      let m = i;
      if (l < n && heapKey[l] < heapKey[m]) {
        m = l;
      }
      if (r < n && heapKey[r] < heapKey[m]) {
        m = r;
      }
      if (m === i) {
        break;
      }
      const tk = heapKey[m];
      heapKey[m] = heapKey[i];
      heapKey[i] = tk;
      const tv = heapVal[m];
      heapVal[m] = heapVal[i];
      heapVal[i] = tv;
      i = m;
    }
  }
  return top;
}

function shortestPaths(source, dist) {
  const heapKey = [];
  const heapVal = [];
  for (let v = 0; v < V; v++) {
    dist[v] = Infinity;
  }
  dist[source] = 0;
  heapPush(heapKey, heapVal, 0, source);
  let settled = 0;
  while (heapKey.length > 0) {
    const u = heapPop(heapKey, heapVal);
    const d = popKey;
    if (d > dist[u]) {
      continue;
    }
    settled++;
    for (let e = offsets[u]; e < offsets[u + 1]; e++) {
      const v = targets[e];
      const nd = d + weights[e];
      if (nd < dist[v]) {
        dist[v] = nd;
        heapPush(heapKey, heapVal, nd, v);
      }
    }
  }
  return settled;
}

function main() {
  const lines = [];
  const dist = [];
  for (let v = 0; v < V; v++) {
    dist.push(0);
  }
  const sources = [0, V - 1, Math.floor(V / 2) + Math.floor(N / 3)];
  for (const s of sources) {
    const settled = shortestPaths(s, dist);
    let far = 0;
    let sum = 0;
    for (let v = 0; v < V; v++) {
      far = Math.max(far, dist[v]);
      sum += dist[v];
    }
    lines.push(`source ${s}: settled ${settled}, farthest ${far}, mean ${Math.round(sum / V)}`);
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
