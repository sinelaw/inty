// Log analytics: generate ~40 MB of web-server access logs as text,
// then parse them byte by byte (no regexes, no split) and aggregate
// status codes, bytes served, latency percentiles and the busiest
// paths — what a log shipper or a metrics sidecar does all day.
let seed = 2024;
function rand() {
  seed = (seed * 16807) % 2147483647;
  return seed / 2147483647;
}

const PATHS = ["/", "/login", "/api/items", "/api/cart", "/static/app.js", "/static/app.css", "/search", "/checkout"];
const STATUS = [200, 200, 200, 200, 200, 304, 301, 404, 500, 200];

/** function parseIntAt(String, Int) => Int */
function parseIntAt(s, i) {
  let n = 0;
  let c = s.charCodeAt(i);
  while (c >= 48 && c <= 57) {
    n = n * 10 + (c - 48);
    i++;
    c = s.charCodeAt(i);
  }
  return n;
}

/** function skipPast(String, Int, Int) => Int */
function skipPast(s, i, ch) {
  while (s.charCodeAt(i) !== ch) {
    i++;
  }
  return i + 1;
}

/** function percentile(Number[], Number, Number) => Int */
function percentile(buckets, total, q) {
  let seen = 0;
  for (let i = 0; i < buckets.length; i++) {
    seen += buckets[i];
    if (seen >= total * q) {
      return i;
    }
  }
  return buckets.length - 1;
}

function main() {
  seed = 2024;
  const lines = [];
  const parts = [];
  for (let i = 0; i < 400000; i++) {
    const ip = `10.${Math.floor(rand() * 256)}.${Math.floor(rand() * 256)}.${Math.floor(rand() * 256)}`;
    const path = PATHS[Math.floor(rand() * PATHS.length)];
    const status = STATUS[Math.floor(rand() * STATUS.length)];
    const bytes = Math.floor(rand() * 50000);
    const ms = Math.floor(rand() * rand() * 2000);
    parts.push(`${ip} - - [24/Sep/2026:10:00:00 +0000] "GET ${path} HTTP/1.1" ${status} ${bytes} ${ms}ms\n`);
  }
  const text = parts.join("");

  const statusCounts = [];
  const latencyBuckets = [];
  for (let i = 0; i < 600; i++) {
    statusCounts.push(0);
  }
  for (let i = 0; i < 2001; i++) {
    latencyBuckets.push(0);
  }
  const pathHits = [];
  const pathBytes = [];
  for (let i = 0; i < PATHS.length; i++) {
    pathHits.push(0);
    pathBytes.push(0);
  }

  let lineCount = 0;
  let totalBytes = 0;
  let pos = 0;
  const QUOTE = 34;
  const SPACE = 32;
  const NEWLINE = 10;
  while (pos < text.length) {
    pos = skipPast(text, pos, QUOTE);
    pos = skipPast(text, pos, SPACE);
    const pathStart = pos;
    pos = skipPast(text, pos, SPACE);
    const path = text.substring(pathStart, pos - 1);
    pos = skipPast(text, pos, QUOTE);
    pos++;
    const status = parseIntAt(text, pos);
    pos = skipPast(text, pos, SPACE);
    const bytes = parseIntAt(text, pos);
    pos = skipPast(text, pos, SPACE);
    const ms = parseIntAt(text, pos);
    pos = skipPast(text, pos, NEWLINE);

    lineCount++;
    totalBytes += bytes;
    statusCounts[status]++;
    latencyBuckets[ms]++;
    const p = PATHS.indexOf(path);
    pathHits[p]++;
    pathBytes[p] += bytes;
  }

  lines.push(`parsed ${lineCount} lines, ${text.length} bytes of log`);
  lines.push(`bytes served: ${totalBytes}`);
  lines.push(`2xx ${statusCounts[200]}  3xx ${statusCounts[301] + statusCounts[304]}  4xx ${statusCounts[404]}  5xx ${statusCounts[500]}`);
  lines.push(`latency p50 ${percentile(latencyBuckets, lineCount, 0.5)}ms  p90 ${percentile(latencyBuckets, lineCount, 0.9)}ms  p99 ${percentile(latencyBuckets, lineCount, 0.99)}ms`);
  for (let i = 0; i < PATHS.length; i++) {
    lines.push(`${PATHS[i]}: ${pathHits[i]} hits, ${pathBytes[i]} bytes`);
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
