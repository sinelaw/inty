// A small Whitted-style ray tracer: spheres, a checkered floor plane,
// diffuse + specular shading, hard shadows and recursive reflections.
// Renders 1280x960 and prints a checksum and a few pixel samples.
// Vector math on short-lived {x, y, z} objects throughout.
function vec(x, y, z) {
  return { x: x, y: y, z: z };
}
function add(a, b) {
  return vec(a.x + b.x, a.y + b.y, a.z + b.z);
}
function sub(a, b) {
  return vec(a.x - b.x, a.y - b.y, a.z - b.z);
}
function scale(a, s) {
  return vec(a.x * s, a.y * s, a.z * s);
}
function mul(a, b) {
  return vec(a.x * b.x, a.y * b.y, a.z * b.z);
}
function dot(a, b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}
function norm(a) {
  return scale(a, 1 / Math.sqrt(dot(a, a)));
}

function sphere(cx, cy, cz, r, color, reflect) {
  return { center: vec(cx, cy, cz), radius: r, color: color, reflect: reflect };
}

const spheres = [
  sphere(0, 1, 5, 1, vec(0.9, 0.2, 0.2), 0.3),
  sphere(-2.2, 0.8, 6, 0.8, vec(0.2, 0.9, 0.3), 0.2),
  sphere(2.2, 1.2, 6.5, 1.2, vec(0.3, 0.4, 0.95), 0.5),
  sphere(0.8, 0.35, 3.2, 0.35, vec(0.95, 0.85, 0.2), 0.1),
  sphere(-0.9, 0.3, 3.4, 0.3, vec(0.9, 0.9, 0.9), 0.7),
];
const light = vec(-4, 7, -2);
const INF = 1e30;

// Distance along the ray to the nearest sphere hit (or INF), and its index.
let hitIndex = -1;
function nearestSphere(orig, dir) {
  let best = INF;
  hitIndex = -1;
  for (let i = 0; i < spheres.length; i++) {
    const s = spheres[i];
    const oc = sub(orig, s.center);
    const b = dot(oc, dir);
    const c = dot(oc, oc) - s.radius * s.radius;
    const disc = b * b - c;
    if (disc > 0) {
      const sq = Math.sqrt(disc);
      let t = -b - sq;
      if (t < 1e-4) {
        t = -b + sq;
      }
      if (t > 1e-4 && t < best) {
        best = t;
        hitIndex = i;
      }
    }
  }
  return best;
}

function floorHit(orig, dir) {
  if (dir.y >= -1e-6) {
    return INF;
  }
  const t = -orig.y / dir.y;
  return t > 1e-4 ? t : INF;
}

function inShadow(p) {
  const toLight = sub(light, p);
  const dist = Math.sqrt(dot(toLight, toLight));
  const t = nearestSphere(p, scale(toLight, 1 / dist));
  return t < dist;
}

function shade(p, n, base, dir) {
  const l = norm(sub(light, p));
  const ambient = 0.08;
  if (inShadow(p)) {
    return scale(base, ambient);
  }
  const diffuse = Math.max(dot(n, l), 0);
  const refl = sub(l, scale(n, 2 * dot(n, l)));
  const spec = Math.pow(Math.max(dot(refl, dir), 0), 40);
  return add(scale(base, ambient + diffuse * 0.9), vec(spec, spec, spec));
}

function trace(orig, dir, depth) {
  const ts = nearestSphere(orig, dir);
  const si = hitIndex;
  const tf = floorHit(orig, dir);
  if (ts === INF && tf === INF) {
    const k = 0.5 * (dir.y + 1);
    return add(scale(vec(1, 1, 1), 1 - k), scale(vec(0.5, 0.7, 1), k));
  }
  let p = vec(0, 0, 0);
  let n = vec(0, 1, 0);
  let base = vec(0, 0, 0);
  let reflect = 0;
  if (ts < tf) {
    const s = spheres[si];
    p = add(orig, scale(dir, ts));
    n = norm(sub(p, s.center));
    base = s.color;
    reflect = s.reflect;
  } else {
    p = add(orig, scale(dir, tf));
    const check = (Math.floor(p.x) + Math.floor(p.z)) % 2 === 0;
    base = check ? vec(0.85, 0.85, 0.85) : vec(0.15, 0.15, 0.15);
    reflect = 0.25;
  }
  let color = shade(p, n, base, dir);
  if (depth < 4 && reflect > 0) {
    const r = sub(dir, scale(n, 2 * dot(dir, n)));
    color = add(scale(color, 1 - reflect), scale(trace(p, r, depth + 1), reflect));
  }
  return color;
}

function clamp(x) {
  return x < 0 ? 0 : x > 1 ? 1 : x;
}

function main() {
  const lines = [];
  const WIDTH = 1280;
  const HEIGHT = 960;
  const eye = vec(0, 1.4, -1.5);
  let checksum = 0;
  const samples = [];
  for (let y = 0; y < HEIGHT; y++) {
    for (let x = 0; x < WIDTH; x++) {
      const dx = ((x + 0.5) / WIDTH - 0.5) * 1.6;
      const dy = (0.5 - (y + 0.5) / HEIGHT) * 1.2;
      const c = trace(eye, norm(vec(dx, dy, 1)), 0);
      const r = Math.floor(clamp(c.x) * 255);
      const g = Math.floor(clamp(c.y) * 255);
      const b = Math.floor(clamp(c.z) * 255);
      checksum = (checksum * 31 + r * 65536 + g * 256 + b) % 1000000007;
      if (x === WIDTH / 2 && y % 192 === 0) {
        samples.push(`${r},${g},${b}`);
      }
    }
  }
  lines.push(`checksum ${checksum}`);
  lines.push(samples.join(" "));
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
