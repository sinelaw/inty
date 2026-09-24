// Spectral norm (after the Computer Language Benchmarks Game): tight
// numeric loops over arrays of doubles plus a small hot helper function.
function a(i, j) {
  return 1 / (((i + j) * (i + j + 1)) / 2 + i + 1);
}

function multiplyAv(n, v, av) {
  for (let i = 0; i < n; i++) {
    let sum = 0;
    for (let j = 0; j < n; j++) {
      sum += a(i, j) * v[j];
    }
    av[i] = sum;
  }
}

function multiplyAtv(n, v, atv) {
  for (let i = 0; i < n; i++) {
    let sum = 0;
    for (let j = 0; j < n; j++) {
      sum += a(j, i) * v[j];
    }
    atv[i] = sum;
  }
}

function multiplyAtAv(n, v, out, tmp) {
  multiplyAv(n, v, tmp);
  multiplyAtv(n, tmp, out);
}

function zeros(n) {
  const xs = [];
  for (let i = 0; i < n; i++) {
    xs.push(0);
  }
  return xs;
}

function spectralNorm(n) {
  const u = zeros(n);
  for (let i = 0; i < n; i++) {
    u[i] = 1;
  }
  const v = zeros(n);
  const tmp = zeros(n);
  for (let i = 0; i < 10; i++) {
    multiplyAtAv(n, u, v, tmp);
    multiplyAtAv(n, v, u, tmp);
  }
  let vBv = 0;
  let vv = 0;
  for (let i = 0; i < n; i++) {
    vBv += u[i] * v[i];
    vv += v[i] * v[i];
  }
  return Math.sqrt(vBv / vv);
}

console.log(spectralNorm(3000));
