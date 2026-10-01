const TABLE = ["C", "D"];
function h(o) {
  const d = o.a - o.b;
  return o.f(d);
}
const r = h({ a: 0.5, b: 1, f: (i) => TABLE[i] });
