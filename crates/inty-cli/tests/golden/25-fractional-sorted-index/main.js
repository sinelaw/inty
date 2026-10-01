const TABLE = ["C", "D"];
function low(xs) {
  const sorted = xs.slice().sort((a, b) => a - b);
  return TABLE[sorted[0] % 2];
}
const r = low([64.5, 60]);
