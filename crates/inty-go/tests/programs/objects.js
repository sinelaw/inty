// Objects become structs; arrays become slices behind a pointer.
function point(x, y) {
  return { x: x, y: y };
}

function norm2(p) {
  return p.x * p.x + p.y * p.y;
}

const pts = [point(1, 2), point(3, 4)];
pts.push(point(5, 6));
let s = 0;
for (const p of pts) {
  s += norm2(p);
}
console.log(s);
pts[0].x = 10;
console.log(pts[0].x + pts.length);

const alias = pts;
alias.push(point(0, 0));
console.log(pts.length);

const grid = [];
for (let i = 0; i < 3; i++) {
  grid.push([i, i * 2, i * 3]);
}
console.log(grid[2][1]);
const filled = [];
filled[0] = 1;
filled[1] = 2;
console.log(filled.join("-"));

let last = pts.pop();
console.log(last.x + last.y);
console.log(pts.indexOf(pts[1]));
