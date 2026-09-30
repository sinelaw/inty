class Box { constructor(v) { this.v = v; } }
class Pair { constructor(a, b) { this.a = a; this.b = b; } }
function either(flag, x) {
  const made = flag ? new Box(x) : new Pair(x, "y");
  return made;
}
