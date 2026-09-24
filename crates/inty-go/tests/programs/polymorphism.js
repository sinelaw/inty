// Monomorphisation: every polymorphic function is emitted once per
// concrete instantiation that the program reaches.

// Plain parametric polymorphism.
function identity(x) {
  return x;
}
console.log(identity(42));
console.log(identity("forty-two"));
console.log(identity(true));

function first(xs) {
  return xs[0];
}
console.log(first([3, 1, 2]));
console.log(first(["c", "a", "b"]));

// Type-class polymorphism: `+` is addition for numbers, concatenation
// for strings.
function twice(x) {
  return x + x;
}
console.log(twice(21));
console.log(twice("ab"));

// Row polymorphism: works on any object with a numeric `x`.
function getX(p) {
  return p.x;
}
function point(x, y) {
  return { x: x, y: y };
}
const labelled = { x: 7, name: "seven", tags: ["odd", "prime"] };
console.log(getX(point(1, 2)) + getX(labelled));

// User-defined higher-order functions, used at several element types.
function mapAll(xs, f) {
  const out = [];
  for (const x of xs) {
    out.push(f(x));
  }
  return out;
}
function foldl(xs, f, acc) {
  let result = acc;
  for (let i = 0; i < xs.length; i++) {
    result = f(result, xs[i]);
  }
  return result;
}
const nums = [1, 2, 3, 4];
const words = mapAll(nums, (n) => `#${n}`);
console.log(words.join(" "));
console.log(foldl(nums, (a, b) => a + b, 0));
console.log(foldl(words, (a, b) => a + b, ""));
console.log(mapAll(words, (w) => w + "!").join(","));

// A polymorphic function passed as a value.
console.log(mapAll(words, identity).join("|"));

// Recursion inside a polymorphic function: the recursive call resolves
// to the same specialisation.
function lastFrom(xs, i) {
  if (i >= xs.length - 1) {
    return xs[i];
  }
  return lastFrom(xs, i + 1);
}
console.log(lastFrom([9, 8, 7], 0));
console.log(lastFrom(["x", "y", "z"], 1));

// Polymorphic `const` arrow functions.
const pair = (a, b) => ({ first: a, second: b });
const p1 = pair(1, "one");
const p2 = pair("two", 2);
console.log(`${p1.first} ${p1.second} ${p2.first} ${p2.second}`);

// A polymorphic closure declared inside another function.
function describe(n, s) {
  function wrap(v) {
    return [v, v];
  }
  const a = wrap(n);
  const b = wrap(s);
  return `${a.length + b.length}: ${a[0]} ${b[1]}`;
}
console.log(describe(5, "five"));

// Specialisations of a polymorphic function inside another polymorphic
// function follow the outer specialisation.
function both(x) {
  return pair(x, identity(x));
}
const b1 = both(1.5);
const b2 = both("s");
console.log(`${b1.first + b1.second} ${b2.first + b2.second}`);
