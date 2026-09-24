// Functions are hoisted above the top-level constants they read. inty
// infers them first and records a structural view of those constants
// at the use site (e.g. `{length: Number | r}`); the Go types must still
// come from the declarations.
function pick(i) {
  return NAMES[i % NAMES.length];
}

function count() {
  return WEIGHTS.length;
}

const NAMES = ["alpha", "beta", "gamma"];
const WEIGHTS = [0.5, 1.5, 2.5, 3.5];
for (let i = 0; i < 5; i++) {
  console.log(pick(i));
}
console.log(count());
