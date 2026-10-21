// A function is always truthy, so testing one instead of calling it
// always takes the same branch. TypeScript catches `if (isLocked)`
// directly, but not once the function is passed to a generic function
// that tests its argument: with full JSDoc types and `--strict`, tsc
// accepts this, and at runtime it prints "locked".
//
// Inty: a test needs its value to be `Testable`, any type but a
// function's. A function that tests its parameter says so in its type,
// `label: <a> where Testable a => (a) => String`, so passing it a function
// is rejected at the call.

function isLocked() { return false; }

function label(flag) { return flag ? "locked" : "open"; }

console.log(label(isLocked));
// Inty: Type '() => Boolean' is not an instance of Testable
//       (a function is always truthy ...: call it).
//
// The fix:
//   console.log(label(isLocked()));
