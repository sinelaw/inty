// TypeScript checks for extra properties only on an object literal
// written in place. Passed through a variable, a misspelled field is
// silently dropped: tsc accepts this with full JSDoc types and
// `--strict`, and at runtime the age is lost, so this prints "Ann (0)".
//
// Inty's records are closed: `{name, agee}` is not a `{name, age?}`.

/** function show(p: {name: String, age: Number?}) => String */
function show(p) { return p.name + " (" + String(p.age ?? 0) + ")"; }

const input = { name: "Ann", agee: 30 };
console.log(show(input));
// Inty: expected '{age: Number | Undefined, name: String}',
//       found '{agee: Number, name: String}'.
