// TypeScript reads a `Record<string, number>` at any key as a `number`
// (unless `noUncheckedIndexedAccess` is on, which `--strict` doesn't turn
// on). tsc accepts this, and at runtime `stock["pear"]` is undefined.
//
// Inty: a `Dict<V>` read gives `V | Undefined`, so the missing key must
// be handled (`?? 0`).

/** const stock: Dict<Number> */
const stock = { apple: 3 };

console.log(stock["pear"].toFixed());
// Inty: 'toFixed' not found in Number | Undefined: the value may be undefined.
//
// The fix:
//   console.log((stock["pear"] ?? 0).toFixed());
