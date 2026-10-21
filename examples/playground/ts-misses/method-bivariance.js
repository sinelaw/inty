// TypeScript checks method parameters bivariantly: a handler declared as
// taking `number | string` may be implemented by a method that only takes
// a `number`. With full JSDoc types and `--strict`, tsc accepts this, and
// at runtime `v.toFixed` is not a function.
//
// Inty: a function's parameters are checked one way only, whether it is
// written as a method or not. The handler doesn't fit the type.

/** type Handler = {handle: (Number | String) => String} */

/** const handler: Handler */
const handler = { handle(v) { return v.toFixed(2); } };
// Inty: Property 'toFixed' not found in type String.

handler.handle("abc");
