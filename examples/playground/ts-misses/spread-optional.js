// An optional field may hold `undefined`, and spreading it writes the
// `undefined` over the default before it. TypeScript types the result's
// field as `number` all the same: with full JSDoc types and `--strict`,
// tsc accepts this, and at runtime `cfg.retries` is undefined.
//
// Inty: the spread's field is `Number | Undefined`, the optional field's
// type.

/** type Opts = {retries: Number?} */

/** const userOpts: Opts */
const userOpts = { retries: undefined };

const cfg = { retries: 3, ...userOpts };
console.log(cfg.retries.toFixed());
// Inty: 'toFixed' not found in Number | Undefined: the value may be undefined.
