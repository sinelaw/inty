// minfern stdlib: core JavaScript built-ins.
//
// This file is embedded in the minfern binary and auto-loaded before every
// user program. It is parsed and type-checked by minfern but never executed
// by any JavaScript runtime, so it freely uses `const x;` without an
// initializer (a SyntaxError in real JS) to express external bindings.
//
// The polymorphic primitive constructors (`Array`, `String`, `Number`,
// `Boolean` used as functions) stay in Rust (`src/builtins/mod.rs`) so each
// lookup produces fresh type variables — minfern's handling of polymorphic
// types inside annotation-declared schemes doesn't yet re-instantiate on
// every use. Library-shaped bindings (Math, console, JSON, Object, Array
// statics, Promise helpers, parseInt/Float, isNaN/Finite) live here.
// Bindings declared with type variables in this file (`JSON.parse`,
// `Object.keys`, `Promise.resolve`, etc.) share that variable across every
// call site rather than instantiating fresh — see the per-binding notes
// below for the consequences.

/** const console: {log: (T) => Undefined, error: (T) => Undefined, warn: (T) => Undefined} */
const console;

/** const Math: {PI: Number, E: Number, LN2: Number, LN10: Number, LOG2E: Number, LOG10E: Number, SQRT2: Number, abs: (Number) => Number, floor: (Number) => Number, ceil: (Number) => Number, round: (Number) => Number, trunc: (Number) => Number, sign: (Number) => Number, sqrt: (Number) => Number, cbrt: (Number) => Number, pow: (Number, Number) => Number, min: (Number, Number) => Number, max: (Number, Number) => Number, hypot: (Number, Number) => Number, log: (Number) => Number, log2: (Number) => Number, log10: (Number) => Number, exp: (Number) => Number, expm1: (Number) => Number, log1p: (Number) => Number, sin: (Number) => Number, cos: (Number) => Number, tan: (Number) => Number, asin: (Number) => Number, acos: (Number) => Number, atan: (Number) => Number, atan2: (Number, Number) => Number, sinh: (Number) => Number, cosh: (Number) => Number, tanh: (Number) => Number, random: () => Number, imul: (Number, Number) => Number, fround: (Number) => Number, clz32: (Number) => Number} */
const Math;

// parse and stringify share the same type variable T within this annotation,
// so `JSON.stringify(JSON.parse(s))` threads a consistent round-trip type.
// They are not truly polymorphic (each lookup does not re-instantiate), but
// this matches the prior behaviour when JSON was defined in Rust.
/** const JSON: {parse: (String) => T, stringify: (T) => String} */
const JSON;

// Object and Array static methods. The inner `a` is a fresh type variable
// scoped to each annotation, so `const Object` binds a polymorphic scheme
// and each `Object.keys(...)` call instantiates `a` fresh.
//
// These shadow the bare `Object` / `Array` constructors in the Rust initial
// env, which means `new Object()` / `new Array()` no longer type-check —
// use object/array literals (`{}` / `[]`) instead.
/** const Object: {keys: (a) => String[]} */
const Object;

/** const Array: {isArray: (a) => Boolean} */
const Array;

// Promise constructor helpers. `resolve` and `reject` are both
// polymorphic — each `Promise.resolve(x)` call instantiates T fresh —
// which is exactly what the async desugaring needs to wrap the result
// of an IIFE whose return type isn't known until inference finishes.
/** const Promise: {resolve: (T) => Promise<T>, reject: (E) => Promise<T>, all: (Promise<T>[]) => Promise<T[]>} */
const Promise;

/** const parseInt: (String) => Number */
const parseInt;

/** const parseFloat: (String) => Number */
const parseFloat;

/** const isNaN: (Number) => Boolean */
const isNaN;

/** const isFinite: (Number) => Boolean */
const isFinite;
