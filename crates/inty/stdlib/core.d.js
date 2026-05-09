// inty stdlib: core JavaScript built-ins.
//
// This file is embedded in the inty binary and auto-loaded before every
// user program. It is parsed and type-checked by inty but never executed
// by any JavaScript runtime, so it freely uses `const x;` without an
// initializer (a SyntaxError in real JS) to express external bindings.
//
// The polymorphic primitive constructors (`Array`, `String`, `Number`,
// `Boolean` used as functions) stay in Rust (`src/builtins/mod.rs`) so each
// lookup produces fresh type variables. Library-shaped bindings (Math,
// console, JSON, Object, Array statics, Promise helpers, parseInt/Float,
// isNaN/Finite) live here. Type variables in annotations are bound by an
// explicit `<T>` (or `<a, b>`, etc.) quantifier on the binding's scheme;
// each lookup re-instantiates fresh so different call sites don't share
// the variable.

/** const console: <T>{log: (T) => Undefined, error: (T) => Undefined, warn: (T) => Undefined} */
const console;

/** const Math: {PI: Number, E: Number, LN2: Number, LN10: Number, LOG2E: Number, LOG10E: Number, SQRT2: Number, abs: (Number) => Number, floor: (Number) => Number, ceil: (Number) => Number, round: (Number) => Number, trunc: (Number) => Number, sign: (Number) => Number, sqrt: (Number) => Number, cbrt: (Number) => Number, pow: (Number, Number) => Number, min: (Number, Number) => Number, max: (Number, Number) => Number, hypot: (Number, Number) => Number, log: (Number) => Number, log2: (Number) => Number, log10: (Number) => Number, exp: (Number) => Number, expm1: (Number) => Number, log1p: (Number) => Number, sin: (Number) => Number, cos: (Number) => Number, tan: (Number) => Number, asin: (Number) => Number, acos: (Number) => Number, atan: (Number) => Number, atan2: (Number, Number) => Number, sinh: (Number) => Number, cosh: (Number) => Number, tanh: (Number) => Number, random: () => Number, imul: (Number, Number) => Number, fround: (Number) => Number, clz32: (Number) => Number} */
const Math;

// `<T>` quantifies the scheme for the whole row, so each `JSON.parse(s)`
// and `JSON.stringify(x)` lookup re-instantiates `T` fresh. Round-tripping
// `JSON.stringify(JSON.parse(s))` in one expression still unifies the two
// instantiations through the value flowing between them.
/** const JSON: <T>{parse: (String) => T, stringify: (T) => String} */
const JSON;

// Object and Array static methods. `<a, b>` quantifies each annotation;
// every `Object.keys(...)` (etc.) call instantiates `a` and `b` fresh.
//
// These shadow the bare `Object` / `Array` constructors in the Rust initial
// env, which means `new Object()` / `new Array()` no longer type-check —
// use object/array literals (`{}` / `[]`) instead.
/** const Object: <a, b>{keys: (a) => String[], values: (a) => b[], entries: (a) => b[][], assign: (a, b) => a, fromEntries: (a[][]) => b} */
const Object;

/** const Array: <a, b>{isArray: (a) => Boolean, from: (a) => b[], of: (a) => a[]} */
const Array;

// Primitive constructors as callable rows. The keyless `(a) => T`
// signature inside the row is the call form (`String("hi")`); the
// other entries are the well-known statics. The unified callable-row
// design (examples/fizzy/design.md § "Callable rows") makes these
// first-class without a special case in the type system.
//
// `<T>` quantifies the polymorphic argument so each call site
// instantiates fresh. `String("hi")` types as String; `String(42)`
// types as String — both work because the call signature is
// `(T) => String` for some fresh T per use.

/** const String: <T> {
        (T) => String,
        fromCharCode: (Number) => String,
        fromCodePoint: (Number) => String
    } */
const String;

/** const Number: <T> {
        (T) => Number,
        isInteger: (Number) => Boolean,
        isFinite: (Number) => Boolean,
        isNaN: (Number) => Boolean,
        MAX_SAFE_INTEGER: Number,
        MIN_SAFE_INTEGER: Number,
        EPSILON: Number,
        MAX_VALUE: Number,
        MIN_VALUE: Number
    } */
const Number;

/** const Boolean: <T> {
        (T) => Boolean
    } */
const Boolean;

// Promise constructor helpers. `resolve` and `reject` are both
// polymorphic — each `Promise.resolve(x)` call instantiates T fresh —
// which is exactly what the async desugaring needs to wrap the result
// of an IIFE whose return type isn't known until inference finishes.
/** const Promise: <T, E>{resolve: (T) => Promise<T>, reject: (E) => Promise<T>, all: (Promise<T>[]) => Promise<T[]>} */
const Promise;

/** const parseInt: (String) => Number */
const parseInt;

/** const parseFloat: (String) => Number */
const parseFloat;

/** const isNaN: (Number) => Boolean */
const isNaN;

/** const isFinite: (Number) => Boolean */
const isFinite;

// Date constructor and prototype. Single pragmatic shape under the
// unified callable-row design — call/new with a Number (ms) and use
// the prototype methods via member access. Multi-arity construction
// (`new Date(y, m, d)`) and string parsing (`new Date("2024-01-01")`)
// aren't representable without overloading; users wrap those in a
// typed helper. The instance type is closed; `valueOf` / `getTime`
// give Number for arithmetic, `toISOString` / `toString` for display.
/** const Date: {
        (Number) => {
            getFullYear: () => Number,
            getMonth: () => Number,
            getDate: () => Number,
            getDay: () => Number,
            getHours: () => Number,
            getMinutes: () => Number,
            getSeconds: () => Number,
            getMilliseconds: () => Number,
            getTime: () => Number,
            getTimezoneOffset: () => Number,
            getUTCFullYear: () => Number,
            getUTCMonth: () => Number,
            getUTCDate: () => Number,
            getUTCHours: () => Number,
            valueOf: () => Number,
            toString: () => String,
            toISOString: () => String,
            toJSON: () => String,
            toDateString: () => String,
            toTimeString: () => String,
            toLocaleDateString: () => String,
            toLocaleTimeString: () => String,
            toLocaleString: () => String
        },
        now: () => Number,
        parse: (String) => Number,
        UTC: (Number) => Number
    } */
const Date;

// Base64 encoding/decoding. Web platform globals; Node has them since v16.
/** const atob: (String) => String */
const atob;

/** const btoa: (String) => String */
const btoa;
