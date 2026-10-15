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

// Up to five values of any types per call (there are no variadic
// function types; a call with more is an arity error).
/** const console: <A, B, C, D, E>{
        log: (a: A, b?: B, c?: C, d?: D, e?: E) => Undefined,
        error: (a: A, b?: B, c?: C, d?: D, e?: E) => Undefined,
        warn: (a: A, b?: B, c?: C, d?: D, e?: E) => Undefined,
        info: (a: A, b?: B, c?: C, d?: D, e?: E) => Undefined,
        debug: (a: A, b?: B, c?: C, d?: D, e?: E) => Undefined
    } */
const console;

/** const Math: {PI: Number, E: Number, LN2: Number, LN10: Number, LOG2E: Number, LOG10E: Number, SQRT2: Number, abs: (Number) => Number, floor: (Number) => Number, ceil: (Number) => Number, round: (Number) => Number, trunc: (Number) => Number, sign: (Number) => Number, sqrt: (Number) => Number, cbrt: (Number) => Number, pow: (Number, Number) => Number, min: (Number, Number) => Number, max: (Number, Number) => Number, hypot: (Number, Number) => Number, log: (Number) => Number, log2: (Number) => Number, log10: (Number) => Number, exp: (Number) => Number, expm1: (Number) => Number, log1p: (Number) => Number, sin: (Number) => Number, cos: (Number) => Number, tan: (Number) => Number, asin: (Number) => Number, acos: (Number) => Number, atan: (Number) => Number, atan2: (Number, Number) => Number, sinh: (Number) => Number, cosh: (Number) => Number, tanh: (Number) => Number, random: () => Number, imul: (Number, Number) => Number, fround: (Number) => Number, clz32: (Number) => Number} */
const Math;

// High-resolution monotonic clock (milliseconds), as in browsers and Node.
/** const performance: {now: () => Number} */
const performance;

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
// `values`, `entries` and `fromEntries` work on a `Dict<V>` (a plain
// object used as a map; an object literal passed to them is one).
/** const Object: <a, b, v>{
        keys: (a) => String[],
        values: (Dict<v>) => v[],
        entries: (Dict<v>) => [String, v][],
        fromEntries: ([String, v][]) => Dict<v>,
        assign: (a, b) => a,
        freeze: (a) => a
    } */
const Object;

// `new Array(n)` / `Array(n)` make an array of `n` holes. A hole reads
// as `undefined`, which no element type admits, so the result is not an
// array: it has a `length` and `fill(v)`, which replaces every hole and
// gives the `v[]`. (`fill(v, start)` would leave holes, so it has no
// type; nor has `Array(x)` with a non-integer, which makes `[x]`.)
// A stored `const h = new Array(n)` has one element type, like any
// other binding of a call's result (the value restriction).
// `Array.from(it)` iterates `it`; a call with a map function,
// `Array.from(it, (x, i) => …)`, is typed by its own rule (its result
// depends on whether the map function is passed), which also takes an
// array-like `{length: n}` (with `undefined` elements).
/** const Array: <a, b, c, d> where Iterable b d => {
        (Number) => {length: Number, fill: (c) => c[]},
        isArray: (a) => Boolean,
        from: (b) => d[],
        of: (a) => a[]
    } */
const Array;

// Raw binary data, as `fetch`, `WebSocket` and WebAssembly memory hand
// it out; read and write it through a typed-array view.
/** type ArrayBuffer = {byteLength: Number, slice: (begin: Number, end?: Number) => ArrayBuffer} */
/** const ArrayBuffer: (Number) => ArrayBuffer */
const ArrayBuffer;

// Typed arrays: fixed-length arrays of one machine number type. An
// integer array stores a number as JavaScript does, wrapping it to its
// bits (see `TypedArrayKind::element`). A length makes a zeroed array;
// `from` copies an ordinary array. (A view of an `ArrayBuffer`,
// `new Float32Array(buffer, offset, length)`, would make the argument
// `Number | ArrayBuffer`, which an unannotated argument can't pick between;
// declare such a view in a typed FFI module — docs/patterns.md.)
/** const Int32Array: {(Number) => Int32Array, from: (Number[]) => Int32Array} */
const Int32Array;
/** const Uint8Array: {(Number) => Uint8Array, from: (Number[]) => Uint8Array} */
const Uint8Array;
/** const Float32Array: {(Number) => Float32Array, from: (Number[]) => Float32Array} */
const Float32Array;
/** const Float64Array: {(Number) => Float64Array, from: (Number[]) => Float64Array} */
const Float64Array;

// WebAssembly. A module's exports are whatever the program says they
// are (`E`): annotate the result of `instantiate` where it is used.
/** type WebAssemblyMemory = {buffer: ArrayBuffer, grow: (Number) => Number} */
/** const WebAssembly: <E, I>{
        instantiate: (bytes: ArrayBuffer | Uint8Array, imports?: I) => Promise<{instance: {exports: E}, module: {}}>,
        Memory: (descriptor: {initial: Number, maximum?: Number}) => WebAssemblyMemory,
        validate: (ArrayBuffer | Uint8Array) => Boolean
    } */
const WebAssembly;

// A deep copy of a value (the structured-clone algorithm).
/** const structuredClone: <T>(T) => T */
const structuredClone;

/** const queueMicrotask: (() => Undefined) => Undefined */
const queueMicrotask;

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

/** const parseInt: (s: String, radix?: Number) => Number */
const parseInt;

/** const parseFloat: (String) => Number */
const parseFloat;

/** const isNaN: (Number) => Boolean */
const isNaN;

/** const isFinite: (Number) => Boolean */
const isFinite;

// Date constructor and prototype. Single pragmatic shape under the
// unified callable-row design — call/new with no argument (now) or a
// Number (ms) and use
// the prototype methods via member access. Multi-arity construction
// (`new Date(y, m, d)`) and string parsing (`new Date("2024-01-01")`)
// aren't representable without overloading; users wrap those in a
// typed helper. The instance type is closed; `valueOf` / `getTime`
// give Number for arithmetic, `toISOString` / `toString` for display.
/** const Date: {
        (ms?: Number) => {
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

// Numeric constants and globals. `undefined` is already bound in the
// Rust initial env (builtins/mod.rs) but `NaN` and `Infinity` are not.
/** const NaN: Number */
const NaN;

/** const Infinity: Number */
const Infinity;

// Error constructors. The standard JS Error hierarchy collapses to a
// single shape here because inty has no nominal types — every Error
// instance has the same `name` / `message` / `stack` row. Callers can
// still throw and catch any of them; they unify structurally.
/** const Error: <T>(String) => {name: String, message: String, stack: String} */
const Error;

/** const TypeError: <T>(String) => {name: String, message: String, stack: String} */
const TypeError;

/** const RangeError: <T>(String) => {name: String, message: String, stack: String} */
const RangeError;

/** const SyntaxError: <T>(String) => {name: String, message: String, stack: String} */
const SyntaxError;

/** const ReferenceError: <T>(String) => {name: String, message: String, stack: String} */
const ReferenceError;

// RegExp constructor. Returns the primitive `Regex` type, which inty
// already understands (`/foo/g` literals carry it natively). The two-
// argument form covers both `new RegExp(pattern)` and `new RegExp(pat, flags)`
// — for the one-argument call, callers pass `""` (empty flags).
/** const RegExp: (String, String) => Regex */
const RegExp;

// Keyed collections. Map and Set are widely used in htmx-class code
// for caching and deduplication; WeakMap is used for DOM-keyed metadata.
// `<K, V>` quantifies fresh per construction.
// `Map<K, V>` and `Set<T>` also name the instance types in annotations.
/** type Map<K, V> = {
        get: (this: Map<K, V>, K) => V,
        set: (this: Map<K, V>, K, V) => Undefined,
        has: (this: Map<K, V>, K) => Boolean,
        delete: (this: Map<K, V>, K) => Boolean,
        clear: (this: Map<K, V>) => Undefined,
        forEach: (this: Map<K, V>, (V, K) => Undefined) => Undefined,
        keys: (this: Map<K, V>) => {[Symbol.iterator]: K},
        values: (this: Map<K, V>) => {[Symbol.iterator]: V},
        entries: (this: Map<K, V>) => {[Symbol.iterator]: [K, V]},
        size: Number,
        proto readonly [Symbol.iterator]: [K, V]
    } */
/** type Set<T> = {
        add: (this: Set<T>, T) => Undefined,
        has: (this: Set<T>, T) => Boolean,
        delete: (this: Set<T>, T) => Boolean,
        clear: (this: Set<T>) => Undefined,
        forEach: (this: Set<T>, (T) => Undefined) => Undefined,
        values: (this: Set<T>) => {[Symbol.iterator]: T},
        size: Number,
        proto readonly [Symbol.iterator]: T
    } */
// `new Map(entries?)`, `new Set(items?)`: from any iterable of `[K, V]`
// pairs, of items (an array, a string, another set, …).
/** const Map: <K, V, I> where Iterable I [K, V] => (entries?: I) => Map<K, V> */
const Map;

/** const Set: <T, I> where Iterable I T => (items?: I) => Set<T> */
const Set;

/** type WeakMap<K, V> = {
        get: (this: WeakMap<K, V>, K) => V,
        set: (this: WeakMap<K, V>, K, V) => Undefined,
        has: (this: WeakMap<K, V>, K) => Boolean,
        delete: (this: WeakMap<K, V>, K) => Boolean
    } */
/** const WeakMap: <K, V>() => WeakMap<K, V> */
const WeakMap;

/** type WeakSet<T> = {
        add: (this: WeakSet<T>, T) => Undefined,
        has: (this: WeakSet<T>, T) => Boolean,
        delete: (this: WeakSet<T>, T) => Boolean
    } */
/** const WeakSet: <T>() => WeakSet<T> */
const WeakSet;

// Proxy. The handler shape is opaque (H) — modelling all the trap
// signatures correctly requires variadic arguments and self-reference,
// neither of which inty has. The result row is whatever T the target
// already had, since Proxy is supposed to be transparent.
/** const Proxy: <T, H>(T, H) => T */
const Proxy;

// URI encode/decode. Web platform globals.
/** const encodeURIComponent: (String) => String */
const encodeURIComponent;

/** const decodeURIComponent: (String) => String */
const decodeURIComponent;

/** const encodeURI: (String) => String */
const encodeURI;

/** const decodeURI: (String) => String */
const decodeURI;

// Dynamic-evaluation primitives. inty can't type their effects beyond
// "returns something" — callers carry the burden.
/** const eval: <T>(String) => T */
const eval;

/** const Function: <T>(String) => T */
const Function;
