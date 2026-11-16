// JSDoc `@type` annotations on object-literal fields.
//
// A widespread JS pattern (popularised by htmx, jQuery, lodash):
// declare a public-API object with `null`-initialised fields, then
// fill them in with forward-declared helpers. `@type {typeof helper}`
// tells the type checker what type the field holds. The initialiser
// is checked against it, as a `const`'s is: a field that starts as
// `null` says so, `(typeof helper) | Null`, and is tested before a
// call, since calling it before it is filled in would throw.

const api = {
    /** @type {(typeof greet) | Null} */
    greet: null,
    /** @type {(typeof add) | Null} */
    add: null,

    // The bare form `@type T` (no braces) is also accepted —
    // this is the older JSDoc convention.
    /**
     * @type Boolean
     * @default true
     */
    enabled: true,
};

// Helpers declared *after* the object literal — function declarations
// hoist (via SCC analysis), so `typeof greet` works above.
function greet(name) { return "Hello, " + name; }
function add(x, y)   { return x + y; }

// Late assignment fills in the placeholders.
api.greet = greet;
api.add   = add;

// `api.greet` is `((String) => String) | Null`, from the `@type`
// annotation: copy it into a const and test that before calling.
const g = api.greet;
var msg = g ? g("world") : "";
const a = api.add;
var n   = a ? a(1, 2) : 0;

// The `enabled` field is `Boolean` (not the literal `true`).
var on  = api.enabled && true;

// The initialiser is checked against the annotation: uncomment the
// next line to see the error.
// var bad = { /** @type {() => String} */ f: null }; // error!
