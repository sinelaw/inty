// JSDoc `@type` annotations on object-literal fields.
//
// A widespread JS pattern (popularised by htmx, jQuery, lodash):
// declare a public-API object with `null`-initialised fields, then
// fill them in with forward-declared helpers. `@type {typeof helper}`
// tells the type checker what type the field will end up holding —
// the `null` is just a placeholder, not the real value.

const api = {
    /** @type {typeof greet} */
    greet: null,
    /** @type {typeof add} */
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

// `api.greet` is typed as `(String) => String`, not `Null`, because
// of the `@type` annotation.
var msg = api.greet("world");
var n   = api.add(1, 2);

// The `enabled` field is `Boolean` (not the literal `true`).
var on  = api.enabled && true;

// A non-placeholder value still type-checks against the annotation:
// uncomment the next line to see the error.
// var bad = { /** @type {Number} */ count: "oops" }; // error!
