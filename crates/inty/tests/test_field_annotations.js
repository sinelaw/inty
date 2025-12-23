// Per-field inline type annotations on object literal properties.
// `key /*: T */: value` parses the annotation as attached to `key` and
// unifies T with value's inferred type.

// Typical use: seed a typed empty collection inside a state object.
let state = {
    todos  /*: {id: Number, text: String, done: Boolean}[] */: [],
    nextId /*: Number */: 1,
    filter /*: String */: "all"
};

state.todos.push({id: 1, text: "hello", done: false});
let first = state.todos[0];
let greeting = first.text + "!";       // first.text is String
let n = state.nextId + 1;              // Number
let f = state.filter;                  // String

// Annotation and value disagreement is caught.
function tryIt() {
    // Uncommenting the next line should fail type-checking:
    // let bad = { count /*: Number */: "oops" };
    return 0;
}

// Per-field annotations compose with polymorphism: each field is typed
// independently from the others.
let config = {
    name       /*: String */: "demo",
    retries    /*: Number */: 3,
    enabled    /*: Boolean */: true,
    tags       /*: String[] */: [],
    buckets    /*: Number[] */: []
};

config.tags.push("alpha");
config.tags.push("beta");
config.buckets.push(10);
let tagCount = config.tags.length;
let label = `${config.name} x${config.buckets.length}`;
