// Without annotations, TypeScript quietly widens this literal to
// `(string | number)[]`. In a plain .js file nothing is reported at
// all, and the mix only surfaces when an element is used as the
// wrong type at runtime.
//
// Inty doesn't guess unions. An array whose elements disagree is an
// error right at the literal:

var items = [1, "two", 3, "four"];
//          ^^^^^^^^^^^^^^^^^^^^^
// Inty: Array elements have different types: Number and String.

// If the mix is intended, declare it (see unions.js):
//   /** var items: (Number | String)[] */
//   var items = [1, "two", 3, "four"];
