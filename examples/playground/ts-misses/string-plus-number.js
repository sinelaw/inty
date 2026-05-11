// TypeScript happily allows String + Number — JavaScript coerces,
// and so does the TS `+` rule. The intent is almost always wrong.
//
// Inty's `Plus` type class requires both operands to be the *same*
// instance: two Numbers, or two Strings. No silent coercion.

var count = 3;
var msg   = "Got " + count + " items";

// Inty: error — operands disagree.
// At runtime: "Got 3 items" (works by accident).
//
// The fix says what you mean:
//   var msg = "Got " + String(count) + " items";
