// In JavaScript, `||` returns one of its operands — not a boolean.
// So `0 || "Guest"` evaluates to "Guest" and the variable's type
// silently widens to `Number | String`.
//
// TypeScript: tolerates the union without complaint.
// Inty: infers `label(String) => String` — calling with a Number
// fails at the call site, not silently inside the body.

function label(n) {
    var name = n || "Guest";        // n: Number, fallback: String — mismatch
    return name;
}

// Pass a Number to expose the bug:
// var r = label(3);   // error!

// Fix: make the default match the type, or convert explicitly.
//   var name = n === 0 ? "Guest" : String(n);
