// Postfix `T?` desugars to `T | Undefined`.
// Composes with the existing union machinery — `??`, narrowing.

var arr = [1, 2, 3];
var v   = arr.find(function(n) { return n > 0; });   // Number | Undefined

// Defaulting:
var pick = v ?? 0;                                    // Number

// Narrowing:
var safe = (typeof v === "undefined") ? 0 : v;       // Number
