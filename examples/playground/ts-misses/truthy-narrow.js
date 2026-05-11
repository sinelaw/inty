// JavaScript treats 0, "", NaN, null, undefined all as falsy.
// TypeScript's narrowing on `if (x)` doesn't distinguish between
// "missing" and "empty/zero" — easy bug.

function priceLabel(price) {
    if (price) { return "$" + price; }
    else       { return "free"; }
}

// Inty infers `priceLabel(String) => String` — the `+` inside fixes
// `price` to a String. Calling with the literal `0` then errors at
// the call site:
// var lbl = priceLabel(0);   // error!
//
// In TS, calling this with the literal `0` is fine — and silently
// returns "free" for a perfectly valid price of zero.
//
// The deeper fix — explicit `price === undefined` narrowing — is
// enforceable because inty types optional values as a real union.
