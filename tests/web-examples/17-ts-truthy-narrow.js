// JavaScript treats 0, "", NaN, null, undefined all as falsy.
// TypeScript's narrowing on `if (x)` doesn't distinguish between
// "missing" and "empty/zero" — easy bug.

function priceLabel(price) {
    if (price) { return "$" + price; }
    else       { return "free"; }
}

// In TS, calling this with the literal `0` is fine — and silently
// returns "free" for a perfectly valid price of zero.
//
// Inty: `+` here mixes String and Number anyway, so the bug
// surfaces immediately at the operator. The deeper fix —
// explicit `price === undefined` narrowing — is enforceable
// because inty types optional values as a real union.
