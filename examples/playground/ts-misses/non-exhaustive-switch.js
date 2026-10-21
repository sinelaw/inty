// A switch over a union of literals that forgets a case falls through to
// the code after it. TypeScript says nothing when that code returns a
// value; here `color("fail")` quietly returns "gray".
//
// Inty warns about the missing case (a warning, not an error: the
// program is well-typed). Add the case, or a `default:` that says the
// fallback is meant.

/** type Status = "ok" | "warn" | "fail" */

/** function color(s: Status) => String */
function color(s) {
    switch (s) {
        case "ok": return "green";
        case "warn": return "yellow";
    }
    // Inty: warning — non-exhaustive switch: missing case(s) for "fail".
    return "gray";
}

console.log(color("fail"));
