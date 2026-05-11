// Optional row fields with presence polymorphism (Rémy 1994).
//
// `name?: T` in a row annotation marks the field *presence-polymorphic*:
// the caller may supply it or omit it, and the field's type is plain
// `T` — not `T | Undefined`. Optionality lives in the row, not in the
// value's type.

/** function request(opts: {url: String, method?: String, body?: String}) => String */
function request(opts) {
    // The body only reads `opts.url`. `method` and `body` stay
    // presence-polymorphic, so each call site decides independently
    // whether to supply them.
    return opts.url;
}

var a = request({url: "/api"});                                  // ok — method, body absent
var b = request({url: "/api", method: "POST"});                  // ok — method present, body absent
var c = request({url: "/api", method: "POST", body: "hello"});   // ok — both present

// Closed-row strictness still applies. Unknown fields don't fit:
//
// var d = request({url: "/api", verb: "POST"});
//   error: extra field `verb` doesn't appear in the row.

// If the body had read `opts.method`, the presence variable for
// `method` would be pinned to `Pre`, and the no-method call (`a`
// above) would fail to unify. Reading a field demands presence.
