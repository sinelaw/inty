# Design notes: dictionaries, newtypes, polymorphic record fields

Three features a real application (Rosaclef, see
[rosaclef-report.md](rosaclef-report.md)) asked for, with what was done
and why. inty's type system is deliberately small; each note says what
fits it and what wouldn't.

## Dictionaries (`Dict<V>`) — implemented

**Need.** JSON objects used as maps (`{"cutoff": 1200, "resonance": 0.3}`)
couldn't be typed: a record type lists its fields, and there was no
index-signature type. Rosaclef decoded such objects into `{key, value}[]`
entry lists and encoded them back.

**What exists.** The type system already had a string-keyed map,
`Type::Map(V)`, for Python's `dict[str, V]`, with indexing and unification.
It only lacked a JavaScript spelling and the JavaScript-specific rules. Now:

- `Dict<V>` and TypeScript's `{ [String]: V }` (also `{ [key: String]: V }`)
  name it in annotations; it prints as `Dict<V>`.
- An object literal where a `Dict<V>` is expected is one: each value is
  checked against `V` (a spread must be a `Dict<V>`; methods and accessors
  are rejected).
- A read — `d.k` or `d[k]` — is `V | Undefined` in JavaScript, since a key
  may be missing (Python raises instead, so its reads stay `V`). Write
  `d.k ?? fallback`, or narrow.
- `Object.values(d)` is `V[]`, `Object.entries(d)` is `[String, V][]`
  (tuples are now available too), `Object.fromEntries` builds one, and
  `Object.keys` takes anything.
- `Map<K, V>` and `Set<T>` now name the types of `new Map()` / `new Set()`
  instances (they were unknown names).

```javascript
/** type Device = { type: String, params: Dict<Number> } */
/** const d: Device */
const d = { type: "filter", params: { cutoff: 1200, resonance: 0.3 } };
const cutoff = d.params.cutoff ?? 1000;
let sum = 0;
for (const [k, v] of Object.entries(d.params)) sum = sum + v;
```

**Not done.** A record is not a `Dict` (no subtyping from `{a: Number}` to
`Dict<Number>`): that would be sound for reads, but it is a new subtyping
rule, and the literal and JSON-decoding cases don't need it. `Map.get`
still returns `V` rather than `V | Undefined`, as before.

## Newtypes — use `nominal type`

**Need.** Integers with different meanings (a mixer insert, a playlist
track, a note) must not be mixed up, at no runtime cost. Rosaclef used
empty classes in a `.d.js` as brands, loaded before its aliases (bug 4),
and identity casts in a `#brands` module.

**What exists.** inty already has declared nominal types:
`/** nominal type InsertIx = Int */`. A nominal type keeps its identity
through unification — an `InsertIx` is neither a `TrackIx` nor an `Int` —
while comparisons and field access see through it. It needs no empty
class, and with bug 4 fixed it can sit next to the aliases that use it.

```javascript
// globals.d.js
/** nominal type InsertIx = Int */
/** nominal type TrackIx = Int */
/** type Channel = { name: String, mixer: InsertIx } */

// brands.d.js — typed identity casts, `x => x` at runtime (brands.js)
/** const insertIx: (Int) => InsertIx */
export const insertIx;
/** const insertIndex: (InsertIx) => Int */
export const insertIndex;
```

What that gives, checked: `a < b` on two `InsertIx`s is fine; `a + 1` and
`xs[a]` are errors (unwrap with `insertIndex(a)`); passing an `InsertIx`
where a `TrackIx` is expected is an error. inty also injects a constructor
`InsertIx(n)` for the checker, but inty doesn't transform code, so at
runtime there is nothing by that name: the casts have to exist as plain
functions, which is what Rosaclef's `#brands` module already is. That is
the "zero-cost" that a checker-only tool can offer.

**Considered, not done.**

- *Arithmetic lifting* (`InsertIx + 1 : InsertIx`), opt-in per type: it
  needs a declaration syntax and a rule for mixed operands (`InsertIx +
  TrackIx`), and it is exactly what makes newtypes leak meaning (an index
  plus an index isn't an index). The explicit unwrap is clearer.
- *An array-index capability* (`xs[ix]` for `ix: InsertIx` when `xs` is an
  "array indexed by InsertIx"): it needs arrays parameterised by their
  index type, a change to the array type itself.

## Polymorphic record fields — rank-1 only, with a clearer error

**Need.** A generic function stored in a record (a table of helpers, or a
DOM element's `addEventListener`, whose event type should depend on the
event name) loses its polymorphism: every use of the field shares one
instance.

```javascript
const utils = { id: (x) => x };
utils.id(1);
utils.id("s");   // error: expected 'Number | Int', found 'String'
```

**Why.** inty's polymorphism is rank-1, as in Hindley–Milner: a binding's
whole type can be generic, and each *use of the binding* instantiates it.
A record literal isn't generalised (the value restriction: its fields can
be written), and its fields hold types, not type schemes. In a
declaration, the quantifiers of an annotation such as
`const Math: {abs: <a> where Num a => (a) => a, …}` are hoisted to the
whole binding, so each *reference to `Math`* instantiates them — which is
why `Math.abs` works, but a field of a value stored anywhere else doesn't.

Genuine polymorphic fields need a scheme inside a record type (a new kind
of type), instantiated at each field access; checking a record against
such a type requires an annotation (rank-2 inference is undecidable), and
mutating such a field needs the polytype-assignment check inty already
has for bindings. It is a self-contained extension, but a real change to
the type system, and it was out of scope for this round.

**What was done.** The error for writing one in an annotation now says
what is generic and what to do:

```
Error: Rank-1 restriction: type parameters not allowed in nested position
  Help: inty's polymorphism is rank-1: only a binding's whole type can be
  generic (`/** function f<T>(x: T) => T */`), not a record field or a
  parameter (`{ id: <T>(T) => T }`). Keep a generic function at the top
  level and call it by name, or give the field the one type all its uses
  share. (A function stored in a record likewise has one type for all its
  uses.)
```

**Consequence for the DOM.** Typing each event by its name
(`addEventListener("keydown", (e) => …)` giving a `KeyboardEvent`) needs
exactly this: the method's event type must be chosen per call, on one
element value. Until then, listeners get one event shape, `DomEvent<T>`,
with the fields of all the common event kinds — the same trade-off the
stdlib makes for elements. A literal-keyed lookup (`Indexable EventMap<T>
K E`, deferring the lookup until the key is a known literal) works
mechanically and was prototyped, but it needs the per-access
instantiation above to be usable on one element.
