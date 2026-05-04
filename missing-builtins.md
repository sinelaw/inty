# JavaScript Built-in Coverage

Status of standard JavaScript built-ins inty knows about. The original
version of this document was a wishlist written while running inty
against the [depflame](https://github.com/example/depflame) codebase; most
of those gaps have since been filled in. What's left is genuinely missing
or deliberately out of scope.

`String` and `Array` prototype methods are looked up by `src/builtins/mod.rs`
(`string_method_type`, `array_method_type`, `promise_method_type`). Library
objects like `Math`, `console`, `JSON`, `Object`, `Array` (statics) and
`Promise` are declared in `stdlib/core.d.js`, which is auto-loaded before
every program (use `--no-stdlib` to skip it). Browser globals live in
`stdlib/dom.d.js`, also auto-loaded.

## String prototype

Implemented (`src/builtins/mod.rs::string_method_type`):

`indexOf`, `lastIndexOf`, `substring`, `substr`, `slice`, `split`, `trim`,
`trimStart`, `trimEnd`, `replace`, `replaceAll`, `toUpperCase`, `toLowerCase`,
`charAt`, `charCodeAt`, `startsWith`, `endsWith`, `includes`, `repeat`,
`padStart`, `padEnd`, `concat`, `toString`, plus the `length` property.

`replace` / `replaceAll` only accept a `String` first argument; the regex
overloads from the JS spec aren't modelled because there's no union type.

## Array prototype

Implemented (`src/builtins/mod.rs::array_method_type`):

`push`, `pop`, `shift`, `unshift`, `indexOf`, `lastIndexOf`, `includes`,
`slice`, `concat`, `join`, `reverse`, `sort`, `fill`, `find`, `findIndex`,
`forEach`, `filter`, `some`, `every`, `map`, `reduce`, `reduceRight`,
`toString`, plus the `length` property and `[]` indexing.

`map` and `reduce`/`reduceRight` are polymorphic: each call freshens the
result element type / accumulator type.

`find` returns `T`, not `T | undefined` — there's no union type, so a
`find` that doesn't match returns garbage at runtime. Same caveat as the
rest of the "no nullable" trade-offs in the README.

`sort` doesn't take a comparator yet.

## Promise prototype

Implemented (`src/builtins/mod.rs::promise_method_type`):

`then`, `catch`, `finally`. `then` requires the callback to return a
`Promise<U>` (rather than a plain value or a promise) because inty has
no union types; pass a plain value through `Promise.resolve(v)`.

Constructor helpers `Promise.resolve`, `Promise.reject`, `Promise.all` are
declared in `stdlib/core.d.js`.

## Math

Declared in `stdlib/core.d.js`:

Constants: `PI`, `E`, `LN2`, `LN10`, `LOG2E`, `LOG10E`, `SQRT2`.

Functions: `abs`, `floor`, `ceil`, `round`, `trunc`, `sign`, `sqrt`,
`cbrt`, `pow`, `min`, `max`, `hypot`, `log`, `log2`, `log10`, `exp`,
`expm1`, `log1p`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`,
`sinh`, `cosh`, `tanh`, `random`, `imul`, `fround`, `clz32`.

`min`/`max`/`hypot` are arity-2; the variadic spec form isn't supported
(no rest params).

## Object / Array statics

Declared in `stdlib/core.d.js`: `Object.keys` (returns `String[]`),
`Array.isArray`. Both shadow the bare `Object` / `Array` constructors that
live in the Rust env, which means `new Object()` and `new Array()` no
longer type-check — use `{}` / `[]` literals.

Other statics (`Object.values`, `Object.entries`, `Object.assign`,
`Array.from`, `Array.of`) are not declared yet.

## Global functions

Declared in `stdlib/core.d.js`: `parseInt`, `parseFloat`, `isNaN`,
`isFinite`. The constructor-style coercions `Number(x)`, `String(x)`,
`Boolean(x)` are polymorphic in the Rust env (`src/builtins/mod.rs::initial_env`).

`JSON.parse` and `JSON.stringify` are declared in `stdlib/core.d.js`. The
same `T` is shared between them inside the annotation, so a round-trip
`JSON.stringify(JSON.parse(s))` threads a consistent type — but `T`
is **not** re-instantiated per call site, so two unrelated `JSON.parse`s
in the same program will be unified together. This is a known wart of
declared (vs. Rust-built) polymorphic bindings.

## Browser DOM (auto-loaded)

`stdlib/dom.d.js` declares a small subset: `document` (with
`getElementById`, `createElement`, `title`, `location`), `window`
(`innerWidth`, `innerHeight`), `setTimeout`, `setInterval`,
`clearTimeout`, `clearInterval`, `alert`, and `fetch` (returning a
`Promise<Response>` with `status`, `ok`, `json()`, `text()`).

Because there's no union type, `getElementById` and `createElement` both
return the same generic "element" shape — an `HTMLInputElement` and an
`HTMLDivElement` aren't distinguishable at the type level.

## Genuinely missing / out of scope

- Variadic functions (`Math.min(a, b, c, ...)`, `console.log(a, b, c)`):
  there are no rest parameters yet.
- `Date`, `RegExp` constructor, `Error`, `Map`/`Set` collection types
  (the `Map<T>` *type* exists for object-as-string-dictionary patterns,
  but the JS `Map` constructor isn't declared).
- Iterators / generators / `Symbol` / `for await`.
- Anything that returns `T | undefined` (`Array.prototype.find`,
  `Map.prototype.get`, `Object.prototype.hasOwnProperty` style guards):
  the type is forced to a single shape.

## Known bugs

- Some recursive patterns involving an array referenced by a function that
  rebuilds it can stack-overflow during inference. Last reproduced against
  depflame; not investigated since.
