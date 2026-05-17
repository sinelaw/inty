# JSDoc `@type` annotations on object-literal fields

Status: **implemented**. Scanner + parser + type-parser changes landed
alongside `crates/inty/tests/jsdoc_at_type.rs` and the
`crates/inty/tests/fixtures/jsdoc_at_type_iife.js` fixture.

## Motivation

`bigskysoftware/htmx@master/src/htmx.js` opens with a public-API
declaration that is the dominant single source of inty errors on htmx:

```js
const htmx = {
  /** @type {typeof onLoadHelper} */ onLoad: null,
  /** @type {typeof processNode}  */ process: null,
  /** @type {typeof addEventListenerImpl} */ on: null,
  // ...30 more fields...
};
function onLoadHelper(...) { /* ... */ }
function processNode(...) { /* ... */ }
htmx.onLoad = onLoadHelper;
htmx.process = processNode;
```

Each field is initialised with `null`, then JSDoc-typed to the
forward-declared helper's type, then filled in by a later assignment.
TypeScript's JSDoc reader accepts this pattern. Without `@type`
support, inty infers each field as `Null` and every assignment fails
with `expected 'Null', found '(…) => …'`.

The same scheme also covers the `htmx.config` sub-object, where
fields use the bare `@type T` form (no braces):

```js
config: {
  /**
   * Whether to use history.
   * @type boolean
   * @default true
   */
  historyEnabled: true,
  // ...
}
```

## What inty accepts

### Annotation shape

Two JSDoc forms, both as a tag inside a `/** ... */` block immediately
preceding the property:

- Braced: `@type {T}` — `T` extends until the matching `}`. Supports
  multi-line braced forms with per-line `*` decoration.
- Bare: `@type T` — `T` extends to end of line (or to the next
  `@tag`). This matches the original JSDoc convention used by older
  htmx code.

`T` is the inty type grammar (same as inline `/*: T */` annotations)
extended with `typeof Ident` (see below). Unknown identifiers in `T`
degrade to a non-fatal warning and the annotation is ignored — JSDoc
is a hint, not a contract; this matches TypeScript's behaviour of
ignoring unrecognised JSDoc.

### `typeof Ident`

Resolves to the *value* type of `Ident` from the surrounding scope,
instantiated to a monomorphic snapshot. Reading the binding through
`typeof` does not re-bind the polymorphism — same convention as
TypeScript. The forward-reference case works because the SCC-based
inference (see `docs/scc-inference.md`) hoists all top-level function
declarations before processing non-function statements, so `typeof
helperName` succeeds even when `helperName` is declared after the
annotated object literal.

### The placeholder rule

When the annotation kind is `@type` (JSDoc) **and** the property's
initialiser is a literal `null` or `undefined`, inty skips the usual
"value must subsume annotation" check and binds the field at exactly
the annotated type. This is the rule that makes the htmx pattern
work — `null` is a stand-in for the eventual helper, not a real
value the field is supposed to hold.

Inline `/*: T */` annotations and non-placeholder values still
check normally:

```js
// Inline annotation: subsume check runs — error.
let x = { count /*: Number */: "oops" };

// JSDoc annotation with non-placeholder value: still error.
let y = {
  /** @type {Number} */
  count: "oops"
};

// JSDoc annotation with placeholder: accepted, field typed as Number.
let z = {
  /** @type {Number} */
  count: null
};
z.count = 42;  // type-checks
```

## Where it lives in the code

| File | Change |
|---|---|
| `crates/inty/src/parser/ast.rs` | `TypeAnnotation` gains a `kind: AnnotationKind` field; `AnnotationKind::Inline` (default) vs `AnnotationKind::JsDoc`. |
| `crates/inty/src/lexer/scanner.rs` | `extract_jsdoc_type_tag` scans a `/** ... */` body for `@type` tags. Strips per-line `*` decoration for multi-line braced forms. Records the annotation with an empty `name` (= "attaches to the next named binding") and `JsDoc` kind. |
| `crates/inty/src/parser/mod.rs` | `try_get_jsdoc_type_annotation` consumes unnamed JSDoc annotations whose span ends before the current position. `parse_property_definition` calls it before reading the property key. Inline `/*: T */` still wins when both are present. |
| `crates/inty/src/infer/type_parser.rs` | `TypeOfTable` is a `HashMap<String, Type>` of pre-instantiated `typeof X` references. `TypeParser` consults it from `parse_primary_type` when it sees the `typeof` keyword. |
| `crates/inty/src/infer/features/rows.rs` | `build_typeof_table` pre-scans the annotation content for `typeof IDENT` substrings and instantiates each against the surrounding env. `infer_object` and `check_object` thread it through, skip the subsume check for `JsDoc` annotations with placeholder values, and downgrade parse failures to non-fatal warnings. |

The pre-instantiation approach (rather than a closure stored in the
parser) is deliberate: it sidesteps the `&mut InferState` borrow that
in-parser instantiation would require.

## Why we don't do more

- **Top-level `/** @type {T} */` on `var`/`const` declarations.**
  htmx doesn't use this shape (its `@type`s are all on object-literal
  fields). Adding it is a straight extension — `try_get_jsdoc_type_annotation`
  is already called at the right place; we'd just need an analogous
  consume in `parse_var_declaration` and the subsume relaxation in
  `infer_var`.

- **`@param` and `@returns` on function declarations.** These are
  the next-most-common JSDoc shapes htmx uses. Worth doing, but a
  separate change: parameter annotations don't follow the
  "attaches to the next binding" pattern — they're keyed by parameter
  name, which is a different attach mechanism.

- **`typeof` on values that aren't top-level bindings.** Today's
  resolver looks up names in `TypeEnv`. Member-access shapes
  (`typeof X.y`) aren't supported; htmx doesn't use them.

- **TypeScript-only types referenced by name** (`HtmxSwapStyle`, etc.).
  These degrade to non-fatal warnings rather than failing the field.
  The proper fix is to load the matching `.d.ts` declarations, which
  is a separate piece of infrastructure work.

## References

- [JSDoc spec — `@type`](https://jsdoc.app/tags-type.html)
- [TypeScript handbook — JSDoc reference](https://www.typescriptlang.org/docs/handbook/jsdoc-supported-types.html)
- htmx public-API declaration:
  https://github.com/bigskysoftware/htmx/blob/master/src/htmx.js#L5-L69
