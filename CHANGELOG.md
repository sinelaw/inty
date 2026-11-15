# Changelog

## Unreleased

### Multi-line annotations

Long type annotations can be written across lines, nicely laid out, and mean
exactly what they mean on one line (see
[docs/type-system.md](docs/type-system.md#long-annotations-across-lines)):

```javascript
/** type ScoreView = {
 *   id: String,
 *   fitWidth: Number,  // the width the page is laid out for
 *   engraveMs: Number, // how long the last engraving took
 * } */

/** function sideView(
 *   b: Builder,
 *   v: ScoreView,
 * ) => Undefined */
```

- A JSDoc `*` margin at the start of each line after the first is ignored, in
  `type`, `function`, `const`/`let`/`var` and `class` annotations, with the
  keyword on the first line or on the line after `/**`.
- `//` comments to the end of a line are allowed inside an annotation and
  ignored by the checker.
- Trailing commas are accepted after the last parameter of a function type,
  type argument, type parameter and tuple element (object fields already
  accepted one), and a union may start with `|`.
- Errors inside an annotation are reported at the offending name or
  character, on its own line, instead of across the whole comment. This
  moves the reported position of existing annotation errors (unknown type,
  wrong number of type arguments, rank-1 restriction, required parameter
  after an optional one) from the comment's start to the culprit.
- New `inty fmt [--check] [--width=N] <file | dir>...`: rewrites each one-line
  annotation longer than the width (default 100) one field, parameter or
  union member per line, with a `*` margin and a trailing comma. Short and
  already multi-line annotations, and all code, are left as they are, so it
  is idempotent.

One-line annotations check exactly as before. Two edge cases of malformed
annotations change: a doc comment that starts like an annotation but stops
early (`/** const a: A, (b) */`) is now skipped whole instead of having its
leftover text read as code, and an unterminated `/** type …` is now an
unterminated-comment error.

### Fixes

- An empty comment `/**/` ends at its own `*/`. It used to be read as the
  start of a doc comment running to the next `*/`, swallowing the code in
  between.
