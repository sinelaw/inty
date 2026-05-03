# minfern

Type checker with full type inference for a subset of JavaScript.

Try it online at: https://sinelaw.github.io/minfern/

Based on the type system developed for [infernu](https://github.com/sinelaw/infernu). See [infernu.md](infernu.md) for a partial formalization. The implementation also covers `this` resolution, Rank-1 restrictions on type annotations, and a value restriction for generalisation and polymorphic-property mutation; the formal document doesn't go into these.


The JavaScript checked by minfern is just JavaScript and can be run by browsers or any other runtime, or even embedded engines. See [mquickjs](https://github.com/bellard/mquickjs) which is a runtime that also supports a subset of JavaScript.

## Project Overview

minfern is built as a small set of cooperating modules. Each one does one job; together they form a self-checking type system.

- **`src/lexer/` + `src/parser/`** — turn source into an AST. Type annotations live in JSDoc-style comments and are surfaced through the same lexer.
- **`src/types/`** — the core lattice (primitives, rows, arrays, functions, unions, literals, type schemes) and substitution.
- **`src/infer/`** — HMF-style type inference. Split along feature lines: `features/scalars.rs`, `features/arrays.rs`, `features/rows.rs`, `features/functions.rs`, `features/operators.rs`, `features/control.rs`, `features/bindings.rs`. The dispatcher in `features/../mod.rs` matches the AST shape and delegates. Per-feature reasoning lives in one file each.
- **`src/operators/`** — a static catalog describing every operator (`+`, `-`, `===`, `typeof`, `[]`, …) as data: arity, dispatch axis, and one or more typing arms. Documentation that gets cross-checked, not the implementation.
- **`src/dynamics/`** — a small-step operational semantics. A reduction relation over the typed subset that defines what each operator and statement *means at runtime*, with a fuel bound and an explicit `Stuck` reason for soundness reporting.
- **`src/classes/`** — declarative type-class instance tables (`Plus`, `Indexable`). Adding an instance is a one-line change here; the constraint solver in `src/builtins/` consults the table indirectly.
- **`src/meta/`** — meta-tests that cross-check the type system against itself. See [Testing](#testing-and-self-checking).
- **`src/infer::InferConfig`** — runtime knobs for type-system policy (currently exhaustiveness warnings, value-restriction strictness). Defaults match the previous hardcoded behaviour; flipping a knob changes one rule.
- **`src/decorate.rs`** — re-emits the source with inferred types as comments, for IDE display and `--annotate` output.

The end-to-end pipeline is: `parse → infer → (optionally) decorate`. The dynamics, catalog, and meta-tests don't run in production; they exist so that adding a typing rule means you also describe its operator (catalog) and runtime behaviour (dynamics), and the test suite mechanically verifies the three agree.

## Strictest ever mode

minfern requires every variable (or function or object) to have a specific type, there are no union types. Every variable, expression, and function return must have exactly ONE type (though it may be polymorphic - see below). No type unions, no type changes, complete static type safety.

## Type System Features

- **Full type inference**: No type annotations required, all types inferred. You probably want them for documentation, minfern can add them for you.

- **Polymorphic ("generic") functions**: `function id(x) { return x; }` works with any type. See `tests/test_polymorphism.js` for more examples.
  
- **Structural typing**: Objects typed by their shape:

  ```javascript
  function getName(obj) {
      return obj.name;
  }
  
  var person = {name: "Alice", age: 30};
  var dog = {name: "Rover", breed: "Labrador"};
  var product = {name: "Widget", price: 9.99};
  
  var name1 = getName(person);   // "Alice"
  var name2 = getName(dog);      // "Rover"
  var name3 = getName(product);  // "Widget"
  ```

- **Type classes**: `+` on Number/String, `[]` on Array/String/Map/Object

- **Equi-recursive types**: Method chaining and builder patterns work naturally:

  ```javascript
  var requestBuilder = {
      url: "",
      method: "GET",

      setUrl: function(u) {
          this.url = u;
          return this;  // Returns the builder itself
      },

      setMethod: function(m) {
          this.method = m;
          return this;
      },

      send: function() {
          return this.method + " " + this.url;
      }
  };

  // Fluent chaining - each method returns the builder
  var response = requestBuilder
      .setUrl("/api/users")
      .setMethod("POST")
      .send();
  ```

  See `tests/test_builder_pattern.js` for more examples.

The rest is pretty basic (homogenous arrays, same-type conditionals and logical ops).

## Unsupported JavaScript Idioms

TLDR: Everything must have a specific type. An object can't sometimes have a value and sometimes be `null` or `undefined` or a change its type.

- No variable type changes: `var x = 1; x = "hello"`
- No union types: `return found ? obj : null` (Object vs Null)
- No mixed-type ternary: `condition ? 42 : "error"`
- No logical operators with different types: `obj && obj.property` (Object vs String)
- No default value pattern: `userName || "Guest"` (if types differ)
- No mixed-type arrays: `[1, "two", 3]`
- No type coercion: `"Count: " + 42` (String + Number)
- No multiple return types: `if (found) return obj; else return null;`
- No optional properties: `var u = {name: "Bob"}; u.age` → undefined (vs Number)
- No dynamic property access: `obj[key]` where `obj.name` is String, `obj.age` is Number
- No type guards: `if (typeof x === "string") return x.toUpperCase(); return x * 2;`

## Supported Syntax

Template literals, regex literals, getters/setters, method shorthand, `for-of`, `const`, `let` (treated as `var` — block scoping isn't modelled), arrow functions, destructuring (object and array, desugared at parse time), `class` declarations (desugared into factory functions; no inheritance, no static members), `async`/`await` (desugared via `Promise.resolve`), and `import`/`export` with file-system-based module resolution.

Type annotations are accepted in two forms: inline `var x /*: T */` and doc-comment `/** var x: T */`. See [declare.md](declare.md) for the rules around external declarations and Rank-1 polymorphism.

## Testing and self-checking

minfern's tests are layered. The bottom layer is hand-written — exactly what you'd expect from any Rust project. The upper layers are mechanical: they generate inputs and assert invariants, so type-system bugs surface as failing tests rather than mystery behaviour at runtime.

Run everything with:

```
cargo test --lib -- --skip parser::proptests
cargo test --test metamorphic
```

(The skipped `parser::proptests` regression has a known-flaky seed unrelated to inference.)

### 1. Hand-written tests (`src/*/tests.rs`, `tests/*.js`)

The familiar layer: per-module unit tests under `src/`, plus end-to-end JavaScript fixtures under `tests/` driven by `tests/test_language.js`-style assertions. These pin specific behaviour: "this construct should infer this type", "this value-restriction case should reject", and so on.

### 2. Operator catalog and operational semantics

Two parallel descriptions of every operator. They exist so the meta-tests in §3–4 have something to compare.

- **The catalog (`src/operators/mod.rs`)** is a `static [OpInfo]` table. For each operator (`+`, `<=`, `===`, `typeof`, `[]`, etc.) it records the kind (BinOp / UnOp / pseudo), the dispatch axis, and a list of `TypingArm`s — input/output `TypeShape`s that the typing rule accepts. It's read-only metadata: the actual typing logic is in `src/infer/features/operators.rs`. Where the two disagree, the code wins and the catalog is wrong (and the meta-test catches it).

- **The dynamics (`src/dynamics/`)** is a small-step reduction relation. `eval_expr` and `eval_stmt` walk the AST and produce values via per-operator semantics in `step.rs`. Heap-allocated state (`Cell::{Object, Array, Var}`) lives in `src/dynamics/heap.rs`, closures snapshot a runtime env (`src/dynamics/env.rs`). Reduction is bounded by fuel (default 10 000 steps): non-terminating typed programs raise `Stuck::FuelExhausted` rather than hang. A program that gets stuck for any *other* reason (`TypeMismatch`, `NotCallable`, …) is a soundness violation by definition.

The dynamics is not a JS engine. It does just enough to give the typing rules something falsifiable to be consistent with — `await` is identity on `Promise<T>`, `instanceof` and `in` are `NotImplemented`, regex literals don't reduce. Anything outside the typed subset is documented inline.

### 3. Cimini-Blame meta-test (`src/meta/blame.rs`)

Cross-checks the catalog (§2) against the dynamics (§2). For every operator and every input shape its typing arm accepts, the prober synthesises a tiny program (`(0) + ("")`, `void (0)`, `var __x = 1; ++__x`, …), runs it through `dynamics::run_to_end`, and records a `BlameTriple` if reduction got stuck.

```
test meta::blame::tests::no_blame_triples_in_catalog ... ok
```

A passing run means: every typing arm the type-checker promises is also a reduction rule the operational semantics delivers. Catalog arms that document a side-condition the table can't express carry a `notes` exemption and are skipped.

The first time this ran, it caught two real catalog bugs (the `+` arm declaring `(AnyOfClass(Plus), AnyOfClass(Plus))` instead of `(AnyOfClass(Plus), SameAsArg(0))`, and an `undefined` probe that was an identifier lookup rather than a literal). That's the meta-test working as designed: structural mistakes in the type-system description fail loudly.

### 4. Property-tested soundness (`src/meta/soundness.rs`)

Where the blame meta-test enumerates *operators*, the soundness probe enumerates *whole programs*.

`arb_number`, `arb_string`, `arb_boolean` are proptest strategies that build expressions of a target type by construction (sample a target type, then assemble an expression of that type out of literals, arithmetic, comparisons, conditionals, and function calls). For each generated source:

1. Parse it.
2. Type-check via `crate::infer` and assert the inferred type matches the target.
3. Reduce via `crate::dynamics` and assert the resulting value matches the target.
4. Any `Stuck` other than `FuelExhausted` is a soundness violation.

The generator is deliberately conservative — it only emits constructions where typing and operational semantics are known to agree. Expanding it is how soundness coverage grows as new typing features land.

```
test meta::soundness::tests::generated_number_programs_sound ... ok
test meta::soundness::tests::generated_string_programs_sound ... ok
test meta::soundness::tests::generated_boolean_programs_sound ... ok
```

64 cases per strategy on every test run.

### How the layers fit together

```
                ┌──────────────────────────────────────────┐
                │   src/infer (typing rules)               │
                │      ▲                ▲                  │
                │      │                │                  │
   describes ───┘      │                │   reduces ───────┘
                       │                │
              src/operators        src/dynamics
              (typing arms)        (reduction relation)
                       ▲                ▲
                       │                │
                       └─── src/meta ───┘
                            blame: catalog ⇔ dynamics
                            soundness: typed programs never stuck
```

A new typing feature touches three files: the rule in `src/infer/features/...`, the catalog entry in `src/operators/mod.rs`, and an operational arm in `src/dynamics/step.rs`. The meta-tests then verify the three agree — by enumeration (blame) and by generation (soundness). If they don't, you find out at `cargo test`, not at runtime.

## Future Work

Some of the limitations above are annoying and may be worth supporting in some way or form. It would be nice to support nullable/optional-style union types, or explicit sum types. It would require some work to avoid losing the principal typing property (every expression has a single unambiguous most general type).

Not yet supported: spread/rest parameters, class inheritance, static class members.

