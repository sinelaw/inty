# minfern — architecture

This document is for contributors. It describes the module layout and the testing strategy. For user-facing docs, see [README.md](README.md).

## Module overview

minfern is built as a small set of cooperating modules. Each one does one job; together they form a self-checking type system.

- **`src/lexer/` + `src/parser/`** — turn source into an AST. Type annotations live in JSDoc-style comments and are surfaced through the lexer alongside the token stream.
- **`src/types/`** — the core lattice: primitives, rows, arrays, functions, unions, literals, type schemes, and substitution.
- **`src/infer/`** — HMF-style type inference. Split along feature lines: `features/scalars.rs`, `features/arrays.rs`, `features/rows.rs`, `features/functions.rs`, `features/operators.rs`, `features/control.rs`, `features/bindings.rs`. The dispatcher in `mod.rs` matches the AST shape and delegates; per-feature reasoning lives in one file each.
- **`src/operators/`** — a `static [OpInfo]` catalog describing every operator (`+`, `-`, `===`, `typeof`, `[]`, …) as data: arity, dispatch axis, and one or more typing arms. The catalog is documentation that gets cross-checked; the implementation is in `src/infer/features/operators.rs`. Where they disagree, the code wins.
- **`src/dynamics/`** — a small-step operational semantics. A reduction relation over the typed subset, with a fuel bound (default 10 000 steps) and an explicit `Stuck` reason. Heap-allocated state (`Cell::{Object, Array, Var}`) lives in `heap.rs`; closures snapshot a runtime env in `env.rs`. Not a JS engine — `await` is identity on `Promise<T>`, `instanceof`/`in` raise `NotImplemented`, regex literals don't reduce.
- **`src/classes/`** — declarative type-class instance tables (`Plus`, `Indexable`). Adding an instance is a one-line change here; the constraint solver in `src/builtins/` consults it.
- **`src/meta/`** — meta-tests that cross-check the type system against itself. See [Testing](#testing).
- **`src/infer::InferConfig`** — runtime knobs for type-system policy (currently exhaustiveness warnings, value-restriction strictness). Defaults match historical behaviour; flipping a knob changes one rule.
- **`src/decorate.rs`** — re-emits the source with inferred types as comments, for IDE display and `--annotate` output.

The production pipeline is `parse → infer → (optionally) decorate`. The dynamics, catalog, and meta-tests don't run in production; they exist so that adding a typing rule means you also describe its operator (catalog) and runtime behaviour (dynamics), and the test suite mechanically verifies the three agree.

## Testing

minfern has four kinds of tests. The first three each fix a specific class of bug; the fourth is a meta-layer that asserts the first three agree with each other. Run everything with:

```
cargo test --lib -- --skip parser::proptests
cargo test --test metamorphic
```

(The skipped `parser::proptests` regression has one known-flaky seed unrelated to inference.)

### 1. Per-module unit tests (`src/*/tests.rs`)

Each module embeds a `#[cfg(test)] mod tests` block whose tests parse a JS source string and assert one fact about it.

- `src/infer/tests.rs` (~70 tests): runs `InferState::infer_program` on a source string and asserts the inferred type via `apply_subst` — annotation handling, value restriction, equi-recursive method chains, narrowing, switch exhaustiveness, union join behaviour.
- `src/infer/{unify,type_parser,decorate}/tests`: lower-level tests on individual algorithms.
- `src/dynamics/tests.rs` (~19 tests): runs the operational semantics on a source string and asserts the resulting `Value` — one fixture per arithmetic / comparison / logical / bitwise / unary / pseudo-op, plus closure-capture and fuel-exhaustion shape tests.
- `src/operators/tests.rs` (4 tests): structural integrity of the static catalog — every `BinOp`/`UnaryOp` AST variant has an entry, no duplicate names, every `SameAsArg(N)` references a valid input position, every `class: Some(c)` arm mentions `c` via at least one `AnyOfClass(c)`.

These pin specific behaviour: "this construct should infer this type", "this value-restriction case should reject", "`++x` on a number should produce `x + 1`".

### 2. Metamorphic property tests (`tests/metamorphic.rs`)

There's no oracle for "is this program well-typed?", but there are *transformations* the type checker should be invariant under. Each property test generates a random program, applies one transformation, and asserts that `check(p) ≈ check(T(p))`:

- `t_swap_first_independent_pair` — swap two adjacent statements when neither uses the other's bindings; type result must be unchanged.
- `t_alpha_rename_existing` — capture-avoiding rename of a binding; type result unchanged modulo the rename.
- `t_prepend_empty`, `t_intersperse_empty`, `t_prepend_dead_var`, `t_wrap_expr_statements` — additions that shouldn't change anything.

These catch order-dependence and accidental name capture without anyone having to think of the specific case in advance.

### 3. Operator catalog and operational semantics

Two parallel *descriptions* of every operator. They exist so the meta-tests in §4 have something to cross-check.

- **The catalog (`src/operators/mod.rs`)** is the `static [OpInfo]` table described above. For each operator it records the kind (BinOp / UnOp / pseudo), the dispatch axis, and a list of `TypingArm`s — input/output `TypeShape`s that the typing rule accepts.
- **The dynamics (`src/dynamics/`)** is a small-step reduction relation. `eval_expr` and `eval_stmt` walk the AST and produce values via per-operator semantics in `step.rs`. A program that gets stuck for any reason other than `FuelExhausted` is a soundness violation by definition.

### 4. Catalog ⇔ dynamics meta-tests (`src/meta/`)

Two complementary tests over the catalog and the dynamics. Together they assert "every typing rule the catalog promises is one the operational semantics actually delivers".

**Cimini-Blame (`src/meta/blame.rs`)** enumerates *operators*. For each catalog `OpInfo`, for each `TypingArm`, for each enumeration of the arm's input shapes drawn from a fixed alphabet (`Number = "0"`, `String = "\"\""`, `Boolean = "true"`, `Null = "null"`, `Undefined = "void 0"`), the prober synthesises a tiny program (`(0) + ("")`, `void (0)`, `var __x = 1; ++__x`, …) and runs it through `dynamics::run_to_end`. If reduction gets stuck, the prober records a `BlameTriple`. The test asserts the resulting set is empty:

```
test meta::blame::tests::no_blame_triples_in_catalog ... ok
```

Catalog arms that document a side-condition the table can't express (`==` allowing coercion, indexing dispatching on container kind, etc.) carry a `notes` field that opts them out of blame-checking.

The first time this test ran, it found two real catalog bugs: the `+` Plus arm declared `(AnyOfClass(Plus), AnyOfClass(Plus))` (which the prober expanded into mixed `(Number, String)` pairs that real typing rejects — the second slot should be `SameAsArg(0)`), and an `undefined` probe that was an identifier lookup rather than a literal.

**Soundness proptest (`src/meta/soundness.rs`)** enumerates *whole programs*. Three proptest strategies (`arb_number`, `arb_string`, `arb_boolean`) build expressions of a target type by construction — sample a target, then assemble an expression of that type from literals, arithmetic, comparisons, conditionals, the identity-function application, etc. For each generated source the probe:

1. Parses it.
2. Type-checks via `crate::infer` and asserts the inferred type matches the target.
3. Reduces via `crate::dynamics` and asserts the resulting `Value` matches the target.
4. Any `Stuck` other than `FuelExhausted` (soundness violation) or any type-vs-value mismatch (generator bug) fails the property.

64 generated cases run per strategy on every test invocation:

```
test meta::soundness::tests::generated_number_programs_sound ... ok
test meta::soundness::tests::generated_string_programs_sound ... ok
test meta::soundness::tests::generated_boolean_programs_sound ... ok
```

The generator is deliberately conservative — it emits only the constructions where typing and operational semantics are known to agree. Adding cases here is how soundness coverage grows as new typing features land. A failing case shrinks via proptest to a minimal counterexample.

### Adding a typing feature

A new typing feature touches three files:

1. The rule in `src/infer/features/...`.
2. The catalog entry in `src/operators/mod.rs` (or a new arm on an existing op).
3. An operational arm in `src/dynamics/step.rs`.

The meta-tests then verify the three agree — by enumeration (blame) and by generation (soundness). If they don't, you find out at `cargo test`, not at runtime.
