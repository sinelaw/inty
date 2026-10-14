# tysearch

Discover a type system for a language from its operational semantics, as a
search problem.

Give tysearch a language as a black box: its term constructors, and an
evaluator that says whether a term runs to a value, gets stuck, faults or
times out. It returns typing rules that never type a stuck program, type as
much of the rest as they can, and are as small as possible. It also returns
the evidence behind each rule.

It is a separate project from inty, with its own Cargo workspace and no
dependencies. The design, the theory behind it, related work and the
roadmap are in [DESIGN.md](DESIGN.md).

## Status

This is the first prototype, for first-order languages (layer L0 in the
design). Given only an interpreter, it:

- splits values into sorts by which immediate contexts they get stuck in;
- enumerates rule schemas for each constructor, refutes them by observation
  and by sampled compatibility tests, and picks a small, general set;
- folds overloaded rules into type classes by anti-unification;
- checks the result on every term up to a larger size than it learned from.

On TAPL's arithmetic language it finds TAPL's `Bool`/`Nat` rules. On a slice
of inty's model it finds inty's `Plus` class for `+`.

```sh
cargo run --release -- arith
cargo run --release -- core
cargo run --release -- core --learn 2 --check 6
cargo test --release
```

## Layout

| File | Role |
|---|---|
| `src/lang.rs` | The `Language` trait: signature, `eval`, `quote` |
| `src/enumerate.rs` | Every term up to a size |
| `src/sorts.rs` | Cached oracle; sorts from fingerprints |
| `src/rules.rs` | Rule schemas, enumeration, the induced checker, anti-unification |
| `src/discover.rs` | The pipeline and the report |
| `src/langs/` | Example languages: `arith` (TAPL ch. 3), `core` (inty's model) |
