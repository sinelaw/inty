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

The prototype handles languages with binders and functions. Given only an
interpreter, it:

- splits values into sorts, by the immediate contexts they get stuck in;
- refines a sort whose eliminator's result depends on the member. For
  closures under application, that is the function type `T<A -> R>`, found
  rather than given;
- finds where each bound variable's value comes from (another child, the
  node itself, or its eliminator's argument), so that recursion and
  parameters are typed correctly;
- proposes rules both top down (every rule with at most one sort constant)
  and bottom up (lgg of observed instances, and lgg climbing). It refutes
  them by observation, attacks the survivors' compatibility lemmas
  (CEGIS), and picks a small, general cover;
- checks the result on all terms up to a size, and on random larger ones.

On TAPL's arithmetic language it finds TAPL's rules. On the model of inty's
core, with functions, calls and `const`, it finds the Lean model's rules,
with differences that are all sound. [ITERATIONS.md](ITERATIONS.md) has
what each round found, and what had to change in the search to find it.

```sh
cargo run --release -- arith
cargo run --release -- core
cargo run --release -- model
TYSEARCH_TRACE=1 cargo run --release -- model     # timings, rejected rules
TYSEARCH_EXPLAIN=app2 cargo run --release -- model # one constructor's candidates
cargo test --release
```

## Layout

| File | Role |
|---|---|
| `src/lang.rs` | The `Language` trait: signature (with binders), `eval_in` |
| `src/enumerate.rs` | Every term up to a size and scope depth; a seeded RNG |
| `src/semantics.rs` | Sorts from fingerprints, refined sorts, the universe of ground types, membership by testing |
| `src/types.rs` | Types, rule schemas, matching, unification, lgg |
| `src/search.rs` | Per constructor: binder flow, observation, proposals, refutation, `falsify`, selection |
| `src/infer.rs` | The checker a rule set induces: algorithm W with overloads |
| `src/discover.rs` | The pipeline, the end-to-end check, the report |
| `src/langs/` | `arith` (TAPL ch. 3), `core` (first-order slice), `model` (the growing model of inty's) |
