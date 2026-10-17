# tysearch

Discover a type system for a language from its operational semantics, as a
search problem.

Give tysearch a language as a black box: its term constructors, and an
evaluator that says whether a term runs to a value, gets stuck, faults or
times out. It returns typing rules that never type a stuck program, type as
much of the rest as they can, and are as small as possible. It also returns
the evidence behind each rule.

For a plain-language tour of one session, for readers who aren't type
theorists, see [WALKTHROUGH.md](WALKTHROUGH.md).

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
core (functions, calls, `let` with assignment, objects, arrays, `throw`,
`try`, loops and `return`), it finds the Lean model's rules, its value
restriction and its functions' exit types, with differences that are all
sound. To keep it from fitting itself to
inty, a suite of languages with other kinds of type system runs alongside:

- a unityped control;
- products;
- subtyping, where it finds `Int <: Float` from the fingerprints' order;
- JavaScript-style coercion;
- ML-style references, where it finds that a cell's type is invariant,
  and Wright's value restriction for `let`;
- five languages unlike inty's (units of measure, typestate, an effect,
  information flow, printf), to see where the rule format stops. It finds
  information flow's type system; elsewhere it leaves what it can't
  express untyped, and never types a program that crashes. [ITERATIONS.md](ITERATIONS.md) has
what each round found, and what had to change in the search to find it.

**The climb.** tysearch grows the type system itself, with nothing to
configure. It starts from sorts and ground rules, and tries each capability
in turn: type variables, function and object types, binders,
`let`-generalisation, exit types, subtyping, unions, narrowing. It keeps one
if the result types more of the safe programs, or as many with a smaller
system, and still gets none stuck. The programs it judges by include those
each tried system generated, so a capability shows what only it can type.
When no single capability helps, it tries pairs. It stops when nothing
helps or nearly everything is typed, then removes what the result can do
without, and prints each type system as it finds it.

```sh
cargo run --release -- core          # the climb: each step and its type system
cargo run --release -- arith
cargo run --release -- model         # about an hour
cargo run --release -- refs        # also: unityped, pairs, subtyping, coerce,
                                   #   units, files, effects, secrets, printf
cargo run --release --example climb_walkthrough  # the model's climb, with examples
TYSEARCH_TRACE=1 cargo run --release -- model     # timings, rejected rules
cargo run --release -- model --features vars,refined,binders  # one run, pinned
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
| `src/discover.rs` | The pipeline, the end-to-end check, the report; the climb |
| `src/langs/` | `arith` (TAPL ch. 3), `core` (first-order slice), `model` (the growing model of inty's), and the suite: `unityped`, `pairs`, `subtyping`, `coerce`, `refs`, `units`, `files`, `effects`, `secrets`, `printf` |
