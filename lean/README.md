# Lean formalization of inty's type system

A machine-checked model of inty's type system, in Lean 4 (core library only,
no Mathlib). It covers a small core calculus, with let-polymorphism under the
value restriction and type schemes that carry class constraints (inty's
`<a> where Plus a => (a, a) => a`), a complete type-soundness proof, and an
executable type-inference algorithm proved sound. It is laid out so
that each inty feature can be added the way it is added to the Rust code: a
typing rule, an operator arm and a runtime arm, plus one new case in the
proof. Paths like `src/dynamics` are relative to `crates/inty`.

```sh
cd lean
lake build      # checks every proof; a `sorry` fails the build
```

Install Lean with [elan](https://github.com/leanprover/elan); `lean-toolchain`
pins the version.

## What is proved

`Inty.eval_sound` (in `Inty/Soundness.lean`): for every expression `e`, type
`τ`, `Plus` assumptions `C` that hold, context `Γ` and environment `env`
matching `Γ`, enclosing function's return type `R`, and every amount of
fuel,

```
HasType C Γ R e τ → Holds C → EnvTy env Γ →
  eval fuel env e = timeout ∨ (∃ v, eval fuel env e = ok v ∧ ValTy v τ) ∨
  (∃ v, eval fuel env e = thrown v) ∨
  (∃ τr v, R = some τr ∧ eval fuel env e = returned v ∧ ValTy v τr)
```

That is CakeML's shape of theorem (Owens et al., "Functional Big-step
Semantics", ESOP 2016): for every clock, a value of the right type, an
exception, or out of time, and never stuck.

Its corollary `Inty.never_stuck` says a closed well-typed program never
evaluates to `stuck`. That is the property `src/meta/soundness.rs` samples
with proptest ("Whenever inty accepts a program, the operational semantics
must not get stuck on it"), here proved for all programs of the calculus.
The key lemma for polymorphism is `Inty.HasType.subst` (in
`Inty/TypeSubst.lean`): typing is preserved by substituting types for type
variables. The soundness proof uses it to type a generalised `const` at each
instance of its scheme.

`Inty.inferProgram_sound` (in `Inty/InferSound.lean`): whatever type inference
finds is a valid typing,

```
inferProgram e = some τ → HasType [] [] e τ
```

so, by `Inty.inferProgram_never_stuck`, a program inference accepts never
gets stuck. Completeness, that inference finds a type whenever one exists,
is not proved yet.

`Inty/Axioms.lean` pins the axioms these theorems use to Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

## The calculus

| Lean | inty |
|---|---|
| `Ty`: `number`, `string`, `boolean`, `undefined`, `null`, `arrow`, type variables | `types::Type` (an `arrow` is the call signature of a callable row; `number` stands for both `Int` and `Number`) |
| `Scheme` (`∀ α₀ … αₖ₋₁. plus ⇒ τ`, body and constraints `PTy`s) | `types::TypeScheme`, with its `where` clause |
| `Expr`: literals, variables, named one-parameter functions (recursive), application, `const`, `?:`, `!`, `typeof`, unary `-`, `+`, `-`, `return`, `throw`, statement sequences | `ast::Expr`, `ast::Stmt` |
| `Result`: `ok`, `stuck`, `timeout`, `returned`, `thrown`; `Result.bind` | `dynamics::StmtOutcome`, `Stuck` |
| `HasType` (declarative typing, Hindley–Milner style) | what `src/infer` implements |
| `Expr.IsValue` (the value restriction) | `is_syntactic_value`, `src/infer/features/bindings.rs` |
| `UnOpTy`, `BinOpTy` (one constructor per operator rule) | the operator catalog, `src/operators` |
| `PlusInst` | the `Plus` instance table, `src/classes` |
| `Entails C τ` (`τ` is an instance, or assumed to be one) | a scheme's constraints in scope while checking its body |
| `unify`, `infer`, `inferProgram` (Algorithm W) | `src/infer` (`unify.rs`, the per-feature rules) |
| `Out.plus` (pending `Plus` constraints) | the constraints `src/infer` resolves once types are known |
| `Value`, `Stuck`, `eval` (fuel-bounded interpreter) | `src/dynamics` (`Value`, `Stuck`, fuel) |
| `Value.truthy`, `Value.typeString` | `Value::truthy`, `Value::type_string` |
| `ValTy`, `EnvTy`, `eval_sound` | `src/meta/soundness.rs` |

`Inty/Examples.lean` has small programs with their typing derivations; the
interpreter runs them at build time (`#guard`).

## Design choices

These choices are meant to hold up as the calculus grows.

- **The semantics is a definitional interpreter with fuel** (Amin and Rompf,
  "Type Soundness Proofs with Definitional Interpreters", POPL 2017), not a
  substitution-based small-step relation. It has the same shape as
  `src/dynamics`: closures over environments, a fuel bound, and an explicit
  `stuck`. Terms are never substituted into, so there are no term
  substitution lemmas.
  Running out of fuel is distinct from getting stuck, so the soundness
  theorem holds even for diverging programs. Amin and Rompf extend the
  approach to mutable references with a syntactic store typing (§4.1), which
  inty's objects and `let` cells need; see roadmap step 6 for what inty adds.
- **The interpreter is executable.** `eval` is an ordinary function, so the
  model can serve as a test oracle against the Rust implementation, as
  Cedar's Lean model does for Cedar's Rust code (differential random
  testing).
- **Term variables are de Bruijn indices.** The typing context and the
  runtime environment are lists indexed the same way.
- **Type schemes are locally nameless.** A scheme's quantified variables
  (`PTy.bound i`) are syntax apart from free type variables (`Ty.var a`), so
  substitution can't capture, and a monotype can't contain a dangling bound
  variable. The `const` rule quantifies cofinitely: its initialiser must have
  the scheme opened at every block of variables above some finite set. That
  stands in for "the generalised variables aren't free in `Γ`" without
  renaming lemmas (Charguéraud's mini-ML, and fhm, do the same).
- **Typing is extrinsic and declarative.** `HasType` is a relation on plain
  syntax, separate from any algorithm. Inference is proved sound against it;
  completeness is next.
- **Values are typed by a value-typing relation** (`ValTy`): a closure has
  type `τ₁ → τ₂` when its body is well typed in a context its captured
  environment satisfies. It is inductive, not a logical relation, so it
  needs no step indices; a switch to semantic typing (as the occurrence
  typing paper makes) would bring them.
- **Inference is proved sound without freshness invariants.** The theorem
  says the inferred type is valid under the inferred substitution and any
  further substitution that resolves the pending `Plus` constraints. Stated
  that way, a `const`'s generalisation is justified by renaming, and the
  proof never needs inference's fresh variables to be fresh; completeness
  will. Unification is bounded by fuel for the same reason.
- **Class constraints are assumptions in the judgement.** `HasType C Γ e τ`
  types `e` assuming the types in `C` are `Plus` instances, as in HM(X). A
  `const` types its initialiser assuming its scheme's constraints, and each
  use of the variable must establish them. Inference records a pending
  constraint at each `+`; a `const` takes the ones mentioning a generalised
  variable into its scheme, and the rest must be resolved by the end of the
  program.
- **`Int` is folded into `number`.** inty's `Int ≤ Number`, with the `Num`
  and `Arith` classes, is a roadmap item.

## Adding a feature

This mirrors "Adding a typing feature" in `ARCHITECTURE.md`:

1. Syntax: a constructor in `Expr` (and in `Ty` / `Value` if needed).
2. Typing: a rule in `HasType`, or an arm in `UnOpTy` / `BinOpTy`.
3. Semantics: an arm in `eval` (or `UnOp.eval` / `BinOp.eval`).
4. Inference: an arm in `infer`.
5. Proof: a case in `HasType.subst`, `eval_sound` (or `UnOp.eval_sound` /
   `BinOp.eval_sound`) and `infer_sound`, plus a `ValTy` constructor for any
   new value form.
6. An example in `Inty/Examples.lean`.
7. The wire format (`Inty/Wire.lean`) and the differential test's
   generator and JavaScript printer (`crates/inty/tests/differential.rs`).

Lean's exhaustiveness checks point at every case still missing.

## Roadmap

Each step keeps `lake build` green, with no `sorry`. The order puts the
cheapest proofs first and the hardest last.

1. ~~**Let-polymorphism.**~~ Done: type variables and schemes, `const`
   generalising under the value restriction, and the type substitution
   lemma. A value in the environment has every instance of its variable's
   scheme whose constraints hold. Schemes carry `Plus` constraints.
2. **Inference.** Soundness is done: Algorithm W, executable, proved sound
   against `HasType`. Completeness needs three decisions first:
   - **Ambiguous constraints.** `HasType` accepts `!(function (y) { return
     y + y; })` at both `Number` and `String`, while `inferProgram` rejects
     it (a `Plus` constraint nothing resolves) and the Rust checker accepts
     it. Either default, as Rust does for `Num`, or make such programs
     untypable in the spec, as CakeML does to keep principal types.
     Completeness is then stated for constrained types: the inferred type,
     with its pending constraints, has every valid type as a solved
     instance.
   - **Well-scoped schemes.** A scheme may mention `bound i` past its arity
     (instantiated as `undefined`). Harmless for soundness, but "more
     general than" should range over well-scoped schemes only, by a
     well-formedness predicate or by construction.
   - **Termination of unification.** Its fuel counts recursion depth, so
     it fails on unifiable types nested about 1000 deep. fhm's measure
     (number of variables, then size) proves termination, but a definition
     by well-founded recursion doesn't reduce in the kernel, so the
     `by decide` example would move to `#guard`. Rows allocate fresh
     variables during unification, which that measure doesn't cover.
   [fhm](https://github.com/Arrow7000/fhm) is the Lean 4 template (its
   completeness needs freshness invariants and a rigid-variable set), as is
   CakeML's verified type inference.
3. ~~**Differential testing.**~~ Done; see below.
4. ~~**Statements and abrupt completion.**~~ Done for `return`, `throw` and
   sequencing: `returned` and `thrown` results, the enclosing function's
   return type in the judgement, and `if` statements as conditionals in
   statement position. A `const` doesn't generalise a variable the return
   type mentions. Loops and `break` come with mutable state (step 6), where
   they can do something.
5. **Records and row polymorphism.** Record types, the `HasProp`
   constraint, and method chains through `this`. Garrigue's Coq development
   of ML structural polymorphism (record and variant constraints in a
   kinding environment, recursive types through kinds rather than μ-binders,
   inference proved sound and principal with cofinite quantification) fits
   inty's `a has {name: b}` better than Rémy rows over μ-types.
6. **Mutable state.** A store threaded through `eval`, typed by a syntactic
   store typing that only grows (Amin and Rompf §4.1). inty also generalises
   `var` and `let` bindings and checks a later assignment against the
   binding's scheme, with its variables rigid (`id = function (x) { return
   x - 1; }` is rejected for a polymorphic `id`). So a cell's store type is a
   scheme, the assignment rule quantifies over rigid variables, and `Ty`
   needs a notion of rigid variable.
7. **Literal types, `Int`, unions and subsumption**: `Int ≤ Number` with
   the `Num` and `Arith` classes. `Int` arithmetic is checked (a result
   past ±2^53, or `% 0`, is a fault: `Stuck::IntRange` in `dynamics`), so
   the model needs a fault outcome beside `timeout`, and a number model it
   can reason about rather than `Float`. Then inty's join rules
   ("declared, not guessed", `docs/type-system.md`). Subsumption treats a
   mutable array or record as invariant: only a value is subsumed into a
   union, never the element type of a container someone can write to (#96).
8. **Narrowing** of bindings that never change (`docs/flow-narrowing-safe.md`).
   This is Typed Racket's rule; "Revisiting Soundness for Occurrence
   Typing, Semantically" (arXiv 2609.16299) gives a Lean mechanization of its
   soundness.
9. **More type classes and callable rows.** Schemes carry `Plus`
   constraints already, but `Indexable` and `HasProp` need more than extra
   arguments: the Rust solver improves types through their functional
   dependencies (a container determines its index and element types, a
   receiver its property's type), so inference unifies where `Plus` only
   checks, and the declarative rules must justify each improvement. Also
   functions as rows carrying a call signature alongside statics.
10. **Equi-recursive types.** The cost is in the types, not in `ValTy`:
    types up to unfolding, unification without the occurs check, and
    `HasType.subst` under recursive binders. An unfolding rule is an
    ordinary inductive rule, and Amin and Rompf handle recursive self types
    without step indices.

## Differential testing

`crates/inty/tests/differential.rs` checks inty against the model on
generated programs of the core calculus, both type-directed and adversarial.
Each one is written as JavaScript for inty and in a wire format
(`Inty/Wire.lean`) for `inty-model`, the executable `lake build` makes
(`Main.lean`), which answers with Lean inference's verdict and the
interpreter's result. The test fails on:

- a program inty accepts that gets stuck in `dynamics` (and, as a check on
  the harness, one the model accepts that gets stuck in `eval`, which
  `inferProgram_never_stuck` rules out);
- a program on which both interpreters finish but disagree, on the value or
  on getting stuck (`eval_mono` makes the model's answer independent of its
  fuel; a timeout on either side is not compared);
- inty and the model typing a program differently, unless inty's own types
  show a feature the model doesn't have yet.

```sh
cd lean && lake build && cd ..
cargo test -p inty --test differential -- --nocapture
INTY_DIFF_CASES=20000 INTY_DIFF_SEED=7 cargo test -p inty --test differential
```

Over 200,000 programs (ten seeds), the interpreters never disagreed, and
the model never accepted a program inty rejects, except as below. The
disagreements in typing all fall into features the model lacks:

| Divergence | inty | model | Roadmap |
|---|---|---|---|
| Nullable join: `c ? 1 : null` | `Number \| Null` | rejects | 7 |
| A function that only throws | returns `never`, which nothing else unifies with | a free type variable | 7 |
| Nullable join with an unknown: `c ? undefined : x` | `Undefined \| t`, sometimes an infinite type | unifies | 7 |
| Recursive types: `function f(x) { return f; }` | `(a) => μ` | rejects (occurs check) | 10 |
| `Int` and `Number` under a function type: `(a) => Int` vs `(b) => Number` | rejects (`Int ≤ Number` holds for values only) | accepts | 7 |
| A `Plus` constraint nothing resolves | accepts (defaulting) | ambiguous | 2 |

Each row is recognised from evidence, not guessed: a union or `μ` in the
types inty gave the program's expressions, or inty accepting the program
once its number literals are made fractional. The harness's first run also
found that `meta::soundness::check_program` never called
`resolve_constraints`, so it could accept programs the CLI rejects; it does
now.

## Working with AI agents

The evidence so far (System Capless, Typed Racket, fhm) suggests a split:
agents do the proof engineering well, while the definitions and theorem
statements need human review. A wrong statement compiles just as well as a
right one. So review changes to `Types`, `Syntax`, `Typing`, `Semantics`
and the statements of `eval_sound`, `HasType.subst` and `inferProgram_sound`
closely, and treat proofs as checked by Lean. `Inty/Statements.lean` restates
each headline theorem, so a change to one shows up in the diff, and lists
programs the typing rules must reject.
[lean-lsp-mcp](https://github.com/project-numina/lean-lsp-mcp) gives an agent
goal states and diagnostics:

```sh
claude mcp add lean-lsp uvx lean-lsp-mcp
```
