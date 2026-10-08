# Lean formalization of inty's type system

A machine-checked model of inty's type system, in Lean 4 (core library only,
no Mathlib). It covers a small core calculus, with let-polymorphism under the
value restriction, type schemes that carry class constraints (inty's
`<a> where Plus a => (a, a) => a`), a heap with `let` and assignment, a
complete type-soundness proof, and an executable type-inference algorithm
proved sound and complete. It is laid out so
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
`τ`, class constraints `C` that hold, context `Γ`, world `W` (the scheme of
each cell of the heap), environment `env` whose variables' cells have the
schemes `Γ` gives them, heap `h` that `W` describes for `clock` calls,
enclosing function's return type `R`, and every clock, writing
`(r, c, h') = run clock env h e` for the result, the clock left and the heap
after,

```
HasType C Γ R e τ → Holds C → G W Γ env → HeapOK clock W h →
  c ≤ clock ∧
  (r = timeout ∨ ∃ W', W <+: W' ∧ HeapOK c W' h' ∧
    ((∃ v, r = ok v ∧ V c W' τ v) ∨ (∃ v, r = thrown v) ∨
     (∃ v, r = returned v ∧ ∃ τr, R = some τr ∧ V c W' τr v)))
```

That is CakeML's shape of theorem (Owens et al., "Functional Big-step
Semantics", ESOP 2016): for every clock, a value of the right type, an
exception, or out of time, and never stuck. `V k W τ v` is a step-indexed
Kripke logical relation: `v` behaves as a `τ` for `k` more calls, in any
heap that a world extending `W` describes (see the design choices).
`Inty/Statements.lean` pins each of its clauses.

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
inferProgram e = some τ → HasType [] [] none e τ
```

so, by `Inty.inferProgram_never_stuck`, a program inference accepts never
gets stuck.

`Inty.infer_complete` (in `Inty/InferComplete.lean`): inference finds a type
whenever one exists, one of which every valid type is an instance (Damas
and Milner's completeness; the freshness invariants follow Naraschewski and
Nipkow's proof of algorithm W):

```
ctxFtv Γ = [] → e.assignsMutable (Γ.map fun _ => false) → HasType [] Γ none e τ' →
  ∃ o, infer Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ inferIn Γ e ≠ none
```

`assignsMutable` is the scope check that a program assigns only to its own
`let`s and parameters, never to a `const`; it is a check beside the typing
rules, not one of them, since such an assignment would be type-safe.

(`inferIn_complete`, `inferProgram_complete`). It rests on unification
being most general (`Inty.unify_mgu`).

`Inty.never_stuck_with_builtins` (in `Inty/Builtins.lean`): the same for a
program run with native functions in scope, `Math.abs : number → number`
and `Boolean : ∀ a. a → boolean`. No typing derivation describes them; they
are in `V` by what they do (`Prim.abs_sound`, `Prim.truthy_sound`). With
`Inty.inferIn_sound`, a program inference accepts with the builtins never
gets stuck with them.

`Inty.run_mono` (in `Inty/Clock.lean`): more clock doesn't change a result
that didn't run out, so the model's verdicts don't depend on its clock.

`Inty/Axioms.lean` pins the axioms these theorems use to Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

## The calculus

| Lean | inty |
|---|---|
| `Ty`: `number`, `string`, `boolean`, `undefined`, `null`, `fn` (the type of `this`, the parameters' and the result's), type variables | `types::Type` (an `fn` is the call signature of a callable row, `Type::Func`; `number` stands for both `Int` and `Number`) |
| `Scheme` (`∀ α₀ … αₖ₋₁. plus ⇒ τ`, body and constraints `PTy`s) | `types::TypeScheme`, with its `where` clause |
| `Expr`: literals, variables, named functions of any number of parameters (recursive, with `this`), calls outside a receiver (`this` is `undefined`; one argument per parameter), `const`, `let`, assignment to a variable, `?:`, `!`, `typeof`, unary `-`, `+`, `-`, `return`, `throw`, statement sequences | `ast::Expr`, `ast::Stmt` |
| `Result`: `ok`, `stuck`, `timeout`, `returned`, `thrown`; `bindC` | `dynamics::StmtOutcome`, `Stuck` |
| `HasType` (declarative typing, Hindley–Milner style) | what `src/infer` implements |
| `Expr.IsValue` (the value restriction), `Expr.writes` (a `let` that is assigned isn't generalised) | `is_syntactic_value`, `src/infer/features/bindings.rs`; `Resolution::written_at`, `src/ast/resolve.rs` |
| `Expr.assignsMutable` (no assignment to a `const`) | `check_assignment_target` |
| `UnOpTy`, `BinOpTy` (one constructor per operator rule) | the operator catalog, `src/operators` |
| `Cls`, `Pred`, `Inst` (`Inty/Classes.lean`): classes, constraints, instances | `classes::ClassName`, the instance tables in `src/classes` |
| `Entails C p` (`p` is an instance, or assumed in `C`) | a scheme's constraints in scope while checking its body |
| `unify`, `infer`, `inferProgram` (Algorithm W) | `src/infer` (`unify.rs`, the per-feature rules) |
| `Out.preds` (pending class constraints) | the constraints `src/infer` resolves once types are known |
| `Value`, `Stuck`, `run` / `eval` (interpreter with a call clock and a heap, every binding a cell) | `src/dynamics` (`Value`, `Stuck`, fuel, `heap.rs`, `RuntimeEnv`) |
| `Prim`, `builtinCtx`, `builtinEnv`, `builtinHeap` (native functions, with their types) | `Value::Builtin`, `src/builtins` |
| `Value.truthy`, `Value.typeString` | `Value::truthy`, `Value::type_string` |
| `World`, `V`, `HeapOK`, `G`, `eval_sound` (semantic typing) | `src/meta/soundness.rs` |

`Inty/Examples.lean` has small programs with their typing derivations; the
interpreter runs them at build time (`#guard`).

## Design choices

These choices are meant to hold up as the calculus grows.

- **The semantics is a definitional interpreter with a clock** (Amin and
  Rompf, "Type Soundness Proofs with Definitional Interpreters", POPL 2017;
  CakeML's functional big-step semantics), not a substitution-based
  small-step relation. It has the same shape as `src/dynamics`: closures
  over environments, a bound on the work, and an explicit `stuck`. Terms are
  never substituted into, so there are no term substitution lemmas. The
  clock counts calls, and `run` returns what is left of it for the rest of
  the program; it terminates by well-founded recursion on the clock and the
  expression. Running out of clock is distinct from getting stuck, so the
  soundness theorem holds even for diverging programs. As in `dynamics`,
  every binding is a cell of a heap that `run` threads beside the clock, and
  a closure captures its variables' cells, so it sees later assignments to
  them. A call stores its arguments, the function itself and `this` in
  fresh cells. Amin and Rompf extend the approach to mutable references with
  a syntactic store typing (§4.1), as this model does.
- **The interpreter is executable.** `eval` is an ordinary function, so the
  model can serve as a test oracle against the Rust implementation, as
  Cedar's Lean model does for Cedar's Rust code (differential random
  testing).
- **Types and expressions nest lists** (a function's parameters, a call's
  arguments), as rows, unions and tuples will. Lean derives neither
  equality nor induction for nested inductive types, so `Ty.ind`, `PTy.ind`
  and `Expr.ind` are induction principles with a hypothesis for each list
  element, and functions on them recurse through a list by a mutual
  function on the list, which keeps them structural.
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
  syntax, separate from any algorithm. Inference is proved sound and complete
  against it.
- **Values are typed semantically**, by a step-indexed Kripke logical
  relation (Appel and McAllester, TOPLAS 2001; Ahmed, ESOP 2006; Ahmed,
  Appel and Virga's model of general references) whose index is the
  interpreter's clock, as in CakeML. A world gives each cell its scheme;
  cells never change scheme, so worlds only grow (`<+:`). `V k W (τ₁ → τ₂) f`
  says that calling `f` with any clock `j ≤ k`, in any larger world, on a
  heap that world describes one tick down and on any `V j τ₁` argument,
  takes a tick and gives back a `V c τ₂` value at the clock `c` left, in a
  still larger world describing the heap after, or throws, or runs out. A
  type variable has no values. Since worlds map cells to syntactic schemes,
  `V` at index `k` needs `V` at arbitrary types only below `k`, and is
  defined by well-founded recursion on the index and then the type. The
  index is also what lets a recursive function's body assume the function
  itself, one call down. Typing values by behaviour rather than by
  derivation is what admits native functions (`Inty/Builtins.lean`), and
  recursive types later, which a syntactic value typing can't describe.
  This needed the clock to count calls and be threaded: with fuel bounding
  recursion depth, a result computed under `k` steps is good only for
  fewer, and the indices don't line up. Iris (via iris-lean) was the
  alternative; see the roadmap's phase 2 for why not, for now.
- **Inference is proved sound without freshness invariants.** The theorem
  says the inferred type is valid under the inferred substitution and any
  further substitution that resolves the pending class constraints. Stated
  that way, a `const`'s generalisation is justified by renaming, and the
  proof never needs inference's fresh variables to be fresh; completeness
  does, and states them as invariants (`Below`, `Within`). Unification (`Inty/Unify.lean`) terminates by a measure and is
  proved most general (`unify_mgu`): every unifier factors through the one
  it finds.
- **Class constraints are assumptions in the judgement.** `HasType C Γ R e τ`
  types `e` assuming the constraints in `C` hold, as in HM(X). A class is a
  `Cls` with its instances in `Inst` (`Inty/Classes.lean`); `Plus` is the
  only one so far, and adding one is adding its instances and the operator
  rules that use it. A
  `const` types its initialiser assuming its scheme's constraints, and each
  use of the variable must establish them. Inference records a pending
  constraint at each `+`; a `const` takes the ones mentioning a generalised
  variable into its scheme, and the rest must be resolved by the end of the
  program.
- **`Int` is folded into `number`.** inty's `Int ≤ Number`, with the `Num`
  and `Arith` classes, is phase 5 of the roadmap.

## Adding a feature

This mirrors "Adding a typing feature" in `ARCHITECTURE.md`:

1. Syntax: a constructor in `Expr` (and in `Ty` / `Value` if needed).
2. Typing: a rule in `HasType`, or an arm in `UnOpTy` / `BinOpTy`.
3. Semantics: an arm in `run` (or `UnOp.eval` / `BinOp.eval`, or
   `Prim.apply` for a native function).
4. Inference: an arm in `infer`.
5. Proof: a case in `HasType.subst`, `HasType.generalize_ctx`, `run_sound`
   (or `UnOp.eval_sound` / `BinOp.eval_sound`), `run_clock_le`, `run_mono`,
   `infer_inv`, `infer_sound` and `infer_complete`, and a clause of `V` for a
   new type former. A native function needs only its
   `V` proof (`Prim.abs_sound`).
6. An example in `Inty/Examples.lean`.
7. The wire format (`Inty/Wire.lean`) and the differential test's
   generator and JavaScript printer (`crates/inty/tests/differential.rs`).

Lean's exhaustiveness checks point at every case still missing.

## Roadmap

[ROADMAP.md](ROADMAP.md) plans the rest: twelve phases to a complete model
of inty's type system, with the ground rules that keep it faithful to what
inty implements and documents.

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
  clock; a timeout on either side is not compared);
- inty and the model typing a program differently, unless inty's own types
  show a feature the model doesn't have yet;
- a real JavaScript engine (Node, running `tests/differential/engine.js`)
  disagreeing with either interpreter where that interpreter finishes, or
  raising a native error (`TypeError`, `ReferenceError`) on a program inty
  or the model accepts. `never_stuck` is about the model's `eval`; agreement with
  the engine is the (sampled, not proved) evidence that `eval` is
  JavaScript on this fragment.

```sh
cd lean && lake build && cd ..
cargo test -p inty --test differential -- --nocapture
INTY_DIFF_CASES=20000 INTY_DIFF_SEED=7 cargo test -p inty --test differential
```

Over 100,000 programs (five seeds), Node agreed with both interpreters
wherever they finished and raised no error on a program either accepted.
Where `dynamics` gets stuck, Node raises a `TypeError` or `ReferenceError`
in about half the cases and coerces in the rest (`1 - "a"`,
`typeof unbound`): the gap between inty's stricter semantics and
JavaScript's. As a control, an engine that runs `-` as `+` fails 152 of
3000 programs. The engine runs each program in strict mode, which inty
assumes throughout (`docs/scc-inference.md`): it found that in sloppy mode
`(function () { return this; })()` is the global object, where inty, its
dynamics and the model all have `undefined`.

Over 200,000 programs (ten seeds), the interpreters never disagreed, and
the model never accepted a program inty rejects, except as below. The
disagreements in typing all fall into features the model lacks:

| Divergence | inty | model | Roadmap phase |
|---|---|---|---|
| Nullable join: `c ? 1 : null` | `Number \| Null` | rejects | 6 |
| A function that only throws | returns `never`, which nothing else unifies with | a free type variable | 6 |
| Nullable join with an unknown: `c ? undefined : x` | `Undefined \| t`, sometimes an infinite type | unifies | 6 |
| Recursive types: `function f(x) { return f; }` | `(a) => μ` | rejects (occurs check) | 8 |
| `Int` and `Number` under a function type: `(a) => Int` vs `(b) => Number` | rejects (`Int ≤ Number` holds for values only) | accepts | 5 |

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
