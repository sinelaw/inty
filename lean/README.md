# Lean formalization of inty's type system

A machine-checked model of inty's type system, in Lean 4 (core library only,
no Mathlib). It covers a small core calculus, with let-polymorphism under the
value restriction, a complete type-soundness proof, and an executable
type-inference algorithm proved sound. It is laid out so
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
`τ`, context `Γ` and environment `env` matching `Γ`, and every amount of fuel,

```
HasType Γ e τ → EnvTy env Γ →
  eval fuel env e = timeout ∨ ∃ v, eval fuel env e = ok v ∧ ValTy v τ
```

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
inferProgram e = some τ → HasType [] e τ
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
| `Scheme` (`∀ α₀ … αₖ₋₁. τ`, body a `PTy`) | `types::TypeScheme` |
| `Expr`: literals, variables, named one-parameter functions (recursive), application, `const`, `?:`, `!`, `typeof`, unary `-`, `+`, `-` | `ast::Expr` |
| `HasType` (declarative typing, Hindley–Milner style) | what `src/infer` implements |
| `Expr.IsValue` (the value restriction) | `is_syntactic_value`, `src/infer/features/bindings.rs` |
| `UnOpTy`, `BinOpTy` (one constructor per operator rule) | the operator catalog, `src/operators` |
| `PlusInst` | the `Plus` instance table, `src/classes` |
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
  theorem holds even for diverging programs. The approach extends to mutable
  state (thread a store, and type it with a store typing that only grows),
  which inty's objects and `let` cells need.
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
  environment satisfies. Once recursive types arrive, `ValTy` is planned to
  become a step-indexed logical relation.
- **Inference is proved sound without freshness invariants.** The theorem
  says the inferred type is valid under the inferred substitution and any
  further substitution that resolves the pending `Plus` constraints. Stated
  that way, a `const`'s generalisation is justified by renaming, and the
  proof never needs inference's fresh variables to be fresh; completeness
  will. Unification is bounded by fuel for the same reason. A `+` defers
  its `Plus` constraint until the program is checked, and a `const` doesn't
  generalise a variable such a constraint mentions.
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

Lean's exhaustiveness checks point at every case still missing.

## Roadmap

Each step keeps `lake build` green, with no `sorry`. The order puts the
cheapest proofs first and the hardest last.

1. ~~**Let-polymorphism.**~~ Done: type variables and schemes, `const`
   generalising under the value restriction, and the type substitution
   lemma. A value in the environment has every instance of its variable's
   scheme.
2. **Inference.** Soundness is done: Algorithm W, executable, proved sound
   against `HasType`. What remains is completeness with principal types,
   which needs a termination proof for unification in place of its fuel,
   plus the invariant that inference's fresh variables really are fresh.
   [fhm](https://github.com/Arrow7000/fhm) is a Lean 4 template for this,
   including SCC grouping of recursive bindings (`docs/scc-inference.md`).
3. **Differential testing.** A `lean_exe` that reads a serialised core AST
   and prints the checker's and interpreter's verdicts. The Rust side lowers
   the programs `src/meta/soundness.rs` generates and compares. Fuel is
   counted differently (recursion depth here, a global step counter in
   `dynamics`), so a timeout on either side is not a mismatch.
4. **Statements and abrupt completion.** `return`, `throw`, `break` and loops
   as extra `Result` forms, as `dynamics` has them.
5. **Records and row polymorphism.** Record types with Rémy-style row
   variables, the `HasProp` constraint, and method chains through `this`.
6. **Mutable state.** A store threaded through `eval`, `let` cells and
   object fields, and a store typing that only grows.
7. **Literal types, `Int`, unions and subsumption**: `Int ≤ Number` with
   the `Num` and `Arith` classes, and inty's join rules
   ("declared, not guessed", `docs/type-system.md`). Subsumption treats a
   mutable array or record as invariant: only a value is subsumed into a
   union, never the element type of a container someone can write to (#96).
8. **Narrowing** of bindings that never change (`docs/flow-narrowing-safe.md`).
   This is Typed Racket's rule; "Revisiting Soundness for Occurrence
   Typing, Semantically" (arXiv 2609.16299) gives a Lean mechanization of its
   soundness.
9. **Constrained schemes, more type classes, callable rows**: schemes that
   carry class constraints (`<a> where Plus a => (a, a) => a`; for now a
   function using `+` on its parameter stays monomorphic), `Indexable`, and
   functions as rows carrying a call signature alongside statics.
10. **Equi-recursive types.** `ValTy` becomes step-indexed, because a
    recursive type is not structurally smaller than its unfolding.

## Working with AI agents

The evidence so far (System Capless, Typed Racket, fhm) suggests a split:
agents do the proof engineering well, while the definitions and theorem
statements need human review. A wrong statement compiles just as well as a
right one. So review changes to `Types`, `Syntax`, `Typing`, `Semantics`
and the statements of `eval_sound`, `HasType.subst` and `inferProgram_sound`
closely, and treat proofs as checked by Lean.
[lean-lsp-mcp](https://github.com/project-numina/lean-lsp-mcp) gives an agent
goal states and diagnostics:

```sh
claude mcp add lean-lsp uvx lean-lsp-mcp
```
