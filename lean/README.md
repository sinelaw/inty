# Lean formalization of inty's type system

A machine-checked model of inty's type system, in Lean 4 (core library only,
no Mathlib). This first version is a small core calculus with a complete
type-soundness proof. It is laid out so that each inty feature can be added
the way it is added to the Rust code: a typing rule, an operator arm and a
runtime arm, plus one new case in the proof.

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
with proptest ("whenever inty accepts a program, `dynamics` must not get
stuck on it"), here proved for all programs of the calculus.
`Inty/Axioms.lean` pins the axioms the theorems use to Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`).

## The calculus

| Lean | inty |
|---|---|
| `Ty`: `number`, `string`, `boolean`, `undefined`, `null`, `arrow` | `types::Type` (an `arrow` is the call signature of a callable row) |
| `Expr`: literals, variables, named one-parameter functions (recursive), application, `const`, `?:`, `!`, `typeof`, unary `-`, `+`, `-` | `ast::Expr` |
| `HasType` (declarative typing) | what `src/infer` implements |
| `UnOpTy`, `BinOpTy` (one constructor per typing arm) | the operator catalog, `src/operators` |
| `PlusInst` | the `Plus` instance table, `src/classes` |
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
  `stuck`. There is no substitution, so there are no substitution lemmas.
  Running out of fuel is distinct from getting stuck, so the soundness
  theorem holds even for diverging programs. The approach extends to mutable
  state (thread a store, and type it with a store typing that only grows),
  which inty's objects and `let` cells need.
- **The interpreter is executable.** `eval` is an ordinary function, so the
  model can serve as a test oracle against the Rust implementation, as
  Cedar's Lean model does for Cedar's Rust code (differential random
  testing).
- **Variables are de Bruijn indices.** The typing context and the runtime
  environment are lists indexed the same way.
- **Typing is extrinsic and declarative.** `HasType` is a relation on plain
  syntax, separate from any algorithm. Inference is proved sound (later,
  complete) against it.
- **Values are typed semantically** (`ValTy`): a closure has type `τ₁ → τ₂`
  when its body is well typed in a context its captured environment
  satisfies. Step-indexed logical relations are the planned route once
  recursive types arrive.

## Adding a feature

This mirrors "Adding a typing feature" in `ARCHITECTURE.md`:

1. Syntax: a constructor in `Expr` (and in `Ty` / `Value` if needed).
2. Typing: a rule in `HasType`, or an arm in `UnOpTy` / `BinOpTy`.
3. Semantics: an arm in `eval` (or `UnOp.eval` / `BinOp.eval`).
4. Proof: a case in `eval_sound` (or in `UnOp.eval_sound` /
   `BinOp.eval_sound`), plus a `ValTy` constructor for any new value form.
5. An example in `Inty/Examples.lean`.

Lean's exhaustiveness checks point at every case still missing.

## Roadmap

Each step keeps `lake build` green, with no `sorry`. The order puts the
cheapest proofs first and the hardest last.

1. **Let-polymorphism.** Add type variables and schemes. `const` generalises
   under the value restriction (`InferConfig`), and the context holds
   schemes. A value has a scheme when it has every instance of it. The key
   lemma: typing is preserved by type substitution.
2. **Inference.** An executable unification-based algorithm (Algorithm W),
   proved sound against `HasType`, then complete with principal types.
   [fhm](https://github.com/Arrow7000/fhm) is a Lean 4 template for exactly
   this, including SCC grouping of recursive bindings (`docs/scc-inference.md`).
3. **Differential testing.** A `lean_exe` that reads a serialised core AST
   and prints the checker's and interpreter's verdicts. The Rust side lowers
   the programs `src/meta/soundness.rs` generates and compares.
4. **Statements and abrupt completion.** `return`, `throw`, `break` and loops
   as extra `Result` forms, as `dynamics` has them.
5. **Records and row polymorphism.** Record types with Rémy-style row
   variables, the `HasProp` constraint, and method chains through `this`.
6. **Mutable state.** A store threaded through `eval`, `let` cells and
   object fields, and a store typing that only grows.
7. **Literal types, unions and subsumption**, including inty's join rules
   ("declared, not guessed", `docs/type-system.md`). Subsumption treats a
   mutable array or record as invariant: only a value is subsumed into a
   union, never the element type of a container someone can write to (#96).
8. **Narrowing** of bindings that never change (`docs/flow-narrowing-safe.md`).
   This is Typed Racket's rule; "Revisiting Soundness for Occurrence
   Typing, Semantically" (arXiv 2609.16299) gives a Lean mechanization of its
   soundness.
9. **More type classes and callable rows**: `Indexable`, and functions as
   rows carrying a call signature alongside statics.
10. **Equi-recursive types.** `ValTy` becomes step-indexed, because a
    recursive type is not structurally smaller than its unfolding.

## Working with AI agents

The evidence so far (System Capless, Typed Racket, fhm) suggests a split:
agents do the proof engineering well, while the definitions and theorem
statements need human review. A wrong statement compiles just as well as a
right one. So review changes to `Syntax`, `Typing`, `Semantics` and the
statement of `eval_sound` closely, and treat proofs as checked by Lean.
[lean-lsp-mcp](https://github.com/project-numina/lean-lsp-mcp) gives an agent
goal states and diagnostics:

```sh
claude mcp add lean-lsp uvx lean-lsp-mcp
```
