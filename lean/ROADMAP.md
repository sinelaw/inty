# Roadmap: a complete model of inty's type system

The goal is an accurate and complete Lean model of the type system inty
implements:

- declarative typing rules for the whole of inty's shared AST, after
  lowering;
- an executable semantics that agrees with `src/dynamics` and with
  JavaScript engines;
- soundness, and inference proved sound and complete against the rules.

Linking the model to the Rust implementation by proof (for instance, by
checking each program's inferred types in Lean) is a separate track, not
covered here.

Paths like `src/infer` are relative to `crates/inty`.

## Ground rules

1. **inty's documented contract is the theorem.** Soundness says a
   well-typed program never gets stuck except by a fault inty documents as
   allowed: out of clock, an uncaught `throw`, `Stuck::IntRange`, a
   non-finite `Int`, an out-of-bounds read, and so on. A `fault` outcome
   lists them, each citing where `docs/type-system.md` allows it. So the
   model can be neither stronger nor weaker than what inty promises.
2. **The specification is what inty means, not what Hindley–Milner
   allows.** "Declared, not guessed" unions, defaulting and narrowing are
   rules of `HasType`, not features of the algorithm only. That keeps
   completeness provable: a program the rules accept and inty rejects is a
   bug in one of them.
3. **One rule per Rust rule.** Every `HasType` rule, class instance and
   improvement rule names its counterpart in `src/infer/features/*.rs`,
   `src/classes` or `src/operators`. A generated coverage table, checked in
   CI, lists the inty rules that have no Lean counterpart.
4. **The model runs on real programs.** inty writes out its lowered AST in
   the wire format, so the differential test runs on inty's own test suite
   and examples, beside the generated programs. Node, and later CPython and
   Lua, check the semantics.
5. **Every phase ends green.** `lake build` with no `sorry`; soundness, and
   inference sound and complete, for everything modelled so far; the axiom
   audit and pinned statements updated; the differential test extended to
   the new syntax.

## Done

- Hindley–Milner let-polymorphism under the value restriction, with
  schemes carrying `Plus` constraints.
- `return`, `throw` and statement sequences.
- An interpreter with a call clock and a heap, and soundness by a
  step-indexed Kripke logical relation, including native builtins.
- `let` and assignment to a variable.
- Algorithm W, proved sound and complete.
- Differential testing against inty and Node.

## Phases

### 0. Foundations

The parts every later feature touches.

- **Functions.** Done: functions of any number of parameters, with
  `this`; a call outside a receiver binds `this` to `undefined` and has one
  argument per parameter, as in `src/infer/features/functions.rs` and
  `dynamics`. Optional parameters (presence variables, `types::FuncParam`)
  arise in JavaScript only from annotations and the standard library
  (`slice(start, end?)`), and in Python from defaults, so they come with
  phases 10 and 12.
- **A general constraint language.** Done: a constraint is a class applied
  to types (`Pred`), instances are `Inst` (`Inty/Classes.lean`), and
  entailment is an instance or an assumption in scope (HM(X); Jones,
  "Qualified Types"). `Plus` is the first class defined this way. Still to
  come with the classes that need them: improvement rules (functional
  dependencies), first for `HasProp` in phase 3, and defaulting (`Num` to
  `Number`, `NumLit` to `Int`) as a rule of the specification, in phases 1
  and 5.

### 1. Completeness of inference

Done: `infer_complete` (`Inty/InferComplete.lean`), for the whole calculus,
and to be kept for every later phase. The decisions it needed:

- **Ambiguous constraints.** A constraint left on a type variable at the
  end is satisfiable, and inty leaves it in place and accepts the program
  (`resolve_plus`), so `inferProgram` accepts it too, typing the program at
  a default instance (`defaultSubst`). Completeness is stated for
  constrained types: the inferred type, with its pending constraints, has
  every valid type as a solved instance.
- **Constraints in a `const`'s scheme.** `HasType` used to let a scheme
  carry a constraint on a type already known, assumed while typing the
  initialiser and checked only where the variable is used, so it accepted
  `const x = function () { return g + g; }` (with `g` a function) when `x`
  is unused. inty now decides such a constraint when it generalises
  (`InferState::generalize`), and the rule requires every constraint of a
  scheme to be `Plus` on one of its quantified variables (`Scheme.Simple`).
- **Termination of unification.** A worklist algorithm that terminates by
  the variables still to eliminate (an explicit list, so no set library is
  needed) and then the size of the equations, proved sound and most
  general (`unify_mgu`) in `Inty/Unify.lean`.
- **Freshness.** Inference's inputs mention only variables below its
  counter (`Below`), and its substitutions stay within it (`Within`), as in
  Naraschewski and Nipkow's proof of algorithm W. A `const`'s scheme is
  opened at a block above everything in sight, which the cofinite rule
  allows; the block is then sent to `Number`, an instance of every scheme
  constraint, for the constraints left pending.
- Still to come with the features that need them: rigid variables (phase
  10), and well-scoped schemes (`bound i` within the arity) once schemes
  are written by hand, in annotations.

### 2. State and control

Done: the heap, `let` and assignment, with soundness and inference sound
and complete. Still to do: loops, `break`, `continue`, `switch` and `try`.

- **A heap, as `dynamics` has.** Every binding is a cell: a `const`,
  a `let`, a parameter. `run` threads the heap beside the clock, and a
  call stores its arguments in fresh cells.
- **Assignment and `let`.** A `let` that is never written is generalised
  as a `const` is. One that is written has one type, and an assignment
  unifies with it (inty used to generalise it and check each assignment
  against the polymorphic type with rigid variables, which no typing rule
  can state, since a rule could always pick a less general type; inty now
  does this). Assigning to a `const` is rejected by a scope check beside
  the typing rules.
- Loops, `break`, `continue`, `switch`, `try` / `catch` / `finally`. A
  caught exception has an opaque type: anything can be thrown (inty used
  to give it a flexible variable, which was unsound: `e - 1` on a thrown
  string got stuck in `dynamics`).
- **Decision: a hand-built Kripke logical relation, not Iris.** The
  trial found iris-lean usable: it builds against our Lean (4.34.1),
  needs only batteries and Qq, takes about 17 minutes, and has weakest
  preconditions, adequacy and HeapLang. But its adequacy theorem is about
  a small-step semantics, which we would have to write beside the
  interpreter and prove to agree with it for every construct. Our store
  holds values of syntactic types, so a world can map each location to a
  scheme (Ahmed, Appel and Virga's stratified model), with no circularity
  to solve: `V k W τ v` is defined by well-founded recursion on the index
  and the type, a function's promise quantifies over larger worlds, and
  the heap invariant is required one tick down. The theorems stay about
  the executable interpreter. Iris remains the option for the day the
  store needs invariants richer than a type per location.

### 3. Records and rows

- Object literals, property read and write, and spread.
- Row types, and the `HasProp` constraint with its improvement rule: the
  receiver determines the property's type.
- Methods with `this`.
- Garrigue's ML structural polymorphism (record constraints in a kinding
  environment, inference proved sound and principal) fits inty's
  `a has {name: b}` better than Rémy rows.

### 4. Containers

- Arrays, tuples, `Map` and typed arrays.
- The `Indexable` class with its improvement rule: a container determines
  its index and element types.
- Arrays and records invariant while mutable (#96).

### 5. Numbers

- `Int ≤ Number`, at the top level only; the `Num`, `NumLit` and `Arith`
  classes; defaulting.
- Checked `Int` arithmetic (`Stuck::IntRange`) as a fault.
- `Float` is opaque in Lean, so proofs rely on inty's runtime range checks.
  Where inty doesn't check (bitwise operators, `Math.floor`), a bit-level
  binary64 model, tested against Node, proves the facts needed.

### 6. Literal types and unions

- Literal types and their widening to base types.
- The join rules of `docs/type-system.md`: literals widen, `null` and
  `undefined` make a result nullable, a declared union absorbs its arms.
- `never` for what doesn't complete; operations pushed through each arm of
  a union; `&&` and `||`.
- Subsumption only where `src/infer` applies it, at value positions, never
  as a general conversion rule.

### 7. Narrowing

- `typeof`, `===`, `==`, truthiness and discriminant tests, on bindings
  that never change (`docs/flow-narrowing-safe.md`).
- Refinement after an early exit and in loops; `switch` exhaustiveness as
  a separate check.
- The semantic relation handles this directly, as "Revisiting Soundness
  for Occurrence Typing, Semantically" (arXiv 2609.16299) does for Typed
  Racket.

### 8. Equi-recursive types

- `μ` types, as for builders that `return this`, with type equality up to
  unfolding (Brandt and Henglein's coinductive axiomatization).
- Unification without the occurs check, and `HasType.subst` under
  recursive binders.
- `V` defined by well-founded recursion on the index and the type, with
  `V k (μ a. τ)` unfolding to the body. inty's recursive types recur
  through function types, and a call takes a tick, so a function type's
  clause can refer to its argument and result at smaller indices.

### 9. The other type formers

- Callable rows: functions as rows with a call signature and statics
  (`String`, `String.fromCharCode`).
- Nominal types (`Named`).
- Classes, lowered as inty lowers them: factory functions, `#private`
  fields, accessors, `extends` as a spread of the base instance.
- `Promise`, `async` and `await`, with `await` as the identity, as in
  `dynamics`; regex as an opaque base type.

### 10. Annotations

- Checking mode beside inference: an annotation is a typing obligation,
  which is how declared unions are introduced.
- Rigid type variables, and the annotation and `.d.js` type syntax.

### 11. Program structure

- Mutual recursion, inferred one strongly connected component at a time
  (`docs/scc-inference.md`).
- Modules: module types, each `ns.foo` re-instantiating the export's
  scheme, re-exports, and module state shared through the heap of phase 2.
- Checking several files in one run.

### 12. Builtins and the standard library

- Every builtin and standard-library signature as Lean data, generated
  from inty's Rust sources so the two can't drift.
- Each native function implemented as `dynamics` implements it, and
  proved in `V` (as `Math.abs` and `Boolean` are now).

## Frontends

Python and Lua lower onto inty's shared AST. The model types the AST, so
lowering stays outside it. Lowering gets the λJS treatment instead: lowered
programs are run against CPython and Lua, as JavaScript is against Node.

## Done means

- The coverage table has no gaps.
- The theorems hold for the whole AST.
- The model agrees with inty and the engines on inty's whole test corpus.
  Every disagreement is fixed or is a documented fault.
