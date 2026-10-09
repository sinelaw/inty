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
- `let` and assignment to a variable; `while`, `break`, `continue`,
  `try`/`catch`, `try`/`finally`.
- Algorithm W, proved sound and complete.
- Generic types (a constructor applied to types), Rémy's flat rows,
  `HasProp` with improvement and inty's generalisation, object literals,
  reads, writes and spread; arrays, indexing (`Indexable`, `IndexWrite`)
  and `length`, with an index out of bounds a fault (phase 3, in
  progress).
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
  end can't fail, since no value has a type variable's type, and inty
  leaves it in place and accepts the program (`resolve_plus`), so
  `inferProgram` accepts it too, and soundness assumes only that every
  constraint is an instance or on a type variable (`HoldsOrVar`, which
  replaced defaulting to `Number` in phase 3). Completeness is stated for
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

Done: the heap, `let` and assignment, `while`, `break`, `continue`,
`try`/`catch` and `try`/`finally`, with soundness and inference sound and
complete. A loop takes a tick per iteration, so `run` still terminates;
`break` and `continue` are abrupt completions like `throw`, with a scope
check that they are in a loop. Still to do:

- `switch` comes with phase 7: its cases match by `===`, which compares
  functions by identity, and with the narrowing and exhaustiveness checks
  of a `switch`.
- **Statements apart from expressions.** The model treats a statement as an
  expression with a value, as a JavaScript program's completion value is.
  inty types statements without one: `if (c) { 1; } else { "a"; }` and the
  same `try`/`catch` are accepted, where the model wants both branches of
  one type. The differential test generates only the programs both agree
  on; the model needs a separate statement judgement, whose "value" is
  only what `return` returns.

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
- Loops, `break`, `continue`, `try` / `catch` / `finally`. A caught
  exception has the opaque type `unknown`, whose values are all values:
  anything can be thrown (inty used to give it a flexible variable, which
  was unsound: `e - 1` on a thrown string got stuck in `dynamics`). A
  stuck body doesn't run `finally`, as in `dynamics`, since getting stuck
  is not a JavaScript exception.
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

### 3. Generic types, records and rows

The end goal is all of inty's types, so the representation is chosen for
the end now, and the phases after this one add type formers without
touching the generic proofs.

- **One representation for every type former.** `Ty` is a variable or a
  constructor applied to types (`app c args`): `Number`, functions,
  records, presences, and later `Int`, arrays, `Map`, `Promise`, tuples,
  literal types and named types are constructors (`Con`). Substitution,
  free variables, unification and their lemmas are written once.
- **Rows are Rémy's flat rows over the program's labels.** A record type
  has a slot for each label of the program (`L`, a parameter of the typing
  rules and of inference): a presence (`pre`, `abs`, or a variable) and a
  type. An open row (`{x: T | r}` in inty) is a record whose other slots
  are variables; a closed one has them `abs`. Within the program's labels
  this is equivalent to Rémy's row system with presence, which inty
  implements with tails (`types::RowType`), and it keeps unification
  plain Robinson unification, with no type equality up to permutation.
- **Classes with functional dependencies, once.** `HasProp p τ σ` (a read
  or write of `o.p` on a receiver of unknown type, inty's `a has {p: b}`)
  and `Indexable c i e` (`xs[i]`) are both classes some of whose
  arguments determine the rest: the receiver its field, the container its
  index and element. Resolution on a known type (when a binding
  generalises, and at the end) and the closure of the variables the
  environment fixes (`env_fixed_vars`) are written once for any such
  class, so each container adds only a constructor and instances. A
  constraint left on a type variable is harmless, since no value has a
  type variable's type (`HoldsOrVar`); inty defaults a `HasProp` left so
  to an open row (`default_has_prop`).
- **Objects, containers and built-in properties.** Object literals, reads,
  writes and spread (done: an object is a cell of its fields, so a write
  adds a missing property, as in JavaScript); arrays (done: literals,
  `e[i]` by `Indexable τ ι σ`, `e[i] = v` by `Indexable` and `IndexWrite
  τ`, which strings lack, and `e.l = v` by `FieldWrite τ`, which only
  objects have; `s.length` and `xs.length` as `HasProp` instances), then
  tuples and `Map` with their `Indexable` instances. A class's first
  argument determines the rest, so improvement and its completeness are
  written once over each class's arity (`Pred.decide`,
  `Pred.decide_complete`), and a new instance adds an arm to each.
- **Arrays (done).** An array is a cell of its elements, as an object is
  of its fields. An index that isn't a whole number in bounds is a fault
  (`Result.fault`, which `Safe` allows), as `dynamics` makes it
  (`Stuck::OutOfBounds`), where JavaScript reads `undefined`; a store at
  the length appends. Writing the model found four inty bugs, all fixed:
  stores into a string's characters were accepted (`s[0] = "c"`, a
  `TypeError` in strict code), as were stores of a built-in property
  (`xs.length = 0`, `f.call = 1`) and out-of-bounds reads and writes,
  which `dynamics` let through; and a string literal couldn't be indexed
  (`"xyz"[0]` was rejected). inty wants an index to be an `Int`, where
  the model takes any number (phase 4).
- **Spread (done).** inty was unsound three ways: `{a: 1, ...o}` with `o`
  an open row kept the literal's `a` (`f({a: "s"}).a - 1` was accepted), a
  closed spread after an open one closed the result, and an open operand
  after another dropped the first; and `{...f}` kept a function's call
  signature. inty now extends each side's open tail with the other's
  labels and merges by presence, and rejects spreading a function. The
  model decides each label's slot by a `Merge` constraint that waits for
  the operand's presence, so a spread of a row not yet known has a
  principal type; a scheme keeps its `Merge`s as they are, and the top
  level decides them. inty instead decides at once, making a field the
  operand may lack agree with the one it overrides, and unifies two open
  operands' unknown parts: sound, but it rejects
  `(function (o) { return {...{a: 1}, ...o}; })({a: "s"})`, which the model
  accepts, and its verdict can depend on the order of inference. Matching
  the model would need a deferred spread constraint in inty (a row-level
  `Spread a b c`, decided once `b` is known), which is still to do.
  Evaluation copies each operand's fields once it is evaluated, as
  JavaScript and `dynamics` do.
- **Generalisation quantifies every variable the environment doesn't fix.**
  inty quantifies from the type outward (the type's variables, then those
  of the constraints on them) and leaves a constraint the type doesn't
  reach pending. The model takes it into the scheme. Such a constraint's
  variables appear in no type, then or later, so it stays on type
  variables either way, and the two accept the same programs; only the
  printed schemes differ. Leaving it pending would let the declarative
  rules discharge it with a scheme's own (possibly unsatisfiable)
  assumptions, which breaks completeness.

### 4. Numbers and the remaining base types

- Typed arrays, regex, `Promise` (with `await` as the identity, as in
  `dynamics`).
- Arrays and records invariant while mutable (#96).
- **inty's numbers are principal (done).** inty defaulted numeric
  variables where it generalised a binding (an ambiguous literal to
  `Int`, a parameter-only variable to `Number`, a result-only one to
  `Int`), and typed `+` by whether an operand was already known to be a
  number when it met it (`Arith`) or not (`Plus a`, unifying both
  operands), so `xs.length + y` made `y` an `Int`. Neither is a rule a
  declarative system can state. Now a scheme keeps its numeric variables
  and constraints (`inc` is `<a, b, c> where Arith a b c, NumLit b =>
  (a) => c`); only the end of the program defaults, to `Int`; `+` is one
  class, `Plus a b c` (numbers as `Arith`, or three strings), decided by
  improvement whatever the order; and a recursive group's members are
  generalised over the same variables. Writing it found an unsoundness:
  a scheme's `Arith` didn't check that its operands are numbers (its
  `Num`s are tidied away), so `function h(x) { return x * 2; }
  h("s")` was accepted. Indices stay `Int` (`Indexable`), which is what
  the Go backend needs for machine-integer indexing; the backend compiles
  a function once per type it is used at, takes a parameter that only
  feeds floating-point arithmetic as `float64` (an `Int` argument is a
  `Number`), and gives a polymorphic literal `const` one variable per
  type it is used at. On its benchmarks the generated Go
  has more `int`s and fewer `float64`s, and runs as fast or faster but
  for `spectral-norm` (7% slower, with identical code but for `int` loop
  bounds).
- `Int ≤ Number`, at the top level only; the `Num`, `NumLit`, `Arith`
  and `Plus` classes; `Int` indices; checked `Int` arithmetic (`Stuck::IntRange`) as a
  fault. `Float` is opaque in Lean, so proofs rely on inty's runtime range
  checks, and a bit-level binary64 model, tested against Node, where inty
  doesn't check.

### 5. Literal types, unions and narrowing

- Literal types and their widening; the join rules of
  `docs/type-system.md` (literals widen, `null` and `undefined` make a
  result nullable, a declared union absorbs its arms); `never`; operations
  pushed through each arm of a union; `&&` and `||`. Subsumption only where
  `src/infer` applies it, never as a general conversion rule.
- Narrowing by `typeof`, `===`, `==`, truthiness and discriminants, on
  bindings that never change; after an early exit and in loops; `switch`
  with its exhaustiveness check. The semantic relation handles it as
  "Revisiting Soundness for Occurrence Typing, Semantically" (arXiv
  2609.16299) does.
- Statements apart from expressions (from phase 2).

### 6. Recursive types, methods and classes

- Methods with `this`: an object literal's `this` is its own type, so a
  literal with a method used as one has a recursive type.
- Named types (`Named`) with equality up to unfolding (Brandt and
  Henglein), unification without the occurs check, `V` unfolding a named
  type (inty's recur through functions and fields, so through calls and
  cells).
- Callable rows (`String`, `String.fromCharCode`); classes lowered as inty
  lowers them (factory functions, `#private` fields, accessors, `extends`
  as a spread of the base instance).

### 7. Annotations, program structure and the standard library

- Checking mode beside inference: an annotation is a typing obligation,
  which is how declared unions are introduced; rigid type variables; the
  annotation and `.d.js` type syntax; optional parameters (presence on
  function parameters, `types::FuncParam`).
- Mutual recursion by strongly connected components
  (`docs/scc-inference.md`); modules, each `ns.foo` re-instantiating the
  export's scheme; several files in one run.
- Every builtin and standard-library signature as Lean data generated from
  inty's Rust sources, each native function implemented as `dynamics`
  implements it and proved in `V`.

## Frontends

Python and Lua lower onto inty's shared AST. The model types the AST, so
lowering stays outside it. Lowering gets the λJS treatment instead: lowered
programs are run against CPython and Lua, as JavaScript is against Node.

## Done means

- The coverage table has no gaps.
- The theorems hold for the whole AST.
- The model agrees with inty and the engines on inty's whole test corpus.
  Every disagreement is fixed or is a documented fault.
