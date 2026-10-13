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
   allowed: out of clock, an uncaught `throw`, an out-of-bounds read, and
   so on. A `fault` outcome lists them, each citing where
   `docs/type-system.md` allows it. So the model can be neither stronger
   nor weaker than what inty promises. (So for `outOfBounds`, which cites
   the document's table of faults.)
2. **The specification is what inty means, not what Hindley–Milner
   allows.** "Declared, not guessed" unions, defaulting and narrowing are
   rules of `HasType`, not features of the algorithm only. That keeps
   completeness provable: a program the rules accept and inty rejects is a
   bug in one of them.
3. **One rule per Rust rule.** Every `HasType` rule, class instance and
   improvement rule names its counterpart in `src/infer/features/*.rs`,
   `src/classes` or `src/operators`. A generated coverage table, checked in
   CI, lists the inty rules that have no Lean counterpart. (Done for the
   typing rules: `COVERAGE.md`, checked by
   `crates/inty/tests/lean_coverage.rs`; not yet for the class instances
   and improvement rules.)
4. **The model runs on real programs.** inty writes out its lowered AST in
   the wire format, so the differential test runs on inty's own test suite
   and examples, beside the generated programs. Node, and later CPython and
   Lua, check the semantics. (Done for typing on the unit tests' programs
   in the model's fragment, 1242 of them: `inty::model_wire`,
   `tests/model_corpus.rs`, which also compares their types and runs them
   in `dynamics`, the model and Node. Not yet: the examples, which use what
   the model lacks, and classes, which the corpus sees lowered.)
5. **Every phase ends green.** `lake build` with no `sorry`; soundness, and
   inference sound and complete, for everything modelled so far (one
   exception, stated where it arises: completeness for polymorphic
   annotations holds where no rigid variable escapes, `Expr.PolyOK`, and
   beyond that needs implication constraints); the axiom
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
- Algorithm W, proved sound and complete (complete for programs whose
  annotations are monomorphic).
- Generic types (a constructor applied to types), Rémy's flat rows,
  `HasProp` with improvement and inty's generalisation, object literals,
  reads, writes and spread; arrays, indexing (`Indexable`, `IndexWrite`)
  and `length`, with an index out of bounds a fault (phase 3, in
  progress).
- Method calls and equi-recursive types (phase 6, in part).
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
  dependencies), first for `HasProp` in phase 3.

### 1. Completeness of inference

Done: `inferIn_complete` (`Inty/InferComplete.lean`), for the whole
calculus, and to be kept for every later phase. It is completeness against
`HasType`, whose `let` rule writes inty's generalisation as side conditions
(see the README), for scoped programs, relating types but not the
constraints left. The decisions it needed:

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
  scheme to be on one of its quantified variables (`Scheme.Simple`): its
  first argument, or for a `Merge` (which a binding keeps as it is, since
  deciding it there would depend on whether its presence is known yet) a
  quantified variable in the trees of its determining arguments. So a
  `Merge` no instance satisfies, in a binding that is never used, is
  accepted, where the same with `Plus` isn't; a use decides it.
  Jones's rule, with any constraints in a scheme, is `Sys.jones`
  (`Inty/Textbook.lean`): sound, containing `HasType`, and strictly
  larger (`jones_separates`).
- **Termination of unification.** A worklist algorithm that terminates by
  the variables still to eliminate (an explicit list, so no set library is
  needed) and then the size of the equations, proved sound and most
  general (`unify_mgu`) in `Inty/Unify.lean`.
- **Freshness.** Inference's inputs mention only variables below its
  counter (`Below`), and its substitutions stay within it (`Within`), as in
  Naraschewski and Nipkow's proof of algorithm W. A `const`'s scheme is
  opened at a block above everything in sight, which the cofinite rule
  allows. The initialiser is typed assuming the opened scheme's
  constraints; a pending one not on the block is entailed without them
  (`Entails.drop_block`), and the rest are the generalised scheme's.
- Rigid variables came with polymorphic annotations (phase 7). Still to
  come: well-scoped schemes (`bound i` within the arity), now that schemes
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
- **Statements apart from expressions.** Done: a statement's value is
  dropped. The model still treats a statement as an expression with a
  value, as a JavaScript program's completion value is, but checks an
  expression whose value nothing uses (the first part of a sequence, a
  loop's body, a `finally` block) against `unknown`, the type of every
  value, by a rule that drops the synthesised type (`HasTypeS.drop`).
  Check mode pushes `unknown` into an `if`'s or a `try`'s branches, so
  `if (c) { 1; } else { "a"; }` is typed as inty types it. Soundness,
  inference (`checkEx` drops a type checked against `unknown`) and its
  completeness are proved. inty matches: an expression statement's value
  is dropped too (`infer_discarded`), so `c ? 1 : "a";` is a statement
  whose branches needn't agree, but the program's last statement, if it is
  an expression statement, still has one type (an approximation of
  JavaScript's completion value, which a trailing declaration or a final
  `if` or `try` would pass through; the CLI never uses it). The
  differential generator makes
  such statements, in sequences, loop bodies and `finally` blocks.

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
  records, presences, and later arrays, `Map`, `Promise`, tuples,
  literal types and named types are constructors (`Con`). Substitution,
  free variables, unification and their lemmas are written once.
- **Rows are Rémy's flat rows over the program's labels.** A record type
  has a slot for each label of the program (`L`, a parameter of the typing
  rules and of inference): a presence (`pre`, `abs`, or a variable) and a
  type. An open row (`{x: T | r}` in inty) is a record whose other slots
  are variables; a closed one has them `abs`. Within the program's labels
  this is equivalent to Rémy's row system with presence, which inty
  implements with tails (`types::RowType`), and it keeps unification free
  of type equality up to permutation.
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
  τ`, which strings lack, and `e.l = v` by `HasProp l τ data σ`, a field
  that holds a value, which only objects have; `s.length` and `xs.length`
  as `HasProp` instances of kind `getter`), then
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
  (`"xyz"[0]` was rejected). An index is any number, in inty as in the
  model; a fractional one is out of bounds, a fault.
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

- **The operators of numbers and `===` (done, in the model's one number
  type).** `*` and `/` (`BinOp.times`, `div`), the comparisons `<`,
  `<=`, `>`, `>=` (`lt`, `le`, `gt`, `ge`, of numbers, IEEE: false with
  a `NaN`) and `===`, `!==` (`strictEq`, of any two values; the model's
  functions have no identity, so two are never equal) share one typing
  rule, `BinOpTyS.num` (operands `number`, result `BinOp.resTy`), beside
  `strictEq`'s; soundness and inference sound and complete. `%` waits for
  an exact `fmod` (Lean's `Float` has none), and comparisons of strings
  and of other values (inty compares any two values of one type, by
  JavaScript's coercions) wait for a model of those coercions. inty's
  lowering takes `&&` and `||` to `?:` (`const t = a; t ? b : t`, or
  `a ? b : false` when `a` is a test). The differential generator uses
  them all.
- Typed arrays, regex, `Promise` (with `await` as the identity, as in
  `dynamics`).
- Arrays and records invariant while mutable (#96).
- **One number type (done).** inty had `Int` beside `Number`: `Int ≤
  Number` for values, the `Num`, `NumLit` and `Arith` classes deciding
  which an operation gave, defaulting at the end of the program, integer
  indices and checked `Int` arithmetic, all for its Go backend's machine
  integers. Now numbers are one type, `Number`, in inty as in the model:
  arithmetic takes and gives `Number`s, `+` is `Plus a` on its operands'
  one type, an index is a number (a fractional one a fault), and an
  integer typed array wraps what it stores. The Go backend finds the
  integers itself, by a type-qualifier analysis (`int ⊑ float`, after
  Foster, Fähndrich and Aiken; `crates/inty-go/src/kinds.rs`): least
  kinds over where values flow, a function copied per pattern of integer
  and float arguments, a parameter a float where no use needs it as an
  integer and it meets a float anyway. It can't reject a program, so it
  is no part of the type system. On the backend's benchmarks the Go code
  prints the same and runs as fast or faster (`fuzzy-search` 1.9x).
  The model's three corpus disagreements on numbers and the differential
  test's two went with it.
- A bit-level binary64 model, tested against Node, for `%` and the
  conversions (`ToInt32`) Lean's opaque `Float` can't state.

### 5. Literal types, unions and narrowing

- **Literal types, in the model's own terms (done for strings and
  booleans).** A literal synthesises its base type; a string literal type
  is made by checking a literal against it, and a value of one is injected
  wherever a `String` is (`Inst.injectLit`, an instance of the `Inject`
  that checking mode uses): into `String`, a sum of it and a sum told
  apart by `typeof` with a string case. A variant's tag is a string or a
  boolean (`Tag`), so `{ok: true, value: T} | {ok: false, error: E}` is a
  variant, built by a tagged literal (`HasTypeS.litBool` checks `true`
  against the type of that boolean, `Con.boolLit`) and taken apart by
  `x.ok === true`. Joins stay what the model has: one type, or the
  expected type pushed into each branch. Soundness and inference sound
  and complete; the differential generator annotates string literal types
  and variants tagged by booleans. It found inty widening a boolean tag
  where the union's arms have one shape (`{a: false, b: undefined}`
  against `{a: true, b: Number} | {a: false, b: Undefined}`), now fixed.
  Left out on purpose ([GAPS.md](GAPS.md)): number literal types, boolean
  literal types beyond tags, and inty's widening of a literal type where
  it synthesises.
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

### 6. Recursive types, methods and classes

- Done: method calls `e.l(args)`, whose method's `this` is the receiver's
  type (inty's `method_receiver`), so a method that returns `this`, or
  reads a property holding a method, makes the receiver's type recursive.
- Done: equi-recursive types. A type can be the `i`-th type of a system of
  equations (`Ty.mu i sys`); inty keeps such systems in one table
  (`Type::Named`), without parameters, where each of the model's carries
  its own, so a recursive type can be polymorphic. Two types are equal
  (`TyEq`) when they unfold to the same infinite tree, defined by its
  finite approximations; typing has a conversion rule; entailment
  compares types up to `TyEq`; `V` gives a recursive type its unfolding's
  values (a call clock bounds the recursion, the arguments of a call being
  good only below it). Unification tries syntactically, then up to
  unfolding, binding a variable that occurs only under a record or a
  function to a recursive type, as inty's `create_recursive_type` does.
  Unification is a congruence closure on the types' finite graphs of
  subterms, most general up to `TyEq`; inference is sound and complete for
  the whole of `HasType`, conversion included. Generalisation is over the
  variables of the unfolded trees (`Ty.tv`), not the free variables of an
  equation system some of whose equations the unfolding never reaches, and
  a simple scheme's `Merge` has a quantified variable in the trees of its
  determining arguments.
- Done: methods written `m() {…}`. In JavaScript a method's `this` is its
  receiver at each call, as a `function`'s is; inty types it as the
  literal's own type (`shared_this` in `infer_object`), which is sound but
  rejects a method borrowed by an object of another type. The model types
  it as inty does: soundness covers it, inference unifies the methods'
  `this`s with each other and then with the literal's type, and
  completeness covers methods, getters, method calls and classes.
- Done: classes without `extends`. inty lowers a class to a factory taking
  the constructor's parameters and returning an object literal whose
  methods are written as methods, and `new C(…)` to a call, which the
  model expresses as it is (`classC` in `Inty/Examples.lean`). Inheritance
  is out of scope: inty rejects `extends`, since a base method, checked
  with the base's instance as `this`, isn't safe on a subclass instance,
  which has more fields. inty also rejects a method or class-body field
  initialiser that reads a name which is a constructor parameter, which
  the lowering would make it read.
- Done: getters, an object literal's and a class's, run with the object
  as `this` at each read, and arrow fields, whose `this` is the instance
  and which `new` doesn't call (`NotNew`). Still to come for classes:
  `#private` fields (labels JavaScript can't write), and inty's nominal
  class types (a brand only rejects more programs).
- Callable rows (`String`, `String.fromCharCode`).

### 7. Annotations, program structure and the standard library

- Checking mode beside inference: an annotation is a typing obligation,
  which is how declared sums are introduced; rigid type variables; the
  annotation and `.d.js` type syntax; optional parameters (presence on
  function parameters, `types::FuncParam`). Done, each with soundness
  and inference sound and complete (but polymorphic annotations: sound,
  and complete where no rigid variable escapes):
  - a binding annotated with a type without variables
    (`/** const x: Number */`);
  - check mode (`HasType`'s return and expression modes): an annotation
    is pushed into `?:`, `unwrap`, a sequence's last statement, a `let`'s
    body, `try`, `return`, function literals against function types and
    array literals against array types; anywhere else the synthesised type
    waits to be injected into it (`Inject T τ`);
  - the sums `Nullable τ` and `Optional τ` (`Con.maybe`), built by an
    annotation and eliminated by `unwrap e₁ e₂ e₃`
    (`const x = e₁; x != null ? e₃ : e₂`; `e₁ ?? e₂` is
    `unwrap e₁ e₂ x`), whose bound value has the type `Strip τ₁ σ` leaves.

  inty matches: tagged sums (`Type::Maybe`), no nullable join, `??` and
  `!= null` with `Strip`, subsumption into a sum with `Inject`; the
  differential generator produces sums and `unwrap`, and finds no
  disagreement on them outside the other known divergences.

  - polymorphic annotations (`/** const id: <a>(a) => a */`,
    `HasTypeS.letPoly`): the initialiser, a syntactic value, is checked with
    the quantified variables rigid (`Con.rigid`), at any name outside a
    finite set, and the binding has every instance. Soundness and inference
    soundness are proved; inference rejects a rigid variable escaping into
    the context or into the constraints left. Completeness is proved for
    every program where no rigid variable escapes (`Expr.PolyOK`,
    `Inty/PolyAnn.lean`), which includes those whose annotations are
    monomorphic, and can fail where one does (`polyGap_separates`): a complete
    algorithm would keep the escaping constraint, on a rigid variable and
    waiting on a type variable, as an implication constraint (GHC's
    OutsideIn(X)). An annotation with constraints (`<a> where Plus a => …`)
    isn't in the model.

  inty matches: a polymorphic annotation on an initialiser is checked with
  skolems and an escape check (`check_polymorphic_annotation`), the
  initialiser seeing its own name at the annotation's scheme (polymorphic
  recursion; the model has no recursive binding). Outside the model, and
  still checked with flexible variables: an annotation with constraints, one
  on an initialiser that isn't a value (`/** const e: <a>a[] */ const e =
  [];`) or on a binding that is assigned; and an optional field's presence,
  which stays flexible.
  The differential generator annotates the polymorphic identity with
  `<a>(a) => a`, sometimes over an initialiser that isn't that polymorphic.

  - variants tagged by a field (`Con.variant l ts`, its tags `ts` the
    constructor's so that a case is picked whatever is known of the cases,
    and `Con.strLit s`, a tag's type): an object literal checked against a
    variant is checked against the case of the tag it writes, a string
    literal (`ObjCase`, and `HasTypeS.litStr` for the tag); against a record
    type, field by field (`HasTypeS.objCheck`). `caseTag e₁ l t e₂ e₃`
    (`const x = e₁; x.l === "t" ? e₃ : e₂`) takes a variant apart:
    `Case_{l,t} τ₁ σ ρ` relates its type to the case of the tag `t` (`σ`,
    which `e₃` sees) and the rest (`ρ`, a variant of the other cases or the
    one left, which `e₂` sees). A variant's values are its cases', each a
    record whose tag field holds its tag (`V`). Soundness and inference
    sound and complete. Not yet: `switch` on the tag and its exhaustiveness,
    and a field read on a variant without a test of the tag (one every case
    has, which inty allows).

  inty matches: an object literal checked against a discriminated union
  takes the arm whose tag it writes, when several arms have its shape and
  a field holds a different string literal type in each (`try_check_object`),
  and widening keeps a declared union that isn't one of literals. Reviewing
  this found a soundness bug in inty's widening: an unannotated `let w = v`
  widened the literal fields of `v`'s declared record, so `w.k = "z"` broke
  `v: {k: "a"}`; widening now stops at what may be shared (a record, an
  array, a function), a literal's own parts being widened where it is
  made. The differential generator annotates variants, builds them from
  tagged literals and takes them apart by their tags; a disagreement on a
  program reading a field of a variant without a test is put down to that
  gap, for the whole program.

  - sums told apart by `typeof` (`Con.variant .typeOf ts`, sharing the
    variants' constructor: `Disc` is a tag field `l` or `typeOf`, a case's
    tag the `typeof` of its head, `Con.typeTag`, no two the same): a value
    of a case is checked into the sum by `Inject` (`Inst.injectArm`, the
    case whose tag is the value's head's); `caseTag e₁ .typeOf t e₂ e₃`
    (`const x = e₁; typeof x === "t" ? e₃ : e₂`) takes one apart by the
    same `Case` class. A sum's values are its cases', with the case's
    `typeof` (`V`, a rank between the variants' and the nullable sums'). An
    assignment to an annotated `let` is read by the wire format's front end
    as `x = (const t: T = e; t)`, so its value is checked against the
    annotation. Soundness and inference sound and complete.

  inty matches: a variable of a type not known yet flowing into a sum told
  apart by `typeof` waits for it (`Inject`, as for the nullable sums,
  `Type::is_typeof_sum`) rather than being bound to the sum, also across
  a module boundary (an `Inject` or a `Strip` on a variable an importer
  still sees waits for its uses), and `typeof x !== "object"` drops an
  array, a tuple or `null` case, but not a record's (a declaration may
  type a function as a record, `Promise` as `{resolve: …}`). The
  differential generator annotates sums of numbers, strings, booleans,
  functions and records, checks values of their cases into them and takes
  them apart by `typeof`; inty's join of a sum with one of its cases
  (`c ? v : 1`, its value used) and the record case it keeps are the
  divergences, put down to the waiting `Join` still to come and to a
  `typeof` for declared values.

  Next: an annotated function type without `this:` is polymorphic in
  `this`; the model fixes it to `undefined`, as inty does for an
  initialiser.
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

- The coverage table has no gaps but those [GAPS.md](GAPS.md) lists.
- The theorems hold for the whole AST.
- The model agrees with inty and the engines on inty's whole test corpus.
  Every disagreement is fixed or is a documented fault.
