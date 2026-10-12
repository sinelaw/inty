# Lean formalization of inty's type system

A machine-checked model of inty's type system, in Lean 4 (core library only,
no Mathlib). It covers a small core calculus, with let-polymorphism under the
value restriction, type schemes that carry class constraints (the ones
inference generalises, with what inty prints as `<a> where Plus a => (a, a)
=> a`; an annotation's scheme carries none, `HasTypeS.letPoly`), a heap with `let` and assignment,
loops, `break`, `continue` and `try`, objects with row-polymorphic record
types and property constraints (`a has {name: b}`), method calls, methods
written `m() {…}` and the classes inty lowers to them, equi-recursive
types, a
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

| Claim | Theorem | File |
|---|---|---|
| A typed program's result is good for its type, at every clock | `eval_sound` | `Soundness.lean` |
| A closed typed program never gets stuck | `never_stuck` | `Soundness.lean` |
| ... with native builtins in scope | `never_stuck_with_builtins` | `Builtins.lean` |
| A program making no call and running no loop never runs out of clock | `eval_noClock` | `NoTimeout.lean` |
| More clock doesn't change a finished result | `run_mono` | `Clock.lean` |
| Typing is closed under type substitution | `HasTypeS.subst` | `TypeSubst.lean` |
| ... under instantiating rigid variables | `HasTypeS.rsub` | `Rigid.lean` |
| ... under adding labels the program doesn't use | `HasType.extLabels` | `LabelWeaken.lean` |
| Unification is most general up to equal types | `unify_mgu` | `Unify.lean` |
| What inference finds is a typing | `inferProgram_sound`, `inferIn_sound` | `InferSound.lean` |
| A program inference accepts never gets stuck | `inferProgram_never_stuck` | `InferSound.lean` |
| Inference finds a most general type whenever there is one | `inferIn_complete`, `inferProgram_complete` | `InferComplete.lean` |
| ... with polymorphic annotations, where no rigid variable escapes | `infer_complete_polyOK`, `inferProgram_complete_polyOK` | `InferComplete.lean` |
| Inference's type with its constraints is principal | `inferInC_principal`, `inferProgramC_principal`, `inferProgramC_principal_polyOK` | `Principal.lean` |
| Where a rigid variable escapes, inference is incomplete | `polyGap_separates` | `PolyAnn.lean` |
| Jones's `let` rule is sound and types strictly more | `jones_eval_sound`, `jones_separates` | `Textbook.lean` |
| inty's assignment rule is sound and types strictly more | `inty_eval_sound`, `assignSub_separates` | `AssignSub.lean` |
| A scheme needs its `Merge` | `spreadMerge_needed` | `MergeScheme.lean` |
| Each checking rule types what synthesis and injection can't | `litStr_needed`, `arrCheck_needed`, `funcCheck_needed` | `Modes.lean` |

`Inty/Statements.lean` restates each of them in full, and `Inty/Axioms.lean`
checks they use only Lean's standard axioms.

`Inty.eval_sound` (in `Inty/Soundness.lean`): for every expression `e`, type
`τ`, labels `L` (records have a slot for each), class constraints `C` each
an instance or on a type variable (`HoldsOrVar`), context `Γ`, world `W` (the scheme of
each cell of the heap), environment `env` whose variables' cells have the
schemes `Γ` gives them, heap `h` that `W` describes for `clock` calls,
enclosing function's return type `R`, and every clock, writing
`(r, c, h') = run clock env h e` for the result, the clock left and the heap
after,

```
HasType L C Γ R rm md e τ → HoldsOrVar C → G W (Γ.map Scheme.toW) env →
  HeapOK clock W h →
  c ≤ clock ∧
  (r = timeout ∨ ∃ W', W <+: W' ∧ HeapOK c W' h' ∧
    ((∃ v, r = ok v ∧ V c W' τ v) ∨ r.Abrupt ∨
     (∃ v, r = returned v ∧ ∃ τr, R = some τr ∧ V c W' τr v)))
```

where an abrupt completion is a `throw` of any value, a `break` or a
`continue` (one outside any loop is ruled out apart, by the scope check
below), or a fault: an index out of bounds, where the program stops, as
`dynamics` does (`Result.fault`). JavaScript reads `undefined` there and
goes on, perhaps to a `TypeError` further on, so for a program that indexes,
"never stuck" is the model's guarantee up to its faults, not JavaScript's.
Soundness is relative to the model's interpreter: that `eval` is
JavaScript on this fragment is the differential test's evidence (below),
not a theorem. `rm` and `md` are the modes of the enclosing function's
`return` and of the expression (`synth` or `check`); `Scheme.toW` reads a
context's schemes in the wide system, `Sys.wide`, which soundness is proved
for and which every typing of `HasType` is one of (`HasTypeS.toWideOf`).

`HoldsOrVar C` asks each assumed constraint to be an instance or to be on a
type variable. A type variable is read as the type with no values, not
parametrically: `V k W (.var a) v` is false. So a constraint on a variable
is vacuous at run time, and soundness says nothing about the parametricity
of polymorphic code (no free theorems); it needs none, since each use of a
polymorphic binding is typed at an instance (`HasTypeS.subst`).

A timeout is allowed at every clock, so the theorem could be met by an
interpreter that always times out. It isn't: the clock counts calls and
loop iterations, and a program that makes no call, runs no loop and has no
getter never runs out of it, whatever the clock (`eval_noClock`); for the
rest, `run_mono` and the examples run at build time (`#guard`) show the
results.

That is CakeML's shape of theorem (Owens et al., "Functional Big-step
Semantics", ESOP 2016): for every clock, a value of the right type, an
exception (here any abrupt completion), or out of time, and never stuck. `V k W τ v` is a step-indexed
Kripke logical relation: `v` behaves as a `τ` for `k` more calls, in any
heap that a world extending `W` describes (see the design choices).
`Inty/Statements.lean` pins each of its clauses.

Its corollary `Inty.never_stuck` says a closed well-typed program never
evaluates to `stuck`. That is the property `src/meta/soundness.rs` samples
with proptest ("Whenever inty accepts a program, the operational semantics
must not get stuck on it"), here proved for all programs of the calculus.
The key lemma for polymorphism is `Inty.HasTypeS.subst` (in
`Inty/TypeSubst.lean`): typing is preserved by substituting types for type
variables. The soundness proof uses it to type a generalised `const` at each
instance of its scheme.

A binding annotated with a polymorphic scheme
(`/** const id: <a>(a) => a */`, `HasTypeS.letPoly`) checks its
initialiser, a syntactic value, with the quantified variables rigid: fresh
constants (`Con.rigid`), named apart from everything in sight by cofinite
quantification, as a `let`'s generalised variables are. Soundness types the
initialiser at each instance by instantiating the rigid variables
(`Inty.HasTypeS.rsub`, in `Inty/Rigid.lean`), in the wide system, which
holds whatever types they are. Inference checks the initialiser at fresh
rigid variables, decides the constraints on known types, and rejects the
program if a rigid variable escapes into the context or into the
constraints left; its soundness swaps the rigid names (`Inty/Rename.lean`).

`Inty.inferProgram_sound` (in `Inty/InferSound.lean`): whatever type inference
finds is a valid typing,

```
inferProgram e = some τ → ∃ C, HoldsOrVar C ∧ HasType e.labels.eraseDups C [] none e τ
```

The constraints `C` are what inference leaves on type variables (`Plus a`,
or a property read on a value of unknown type): inty accepts the program
with them in place, and they can't fail, since no value has a type
variable's type. So, by `Inty.inferProgram_never_stuck`, a program
inference accepts never gets stuck.

Soundness produces a typing under some `C`, while completeness below
starts from a typing under constraints on type variables only, `C = []`
for a closed program. The principal-type theorem joins the two: the `C`
soundness produces is the constraints inference leaves, `P`, and every
typing under any assumptions is an instance of `(τ, P)`
(`inferProgramC_principal`).

`Inty.inferIn_complete` (in `Inty/InferComplete.lean`): inference finds a type
whenever one exists, one of which every valid type is an instance up to
equal types (Damas and Milner's completeness; the freshness invariants,
`Inty/InferInv.lean`, follow Naraschewski and Nipkow's proof of algorithm
W), for the whole of `HasType`: conversion between equal types, methods
and getters, method calls, classes and `new`:

```
ctxFtv Γ = [] → (∀ p ∈ C, p.OnVarShaped) → e.scoped (Γ.map fun _ => false) →
  e.monoAnn → HasType L C Γ none e τ' →
  ∃ τ, inferIn L Γ e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ'
```

Inference has fuel in two places, and neither costs completeness: it
improves constraints at most `preds.length` times, and each improvement
removes a constraint, so the fuel never runs out first (`improveAll_complete`
holds for any fuel at least the length); likewise `fixLoop`, whose every
round sets a constraint aside.

`monoAnn` says the program's annotations are monomorphic. With
polymorphic ones (`Inty/PolyAnn.lean`), inference has one more way to
reject a program than the rules: a rigid variable escaping. `RigidStays`
says none does: in every context where an annotation's initialiser is
checked and typable as the rules allow, inference's check at fresh rigid
variables leaves them out of the context's instance, out of the enclosing
return type and out of the constraints left after improvement, which is
exactly the test inference makes. `Expr.PolyOK` asks it of every
annotation in the program. Under it inference finds every typing
(`infer_complete_polyOK`, `inferProgram_complete_polyOK`), and its
constrained type is principal (`inferProgramC_principal_polyOK`): the typing
checks the initialiser at any rigid names outside a finite set, and renamed
(`HasTypeS.rsub` with a swap), it is a typing at inference's. Escaping
into the context is the case the proof handles itself: a typing's context
has no rigid variables, so no unfolded tree of the context's instance can
have one (`Ty.TreeRk`, `Inty/RigidKeys.lean`); only an equation of a
recursive type its unfolding never reaches could, which the check counts
and the rules don't see. Every program with only monomorphic annotations is
`PolyOK` (`Expr.polyOK_of_monoAnn`), and so is
`/** const id: <a>(a) => a */ const id = (y) => y; id(1)` (`polyId_polyOK`).
`PolyOK` is a semantic condition, decided here per program, not a syntactic
class: inference accepts `polyApp`, an annotated function applied to
itself, but its `PolyOK` is not proved. Where a rigid variable does escape,
inference is incomplete (`polyGap_separates`): in

```
/** const f: <a>(a) => a */
const f = (y) => { const g = true ? (o) => o.l : (o) => y; return y; };
```

`o.l` has the rigid type `a`, which leaves `HasProp l` on `o`'s type, a
variable nothing fixes, with the field's type `a`. A typing picks `o` the
type `{l: a}` at each rigid name; inference would have to keep the
constraint on the rigid variable waiting on a type variable, an implication
constraint, as GHC's OutsideIn(X) does, and rejects it instead.

One more divergence of the model from inty: inty checks a polymorphic
initialiser with the binding itself in scope at its scheme
(`check_polymorphic_annotation`), so an annotated function can call itself
at another instance (polymorphic recursion); the model's `letPoly` checks
it in the enclosing context, where a named function sees itself only at the
rigid instance.

`scoped` is the pair of scope checks JavaScript makes: a program assigns
only to its own `let`s and parameters, never to a `const`
(`assignsMutable`), and has `break` and `continue` only inside a loop
(`jumpsInLoop`). They are checks beside the typing rules, not among them:
an assignment to a `const` would be type-safe, and a stray `break` is
safe too, just not JavaScript.

Completeness is relative to a specification designed with the algorithm:
`HasType` is declarative, but some of its rules are inty's choices, each
narrower than a textbook rule, and each is checked by a theorem relating it
to the wider one or showing it can't be dropped:

- **A `let`'s scheme has constraints only on its quantified variables**
  (`Scheme.Simple`). Jones's rule allows any; `Inty/Textbook.lean` proves
  it sound and strictly wider (`jones_separates`), below.
- **A scheme keeps its `Merge`s undecided** (`PTy.TreeBound`).
  `spreadMerge_needed` (`Inty/MergeScheme.lean`): a function spreading its
  parameter, used at two field lists, has typings only at schemes carrying a
  `Merge`.
- **Checking mode has rules of its own** for literal forms; each types
  something synthesis followed by injection can't (`Inty/Modes.lean`).
- **An assignment's value has the variable's type exactly.** inty's rule,
  which checks it against the type, is `Sys.inty`, sound and strictly wider
  (`assignSub_separates`, `Inty/AssignSub.lean`); the wire format's front
  end rewrites the one case where they differ, an annotated `let`.
- **Annotations are closed** (`Annotated`: no type variables), **an object
  literal checked against a record has only data fields** (`objCheck`), and
  **a class's labels are distinct** (`ls.Nodup`, though JavaScript allows a
  member defined twice). These are restrictions inty has too, or that the
  wire format's front end avoids; no theorem relates them to wider rules.

Completeness rests on unification
being most general up to equal types (`Inty.unify_mgu`): `unify` is a
congruence closure on the types' finite graphs of subterms (Huet's
algorithm for rational trees, `Inty/Unify.lean`). A typing's context need
only have schemes equal to inference's (`CtxEq`), and a `let`'s typing of
the rest moves to inference's more general scheme (`HasType.weaken`, in
`Inty/Weaken.lean`).

Why each of the `let` rule's side conditions is the rule, not a choice
copied from the algorithm:

- **The value restriction** is ML's (Wright 1995): only a syntactic value
  is generalised, and a `let` that is assigned isn't, since a cell holds
  one type. inty's `is_syntactic_value` and `written_at` are the same test.
- **A scheme's constraints are on its quantified variables**
  (`Scheme.Simple`): the initialiser's constraints split into those on the
  quantified variables, kept in the scheme, and the rest, which stay
  assumptions of the enclosing context (`C`), as HM(X) splits them. A
  constraint on no quantified variable in a scheme would be checked at
  every use instead of once. Jones's textbook rule (*Qualified Types*)
  allows a scheme any constraints, and `Inty/Textbook.lean` relates the
  two: `Sys.jones` is the system with Jones's rule (`Sys.anyScheme`, which
  `HasType`'s `Sys.narrow` turns off), every typing of `HasType` is one of
  it (`HasType.toJones`), it is sound too (`jones_eval_sound`,
  `jones_never_stuck`), so the side condition is there for inference, not
  for soundness, and it types strictly more (`jones_separates`):
  `const f = (y) => true + true; 1`, whose unused `f` carries `Plus
  boolean`, which no instance satisfies. Jones's rule accepts it, as
  Haskell accepts an unused binding with an unsatisfiable constraint;
  `HasType` and inty reject it.
- **`Merge` stays undecided in a scheme** while its determining arguments
  are quantified (`PTy.TreeBound`): a spread over a parameter's object
  has no field list until a call gives one, so deciding it at the `let`
  would guess, and the most general scheme keeps it, as Haskell keeps a
  class constraint on a quantified variable. Without it some programs have
  no typing: `spreadMerge_needed`. inty decides a spread at
  once (`merge_spread`), which is less general: the known divergence of
  a spread over an operand of an unknown type. One consequence, as in
  Haskell without the monomorphism restriction: a binding never used can
  carry a `Merge` no instance satisfies, which is harmless, since only a
  use instantiates it.
- **The scope checks are beside the rules** (`Expr.scoped`): a `break`
  outside a loop is one of JavaScript's early errors, static semantics
  apart from typing, and an assignment to a `const` throws a `TypeError`
  when it runs, which a value's type doesn't predict (the variable keeps
  its type either way). Neither is about the types of values, so each is a
  check of its own, as inty reports them apart from its type errors.

**Principal constrained types** (`Inty/Principal.lean`). Inference's type
comes with the constraints it leaves (`inferInC`, which is `inferIn`
keeping them), and the pair `(τ, P)` is principal: under assumptions `C`
on type variables, a program with only monomorphic annotations has the
type `τ'` exactly when `τ'` is an instance `τ.subst φ`, up to equal types,
whose constraints `P.subst φ` the assumptions entail
(`inferInC_principal`, `inferProgramC_principal`). One direction is
completeness, now with constraints (`inferInC_complete`); the other is
soundness (`inferInC_sound`) with substitution and the cut rule
(`HasTypeS.cutC`: a typing under assumptions `D` holds under any `C`
entailing each of them).

A recursive type carries its whole system of equations, and an equation
its unfolding never reaches may mention variables the type doesn't have,
so equal types can differ in their free variables. Generalisation is over
the variables of the unfolded trees (`Ty.tv`, `Inty/TreeVars.lean`), and a
scheme's `Merge` must have a quantified variable in the trees of its
determining arguments (`Scheme.Simple`, `PTy.TreeBound`): a variable that
appears only in an unreached equation fixes nothing and is fixed by
nothing.

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
| `Ty`: a type variable, a constructor (`Con`) applied to types (`number`, `string`, `boolean`, `undefined`, `null`, `unknown` (what a `catch` binds: any value), `fn` (the type of `this`, the result's and the parameters'), `record` over a list of labels (a slot per label: a presence, `pre` or `abs` or a variable, and a type), `array`), or the `i`-th type of a system of recursive equations (`mu i sys`, right-hand sides `RTy` referring to the system's types as `self j`) | `types::Type` (an `fn` is the call signature of a callable row, `Type::Func`; a `record` is a `RowType`, whose tail the flat slots stand for; `number` is `Number`; a `mu` is a `Type::Named` with its equation in `InferState::named_types`) |
| `TyEq` (`Inty/Equi.lean`): equality up to unfolding, as the unfolded trees' finite approximations | `unify` on `Named` types (`unroll_named`) |
| `Scheme` (`∀ α₀ … αₖ₋₁. plus ⇒ τ`, body and constraints `PTy`s) | `types::TypeScheme`, with its `where` clause |
| `Expr`: literals, variables, named functions of any number of parameters (recursive, with `this`), calls outside a receiver (`this` is `undefined`; one argument per parameter), `const`, `let`, assignment to a variable, `?:`, `!`, `typeof`, unary `-`, `+`, `-`, `*`, `/`, `<`, `<=`, `>`, `>=` (of numbers), `===`, `!==`, `return`, `throw`, statement sequences, `while`, `break`, `continue`, `try`/`catch`, `try`/`finally`, object literals (a field holds a value, or is a method `l(…) {…}` or a getter `get l() {…}` written as a function expression whose `this` is the literal's type: `FieldSlot`), property reads and writes, object spread (`{...e₁, ...e₂}`, which a literal with spreads and fields lowers to), array literals, `e[i]`, `e[i] = v`, method calls `e.l(args)` (`this` the receiver) | `ast::Expr`, `ast::Stmt` |
| A class without `extends` (`cls`: fields with initialisers that see the fields before them, arrow fields, methods and getters on the prototype, `MemberSlot`), its constructor (`ctor`, whose `this` is what `new` makes, `newTarget`) and `new`, which calls only a closure (`Value.asCtor`: an arrow field isn't a constructor, its `this` is `NotNew`) | the class lowering, `parse_class_declaration_named` in `src/frontends/javascript/parser`, `class_fields.rs`; an arrow function's `this` is `Type::ArrowThis`, which `unify_this` keeps from `NewTarget` |
| `Result`: `ok`, `stuck`, `timeout`, `returned`, `thrown`, `broke`, `continued`; `bindC` | `dynamics::StmtOutcome`, `Stuck` |
| `HasType` (declarative typing, Hindley–Milner style, with a conversion rule between equal types) | what `src/infer` implements |
| `Annotated`, `HasTypeS.letPoly`, `Con.rigid` (an annotation: a type without variables, or a polymorphic scheme whose variables are rigid constants in the initialiser) | `infer_stmt_var`, `check_polymorphic_annotation` in `src/infer/features/bindings.rs` (skolems, `skolemize`, and the escape check) |
| `HasTypeS.drop` (a statement's value is dropped: an expression nothing uses the value of is checked against `unknown`) | `infer_discarded` in `src/infer/features/control.rs`; `infer_stmt_if` and `try` don't join their branches |
| `Expr.IsValue` (the value restriction), `Expr.writes` (a `let` that is assigned isn't generalised) | `is_syntactic_value`, `src/infer/features/bindings.rs`; `Resolution::written_at`, `src/ast/resolve.rs` |
| `Expr.scoped`: `assignsMutable` (no assignment to a `const`), `jumpsInLoop` (`break` and `continue` only in a loop) | `check_assignment_target`; the parser |
| `UnOpTy`, `BinOpTy` (one constructor per operator rule) | the operator catalog, `src/operators` |
| `Cls`, `Pred`, `Inst` (`Inty/Classes.lean`): classes (`Plus`, `HasProp`, `Merge`, `Indexable`, `IndexWrite`, `NotNew`), constraints, instances | `classes::ClassName`, the instance tables in `src/classes`, `resolve_has_prop`; `Merge` is a spread's per-field merge (`merge_spread` in `src/infer/features/rows.rs`, which decides it at once) |
| `improveAll` (deciding constraints on known types), `fixedVars` and `genVars` (what a `let` quantifies) | `simplify_has_props`, `env_fixed_vars`, `InferState::generalize` |
| `Entails C p` (`p` is an instance up to equal types, or assumed in `C`) | a scheme's constraints in scope while checking its body |
| `unify` (up to unfolding, by congruence closure: a variable occurring under a record or a function is bound to a recursive type), `infer`, `inferProgram` (Algorithm W) | `src/infer` (`unify.rs`, `var_bind`, `create_recursive_type`, the per-feature rules) |
| `Out.preds` (pending class constraints) | the constraints `src/infer` resolves once types are known |
| `Value`, `Stuck`, `run` / `eval` (interpreter with a call clock and a heap, every binding a cell, an object a cell of its fields) | `src/dynamics` (`Value`, `Stuck`, fuel, `heap.rs`, `RuntimeEnv`, `Cell::Object`) |
| `Prim`, `builtinCtx`, `builtinEnv`, `builtinHeap` (native functions, with their types) | `Value::Builtin`, `src/builtins` |
| `Value.truthy`, `Value.typeString` | `Value::truthy`, `Value::type_string` |
| `World` (a cell's scheme, or the record type of an object's fields, or an array's element type), `V`, `CellV`, `HeapOK`, `G`, `eval_sound` (semantic typing) | `src/meta/soundness.rs` |

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
- **Every type former is a constructor applied to types** (`Ty.app c
  args`), so substitution, free variables, unification and their lemmas
  are written once, and a new type former (arrays, `Map`, literal types)
  adds a `Con` and its rules, not cases to every proof. `Ty.fn`,
  `Ty.record` and the rest are pattern-matchable abbreviations.
- **Rows are Rémy's flat rows over the program's labels.** A record type
  has a slot for every label of the program (`L`, a parameter of the typing
  rules and of inference), with a presence and a type. An open row, inty's
  `{x: T | r}`, is a record whose other slots are variables. Within the
  program's labels this is equivalent to Rémy's rows with presence, which
  inty implements with tails, and it keeps unification free of type
  equality up to permutation. A typing over the program's labels is one
  over any more labels (`HasType.extLabels`, `Inty/LabelWeaken.lean`), so
  the choice of `L` doesn't change what is typable. The cost is size: every record has a slot
  per label of the program, so inference slows as a program's labels grow
  (seconds, interpreted, for a few nested spreads over twenty or thirty
  labels). That is fine for an oracle on generated programs and on inty's
  test corpus; larger programs will want rows with tails, or the labels a
  program's records can share.
- **Types and expressions nest lists** (a constructor's arguments, a call's
  arguments). Lean derives neither
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
  interpreter's clock, as in CakeML. A world says what each cell holds (a
  variable's scheme, an object's record type, an array's element type);
  cells never change, so worlds only grow (`<+:`). `V k W (τ₁ → τ₂) f`
  says that calling `f` with any clock `j ≤ k`, in any larger world, on a
  heap that world describes one tick down and on an argument in `V i τ₁`
  for every `i < j`, takes a tick and gives back a `V c τ₂` value at the
  clock `c` left, in a still larger world describing the heap after, or
  completes abruptly (a `throw`, a `break` or `continue` that escapes it,
  a fault), or runs out. A type variable has no values. A recursive type has
  its unfolding's values. Since worlds map cells to syntactic types, `V` at
  index `k` needs `V` at arbitrary types only below `k` (the arguments of
  a call are good only below its clock, since the body runs a tick down,
  which is what makes unfolding a recursive type terminate), and is
  defined by well-founded recursion on the index. The
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
- **Class constraints are assumptions in the judgement.** `HasType L C Γ R e τ`
  types `e` assuming the constraints in `C`, as in HM(X). A class is a
  `Cls` with its instances in `Inst` (`Inty/Classes.lean`): `Plus`;
  `HasProp l a k b`, a property read on a value of unknown type, whose
  receiver determines the field (a functional dependency); `Merge`, a
  spread's slot; `Indexable` and `IndexWrite`, indexing; and `NotNew`, an
  arrow field's `this`, which `new` doesn't give. A `const` types its
  initialiser assuming its scheme's constraints, and each use of the
  variable must establish them. Inference records a pending constraint at
  each `+`, each property access, spread and index, and each arrow field;
  before a `const` generalises, it decides the ones on known types
  (`improveAll`), but a `Plus` (decided at the end) and a `Merge` (decided
  at the top level), and it doesn't quantify a field type whose receiver
  the environment fixes. So a binding that is never used can keep a
  `Merge` no instance satisfies, and be accepted: deciding it at the
  binding would depend on whether its presence is known by then, which no
  rule closed under substitution can state; a use decides it.
- **A constraint left on a type variable is harmless.** No value has a
  type variable's type, so code relying on such a constraint never runs:
  the soundness theorem assumes only `HoldsOrVar C`, and inference accepts
  a program whose leftover constraints are instances or on type variables,
  as inty does.
- **An object is a cell holding its fields**, as in `dynamics`; the world
  gives the cell a record type (`Cell.obj`), and `V` of a record is a
  reference to such a cell, of an equal record type, so aliasing and writes
  need nothing new. The fields are the record's present ones and none of
  its absent ones, and a slot whose presence is a variable has no
  contents, as a type variable has no values.
- **Recursive types are equi-recursive, each carrying its equations.** A
  `mu i sys` is the type its equation gives, with `self j` read as `mu j
  sys`; its right-hand sides are a type of their own (`RTy`), so no
  substitution can capture a `self`. Equality up to unfolding (`TyEq`) is
  the equality of the unfolded trees, through their finite
  approximations: an equivalence, closed under substitution and taken
  apart by constructors without coinduction. inty keeps its recursive
  types in one table, without parameters, so a factory's type variables
  freeze; the model's carry their own and stay polymorphic.
- **A spread merges slot by slot, when the operand's presence is known.**
  `{...e₁, ...e₂}`'s slot for each label is `Merge p τ s r`: `e₂`'s
  presence `p` and type `τ` over `e₁`'s slot `s` give `r`, `e₂`'s field if
  `p` is `pre`, `s` if `abs`. With `p` a variable the constraint waits, so
  `function f(o) { return {a: 1, ...o}; }` has a principal type, under
  which `f({a: "s"}).a` is a string. A scheme keeps its `Merge`s as they
  are (deciding them where a binding generalises would depend on whether
  `p` is known by then, which no rule closed under substitution can
  state), and the top level decides them. inty decides each at once,
  making a field the operand may lack agree with the one it overrides, so
  it rejects that call; the model is the more precise of the two.
- **An index out of bounds is a fault.** An array is a cell of its
  elements; `e[i]` with `i` not a whole number below the length is
  `Result.fault`, which soundness allows, as `dynamics`' `OutOfBounds`
  (JavaScript reads `undefined`). A store at the length appends.
- **Numbers are one type, `number`, as in JavaScript.** inty had an `Int`
  type beside `Number`, with `Int ≤ Number` and classes deciding which an
  operation gave; it now has one number type too, and its Go backend finds
  the integers by an analysis of its own, outside the type system
  (`crates/inty-go/src/kinds.rs`), which can't reject a program. An index
  is any number; a fractional one is out of bounds, a fault.
- **Where the interpreter isn't JavaScript.** Besides the faults: a
  string is a sequence of code points, as `dynamics`' are, where
  JavaScript's are UTF-16 units (`"😀".length` is 1 here, 2 there); `new`
  runs a method and a class's constructor can be called without `new`,
  where JavaScript throws a `TypeError` (typing rules out both: a method's
  `this` is its object, a constructor's `newTarget`); and a `break` in a
  function called from a loop ends that loop, which the scope check rules
  out; and a function has no identity, so `f === f` is false (typing
  allows it: `===` takes any two values; the differential generator
compares only values of one type, never functions). The differential
test keeps to
  programs where none of these arises.

## Adding a feature

This mirrors "Adding a typing feature" in `ARCHITECTURE.md`:

1. Syntax: a constructor in `Expr` (and in `Ty` / `Value` if needed).
2. Typing: a rule in `HasType` (and `HasTypeTop`, its rules but the
   conversion), or an arm in `UnOpTy` / `BinOpTy`.
3. Semantics: an arm in `run` (or `UnOp.eval` / `BinOp.eval`, or
   `Prim.apply` for a native function).
4. Inference: an arm in `infer`.
5. Proof: a case in `HasType.subst`, `HasType.top`, `HasType.weaken`, `run_sound`
   (or `UnOp.eval_sound` / `BinOp.eval_sound`), `run_clock_le`, `run_mono`,
   `infer_inv`, `infer_sound` and `infer_complete`, and a clause of `V` for a
   new type former. A native function needs only its
   `V` proof (`Prim.abs_sound`).
6. An example in `Inty/Examples.lean`.
7. The wire format (`Inty/Wire.lean`), the differential test's
   generator and JavaScript printer (`crates/inty/tests/differential.rs`),
   and inty's lowering into the wire format (`crates/inty/src/model_wire.rs`).

Lean's exhaustiveness checks point at every case still missing.

## Roadmap

[ROADMAP.md](ROADMAP.md) plans the rest: seven phases to a complete model
of inty's type system, with the ground rules that keep it faithful to what
inty implements and documents.

## inty's own programs

`crates/inty/tests/model_corpus.rs` runs the model on inty's own programs
(ground rule 4 of the roadmap): every program inty's unit tests check
that lies in the model's fragment, which inty writes in the wire format
itself (`inty::model_wire`), the inverse of the differential test's
printer: a statement list is a sequence, a declaration binds the rest of
its block (function declarations moved up as JavaScript hoists them), a
function's body ends in what it returns, and a test of a binding for
nothing, of its `typeof` or of its tag field is `unwrap`, `typetest` or
`casetag` (on a binding an annotation declares a sum or a variant; on
another, a plain `?:` on `===`); `&&` and `||` of booleans are `?:`. A
program is left out when it uses what the model lacks (`%`, a bitwise
operator, a comparison of strings or booleans, `&&` or `||` on what isn't
a boolean, whose result inty types as a union, a builtin, a class (inty's
parser lowers it to a factory function, which the corpus would then check
as one; the differential test generates real class declarations), a
module, a loop other than `while`, `?.`, `??`) or whose lowering would
change its meaning (a name used before its declaration, `let x;` without
an initialiser, a `let` or a parameter taken apart by a test and
assigned, a getter or a method beside a spread). Of the programs the unit tests check,
1242 are in the fragment (some tests generate theirs at random, so the
corpus keeps each program it once recorded); inty and the model agree on
accepting each but four, listed with their reasons in
`tests/model_corpus/known.txt`. Where both accept, the test compares more:
the types, compared by their heads (761 programs have the same), and the
values, where the model's type isn't `undefined`: inty's `dynamics`, the
model's `eval` and Node give the same on 630. A type or value that
differs, an accepted program that gets stuck, or one Node raises an error
on fails the test. Without the model built the test skips; CI sets
`INTY_REQUIRE_MODEL`, under which it, and the differential test, fail
instead.

The four:

- an annotated object type's method using `this` (a member of an object
  type is called on the object in inty), inty's spread over an operand of
  an unknown type, a `typeof` test for a tag no case has (inty warns that
  the branch is dead), and `never` from a `while (true)` body.

A fifth went when inty stopped reading a record with a key known only at
run time (`o[k]`, `k` a string variable). inty gave the union of the
fields' types, but the key may name no field, and the read gives
`undefined`: `o[k].length` was accepted and threw. Now only a literal key
reads a record (`o["x"]`, as `o.x`), as in the model, and a string-keyed
map is a `Dict<V>`, whose read gives `V | Undefined`.

Three more went when inty's numbers became one type: an index with a
fraction, and (twice) a property read on an arithmetic result, which
inty left on the variable its `Arith` class constrained.

Writing the lowering found the model's assignment to an annotated `let`
unifying the value with the annotation rather than checking it against
it. `HasType` still does, the front end rewriting the assignment
(`x = (const t: T = e; t)`); `Sys.inty` has inty's rule
(`HasTypeS.assignCheck`). Comparing values found a bug in inty's
`dynamics`, which treated `undefined` as an unbound name, and two in the
harness (strings escaped on one side only; a result read from `"use
strict"` instead of the program). With `*`, `/`, the comparisons and `===` in the model, most programs left
out read a builtin's property or name a builtin, or use a name before its
declaration.

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

With phase 2 (`let`, assignment, loops, `try`), over 100,000 more programs
(five seeds) agreed. They found three bugs in inty: a caught exception
typed with a flexible variable (unsound), a named function expression's
own name assignable (a `TypeError` in JavaScript), and `dynamics` not
catching a `throw` out of a called function, and getting stuck on extra
arguments, which inty's typing lets a function literal ignore.

Over 200,000 programs (ten seeds), the interpreters never disagreed, and
the model never accepted a program inty rejects, except as below. The
disagreements in typing all fall into features the model lacks:

| Divergence | inty | model | Roadmap phase |
|---|---|---|---|
| A function that only throws | returns `never`, which nothing else unifies with | a free type variable | 5 |
| A function literal with fewer parameters than the type expected of it: `f(function () {…})` where `f` calls its argument with one | accepts (extra arguments are ignored) | rejects | 7 |
| A program that can't complete normally, such as a function whose body only throws | a type of its own (`undefined` for a body that ends in a statement) | a free type variable, which no value has | 5 (`never`) |
| A field every arm of a discriminated union has, read without a test of the tag: `v.kind` | accepts (the union of the arms' field types) | rejects (a variant's fields are read once a test takes it apart) | 7 |
| A spread over an operand of an unknown type: `{...a, ...xs[0]}` with `xs` an empty array | a field the operand may write gets a union with a type variable | merges slot by slot once the operand is known | 3 (a deferred `Spread`) |
| A record case after `typeof x !== "object"`: `typeof x === "object" ? 0 : x - 1` with `x: Number \| {a: Number}` | keeps it (a declaration may type a function as a record: `Promise`, `Object`) | drops it (its records are object literals') | a `typeof` for declared values |
| A sum joined with one of its cases: `c ? v : 1` with `v: Number \| String` (or `Number \| Null`) | the sum | rejects (branches have one type) | the waiting `Join` (`docs/sum-types-design.md`) |

The nullable join is gone from both: inty now has the model's sums
(`T | Null` is `Nullable T`, made by an annotation, taken apart by `??`
or a test for nothing), and on programs with sums the two agree but for
the divergences above. So do they on variants tagged by a field
(discriminated unions, `{kind: "circle", r: Number} | {kind: "square", s:
Number}`), built by tagged literals checked against an annotation and
taken apart by a test of the tag (`v.kind === "circle" ? … : …`), but for
the divergences above (a disagreement on a program that reads a variant's
field without a test is put down to that one, for the whole program).
And on sums told apart by `typeof` (`Number | String | (Number) =>
Number | {a: Number}`), introduced by checking against an annotation and
taken apart by a test of `typeof` (`typeof v === "number" ? … : …`). The
test found that inty bound a variable of a type not known yet (a method's
`this.b`) to the sum it flowed into, where the model's `Inject` waits for
its type; and that the model unified a value assigned to an annotated `let` with the
annotation, where inty checks it against it (the model's front end now
reads `x = e` as `x = (const t: T = e; t)` for an annotated `x`, which
gives the same verdicts and values, the heap one cell apart). Its review
found two more in inty: an `Inject` waiting on a variable an importing
module still sees was dropped at the module's end, as a `Strip` was (both
now wait for the importer's uses), and taking a record case for
definitely an object let `Promise`, declared as a record, through a
`typeof x !== "object"` test (the rule is gone; arrays, tuples and `null`
keep it).

With method calls and recursive types, over 40,000 more programs (eight
seeds), with about 450 accepted method calls per 5,000 programs,
agreed, with no exception for recursive types. Reading inty's handling of
them found a soundness bug: unifying a recursive type against a
structural one memoised the unfolding by the recursive type's id alone,
so `function f(x) { return f; }` was accepted at
`(x: Number) => (y: Number) => Number` and `k(1)(2) - 1` computed `NaN`.

The generator writes an object's function field as a method, `m() {…}`,
half the time it doesn't refer to itself, with about 280 accepted
programs with such a method per 5,000. Modelling methods and the classes
inty lowers to them found two more ways inty accepted programs that
crash, both in classes: a subclass's instances ran its base's methods,
which were checked with the base's instance as `this` (`{label: 5,
...this}.label - 1` in the base read the subclass's string label), and a
method read a constructor parameter where JavaScript reads the variable
outside the class. inty now rejects `extends`, and a method or field
initialiser that reads a name which is a constructor parameter.

Until then the generator had no classes, constructors or `new`, so nothing
exercised an arrow field under `new`, which both inty and the model typed
and ran, where JavaScript throws a `TypeError` (an independent review of
the model found it). It now writes classes as JavaScript class
declarations: fields set in the constructor, each seeing those before it;
arrow fields; methods and getters on the prototype; and a use of a new
instance, including `new` on an arrow field. The class itself appears only
under `new`, since both interpreters run a class called without `new`.
Run against the code before the fix, it reports both accepting a program
that raises `TypeError`; it also found inty's `dynamics` running `new` on
an arrow field that uses `this`, which the class lowering turns into a
method. Over 21,000 programs (seven seeds), about 9% with a class, it
finds no other disagreement.

Each row is recognised from evidence, not guessed: a union in the
types inty gave the program's expressions, say. (Two rows, `Int` and
`Number` under a function type and an index that is a `Number`, went
when inty's numbers became one type.) The harness's first run also
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
