# inty: verified type system — status and the sum-types design

Status: proposed, 2026-10-11. The editable copy of this document, with comments, is in Claude Docs; this file is a snapshot.

## Summary

Proposed: inty replaces general unions with sum types — nullable types, sums tagged by runtime type, and variants tagged by a field — so its type system stays Hindley–Milner with type classes, where inference is principal and the Lean model can prove it.

The Lean model of inty's type system already covers a sound and complete core: about 18,400 lines, no `sorry`, only Lean's standard axioms. It covers functions, state and control, records with rows, spread, arrays, recursive types, methods, getters, classes and `new`. A differential test checks it against inty and Node on random programs. Unions are the largest feature it lacks, and they are the main source of disagreement with inty.

The change would make inty reject two kinds of programs it accepts today: mixtures with no tag, from `&&` and `||` on operands of different types, and unions of object shapes that no field tells apart.

## Status of the effort

All of it is in pull request #97 on branch `ccr-18b19451-y3eoms`, with CI green on the latest commit.

### The Lean model (`lean/`)

A core calculus of JavaScript as inty sees it, with declarative typing rules, an executable interpreter, and an inference algorithm.

- **Language:** functions with `this` and recursion; calls and method calls; `const`, `let`, assignment; `?:`, `!`, `typeof`, `-`, `+`; `return`, `throw`, `while`, `break`, `continue`, `try`; object literals with data fields, methods and getters; property reads and writes; spread; arrays, indexing, `length`; classes without `extends` (fields, arrow fields, methods, getters), constructors and `new`.
- **Types:** Hindley–Milner with type classes (`Plus`, `HasProp`, `Merge`, `Indexable`, `IndexWrite`, `NotNew`); Rémy's flat rows with presence and field kinds; equi-recursive types compared by their unfolded trees.
- **Semantics:** a definitional interpreter with a call clock and a heap of cells, as inty's `dynamics` has.

| Theorem | What it says |
| --- | --- |
| `eval_sound`, `never_stuck` | A well-typed program never gets stuck: it returns a value of its type, completes abruptly (a `throw`, or a fault such as an index out of bounds), or runs out of clock. |
| `inferProgram_sound` | What inference finds is a valid typing. |
| `inferIn_complete`, `inferProgram_complete` | Inference finds a type whenever one exists, and every valid type is an instance of it, up to equal recursive types. |
| `unify_mgu` | Unification finds a most general unifier, up to equal recursive types. |
| `HasType.subst`, `HasType.weaken`, `run_mono` | Typing survives type substitution and more general contexts; results don't depend on the clock. |

### The differential test

`crates/inty/tests/differential.rs` generates random programs, typed and adversarial, and runs each through inty, the model and Node. It fails when an accepted program gets stuck, when the interpreters disagree, when Node raises a native error on an accepted program, or when inty and the model type a program differently outside the known divergences. It passes at 3,000 programs on each of eight seeds since the latest changes, about 9% of them with a class.

### What it found

Writing the model and running the test found inty soundness bugs, all fixed in the pull request:

- A caught exception had a flexible type, so `e - 1` on a thrown string was accepted.
- Unifying a recursive type memoised by name alone: `function f(x) { return f; }` was typed so that `f(1)(2) - 1` computed `NaN`.
- Subclass instances ran base-class methods checked against the base's fields; `extends` is now rejected.
- Spread kept or lost the wrong fields in three ways; stores into strings and built-in properties were accepted.
- A store to a getter, a class called without `new`, and `new` on an arrow function were all accepted.
- inty's interpreter got property order, `try` across calls, and evaluation order wrong in places.

### The independent review

A reviewer read only the Lean model, as a sceptical type theorist. It found no unsoundness, no `sorry` and no extra axioms. Its one major finding was `new` on an arrow field, accepted by both inty and the model; that is fixed in both, the model with a new `NotNew` constraint. Its minor findings are fixed or documented: property order on assignment, a `return` inside a class field initialiser, and out-of-date documentation.

## Known gaps

The model covers perhaps a third of what inty checks, and two kinds of work remain: covering the rest, and making the claims withstand review. The second matters more for publication.

### Coverage

| Area | Missing | Effort |
| --- | --- | --- |
| Unions, literal types, narrowing | `never`, `typeof` and `===` narrowing, `&&`, `\|\|`, `?.`, `switch` exhaustiveness (sums, `??` and tests for nothing are done) | Largest; this doc proposes a different design |
| Annotations and program structure | Checking against declared types, rigid type variables, the `.d.js` syntax, optional parameters, mutual recursion, modules | Large; flat rows assume one closed set of labels, which breaks modularity |
| Numbers | `Int` ≤ `Number`, the `Num` and `Arith` classes, integer indices, checked `Int` arithmetic | Medium to large; Lean's `Float` is opaque |
| Statements apart from expressions | inty types `if (c) {1} else {"a"}`; the model wants one type | Medium |
| Remaining syntax | `for`, `for-in`, `for-of`, `do-while`, labels, templates, destructuring, tuples, computed members, modules | Medium, mostly mechanical |
| Standard library | Every builtin's signature and implementation; the model has two | Large, best generated from inty's sources |

### Rigour

1. **The specification is shaped by the algorithm.** The `let` rule writes inty's generalisation as side conditions: constraints only on quantified variables, `Merge` left undecided in schemes, and the scope check outside the rules. Each needs a justification, or a cleaner declarative system proved equivalent.
2. **Completeness compares types, not leftover constraints.** Principal constrained types should be stated with their constraints.
3. **Nothing proves the interpreter is JavaScript.** Agreement with Node is sampled by the differential test. Runtime gaps remain: strings counted in code points, not UTF-16 units; `new` running a method; a class called without `new`. Typing rejects all three.
4. **Nothing proves the model is inty.** The model types its own calculus, not inty's lowered syntax. Planned but not built: inty writing out its lowered programs so the model runs on inty's test suite, and a table mapping each inty rule to its Lean rule.
5. **Soundness holds up to faults.** An index out of bounds stops the program, where JavaScript reads `undefined` and carries on.
6. **Some choices are non-standard.** A recursive type that is an alias of another counts as headless; an arrow field has one `this` type per instance, where inty accepts any; class labels must be distinct.
7. **Pinning is partial.** `Statements.lean` pins the theorems, not the typing rules or the interpreter, which is where a wrong model would hide.

## The problem with unions

Unions bring subtyping, and Hindley–Milner's guarantees depend on there being none. The model proves those guarantees today, so adding unions as inty has them would break the completeness theorem.

### Where inty uses unions today

inty never guesses a union from disagreeing branches; `b ? 42 : "err"` is an error. Unions arise in four ways:

1. **Inferred, with no annotation.** A `null` or `undefined` branch makes the result nullable (`c ? x : null` is `T | Null`); a function that only throws has type `never`, the empty union; `cond && obj` with both types known is `Boolean | Undefined | {…}`.
2. **From library signatures.** `arr.find` and `s.at` return `T | Undefined`; `s.match` returns `String[] | Null`; `replace` and `split` take `String | Regex`; 12 DOM functions return `… | Null`; reading a missing key of a dictionary gives `V | Undefined`.
3. **From annotations.** `Number | String`, `T?` (meaning `T | Undefined`), and discriminated unions such as `{kind: "circle", r: Number} | {kind: "square", s: Number}`.
4. **Taken apart.** Reading a member applies to every arm; narrowing by `typeof`, `===`, `== null`, truthiness and early exit; `??` and `?.`; `switch` with an exhaustiveness warning; a value of one arm accepted where the union is expected.

### Why they are hard to add

- **No single best unifier.** Equality with unions treats `A | B` as `B | A` and `A | A` as `A`. Under those laws, `α | β = Number | String` has several incomparable solutions, so "inference finds the principal type" has nothing to point at. The model's completeness proof rests on `unify_mgu`, which would no longer hold.
- **Subtyping.** Accepting `Number` where `Number | Null` is expected is subtyping. Constraints become inequalities; principal types then carry sets of subtyping constraints, which are hard to simplify and expensive to compare.
- **inty's join depends on inference order.** inty makes a union only if a side is visibly `null` when the join happens. In `const r = c ? x : y` with both unknown, inty unifies `x` and `y`; a later call `f(true, 1, null)` then fails, though a declarative rule would accept it with `r : Number | Null`. Reordering statements can change the verdict, so no completeness theorem holds for the rule as implemented.
- **Interaction with what the model has.** The linked-list idiom `{next: Node | Null}` puts a union inside a recursive type; reading a property of a union needs a new case in `HasProp`; narrowing needs typing that follows control flow.

Soundness, by contrast, is easy: a value has type `A | B` when it has `A` or has `B`.

### What the literature offers

| Approach | Idea | Trade-off |
| --- | --- | --- |
| Constraint-based subtyping (Mitchell; Fuh and Mishra; Aiken and Wimmers 1993; Pottier) | Principal types carry subtyping constraints | Correct, but types are unreadable without heavy simplification |
| Algebraic subtyping: MLsub (Dolan and Mycroft, POPL 2017), Simple-sub (Parreaux, ICFP 2020), MLstruct (Parreaux and Chau, OOPSLA 2022) | Restrict where unions and intersections appear so the lattice behaves | Principal, decidable and practical; infers unions, which inty deliberately does not |
| Set-theoretic types (Castagna et al.) | Types are sets of values, with union, intersection and negation | Expressive and covers narrowing; full inference is hard |
| Annotation-driven (TypeScript, Flow; Pierce and Turner) | Unions only from annotations, local inference | No principality to claim |

## Proposed design: sum types instead of unions

Every union inty needs is replaced by one of four mechanisms, each a type constructor or a type class. None needs subtyping, so unification keeps a single most general solution and inference stays principal.

A sum is built only by injection and taken apart only by case analysis. JavaScript has no constructor syntax, so each mechanism says where the injection happens and which test takes it apart.

### 1. Nullable types

`Nullable T` holds `null` or a value of `T`; the injection is the identity at run time.

- **No nesting.** `Nullable T` requires `NonNull T`, a class that holds of every type but `Null`, `Undefined` and `Nullable _`, as `NotNew` does for `newTarget`. Without it, `Nullable (Nullable T)` is indistinguishable from `Nullable T`, and a generic `first(xs)` returning `null` would not say whether the array was empty or held a `null`.
- **Joins wait.** A branch join becomes a constraint `Join τ₁ τ₂ τ`, decided once both sides are known, as `Merge` is for spread. That removes the order dependence of today's join.
- **Taking it apart:** `x === null`, `x == null`, `x !== undefined`, truthiness of an object type, `??` and `?.`, each a case analysis on the binding tested.

The instances:

```
Join τ τ τ
NonNull τ ⇒ Join τ Null (Nullable τ)
NonNull τ ⇒ Join τ (Nullable τ) (Nullable τ)
```

plus the symmetric instances, and the same with `Undefined` for `Optional T`.

### 2. Sums tagged by runtime type

For primitives, `typeof` is a tag already. A sum `Number + String` (written `Number | String` in annotations) holds values whose arms are disjoint by `typeof` class: number, string, boolean, null, undefined, object, function.

- **Introduced by annotation**, checked against the expected type.
- **Taken apart by** `typeof x === "…"` on a binding, in `if` or `switch`.
- **At most one arm per tag**, so `{x} + {y}` is not a sum of this kind.

### 3. Variants tagged by a field

Discriminated unions are sum types written in JavaScript. A variant type is a row over tag values, each carrying a record: the dual of the model's records, so it reuses rows with presence.

```
[ circle: {r: Number} | square: {s: Number} | ρ ]
```

- **Built by** an object literal whose tag field (`kind`, or a field named in an annotation) holds a string literal; its type is the variant with that case present and the rest open.
- **Taken apart by** `switch (x.kind)` or `if (x.kind === "…")`. A `switch` with every case and no `default` closes the row, which is the exhaustiveness check.
- **Inference stays principal**, as row-polymorphic variants do in OCaml (Garrigue's polymorphic variants, Rémy's rows).

### 4. Type classes for overloading

Parameters typed `String | Regex` are overloading, not sums. They become a class, `Pattern a`, with instances `String` and `Regex`, using the model's existing class machinery.

### What stays as it is

The empty union `never` remains as the type of what does not complete, and `&&` and `||` require both operands of one type, as plain Hindley–Milner does. `obj && obj.x` and `name || "Guest"` with a `String` still type.

## Consequences

The common idioms keep typing; what inty would newly reject is mixtures with no tag and generic code that nests nullability.

| Idiom | Today | Under the proposal |
| --- | --- | --- |
| `c ? x : null`, `return null` on one path | `T \| Null` | `Nullable T`, through a waiting `Join` |
| `arr.find(f)`, `s.at(i)`, DOM `… \| Null` | union return types | `Optional T`, `Nullable T` |
| `x ?? d`, `x?.f`, `if (x === null) return` | narrowing | case analysis on `Nullable` |
| `first(xs)` on `(Number \| Null)[]` | accepted, ambiguous at run time | rejected: `NonNull` fails |
| `Number \| String` annotation, `typeof` test | union and narrowing | sum tagged by `typeof` |
| `{kind: …}` discriminated union, `switch` | union, narrowing, warning when a case is missing | variant over rows; exhaustiveness closes the row |
| `replace(s \| re, …)` | union parameter | class `Pattern a` |
| `cond && obj` (`Boolean` and an object) | `Boolean \| Undefined \| {…}` | rejected unless both operands share a type |
| `x \|\| fallback`, operands of different types | union | rejected |
| `{x, y} \| {x, z}`, no tag field | annotated union | rejected |
| Tuple read at a non-constant index | union of components | rejected unless the components share a type |

### Changes to inty

- Replace the eager nullable join with a pending `Join` constraint, decided when both sides are known; the same pattern as the still-open deferred spread constraint.
- Add `Nullable` with its `NonNull` side condition, and make library signatures use it.
- Restrict annotated unions to arms disjoint by `typeof`, or to variants with a tag field; reject the rest with an error that suggests a tag.
- Type `&&` and `||` with operands of one type.
- Turn `String | Regex` parameters into a class.

### Alternatives considered

- **Algebraic subtyping (MLsub, MLstruct).** The strongest theory, but it infers unions from disagreeing branches, which contradicts inty's "declared, not guessed" stance, and it would replace the model's unifier and its completeness proof.
- **Constraint-based subtyping.** Faithful to today's unions, but principal types carry subtyping constraints that users would see, and implication between constraint sets is expensive to decide.
- **Unions only from annotations, with local inference.** Close to TypeScript. It gives up the principal inference that distinguishes inty.

## Plan

The work runs in the order below; each step ends with the model building, its theorems extended, and the differential test passing with the new syntax.

1. **Nullable types and the waiting join.** *Done, differently:* the model and inty have `Nullable` and `Optional` as two constructors (`Con.maybe z`, a `T | Null` or `T | Undefined` in inty), with no nesting rule and no join: branches have one type, and a sum is said by an annotation and checked against (check mode). Two waiting constraints take the join's place: `Inject T τ` (a `τ` is accepted where the sum `T` is: `T` itself, its nothing, or its value) and `Strip τ σ` (what a `τ` holds besides nothing), used by `??` and by a test for nothing (`unwrap` in the model). Both are sound, and inference with them sound and complete. inty follows: `Type::Maybe`, subsumption as `Inject`, `??` and `!= null` as `Strip`, and the nullable join removed; the differential test has no nullable-join divergence left. *Originally proposed:* Model: `Nullable`, `NonNull`, `Join` with its instances, `null` and `undefined` branches, `??`, `?.`, `=== null` narrowing as case analysis; soundness, inference soundness and completeness. inty: the pending `Join` constraint and `NonNull`. This removes the two largest known divergences, the nullable join and `never`. Effort: medium.
2. **Statements apart from expressions.** *Done, differently:* rather than a separate statement judgement, a statement's value is dropped: the model checks an expression nothing uses the value of (the first part of a sequence, a loop's body, a `finally` block) against `unknown`, by a rule that drops its type (`HasTypeS.drop`), so `if` branches of different types type as inty types them; soundness and inference sound and complete. inty drops an expression statement's value likewise (but the program's last, its completion value). *Originally proposed:* a statement judgement whose only value is what `return` returns. Effort: medium.
3. **Variants tagged by a field.** Model: variant rows, construction from tagged literals, `switch` and `if` on the tag, exhaustiveness. inty: tag-field variants in place of discriminated unions. Effort: medium, reusing rows.
4. **Sums tagged by runtime type and the `Pattern` class.** Needs checking mode for annotations, which comes with phase 7. Effort: medium.
5. **Rigour items, alongside the above.** Justify or simplify the `let` rule; state completeness with constraints; pin the typing rules and the interpreter; fix the recursive alias case; close or justify the runtime gaps; have inty write out its lowered programs so the model runs on inty's test suite.
6. **Then the remaining phases:** numbers (`Int` ≤ `Number`), annotations and modules, the standard library.

Steps 1 to 3 with the rigour items give a publishable claim: principal inference for JavaScript's tagged-union idioms without subtyping, mechanised in Lean and tested against an engine.

### Open questions

- [ ] Is rejecting `cond && obj` and `x || fallback` with differing types acceptable for inty's users?
- [ ] Which field marks a variant: always `kind`, any string-literal field compared by a `switch`, or one named in an annotation?
- [x] Should `Optional T` (with `undefined`) and `Nullable T` (with `null`) be one constructor or two? Two, tagged by their nothing (`Con.maybe z`).
- [ ] `c ? x : null` now needs its sum declared. Is that acceptable, or should a waiting `Join` come back for it?
- [ ] Do annotated unions that are neither disjoint by `typeof` nor tagged stay as an escape hatch, unchecked by the model?
