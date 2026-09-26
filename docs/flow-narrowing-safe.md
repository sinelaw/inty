# Narrowing, the safe version: refine only what cannot change

Status: implemented (`ast/resolve.rs`, `infer/narrow.rs`,
`infer/features/control.rs`). Field writes (#9, below) are still open.
This is an alternative to [flow-narrowing.md](flow-narrowing.md)
that gives up some precision for a much smaller change, whose soundness
argument fits in one sentence:

> A fact about a value stays true as long as the value is the same, so
> narrowing is only allowed on bindings that are never written after
> they are initialised.

This rule matches Typed Racket's occurrence typing, which never refines a
variable that is ever `set!`. It needs no versions, no flow state, no
invalidation on assignment, no loop fixpoint and no reasoning about
closures, because none of those can change a binding that is never
written.

## Why not just drop narrowing?

That would be the safest option, but it removes more than the PR added.
Main already narrows:
- `typeof x === "…"` checks;
- literal comparisons;
- discriminated unions (`shape.kind === "circle"`, documented in
  docs/type-system.md);
- the `T | undefined` that `find()` returns.

These features are used by tests and examples. Reverting only this PR's
additions (null checks, truthiness, `&&`/`||`, early exit) is not enough
either: it would keep main's own holes. Main narrows a reassigned `let`,
narrows through `switch` fall-through, and lets a closure write a narrowed
variable. The version below closes those holes and keeps the new
predicates.

## The rule

A binding `b` is **stable** if nothing writes it after its initialiser.
The resolution pass decides this per binding (§1), and the following all
count as writes:
- `b = e`, `b op= e`, `b++`, `b--`, `??=`, `||=` and `&&=`;
- being a destructuring target, or a `for (b of …)` / `for (b in …)`
  target;
- a second `var b = …` declaration;
- a `var b = …` inside a loop;
- a write from any nested function.

In practice, the stable bindings are:
- every `const` and every import;
- every parameter the function never reassigns;
- every `let`, and every `var` declared once outside a loop, that is
  never reassigned.

**Narrowing applies to stable bindings only.** For any other binding, a
test yields no fact, and the binding keeps its declared type everywhere.

Because a stable binding's value is fixed from initialisation to the end
of its scope, every fact established about it holds for the rest of the
scope on every path where the test came out that way. The narrowing
environment can then stay exactly as it is today: persistent, passed
down into branches, never updated by assignments.

## What that removes from the current PR

- The statement wrapper that ended narrowings after assignments, and its
  `simple_store` and `If` special cases.
- `loop_entry_env`. A loop cannot change a stable binding, so facts from
  before the loop hold in it.
- The `guarded` operand of `test_facts_in`. The guarded operand cannot
  write a stable binding.
- `closure_assigned`, `assigned_anywhere`, and the function-entry
  unnarrowing. A closure can neither write a stable binding nor observe
  a changed value.
- Checking stores against the declared type. There are no stores to a
  stable binding.

## What stays, or is added

1. **Binding resolution** (the same pass as §2 of flow-narrowing.md,
   minus the per-statement write sets). It records, per binding, whether
   it is stable, and maps each identifier occurrence to its binding. This
   fixes the review's #2 (a `var` redeclaration counts as a write) and
   #4 (the result can no longer depend on names).
2. **Predicates:**
   - `x === e` and `x !== e` narrow by the *type* of `e`:
     - a singleton type (`Null`, `Undefined`, a literal) narrows both
       ways;
     - any other type narrows only in the positive branch.
   - `x == e` and `x != e` narrow to "null or undefined" only when `e`'s
     type is `Null` or `Undefined`.
   - `typeof`, `isinstance`, truthiness per language, `!`, `&&`, `||`
     and `?:` work as in the current PR.

   Deciding by type fixes #3a: a local `const undefined = 0` is an `Int`,
   not the unit value.
3. **Early exit:**
   - After `if (c) S`, where `S` always returns, throws, breaks or
     continues, the rest of the block is checked in `c`'s false
     environment. `else` works the other way round.
   - The conservative syntactic `always_exits` stays, with labeled
     statements counted as not exiting.
   - This is sound without flow tracking, because nothing between the
     test and a later read can change a stable binding.
4. **Loops:**
   - `while (c)` and `for (…; c; …)` check the body in `c`'s true
     environment.
   - After a `while` with no `break`, the rest of the block uses the
     false environment.
   - A `for` loop's update is checked in the body's environment, as in
     the `while` form. This fixes #5.
5. **`try`:** the handler and the `finally` block start from the
   narrowings in force before the `try`. They may run before any test in
   the block, but after every test that preceded the `try`. Bindings the
   block declares keep their types. This fixes #7 without losing the
   narrowings of `const`s.
6. **`switch`:** a case reached by falling through from the case before
   gets no case narrowing (a pre-existing hole).
7. **Python `==`** is lowered to its own operator, since it calls
   `__eq__`, and narrows only in ways `__eq__` cannot break:
   - `x != lit` rules out the literal itself;
   - `x == lit` keeps every member that is an object.

   `is` / `is not` stay identity comparisons (#8).
8. **Exports** use the binding's declared scheme, not a type narrowed
   by top-level control flow (#10).
9. **`new Array(n)`** has the declared type `Holes<a>`, with only
   `length` and `fill(v): a[]` (§6 of flow-narrowing.md). The
   syntax-matching rule goes, which fixes #3b. This is a declaration in
   core.d.js plus type-directed lowering in the Go backend.

## What it gives up, compared to flow-narrowing.md

- **Narrowing of reassigned variables.** For example:

      let cur = head;
      while (cur !== null) { total += cur.v; cur = cur.next; }

  `cur` is written, so it is not narrowed. A programmer can hoist the
  test's subject into a stable binding
  (`const node = cur; if (node !== null) …`), or use a recursive
  function. Linked-list code can't be typed today anyway: a `let` that
  starts as `null` is typed `Null` alone.
- **Order-independence** (#6) stays as on main: a narrowing takes effect
  only if the binding's type is already known at the test. The failure
  is always a rejection, never an acceptance, so it is sound. The
  deferred `Refine` constraint (§4 of flow-narrowing.md) can be added
  later without touching anything here.
- **A behaviour change from main.** Main also narrows *mutable* bindings
  with `typeof` and literal tests, which is unsound (a closure can write
  them). Under this rule, such a program is rejected unless the binding
  is stable. The test corpus shows how much code this affects. Each
  affected program either does reassign the variable or can use a
  `const`.

## Kept separate: field writes (#9)

A discriminant fact (`shape.kind === "c"`) stays true only if no write,
through any alias, can change `kind`. On main two writes are accepted
that break this:
- a write of `kind` through a union type;
- a write of `kind` through a wider field type.

Both are pre-existing, and the fix (writes at the meet of the members'
field types, and invariant mutable fields; §5 of flow-narrowing.md) can
reject existing code. So it lands as its own change, after this one,
with its own corpus check. Until then, discriminant narrowing has
exactly the soundness it has on main.

## Order of work

1. Resolution pass: a stable flag per binding, and occurrence → binding.
2. Replace the invalidation machinery with the stable-only rule. Keep
   the persistent environment, the predicates, early exit, loops, and the
   `try` and `switch` fixes.
3. Facts by the operand's type. Python `==` gets its own operator.
4. `Holes<a>`, in the checker and the Go backend.
5. Exports use the declared scheme.
6. Tests:
   - the review's repros, each rejected, or accepted when it is sound;
   - α-renaming invariance;
   - `for` ≡ `while`;
   - `?:` ≡ `if`;
   - `x === e` ≡ `e === x`;
   - De Morgan.

About half of the current PR's narrowing code is deleted, and the rest
is kept.
