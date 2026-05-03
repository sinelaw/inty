# Add discriminated-union support to minfern

minfern's type lattice is currently products-only: it has `Number`, `String`, `Row`, `Array`, `Func`, `Promise`, `Map`, `Named`, type variables — but no coproducts. That gap shows up in real JS the moment a function returns "either a string or undefined," or a parameter is "one of these literal strings," or a value is one variant of a tagged union. Right now minfern fakes the first case with `Type::Undefined` as a single scalar and gives up entirely on the rest.

Your job is to add **untagged unions**, **`T | undefined` as the canonical Option encoding**, **flow-sensitive narrowing** (on `typeof`, `=== / !==`, and `x.kind === literal`), **TypeScript-style discriminated unions**, and **switch-exhaustiveness** as a derived check. These features are deeply coupled — adding any one without the others produces a type system that is technically more expressive but practically worse, because users will form union types that the checker then refuses to use. Treat this as one project.

## What "good" looks like

```js
function f(x) {                          // x : string | undefined
  if (typeof x === "undefined") return 0;
  return x.length;                       // x narrowed to string here
}

function g(s) {                          // s : "a" | "b" | "c"
  switch (s) {
    case "a": return 1;
    case "b": return 2;
    case "c": return 3;
  }                                      // exhaustive, no fallthrough warning
}

// Discriminated union — the load-bearing pattern in real TS code:
function area(shape) {                   // shape : {kind:"circle", r:number}
                                         //       | {kind:"square", s:number}
                                         //       | {kind:"rect", w:number, h:number}
  switch (shape.kind) {
    case "circle": return Math.PI * shape.r * shape.r;       // shape narrowed
    case "square": return shape.s * shape.s;                 // shape narrowed
    case "rect":   return shape.w * shape.h;                 // shape narrowed
  }                                      // exhaustive
}
```

All three should typecheck. Today, the first fails to find `.length` on the union; the second can't even form the union; the third is unreachable from any angle.

## Design decisions you need to make up front

These are load-bearing — getting them wrong means rewriting everything later.

1. **Untagged vs tagged unions.** Pick untagged. JS doesn't have ADT constructors, and TypeScript-shaped untagged unions match how working code is already written. The "tagged" feel of discriminated unions comes from a *literal property* (`kind: "circle"`) inside otherwise-structural object types — not from a sum-type constructor. The narrowing layer makes them feel tagged.
2. **Normal form.** Unions auto-flatten and dedupe: `(A | B) | A` ≡ `A | B`. Sort members by a stable key for `PartialEq`/`Hash`. Single-element "unions" collapse to the element. The empty union is `never`.
3. **Subtyping or equality?** You're moving off pure HM equality. Decide whether unification becomes asymmetric (`unify_subsume(want, have)`) or whether unions get joined to a least upper bound at if/match join points only. Recommend the second: keep `unify` symmetric, introduce a separate `join(t1, t2)` used at branching constructs and array-literal element merging. This is the smaller blast radius.
4. **`Option<T>` is sugar, not a constructor.** Encode as `T | undefined`. Don't add `Type::Option`. The narrowing rule for `typeof === "undefined"` does the rest.
5. **Literal types are required.** You need string-literal types (`"a"`, `"b"`) for switch-exhaustiveness *and* for the discriminator field of a discriminated union. Add `Type::Literal(LitValue)` where `LitValue` is `String(String) | Number(f64) | Bool(bool)`. They subsume into their base type when joined with anything outside the union (`"a" | string` → `string`, but `"a" | "b"` stays as a closed literal union).
6. **Narrowing is per-occurrence, not global.** Refinement lives in the env passed down into branches, not in the substitution. The substitution is for unification facts that hold *everywhere*; narrowing is a fact that holds *here*.
7. **Narrowing paths must include property access from day one.** Model paths as a small enum: `Path::Ident(String)`, `Path::Member(Box<Path>, PropName)`. A string-keyed map will not extend cleanly to discriminated unions. Get this right in phase 4 or you'll rewrite phases 4–6.

## Sequencing

Each phase should ship green tests before the next starts.

1. **Lattice.** Add `Type::Union(Vec<Type>)` and `Type::Literal(LitValue)`. Update `Substitutable`, `free_vars`, `occurs_in`, pretty-printing. Keep `unify` rejecting unions for now — just get the data through the system.

2. **Join.** Implement `InferState::join(span, t1, t2) -> Type` that produces unions where types disagree. Wire into: ternary/if joining branches, array-literal element merging, switch-case result merging. Existing tests must still pass; if they form unions now, that's expected.

3. **Union elimination at use sites.** When you read a property off a union, the property type is the join of the per-member property types — only succeeds if every member has the field at compatible types. Same for indexing, calls, arithmetic. This is where users start *getting value* from unions.

4. **Narrowing infrastructure.** A `Narrowing` enum (`IsTypeof(String)`, `Equals(LitValue)`, `IsTruthy`, `NotEquals(LitValue)`, …) and a function `apply_narrowing(env, path: Path, narrowing) -> env'` that produces a refined environment. The `Path` enum must support both `Ident("x")` and `Member(Ident("x"), "kind")`. When narrowing a property path, the refinement walks into row types and filters union members accordingly — this is the single most important piece of the project; budget time for it.

5. **Narrowing predicates.** Recognise these patterns in `if`/`?:`/`switch` discriminators, build the `Narrowing`, pass refined env into the consequent, pass the negation into the alternate:
   - `typeof <path> === "string-literal"` → `IsTypeof("string-literal")` on `<path>`
   - `<path> === <literal>` and `<path> !== <literal>` → `Equals` / `NotEquals`
   - `<path>.<prop> === <literal>` (the discriminated-union case) — same `Equals` predicate, but on a `Path::Member`. The narrowing implementation in phase 4 should make this fall out naturally; if it doesn't, your `Path` modeling is wrong.

   For the discriminated-union case specifically, narrowing `Member(x, "kind")` to `Literal("circle")` means: walk `x`'s type, and if it's a union, retain only those members whose `kind` field unifies with `"circle"`. If `x` is a single row whose `kind` field doesn't unify, the branch is unreachable and `x` becomes `never` there.

6. **Switch-exhaustiveness.** A switch over a finite-literal-union discriminator (whether the discriminator is `s` or `s.kind`) with every member covered (and no `default`) is exhaustive — the post-switch type of the discriminator is `never` (the empty union). Emit a warning, not an error, when non-exhaustive: existing programs shouldn't suddenly fail to typecheck. The implementation should be uniform across both forms because phase 5's `Path` machinery already abstracts the difference.

7. **Builtins update.** `Array.prototype.find` / `Map.prototype.get` and friends should now return `T | undefined` instead of `T`. Update `stdlib/core.d.js` and `builtins/mod.rs`. This is the user-facing payoff that closes the loop on phase 1.

## Pitfalls

- **Type-class resolution against unions.** `Plus(string | number)` should not resolve — pick a representative or fail; don't silently accept. Document the decision.
- **Skolems inside unions.** HMF's subsumption check needs to handle `∀a. a → a | undefined`. Verify your existing skolem machinery still works after the lattice change before declaring victory.
- **`is_polymorphic_property` for assignment.** A field whose type is `T | undefined` for free `T` should still be rejected on mutation. The existing `free_vars` check should keep working, but verify with a fixture.
- **Pretty-printer.** Long unions need parenthesisation rules. `(A | B) → C` vs `A | (B → C)`. Get this right early; it's the most user-visible part. For discriminated unions specifically, consider a special-case printer that recognises `{kind:"a", …} | {kind:"b", …}` and renders the discriminator first per member.
- **Discriminator detection is heuristic.** A "discriminated union" isn't a separate type — it's any union whose members are all rows sharing a common literal-typed property. Don't add a `Type::Discriminated` constructor. The narrowing implementation just works on rows, period; discriminated unions are an emergent property.
- **Narrowing under aliasing.** `let s = shape; if (s.kind === "circle") shape.r` won't narrow `shape` because the narrowing is keyed on `s`. Document this as a known limitation; matching TypeScript here means tracking aliases, which is a much bigger project.
- **Backward compatibility.** Every test in `tests/` must still pass. Add new fixtures for the new features; don't modify old ones unless their expected output legitimately changes (e.g., a return type that was `T` is now correctly `T | undefined`).

## Out of scope

- `instanceof` narrowing (needs class types)
- Truthiness narrowing for `if (x)` (semantically thorny in JS — `0`, `""`, `null`, `undefined`, `NaN` all falsy; defer)
- Intersection types (separate project)
- User-defined type guard functions (`function isCircle(s): s is Circle` — needs annotation surface for predicate types)
- Tagged sums with explicit constructors (skipped permanently — discriminated unions cover the same ground for JS)

Report back when phase 2 lands with a summary of which existing tests changed expected output and why; that's the main signal for whether the join semantics are right before you commit to phases 3+. Report again when phase 5 lands, with a fixture demonstrating each of the three patterns from the "What good looks like" section typechecking end-to-end.
