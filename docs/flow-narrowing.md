# Flow-sensitive narrowing: a sound design

Status: design. Replaces the first narrowing implementation on PR #89,
which a review found unsound in four ways and incoherent in several
others (§0). The goal is a small set of judgment rules that read
declaratively, compose with HM inference and the deferred-constraint
solver, and need no ownership, linearity or alias tracking.

## 0. What has to be fixed

| # | problem | principle broken | origin |
| --- | --- | --- | --- |
| 1 | an assignment inside an expression doesn't end the narrowing for the rest of it (`c ? (q = p(0), q.x) : 0`, `if (f(q = p(0), q.x))`, switch/for headers) | soundness | PR |
| 2 | `var q = null` redeclaring a narrowed `var` is not a write | soundness | PR |
| 3a | `undefined` is recognised by name (`const undefined = 0`) | soundness, α-invariance | PR |
| 3b | `new Array(n).fill(v)` is typed even when `Array` is shadowed, and only in that exact syntax | soundness, coherence (let-expansion) | PR |
| 4 | "assigned" and "assigned from a closure" are sets of names over the whole program | α-invariance | PR |
| 5 | `for` and the equivalent `while` disagree (the update is checked before the body) | coherence | PR |
| 6 | narrowing reads the substitution at the moment it is applied, so statement order matters | principality, order-independence | main, extended by PR |
| 7 | `try` drops every narrowing, including those of `const`s | precision (coherence with `if`) | PR |
| 8 | Python `==` narrows although it dispatches to `__eq__` | soundness | main (the parser lowers `==` like `is`) |
| 9 | writing a field of a union-typed object is checked against the *union* of the members' field types, and a `{kind: "c"}` object passes where `{kind: String}` is written | soundness of discriminant narrowing under aliasing | main |
| 10 | an exported binding's type depends on top-level control flow | coherence | PR |

The first implementation handled narrowing with a set of statement-level
patches: a special case for a lone `x = e;`, a bypass for `if`, a
`guarded` operand, name sets, and a syntactic `always_exits` check. Each
patch closed one case of a general problem. The design below replaces all
of them with one mechanism.

## 1. Model

**Bindings, not names.** A resolution pass (§2) gives every declaration a
`BindingId` and resolves every identifier to one. Everything below is
keyed by binding.

**Versions.** Every binding has a current *version*. A write gives it a
fresh version. A version is never reused: that is what makes stale facts
impossible to observe.

**Facts.** Γ maps a binding `b` to `(σ_b, v, Φ)`:
- `σ_b` is its declared scheme, the only type a store is checked against;
- `v` is its current version;
- `Φ` is a set of facts about the value `b` held *at version `v`*.

A fact is a predicate on a path rooted at `b` (`b`, `b.kind`, …):

```
P ::= Is(τ) | IsNot(τ)          -- τ a singleton type: Null, Undefined, a literal
    | EqTo(τ)                    -- equal to some value of type τ (positive only)
    | Nullish | NotNullish
    | Truthy | Falsy
    | Typeof(s) | NotTypeof(s)
    | Instance(C) | NotInstance(C)
```

Every type inside a fact is ground: a singleton type, a string or a brand.
So fact equality is syntactic, and set operations on facts are
independent of the substitution.

**Reads.**
- If `Φ` is empty, a read of `b` instantiates `σ_b` exactly as today.
- Otherwise the read has a fresh type `β` and emits the deferred
  constraint `Refine(τ_b, Φ, β)`, where `τ_b` is `σ_b` instantiated (§4).
  The environment never stores a narrowed type. So generalisation,
  `free_vars`, substitution and the skolem escape check see only `σ_b`,
  and nothing changes for them.

## 2. Binding resolution (fixes 2, 4)

This is one pass before inference, parameterised by `SourceLanguage`. It
reuses the scope model of `ast/free_idents.rs`:
- **JS:** `var` hoists to the function. A second `var x` is the *same*
  binding, and its initialiser is a write. `let`, `const` and `class` are
  block scoped. Parameters, `catch` parameters and function declarations
  are covered too.
- **Python:** function-level locals, plus `global` / `nonlocal`.
- **Lua:** `local` versus global.

It produces:

- `occurrence: Span → BindingId` for every identifier, and for every
  assignment target;
- per binding:
  - `mutable`;
  - `writes`: the number of writes, not counting the declaration's own
    initialiser;
  - `written_from_nested_fn`: some write sits in a function nested inside
    the function that declares `b`;
- `W(s)`: the bindings written anywhere inside a loop or `try`
  statement `s`, nested functions excluded.

Derived predicates:

```
Stable(b)     ⇔ ¬mutable(b) ∨ writes(b) = 0
Refinable(b)  ⇔ ¬written_from_nested_fn(b)
```

These rules are the ones Kotlin uses for smart casts ("a local `var`
captured in a lambda that modifies it is never smart-cast"). They are
exact per binding, so renaming a variable cannot change a result.
- A name that resolves to no binding (a global) is refinable only when its
  declaration is immutable.
- `assignments_in_program`, `closure_assigned`, `assigned_anywhere`,
  `assigned_names_in_*` and the per-statement subtree walks all go away.
  The walks were quadratic in nesting depth.

## 3. Judgments

Three forms:

```
Γ ⊢ e ⇒ τ ⊣ Γ'              expression: Γ' is Γ after e's writes, in evaluation order
Γ ⊢ e ⇒ τ ⊣ Γ⁺ ; Γ⁻         condition: the environment when e was truthy / falsy
Γ ⊢ s ⊣ Γ' | ⊥   ; J        statement: completes with Γ', or never completes (⊥);
                             J collects the environments at each break/continue target
```

**Merge.** `Γ₁ ⊔ Γ₂` is defined per binding:
- equal versions: keep `(v, Φ₁ ∩ Φ₂)`;
- different versions: `(fresh v, ∅)`.

`⊥` is the identity of `⊔`. Merge is commutative, associative and
idempotent, and depends on no substitution.

In practice versions live in `InferState` as a map `BindingId → version`.
Branches snapshot and restore the map, and a merge assigns fresh versions
where the branches disagree. Facts live in the persistent `Γ`, as they do
today.

### Expressions

```
(Read)    b = occ(x)   Γ(b) = (σ, v, Φ)   Φ = ∅ ⇒ τ = inst(σ)   Φ ≠ ∅ ⇒ τ = β, Refine(inst(σ), Φ, β)
          ────────────────────────────────────────────────────────────
          Γ ⊢ x ⇒ τ ⊣ Γ

(Store)   Γ ⊢ e ⇒ τ ⊣ Γ₁     τ ≤ inst(σ_b)
          ────────────────────────────────────────────────────────────
          Γ ⊢ x = e ⇒ τ ⊣ Γ₁[b ↦ (σ_b, fresh, ∅)]

(Update)  x op= e, x++: read x as in (Read), check the result ≤ σ_b, then as (Store)

(Seq)     sub-expressions are threaded left to right in JS evaluation order:
          callee, then arguments; object, then key, then value; and so on
```

(Store) is what fixes #1. The read in `q.x` after `q = p(0)` sees a
version with no facts, however deeply the assignment is nested and
whatever statement contains it. The patches for a lone `x = e;`, for
`if`, and the `guarded` operand are consequences of this rule and are
deleted.

### Conditions (occurrence typing with versions)

Two sources inform these rules: Tobin-Hochstadt & Felleisen, *Logical
Types for Untyped Languages* (2010), and TypeScript's control-flow
analysis. Versions make them sound under mutation.

```
(Atom)    e is a comparison or path yielding fact P about b
          Γ ⊢ e ⇒ Boolean ⊣ Γ₁
          ────────────────────────────────────────────────────────────
          Γ ⊢ e ⊣ Γ₁ + P(b@v) ; Γ₁ + ¬P(b@v)        (only if Refinable(b))

(Not)     Γ ⊢ e ⊣ Γ⁺ ; Γ⁻   ⟹   Γ ⊢ !e ⊣ Γ⁻ ; Γ⁺

(And)     Γ ⊢ a ⊣ A⁺ ; A⁻     A⁺ ⊢ b ⊣ B⁺ ; B⁻
          ⟹ Γ ⊢ a && b ⊣ B⁺ ; A⁻ ⊔ B⁻

(Or)      Γ ⊢ a ⊣ A⁺ ; A⁻     A⁻ ⊢ b ⊣ B⁺ ; B⁻
          ⟹ Γ ⊢ a || b ⊣ A⁺ ⊔ B⁺ ; B⁻

(Other)   Γ ⊢ e ⇒ τ ⊣ Γ₁   ⟹   Γ ⊢ e ⊣ Γ₁ ; Γ₁
```

As an expression, `a && b` has out-environment `A⁻ ⊔ B_out`. Likewise
`c ? a : b` has `A_out ⊔ B_out`, with `a` checked in `C⁺` and `b` in
`C⁻`.

Symmetry: `x === e` and `e === x` produce the same fact, and De Morgan
holds by construction (`!(a && b)` and `!a || !b` give identical pairs).

**Which comparisons yield facts.** A comparison yields a fact according
to the *type* of the other operand, never its name (this fixes 3a). Let
`τ_e` be that type:
- `x === e` gives `Is(τ_e)` when `τ_e` is a singleton type, and `EqTo(τ_e)`
  otherwise. `!==` gives the negation, and only for a singleton (a
  non-singleton inequality says nothing). Because `τ_e` may still be a
  variable, the fact itself is resolved inside `Refine` (§4), not here.
- `x == e` / `x != e` (JS) gives `Nullish` / `NotNullish` when `τ_e` is
  `Null` or `Undefined`, and nothing otherwise, because of coercion.
- `typeof x === "s"` and `isinstance` stay as they are.
- A bare path gives `Truthy` / `Falsy`, with the language's truthiness
  table (already per language).
- Python: `is` / `is not` are identity. `==` / `!=` call `__eq__`, so they
  must be lowered to a distinct operator that yields no facts (this fixes
  #8; today the parser lowers `==` to `===`).
- Lua: `==` against `nil` is raw equality, so it yields `Is(Null)`.

### Statements

```
(If)      Γ ⊢ c ⊣ C⁺ ; C⁻    C⁺ ⊢ s₁ ⊣ R₁    C⁻ ⊢ s₂ ⊣ R₂    ⟹   Γ ⊢ if … ⊣ R₁ ⊔ R₂

(Exit)    return / throw ⊣ ⊥          break ℓ / continue ℓ ⊣ ⊥, depositing Γ at J(ℓ)

(While)   H = Γ with b ↦ (σ_b, fresh, ∅) for b ∈ W(loop)          -- loop head
          H ⊢ c ⊣ C⁺ ; C⁻      C⁺ ⊢ body ⊣ R ; J
          ⟹ Γ ⊢ while … ⊣ C⁻ ⊔ J(break)

(For)     typed as its desugaring  { init; while (test) { body; update } },
          with continue targeting the update:  update is checked in  R ⊔ J(continue)

(Try)     E = Γ with b ↦ fresh for b ∈ W(try block)    -- any point of the block
          catch/finally checked from E (plus the catch binding);
          after: R_try ⊔ R_catch (then through finally)

(Switch)  case k is entered from  (Γ_d + fact(d = case_k)) ⊔ R_{k-1}   -- R_{k-1} is the fallthrough
          the "no case matched" edge is  Γ_d + {¬fact(d = case_k) | all k}
          after: all breaks ⊔ last case ⊔ the no-match edge (when there is no default)

(Fun)     the body starts from Γ with Φ_b := ∅ for every captured b with ¬Stable(b)
```

Notes:
- **Early exit** falls out of (If) and (Exit) with `⊥` as the identity:
  `if (q === null) return 0;` completes with `C⁻` alone. The syntactic
  `always_exits` goes away, and every exit shape works, including
  `if … else throw` and `while (true)` without a break.
- **The loop head** is the least fixpoint of merging the pre-loop
  environment with every back edge. A binding not in `W(loop)` has the
  same version on every edge, so it keeps its facts. A binding in
  `W(loop)` gets a fresh version. That is conservative when a write in
  the loop can't actually be reached, and it is exact otherwise.
  Computing the head from `W` means the body is inferred once, not
  iterated, so no constraint is generated twice.
- **For ≡ while** holds by definition (this fixes #5).
- **Try** keeps the pre-`try` facts of everything the block doesn't write,
  which includes every `const` (this fixes #7).
- **Switch** exhaustiveness falls out: the no-match edge refines the
  discriminant to `never`.
- **Calls** don't touch facts. Only a closure can write a local. A binding
  some closure writes is not `Refinable`, so it never has facts. The same
  holds for getters, setters, `await` and generators.
- **Closures that read.** A closure that reads a captured binding keeps
  the facts only if the binding is `Stable`: it can run after any later
  write, and `Stable` rules out that there is one.

## 4. Refinement as a deferred constraint (fixes 6, and the timing half of 3a)

`Refine(τ, Φ, β)` joins the pending-constraint solver that already
defers `HasProp`. It is solved once the head of `τ`, and of any `EqTo`
operand, is known:

| head of τ | β := |
| --- | --- |
| union `τ₁ \| … \| τₙ` | the union of the members compatible with every fact in Φ, each member refined recursively |
| named (non-nominal) type | refine its one-step unrolling |
| any other concrete type | `τ` if compatible with Φ, else `never` |
| still a variable at generalisation | `τ` (the facts are not used) |

The member-compatibility tables (`could_be`, truthiness per language,
`typeof`, brands) carry over unchanged.

Order-independence is the point. The result no longer depends on when
the checker reaches the `if` relative to the statement that fixes `q`'s
type. The rule for an unresolved variable applies only at generalisation,
after every constraint of the binding group has been collected, so it is
deterministic. It is also sound: the unrefined type is always a valid
type for the read.

On principality, stated honestly:
- Under this rule, the inferred type is the most general one.
- A narrowing on a still-quantified variable doesn't produce a
  constrained type such as `α ≤ {x} | Null`. That would need constrained
  union types and is out of scope. So `function h(q) { if (q !== null)
  return q.x; return 0 }` gets the type `α has {x: b} ⇒ α → b` unless `q`
  is annotated.
- This is the same limit that `typeof` narrowing has today
  (docs/type-system.md, "Narrowing requires an explicit union type").

A dead-branch warning is issued when a `Refine` whose fact kind warns
resolves to `never`, and it is reported at the test's span.

## 5. Discriminants and aliasing (fixes 9)

A fact on `b.kind` narrows `b`'s *union*: it picks members, and never
changes a field's type. That is sound under aliasing, with no alias
analysis, provided one invariant holds: no write through any alias can
move an object from one union member to another. Two ordinary typing
rules give that invariant:

1. **Writing a field of a union-typed object.** The value written must
   fit the field in every member, which is the *meet* of the members'
   field types. A read still gets their join. In `{kind: "c"} | {kind:
   "q"}` the write type of `kind` is `never`. Today it is `"c" | "q"`, and
   `shape.kind = "q"` is accepted.
2. **Mutable fields are invariant** under subsumption. `{kind: "c"} ≤
   {kind: String}` would let a function that writes `x.kind = "q"`
   receive a circle. Width subtyping (extra fields) stays; depth
   subtyping of a field does not.

Both rules are standard for mutable records, and neither needs
linearity. Rule 2 can reject code that works today, so it lands behind
the corpus check in §8. Object literals already widen their literal
fields unless an annotation asks otherwise, so the expected fallout is
small.

## 6. `new Array(n)` (fixes 3b)

Special-casing the syntax in `infer_call` is replaced by a type, declared
in `core.d.js`:

```
Array:        new (n: Int) => Holes<a>,  (n: Int) => Holes<a>
Holes<a>:     { length: Int, fill: (v: a) => a[] }
```

`Holes<a>` has no index, iteration or read method, because a hole reads
as `undefined`, which no element type admits. So:
- a shadowed `Array` is just the user's binding;
- `const t = new Array(3); t.fill(0)` types exactly like the one-liner;
- aliasing a `Holes` value is harmless, because nothing can be read
  through it;
- `fill(v, start)` leaves holes and stays untyped.

The Go backend lowers by type: a `Holes` value is its length, and `fill`
on it is `intyFilled`. There is no syntactic pattern to match.

## 7. Exports (fixes 10)

A module exports each binding's declared scheme `σ_b`, never a
top-level-narrowed type.

## 8. How the properties are tested

Every reviewer repro becomes a test, and each one that Node shows
throwing is paired with its Node behaviour. On top of that, metamorphic
tests check that each transformation leaves the verdict and the inferred
types unchanged:

| transformation | property |
| --- | --- |
| rename any binding (α-conversion) | α-invariance |
| swap two independent statements | order-independence |
| `for (i; t; u) s` ↔ `{ i; while (t) { s; u } }` (no `continue`) | coherence |
| `c ? a : b` ↔ `if (c) r = a; else r = b` | coherence |
| `a === b` ↔ `b === a`, `a == null` ↔ `null == a` | symmetry |
| `!(a && b)` ↔ `!a \|\| !b` | De Morgan |
| `const x = e` ↔ a `let x = e` that is never written | `Stable` |
| `new Array(n).fill(v)` ↔ `const t = new Array(n); t.fill(v)` | let-expansion |

`meta/soundness.rs` can grow a narrowing generator. It builds programs
from the fact, assignment and closure shapes above, and checks that every
program the checker accepts runs under Node without a `TypeError`.

## 9. Order of work

1. **Binding resolution** (§2). It is used only to compute
   `Refinable`/`Stable`/`W`, which fixes 2 and 4. Behaviour otherwise
   stays as today.
2. **Versions, merge and the judgments** (§3). They replace the
   statement wrapper, `always_exits`, `loop_entry_env`, `test_facts_in`
   and the `simple_store` / `If` / `guarded` special cases, which fixes
   1, 5 and 7. `infer_stmt` returns `Option<TypeEnv>` plus jump
   deposits. `infer_expr`'s signature stays: versions live in
   `InferState` and are threaded implicitly in evaluation order, so the
   hundreds of call sites don't change. What needs checking is that
   inference already visits sub-expressions in JS evaluation order.
3. **Facts by type and `Refine` deferred** (§4, §3 comparisons), which
   fixes 3a, 6 and 8. This includes Python `==` lowered to its own
   operator.
4. **`Holes<a>`** (§6), in both the checker and the Go backend (3b).
5. **Field write types and invariance** (§5), fixing 9, gated on the
   whole test corpus and the example programs.
6. **Exports use `σ_b`** (§7), fixing 10.

Steps 1–3 keep every test that passes today and add the reviewer's
repros. Step 5 is the only one expected to reject code that is currently
accepted, and each case it rejects is one where a write could break a
union's discriminant.
