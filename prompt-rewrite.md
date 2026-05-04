# inty architectural rewrite — make the type system data-driven and testable

inty works. It typechecks real JS, produces good error messages, and ships a sensible HMF-with-classes type system. But the implementation has structural weaknesses that will get worse as features land:

- **`src/infer/infer.rs` is 2,814 lines** doing inference for every AST variant in one file. Adding a feature touches a giant match; reviewing a change requires reading the whole file.
- **No operational semantics.** Soundness is asserted, not demonstrated. There's no mechanism that catches the day a typing rule promises something the runtime won't deliver.
- **No structured exploration of design alternatives.** Every type-system choice (binop strictness, record openness, exhaustiveness, value restriction style) is hardcoded. Users with different needs have no way to opt in.
- **Tests are `.js` fixtures only.** No property-test layer, no soundness meta-check, no way to generate well-typed programs and reduce them.
- **Operator typing logic and operator runtime semantics are nowhere expressed together.** The two could disagree silently and no test would catch it.

This rewrite addresses all of these. It is strictly an internal-architecture project — **the user-visible CLI behavior should not change** except where a config knob is explicitly flipped. Existing tests must continue to pass at every phase boundary.

This plan does **not** add new typing features. The discriminated-unions / narrowing / exhaustiveness work lives in `prompt-inty.md` and is a parallel track. Phase 1 of this plan should land before that work begins, to avoid merge conflicts on the file moves. Phases 2–7 of this plan and `prompt-inty.md` can be interleaved.

## Sequencing

Each phase ships green tests before the next starts. Phases are deliberately ordered so that earlier infrastructure makes later phases easier — don't reorder without a reason.

1. Modularize `src/infer/infer.rs` along feature lines.
2. Extract the operator catalog as data.
3. Add a small-step operational semantics for the supported subset.
4. Add a Cimini-Blame meta-test cross-checking typing arms vs operational arms.
5. Add property-tested soundness — generate well-typed programs, reduce, assert never-stuck.
6. Surface type-system policy choices as runtime configuration.
7. Polish: test taxonomy, instance tables as data, mutability/origin extensions.

## Phase 1 — Modularize `infer.rs` along feature lines

**Why.** A 2,814-line match statement is hostile to review and makes per-feature reasoning impossible. The split should be by *feature* (functions, rows, arrays, classes, …), not by *AST node*, because a feature's typing logic, env extension, and helpers all want to live together.

**Deliverables.**

```
src/infer/
├── mod.rs              # InferState, public API, dispatcher
├── state.rs            # (existing — keep)
├── env.rs              # (existing — keep)
├── unify.rs            # (existing — keep)
├── decorate.rs         # (existing — keep)
├── type_parser.rs      # (existing — keep)
└── features/
    ├── mod.rs          # FeatureModule trait + registration
    ├── scalars.rs      # Number, String, Boolean, Null, Undefined, Regex, typeof
    ├── functions.rs    # Function exprs, calls, this, arity, β
    ├── rows.rs         # Object literals, member access, row poly
    ├── arrays.rs       # Array literals, indexing, length
    ├── operators.rs    # Binops, unops, type-class dispatch
    ├── control.rs      # if/?:/switch/while/for joins
    ├── bindings.rs     # let/const/var, value restriction, generalization
    ├── classes.rs      # Plus, Indexable, constraint solving
    ├── recursive.rs    # Type::Named, TypeDef, cycle detection
    └── promise.rs      # Promise<T>, async, await
```

**Decisions.**

- Keep `InferState`, `TypeEnv`, `unify_impl`, and `Subst` in their current locations. They're shared infrastructure, not features.
- `infer_expr(env, expr)` in `mod.rs` becomes a thin dispatcher: match the AST top-level shape, delegate to the relevant feature module's `infer_*` function. Each feature module gets `&mut InferState` and `&TypeEnv`.
- Helpers used by exactly one feature move into that feature's module. Helpers used by two move to `mod.rs`. Helpers used by three move to `state.rs` as methods on `InferState`.
- **No behavior changes.** Every line that moves keeps its current semantics. Renames are fine; rewrites are not.

**Pitfalls.**

- Visibility: features need `pub(super)` or `pub(crate)` access to a few `InferState` internals. Don't make everything `pub` — use the move as an opportunity to tighten the API surface.
- Cyclic deps: `functions.rs` calls `bindings.rs` (for parameter binding), which may need `unify`, which may need to know about `Type::Func`. The cycle is fine; just put types in `core/` and let features import from there.
- Tests: any test reaching into `infer::infer::private_helper` must be either re-exported through the feature module or rewritten to test through public API.

**Success criteria.** `cargo test` passes. `infer.rs` no longer exists (or is < 200 lines as a dispatcher). Each `features/*.rs` is < 600 lines. Per-feature changes only touch one or two files. Reviewer can read a single feature without paging through the rest.

**Report on completion.** A table of which old line ranges in `infer.rs` moved to which new file, and any helpers that ended up in unexpected places.

---

## Phase 2 — Extract the operator catalog as data

**Why.** Right now, every operator's typing rule lives in a match arm somewhere in the new feature modules, and its runtime behavior (when it exists, in phase 3) lives in a separate match arm somewhere else. There's no single place to ask "what does `+` do?" — and consequently no place to verify that the answers from the typing side and the runtime side agree (phase 4).

The catalog is a static table that records, per operator: arity shape, primary dispatch axis, and the canonical typing-arm shapes. The actual typing logic stays in code (it's too irregular to encode), but the *metadata describing what the typing logic accepts* lives in the table.

**Deliverables.**

A new `src/operators/mod.rs`:

```rust
pub struct OpInfo {
    pub name: &'static str,
    pub kind: OpKind,                 // BinOp / UnOp / MemberAccess / Index / ...
    pub dispatch: Dispatch,           // ArgType | OpSymbol | Static
    pub arms: &'static [TypingArm],   // declarative arms — see below
}

pub struct TypingArm {
    pub inputs: &'static [TypeShape],     // e.g. [Number, Number]
    pub output: TypeShape,                // e.g. Number
    pub class: Option<ClassName>,         // None for direct, Some for class-mediated
}

pub enum TypeShape {
    Concrete(BaseType),       // Number, String, Boolean, ...
    SameAsArg(usize),         // for equality: "same type as arg N"
    AnyOfClass(ClassName),    // for Plus / Indexable
    Wildcard,
}
```

Populate it for every operator inty currently knows about: `+`, `-`, `*`, `/`, `%`, `<`, `<=`, `>`, `>=`, `==`, `===`, `!=`, `!==`, `&&`, `||`, unary `-`, `!`, `typeof`, `void`, member access, indexing, function call, `new`, `await`.

**Decisions.**

- The catalog is read by phase 4's blame meta-test and (eventually) phase 5's well-typed-term generator. It is not the primary input to typing — the actual `infer_binop` etc. functions still do the real work. The catalog is a *parallel description* that must agree with the code.
- Where the catalog disagrees with the code, the catalog is wrong (the code is the source of behavior). Phase 4 surfaces these disagreements as test failures.
- Don't try to encode every subtlety. If a typing rule has a side-condition the catalog can't express (e.g., "field type must be monomorphic"), record it in a `Notes` field as free text and have phase 4 skip blame-checking for those arms.

**Pitfalls.**

- **Don't drive typing from the catalog.** That's what rosa does and it leads to a 22-judgment-form explosion. The catalog is documentation that we test against, not the implementation.
- Equality operators (`==`, `===`, etc.) take any two types provided they unify. Use `SameAsArg(0)` for the second slot.
- `+` is the hard case: `(Number, Number) → Number`, `(String, String) → String`, and `(Plus a, Plus a) → a` if you keep the type-class encoding. List both literal arms *and* the class-mediated arm; phase 4 should handle both.

**Success criteria.** `cargo test catalog::comprehensive` passes (every operator in the AST has a catalog entry). Catalog is loaded once, lives in static memory, no allocations.

**Report on completion.** Total operator count, which operators required `Notes` exemptions and why.

---

## Phase 3 — Small-step operational semantics

**Why.** inty has no mechanism for testing its typing rules against actual JS behavior. Without operational rules, there's no definition of "stuck" — and therefore no falsifiable soundness claim. We're not building a JS engine; we're building enough mechanics to define what the typed subset *means*, so that phases 4 and 5 can use it.

**Deliverables.**

A new `src/dynamics/` directory:

```
src/dynamics/
├── mod.rs              # public API: step, run_to_end, is_stuck
├── value.rs            # syntactic values: Number, String, Boolean, Null, Undefined,
│                       #   Closure { params, body, env }, Array<Value>, Object<...>
├── env.rs              # runtime env (different from type env)
├── heap.rs             # Loc + Cell, for mutable refs
└── step.rs             # one-step reduction relation
```

Cover the typed subset: literals, lambdas, application, let/const/var, if/?:, binops, unops, object literals, member access, array literals, indexing, assignment to known-non-polymorphic targets, sequence. **Skip**: async/await (define `await` on a Promise as identity for now and document the limitation), regex evaluation, arithmetic on bigints, prototypes beyond what current type rules already model.

For each operator listed in the phase-2 catalog, write at least one operational arm — the operator catalog and the dynamics should agree on what the operator's job is.

**Decisions.**

- **Reduction is for testing, not execution.** It does not need to be performant. It does not need to handle arbitrary JS programs. It needs to handle the programs inty types as well-formed.
- "Stuck" = "not a value AND no rule applies." A stuck typed term is a soundness violation. Build `is_stuck(state) -> Option<StuckReason>` so phase 5 can produce useful failure reports.
- Pick a small heap model. The simplest correct one: `Heap = HashMap<Loc, Cell>`, with `Cell = Object(BTreeMap<PropName, Value>) | Array(Vec<Value>) | Var(Value)`. Don't model prototypes initially; flatten the prototype field at object construction if you need it.
- If you need a fuel parameter to bound non-termination, set the default to 10,000 steps. Tests fail with a clear "fuel exhausted" message rather than hanging.

**Pitfalls.**

- The operational semantics will reveal weird corners of the type system. Resist the temptation to "fix" them mid-phase. Document, move on, return in phase 4 or 5.
- Object property assignment is the trickiest case: needs to interact with the polymorphic-property check at the type level. If a typing rule rejects the assignment, the operational rule should never fire on a typed-and-typed-good term — but you need to verify this in phase 5, not assume it.
- `==` vs `===` semantics: be explicit. `===` is structural for primitives, reference for objects. `==` does coercion that inty's typing rules currently don't permit, so the operational arm should still implement standard `==` and you'll find out in phase 5 whether the typing rules let you reach it.

**Success criteria.** `cargo test dynamics::operators` passes for every operator in the catalog. `dynamics::run_to_end` on the typed examples in `tests/*.js` produces a value (or, for non-terminating ones, fuel-exhausts cleanly).

**Report on completion.** Which AST forms are reducible vs deliberately-unmodeled, and a brief explanation per unmodeled form.

---

## Phase 4 — Cimini-Blame meta-test

**Why.** Now that you have a typing-side catalog (phase 2) and an operational side (phase 3), you can cross-check them automatically. For every operator and every input shape the typing arm accepts, there must be a matching operational arm. A missing match is a *blame triple*: `(operator, configuration, input-shape)`. The triples are the constructive content of "this typing rule is unsound."

**Deliverables.**

`src/meta/blame.rs`:

```rust
pub struct BlameTriple {
    pub operator: &'static str,
    pub config: ConfigSnapshot,    // empty for now; populated in phase 6
    pub shape: Vec<TypeShape>,
}

pub fn blame_triples_for_op(op: &OpInfo, dynamics: &Dynamics) -> Vec<BlameTriple>;

pub fn all_blame_triples(catalog: &[OpInfo], dynamics: &Dynamics) -> Vec<BlameTriple>;
```

A test `tests/meta/blame.rs` that asserts `all_blame_triples(...).is_empty()`. If this test fails, it prints every blame triple with a clear "operator X promises Y but operational rules don't deliver" message.

**Decisions.**

- Enumerate over a small, fixed alphabet of input shapes: `Number`, `String`, `Boolean`, `Null`, `Undefined`, plus a handful of compound probes (`Array<Number>`, `Map<String>`, `{a: Number}`). Don't try to enumerate exhaustively; the alphabet is for catching obvious gaps, not full coverage.
- Class-mediated arms (`Plus a => (a, a) → a`) need to be expanded against each instance of the class. The catalog from phase 2 should let you do this without per-class special cases.
- A typing arm with a `Notes` exemption from phase 2 is skipped in blame-checking — you noted it can't be fully modeled, that's fine.

**Pitfalls.**

- **False positives are worse than false negatives.** A blame triple that turns out to be sound (because of a side-condition the catalog couldn't express) erodes trust in the meta-test. Be conservative: when uncertain, mark it `Notes` in phase 2 and skip.
- The triples that *do* fire are interesting. Don't suppress them; document each one. If inty has soundness gaps today, we want to find out now.

**Success criteria.** `cargo test meta::blame` passes (i.e., zero blame triples) OR a documented short list of known-acceptable triples is checked in alongside the test, with each entry citing the side-condition that makes it actually sound. The list is a maintenance hazard; aim to keep it empty.

**Report on completion.** Number of triples found, dispositions (fixed / `Notes`-exempted / accepted with citation).

---

## Phase 5 — Property-tested soundness

**Why.** The blame meta-test catches static gaps between typing and operational rules. Property testing catches *combinational* bugs — interactions between features that no individual rule got wrong but that compose into a stuck term. This is what proves (statistically) that the type system is sound, not just that each rule is locally consistent.

**Deliverables.**

`tests/proptest_soundness.rs`:

```rust
proptest! {
    #[test]
    fn well_typed_terms_dont_get_stuck(seed in any::<u64>()) {
        let mut state = InferState::new();
        let env = builtins::initial_env();
        let term = generate_well_typed_term(seed, &env);
        let _ty = state.infer_expr(&env, &term).unwrap();
        let value_or_stuck = dynamics::run_to_end(&term, dynamics::Env::empty(), 10_000);
        prop_assert!(!value_or_stuck.is_stuck(),
                     "stuck on typed term: {:?}", term);
    }
}
```

The hard part is `generate_well_typed_term`. Strategy: a small, top-down generator over a `WellTypedExprStrategy` that maintains a typing context and only emits expressions whose type can be inferred.

**Decisions.**

- Start narrow. Cover scalars, lambdas, applications, let, if, binops on Numbers/Strings, objects, member access. Add features generator-side as you trust them. **Don't** try to generate every AST shape on day one.
- Use proptest's `Strategy::prop_recursive` to bound depth. Default depth 5; size 30. Most terms reduce in a handful of steps; soundness violations don't need huge terms.
- When the generator can't produce a well-typed term at the desired position (because no in-scope variable has the required type), fall back to a literal of that type. Don't ever `panic!` from the generator.

**Pitfalls.**

- **Shrinking matters.** When a property fails on a 50-line term, proptest will shrink it. Make sure your AST type implements `Arbitrary` such that shrinking moves toward simpler terms (drop branches, shorten arrays, replace expressions with literals). Bad shrinking turns this test into "1000-line counterexample on every failure."
- The generator will find *something* on day one. It may not be a soundness bug — it may be a generator bug. Triage carefully before declaring the type system unsound.
- Keep generation fast. If a single `proptest` iteration takes > 100ms, you can't run enough cases. If your inference path is slow, that's a separate problem worth fixing.

**Success criteria.** `cargo test proptest_soundness` runs 1000 cases in under 30 seconds and passes. CI runs it on every PR.

**Report on completion.** Number of cases that found bugs during development, what each bug was, whether it was a generator/type-system/operational issue.

---

## Phase 6 — Surface policy choices as runtime configuration

**Why.** Today, every type-system policy decision is hardcoded: strict binops, row-poly records, unify-take-then ternaries, value-restricted let. These are *choices*, not facts. Different teams want different defaults. The infrastructure from phases 2–5 lets us expose these choices safely: every config combination has a defined soundness story, surfaced by the blame meta-test.

**Deliverables.**

A new `src/config/mod.rs`:

```rust
pub struct intyConfig {
    pub binop_policy: BinopPolicy,             // Strict | Permissive | TypeClass | JsCoerce
    pub record_policy: RecordPolicy,           // Closed | WidthSubtype | RowPoly
    pub case_exhaustiveness: Exhaustiveness,   // Required | Warn | Off
    pub value_restriction: ValueRestriction,   // Syntactic | MutationAware | None
    pub if_branch_unification: IfPolicy,       // UnifyTakeThen | UnifyTakeElse | NoUnify
    pub arity_policy: ArityPolicy,             // Strict | Lax
    pub mcall_policy: McallPolicy,             // ExplicitThis | ImplicitThis | EnforcedThis
}

impl intyConfig {
    pub const DEFAULT: Self = Self { /* matches current behavior */ };
    pub fn soundness_summary(&self) -> SoundnessSummary;  // calls blame analysis
}
```

CLI flag: `inty --config strict` / `--config permissive` / `--config-file foo.toml`. Per-policy CLI flags for individual overrides.

The blame meta-test from phase 4 grows a parameter: it now runs against every (operator × policy combination) and reports which combinations are sound.

**Decisions.**

- **Default config preserves today's behavior.** Existing users see no change. Anyone who flips a knob gets a clearly-labeled non-default and the blame report tells them what they've signed up for.
- Every operator that consults config does so by reading from a `&intyConfig` passed through `InferState` (or stored on it once at startup). No `lazy_static` config; configurability means parameterizable.
- The number of policies is fixed; users can't add their own. Extension is a new variant on the policy enum + a code path in the corresponding feature module + a phase-4 entry. Keep the surface closed.

**Pitfalls.**

- **Combinational explosion.** With 7 axes and ~3 values each, that's 2,000+ configurations. The blame test enumerates the subset that could plausibly differ — read the catalog and only enumerate axis values that affect the rule arm under test. A naive nested loop times out.
- **Users will pick incoherent combinations.** `record_policy = Closed` + `width_subtype` extras in code = surprise rejections. Document each policy's interactions; consider a `intyConfig::validate()` that warns on known-bad combinations.
- **Don't expose policies that don't change behavior yet.** If `if_branch_unification` doesn't actually have alternative implementations because the relevant rule is hardcoded, removing it from config is better than shipping a knob that does nothing.

**Success criteria.** Default config preserves 100% of existing test outcomes. At least 3 non-default policy combinations have working implementations and explicit test coverage. Blame meta-test runs across all configurations in CI; sound configurations test green, unsound ones produce documented blame triples that match a checked-in expected-output file.

**Report on completion.** Which policies are exposed, which combinations are sound, which are documented-unsound, which are infeasible (e.g., haven't built the alternative implementation yet).

---

## Phase 7 — Polish

These are smaller wins that don't deserve dedicated phases but are worth doing once the infrastructure is in place.

**7a. Test taxonomy.**

Each `tests/*.js` gets a frontmatter comment:

```js
// @kind: typecheck-eq | typecheck-rejects | reduce-eq | runtime-error | proptest-seed
// @expect: <type or value or error class>
// @notes: <free text>
```

Rewrite the test runner to read the frontmatter and assert against `@expect` for each `@kind`. A test whose `@kind` and behavior disagree fails loudly with a clear message, not a generic assertion.

**7b. Type-class instances as data.**

Move `Plus` and `Indexable` instance lists out of `src/builtins/mod.rs` into `src/classes/instances.rs` as a static table:

```rust
pub static PLUS_INSTANCES: &[InstanceDecl] = &[
    InstanceDecl { class: "Plus",      types: &[TypeShape::Number] },
    InstanceDecl { class: "Plus",      types: &[TypeShape::String] },
];
pub static INDEXABLE_INSTANCES: &[InstanceDecl] = &[
    InstanceDecl { class: "Indexable", types: &[TypeShape::Array(Wildcard), Number, Wildcard] },
    InstanceDecl { class: "Indexable", types: &[TypeShape::Map(Wildcard),   String, Wildcard] },
    InstanceDecl { class: "Indexable", types: &[TypeShape::String,          Number, String] },
];
```

The constraint solver loads from this table. Adding an instance becomes a one-line PR.

**7c. Surface-form predicates.**

After phase 3 introduces internal/runtime forms (e.g., `Value::Closure`, runtime locations), add `is_surface(expr) -> bool` that rejects any AST containing a runtime-only form. Phase 5's well-typed-term generator must only emit surface forms; the property test's input gates on this predicate.

**7d. Origin-tracking extension.**

`TypeOrigin` already produces `typeof(.length)` in errors. Once `prompt-inty.md` lands its discriminated-union work, extend origins to include `narrowed-from(union, condition)`, so the error message "expected number, got string" can become "expected number, got string (narrowed from `string | undefined` at line 12 via `typeof === 'string'`)."

**7e. Mutability stays — don't switch to syntactic walking.**

Document in `src/infer/env.rs` that the `Mutability` flag plus `is_syntactic_value` is the canonical answer for value restriction. Don't accept PRs that replace it with a body-walker; the body-walker approach (a) misses aliasing, (b) is O(n²), (c) is tempting because it looks more "principled." Add a comment explaining the trap.

**Success criteria.** Each item is a separate PR. Each PR is reviewable in under an hour.

---

## Out of scope

These are real things rosa does that we deliberately do not bring over:

- **Equi-recursive μ-types with auto-folding on row-guarded occurs-check.** Stay with `Type::Named(TypeId, args)` + the registry. Equi-recursion produces unreadable error messages and doesn't compose with imported/named types.
- **22 parallel judgment forms.** Phase 6's config approach gives the same expressiveness as one parameterized inference path, not 22.
- **A separate "rendering grammar" for documentation.** Pretty-printing is a view over the one canonical AST, not a parallel data structure.
- **Replacing the JSDoc-comment annotation surface.** That's a frontend change, not a type-system change; out of scope for this rewrite.
- **New typing features.** Discriminated unions, narrowing, exhaustiveness all live in `prompt-inty.md`. Don't add features here; refactor first, add features after, take advantage of the new infrastructure when you do.

## Coordination with `prompt-inty.md`

That plan adds discriminated unions, untagged unions, literal types, `typeof`-narrowing, property-path narrowing, and switch-exhaustiveness. Recommended ordering with this plan:

1. Land **phase 1** of this plan (modularize `infer.rs`). Required — adding a feature into the old monolithic file would destroy the value of the modularization.
2. Land **phases 1–4** of `prompt-inty.md` (lattice, join, union elimination, narrowing infrastructure). User-visible payoff.
3. Land **phases 2–4** of this plan (operator catalog, dynamics, blame). The operator catalog should now include the new union-eliminating arms; the dynamics should include literal-equality and union-narrowing reductions.
4. Land **phases 5–7** of `prompt-inty.md` (narrowing predicates, exhaustiveness, builtins update).
5. Land **phases 5–7** of this plan (proptest soundness, configuration, polish).

This interleaving means each plan delivers user value periodically and each plan benefits from the other's infrastructure when it matures.

## Reporting cadence

After each phase, post a short summary covering:

- What landed.
- Which existing tests changed expected output, and why.
- Any surprises (blame triples found, generator bugs, perf cliffs).
- Estimated effort for the next phase.

Don't move to the next phase until the previous one's tests are green in CI.
