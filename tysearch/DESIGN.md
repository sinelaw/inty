# tysearch: discovering a type system from an operational semantics

## Summary

Given a language's operational semantics, tysearch looks for a type system
that fits it. "Fits" means three things:

1. **Sound.** A well-typed program never gets stuck.
2. **Permissive.** It accepts as many of the safe programs as it can.
3. **Simple.** It has few rules, and each one is small.

None of these settles the answer by itself. The exact set of safe programs
is undecidable, and it isn't compositional. In TAPL's arithmetic language,
`if true then 0 else false` is safe, but no compositional type system with
only `Bool` and `Nat` can type it. So there is no single correct type
system to find. There is a trade-off between permissiveness and simplicity,
with soundness as a hard constraint. tysearch treats the problem as a search
over a space of candidate rules, and returns the best points on that
trade-off.

Three ideas make the search tractable:

- **Types are read off the semantics.** A value's base type is determined by
  which eliminators accept it. This is the canonical-forms lemma read
  backwards: `if` accepts `true` and `false`, and `succ` accepts numerals.
  Sorting values by which immediate contexts they get stuck in gives the
  base types without guessing them.
- **Soundness becomes local.** Once each type means a set of values
  (semantic typing, as in the logical relation inty's Lean proof uses),
  a type system is sound if each of its rules is sound on its own. That is
  the rule's compatibility lemma. So the search splits into one small
  search per constructor, and a counterexample blames exactly one rule.
- **Generate, test, constrain.** Candidate rules are enumerated from small
  to large. Counterexamples from running the semantics refute them, and
  each refutation also rules out every more general candidate. This is the
  loop that Popper (inductive logic programming) and CEGIS (program
  synthesis) use.

A working prototype for first-order languages is in this directory. On
TAPL's arithmetic language, it finds exactly the rules of TAPL chapter 8,
`Bool` and `Nat` included, without being told those types exist. On a slice
of the operators of inty's Lean model, it finds inty's `Plus` class: `+`
gets two rules, and they fold into `(a, a) -> a where a ∈ {number, string}`.
Neither system has any typed program that gets stuck, among every term up
to size 6.

The rest of this document covers the problem, the theory behind the design,
related work, the architecture, the search, how candidates are verified, how
the design extends to binders, polymorphism and state, how it connects to
inty, and the roadmap.

---

## 1. The problem

### 1.1 Inputs

- **A signature.** The term constructors, their arities and where they bind
  variables, and families of literals (`num`, `str`) with their payloads.
- **An evaluator.** It takes a closed term and returns one of four
  outcomes. This is the only access the search has to the semantics, so it
  is treated as a black box:
  - `Value(v)`: the term ran to a value.
  - `Stuck`: no rule applies. This is what a type system must rule out.
  - `Fault`: a failure the language documents as allowed, such as an index
    out of bounds or an uncaught `throw`. It is safe at any type. This
    matches the `fault` outcome of inty's model (`lean/ROADMAP.md`, ground
    rule 1).
  - `Timeout`: out of fuel. It says nothing either way.
- **A way to plug values back in.** `quote(v)` gives a term that evaluates
  to `v`, so values can be placed into contexts.
- **Optionally, a corpus of real programs.** These weight the search
  towards the programs people actually write. In inty's case, this is the
  1242 programs in the model corpus.

### 1.2 Output

- **A type language.** Sorts that are discovered, not given, plus whichever
  type constructors the search chose from a menu of templates (§5).
- **A set of typing rules** in a fixed format (§5). It also comes as an
  executable checker, and as a Lean `inductive HasType` (planned, §7).
- **Evidence.** The counterexample that refuted each rejected rule, the
  results of checking on a corpus held out from learning, witnesses of safe
  programs the system gives up on, and the system's place on the
  permissiveness/size frontier.

### 1.3 What "matches" means

For a candidate system `T`, let `typed(T)` be the programs it types, and let
`safe` be the programs that never get stuck. Then:

| Criterion | Definition | How it's measured |
|---|---|---|
| Soundness (hard) | `typed(T) ⊆ safe`, and every typed value lies in its type's meaning | Tiers T0–T4 (§7): testing, then optionally proof |
| Permissiveness (↑) | `typed(T) ∩ safe` | Weighted coverage: the corpus, plus every sort tuple, plus enumerated terms |
| Simplicity (↓) | The description length of `T` | Number of rules, constants, variables and type constructors |
| Usability (constraint) | Syntax-directed, with principal types | Enforced by the rule format (§5) |

Soundness is a constraint, and the other two are objectives, so the answer
is a **Pareto frontier**. The tool reports a default point on it, the knee
of the curve, but the whole frontier is part of the result. For instance, a
system with union types types more of `safe` than one without, and costs
more to describe. The person running the tool should see that trade-off, not
have it decided silently.

---

## 2. Foundations

### 2.1 Types as abstract interpretation

Cousot showed that type systems are abstract interpretations of the
semantics ("Types as abstract interpretations", POPL 1997). A type stands
for a set of values, and the typing rules are abstract transformers.
Synthesising abstract transformers from a concrete semantics is now a
synthesis problem with good tools: Amurth finds the most precise transformer
expressible in a given DSL (Kalita et al., OOPSLA 2022).

tysearch adds one restriction: the abstraction must be **compositional and
syntax-directed**. That restriction is what makes the result a type system
rather than a static analysis.

### 2.2 Semantic typing makes soundness local

Give each type `τ` a meaning `⟦τ⟧`, a set of values, and define
`E⟦τ⟧ = {e | e runs to a value in ⟦τ⟧, or faults, or times out}`.

A rule
`c : (P1, …, Pn) -> P0` is **compatible** if, for every instance of its
type variables, `ei ∈ E⟦Pi⟧` for all `i` implies `c(e1, …, en) ∈ E⟦P0⟧`.

The fundamental theorem of logical relations says that if every rule is
compatible, then every typed term is in `E⟦its type⟧`. That is type
soundness. inty's Lean proof has this shape: `V k W τ v` is a step-indexed
Kripke logical relation (`lean/Inty/Soundness.lean`).

For the search, this has two consequences:

- **Soundness can be checked rule by rule.** A failure blames exactly one
  rule. The search space is a product of one menu per constructor, not one
  joint space.
- **A rule's soundness can be tested directly.** Sample members of `⟦Pi⟧`,
  apply `c`, and check that the result is in `⟦P0⟧`. Inty's
  `src/meta/blame.rs` (the Cimini-Blame prober) already does this for the
  operator catalog. tysearch generalises it from *checking* a catalog to
  *producing* one.

This locality holds as long as `⟦τ⟧` is fixed independently of the rules.
That is true for sorts (§2.3). For arrows, schemes and references, the
meaning of a type depends on the other types, and §8 discusses what that
changes.

### 2.3 Sorts from canonical forms

A value's **fingerprint** is a bit vector. It has one bit for each one-hole
context `c(p1, …, [ ], …, pn)`, one constructor deep, with the other
positions filled by probe values. The bit is set if plugging the value in
gets stuck. Two values with the same fingerprint belong to the same
**sort**. This is the same trick as Ruler's characteristic vectors (Nandi et
al., OOPSLA 2021), applied to "gets stuck" rather than to output values.

The contexts are one constructor deep on purpose. With all contexts, the
partition would be the Myhill–Nerode congruence of "doesn't get stuck",
which is the exact semantics, not a type system. For example, the context
`succ(if [ ] then 0 else true)` separates `true` from `false`. A type system
deliberately forgets which value is which, and keeps only which eliminators
accept a value. That is exactly what the canonical-forms lemma states.

Fingerprints are bit sets, so they are also ordered. If one sort's stuck set
is contained in another's, it is accepted everywhere the other is: a
candidate subtype. Example: an `Int` value can be used as an index, and in
every numeric context where any `Num` value can, so `Int <: Num`. The
prototype doesn't use this order yet; §5 does.

### 2.4 First-order systems are tree automata

In a first-order language, a type system whose rules use only sorts is a
bottom-up tree automaton. The sorts are its states and the rules are its
transitions. So the typable programs form a regular tree language contained
in `safe`, and `safe` itself is usually not regular. Two consequences:

- Learning such a system is learning a tree automaton from a membership
  oracle (the evaluator). That problem has known algorithms, such as
  Sakakibara's and Drewes & Högberg's, and known limits.
- Type variables shared between positions, as in `if : (Bool, a, a) -> a`,
  compress many transitions into one schema. Finding these schemas is
  Plotkin's **anti-unification**. Anti-unifying overloaded rules yields a
  **type class**: `+ : (num, num) -> num` and `+ : (str, str) -> str`
  generalise to `+ : (a, a) -> a where a ∈ {num, str}`. That is inty's
  `Plus` (§9).

---

## 3. Related work

Searches turned up no system that discovers typing rules from an
operational semantics. The closest work either transforms existing typing
rules, synthesises other artefacts from semantics, or tests type systems.
tysearch borrows from each:

| Work | What it does | What tysearch takes from it |
|---|---|---|
| Cousot, *Types as abstract interpretations*, POPL 1997 | Derives type systems as abstractions of the semantics | The framing: a type system is a compositional abstraction (§2.1) |
| Kalita, Muduli, D'Antoni, Reps, Roy, *Synthesizing abstract transformers*, OOPSLA 2022 (Amurth) | Most precise transformer in a DSL, via CEGIS | A DSL of rules, and "most precise in the DSL" as an objective |
| Nandi et al., *Rewrite rule inference using equality saturation*, OOPSLA 2021 (Ruler) | Enumerate terms, group them by behaviour, propose rules, validate, keep a small set | The pipeline shape: fingerprints → candidate rules → validation → minimal set |
| Cropper & Morel, *Learning programs by learning from failures*, MLJ 2021 (Popper) | Generate → test → constrain over Horn clauses | Typing rules are Horn clauses. A rule that types a stuck term prunes every generalisation of it; a rule that is too strict prunes its specialisations |
| Garg, Löding, Madhusudan, Neider, *ICE*, CAV 2014 | Learn invariants from positive and negative examples and implications | A type system is a compositional inductive invariant (progress + preservation). Implication examples correspond to rules with premises |
| Cimini & Siek, *The Gradualizer*, POPL 2016 | Generates gradual type systems from static ones written as logic programs | Rules as logic programs, and transforming a rule set automatically |
| Cimini, Miller, Siek, *Well-typed languages are sound*, arXiv 2016 | A syntactic check on language definitions that guarantees progress and preservation | A cheap soundness certificate for candidates when the semantics is given as rules (tier T3) |
| Pombrio & Krishnamurthi, *Inferring type rules for syntactic sugar*, PLDI 2018 | Derives typing rules for sugar from the core language's rules | Derived rules, checked against a reference |
| An, Chaudhuri, Foster, Hicks, *Dynamic inference of static types for Ruby*, POPL 2011 | Observes runs to infer types for a program | Observing runs to propose arrow types for closures (§8.1) |
| Hritcu et al., *Testing noninterference, quickly*, ICFP 2013; Klein et al., *Run your research*, POPL 2012 | Random testing finds broken definitions and rules before any proof | Testing tiers T1–T2, with shrinking |
| Lampropoulos, Paraskevopoulou, Pierce, *Generating good generators for inductive relations*, POPL 2018 | Derives generators of derivations from inductive relations | Generating only well-typed programs from the candidate rules, for end-to-end tests (§7) |

---

## 4. Architecture

```
          ┌───────────────┐    ┌──────────────┐   ┌────────────────┐
 language │ 1 enumerate + │    │ 2 sorts      │   │ 3 observe      │
 ────────▶│   run corpus  │───▶│ fingerprint  │──▶│ per-constructor│
 (black   │ (small scope) │    │ values       │   │ sort tables    │
  box)    └───────────────┘    └──────────────┘   └───────┬────────┘
                                                           │
       ┌───────────────────────────────────────────────────┘
       ▼
 ┌────────────────────────┐  refuted  ┌───────────────────────────┐
 │ 4 search per           │◀──────────│ verify                    │
 │   constructor:         │──────────▶│ T0 counterexample cache   │
 │   enumerate schemas    │ candidate │ T1 compatibility sampling │
 │   (+ Popper pruning)   │           │ T2 typed generation       │
 │   select: cover / MDL  │           │ T3 symbolic, T4 Lean      │
 └──────────┬─────────────┘           └───────────────────────────┘
            ▼
 ┌────────────────────────┐   ┌──────────────────────────────────┐
 │ 5 compose + generalise │──▶│ 6 report: rules, classes,        │
 │   (anti-unify → class) │   │   frontier, held-out check,      │
 │   global switches (§8) │   │   untyped-safe witnesses, Lean   │
 └────────────────────────┘   └──────────────────────────────────┘
```

| Stage | Prototype module | What it does |
|---|---|---|
| 1 | `enumerate.rs` | Enumerates every term up to size *n* and scope depth |
| 2 | `semantics.rs` | Fingerprints values against one-hole contexts (stuck *at the root*), and partitions them into sorts. Refines a sort whose eliminator's result depends on the member (§8.1). Builds the universe of ground types, and tests membership |
| 3 | `search.rs` | Per constructor: binder flow, then nodes built from representatives and open bodies, and observations under typings of the bound variables |
| 4 | `search.rs`, `types.rs` | Proposes rules: simple ones top down, lgg of instances bottom up, lgg climbing. Refutes them by observation (T0), attacks the survivors (`falsify`, T1). Selects a weighted cover |
| 5 | `types.rs` | Anti-unifies overloaded rules into a class |
| 6 | `infer.rs`, `discover.rs` | Checks end to end with the induced checker, on more terms than learning used, and reports |

[ITERATIONS.md](ITERATIONS.md) records how each stage came to be, from the
failures each new feature of the model caused.

---

## 5. The hypothesis space

The space comes in layers. Each layer adds type-language **templates** and
extends the rule format. The search only reaches a layer when the layers
below it can't type something the corpus needs, and the description-length
cost of each template keeps the search from reaching too far.

| Layer | Type language | Rule format adds | Rediscovery target |
|---|---|---|---|
| L0 *(prototype)* | Discovered sorts, type variables | `c : (P…) -> P`, shared variables, several rules per constructor | TAPL ch. 8; the `Plus` class |
| L1 | `→` (and `×`) | Contexts and binders: `Γ, x:P ⊢ e : P'`, and a variable rule | The simply typed λ-calculus |
| L2 | Schemes `∀ā.τ` | A *generalisation point* at a binder, with a side condition from a menu (`always`, `never`, `is-value`, `is-λ`) | Hindley–Milner `let`; the value restriction (§8.2) |
| L3 | Records/rows, containers `C(τ)` | Field labels as payloads; row variables | Rémy rows; inty's `HasProp` |
| L4 | Unions, subtyping from the fingerprint order (§2.3), narrowing by tests | Premises refined by a test (`typeof x === "number"`) | inty's sums and `typetest` |
| L5 | `Ref τ`, worlds | A store typing; Kripke monotonicity | ML references |

### 5.1 Rule format

- **One schema per rule**, as a pattern over the type language. Variables
  are numbered by first appearance, so no two schemas are equal up to
  renaming. A variable in the conclusion must also occur in a premise.
- **Several rules per constructor** are allowed (overloading), but each one
  costs description length. Overloaded rules that anti-unify are reported
  as one class.
- **Syntax-directedness is part of the format.** Checking a program is
  bottom-up matching for L0, and unification for L1 and up. So every
  candidate comes with a checker, and principal types come from the format
  instead of having to be searched for.

### 5.2 The generality order

`R1 ≥ R2` if `R2`'s pattern is an instance of `R1`'s (θ-subsumption). A
counterexample to `R2`, a typed term that gets stuck, is also a
counterexample to every `R1 ≥ R2`, so all of them are pruned. A safe term
that `R1` fails to type is also untyped by every `R2 ≤ R1`. These are
Popper's two constraints. They are what lets the search scale past brute
force once rules have contexts.

---

## 6. The search

### 6.1 Objective

1. **Soundness:** no counterexample within the verification budget (§7).
2. **Coverage:** maximise the weighted number of sort tuples the rules
   accept. Each tuple counts once, plus how often the corpus uses it. The
   once-each part measures permissiveness on the semantics itself, so a
   tiny corpus still gives the full system. The corpus part breaks ties
   towards how people actually write programs.
3. **Description length:** fewer rules, then fewer sort constants (so
   variables are preferred), then fewer type constructors.

The search reports the frontier between (2) and (3) and picks its knee as
the default.

### 6.2 The loop

```
for each constructor c (independently, while soundness stays local):
    candidates ← schemas for c, smallest first
    for each candidate r:
        if a cached counterexample refutes r: prune r and every r' ≥ r     (T0)
        elif sampling finds t with ⊢ t : P0 by r but t ∉ E⟦P0⟧:
            cache t; prune r and every r' ≥ r                              (T1)
        else: keep r as sound
    choose: greedily cover tuples by gain, breaking ties by generality
compose; anti-unify overloads into classes
for each global switch (§8): try its settings, testing end to end          (T2)
verify the composition end to end on held-out terms                        (T2)
```

The prototype implements all of this except the generality-order pruning
and the global switches. At L0 the menus are small enough to enumerate in
full: 114 schemas for `if` with two sorts, 295 with three. Pruning starts to
matter at L1, where premises have contexts.

### 6.3 Proposing rules from data

Blind enumeration grows exponentially with arity and with the number of
templates. Observation tables give proposals directly:

- Each uniformly-sorted row of a table is a ground rule.
- Anti-unifying rows gives the candidate generalisations, from least
  general upwards. The search walks up this lattice and stops at the first
  refutation. This is the bottom-up dual of the top-down enumeration.
- For closures (L1), recording argument and result sorts at each call site
  gives proposals for arrow types (the Rubydust idea).

A language model could be another source of proposals, for templates or
rule shapes. Verification is unchanged: a proposal is a candidate like any
other and passes or fails the same tiers. This is optional and not part of
the core.

### 6.4 The climb: how much type system

What the type language may use is itself chosen by search. Each capability
is something the search can turn on:

- type variables;
- refined sorts (function, object and array types);
- binders, with `unknown`;
- `let`-generalisation;
- exit types;
- subtyping;
- unions;
- narrowing.

The climb starts from sorts and ground rules. It tries the capabilities in
that order, each needing only those before it to be of use, and keeps one
if the result:

- types more of the programs it judges by (one in five hundred), or as many
  with a smaller system (§6.1's description length);
- and gets none of them stuck.

**What it judges by.** It judges by a fixed set of programs (all the small
ones, and random ones), plus a **pool** that grows. Each run generates
programs its own system types, and the climb keeps a sample of them, safe
or not. Every later system, and the best so far, is judged on them too. A
capability is credited with programs only it types, which small or random
programs rarely show: a `let`-bound function used at two types. A crashing
program in the pool counts against any system that types it.

It goes round again while anything was kept. When no capability helps
alone, it tries **pairs**, for capabilities that pay only together. It
stops when nothing helps, or when 99% of the safe programs are typed. Then it minimises: it removes
each kept capability, the latest first, if the system without it types as
many programs and is no bigger. A capability that can't matter for the
language (exit types where nothing returns) is not tried.

Each run reuses the searches of the last for every constructor on which
nothing that changed bears. A new capability costs a full run only where
it touches the search.

---

## 7. Verification tiers

Every candidate goes through tiers in order of cost, and the result records
how far each part of it got.

| Tier | Method | Cost | What it establishes |
|---|---|---|---|
| T0 | Replay cached counterexamples and observation tables | ~free | The candidate is refuted, or not yet |
| T1 | Compatibility sampling: for each instance of the variables, apply `c` to sampled members of each premise's sort | Small, local, with blame | Evidence for the compatibility lemma |
| T2 | Generate well-typed programs from the candidate's rules (derivations, not terms), run them, and shrink failures. Also check every term up to size *n* | Larger, global | Evidence for the whole system, including where §2.2's locality doesn't hold |
| T3 | Symbolic: when the semantics is also given as reduction rules, check preservation of each rule by unification, progress by canonical forms, or the Cimini–Miller–Siek format | Moderate | A proof for that rule format |
| T4 | Export to Lean as `inductive HasType`, and prove soundness against the model's `eval` with inty's logical-relation proof as a template | High | A theorem |

Tiers T0–T2 give **evidence, not proof**. That is the same standing inty's
differential tests have for the claim that the Lean model's `eval` is
JavaScript. Even so, the prototype's results are strong for what they
claim: in the check, every term up to size 6 is tested, not a sample.
These are terms built from the language's literals (two numbers and two
strings), so sampling still decides which values get in. T1 relies on
**value-determinacy**: a subterm's effect on its parent depends only on its
value. That holds for deterministic call-by-value languages, and T2 tests
it. If T1 passes and T2 fails, the assumption is broken, and it is reported.

---

## 8. Beyond first order

### 8.1 Binders and arrows (L1)

- Terms gain binders (de Bruijn indices, as in the Lean model), and premises
  gain contexts.
- To observe an open subterm, close it with a substitution of sampled
  values. The local table becomes: the sorts of the free variables and of
  the children → the outcome.
- The fingerprint separates applicable values (closures) from all others, so
  `Fun` shows up as one sort. Splitting it into `A → B` uses the logical
  relation, bounded in depth: `f ∈ ⟦A → B⟧` if, for each sampled
  `a ∈ ⟦A⟧`, `f a ∈ E⟦B⟧`. `→` is a template with two arguments. It isn't
  discovered by fingerprinting. Its *need* is: the sort `Fun` has no
  uniform result under application.
- Compatibility for `λ` samples the argument, extends the closing
  substitution and runs the body. Compatibility for application samples
  from `⟦A → B⟧` and `⟦A⟧`.
- `quote` for closures: keep, for each value, the term that produced it.
  The black-box evaluator never has to print a closure.
- Target: the simply typed λ-calculus with `Bool` and `Nat`, found without
  being given `→`'s rules.

### 8.2 Polymorphism, and rediscovering the value restriction (L2)

Generalisation is a **global switch** at each binder: generalise or not,
and under which syntactic side condition, from a small menu. Compatibility
alone can't judge the switch, because the meaning of `∀` quantifies over the
other types. So switches are judged end to end (T2): generate typed
programs that use the generalised binding at two instances, and run them.

The flagship target. In a language with references, `generalise always` is
refuted by the classic counterexample:

```
let r = ref (fun x -> x) in r := (fun x -> x + 1); (!r) true
```

T2 finds it and shrinks it. `never` is sound but less permissive than
`is-value` on the corpus. So the search returns ML's value restriction
(Wright 1995) as the knee of the frontier. inty's own choice is in
`InferConfig` and the Lean `Textbook.lean`/`AssignSub.lean` separations,
which gives a reference to compare against.

### 8.3 State (L5)

Values in the heap make a value's meaning depend on the store, so `⟦τ⟧`
becomes world-indexed (the `W` of `V k W τ v`). Compatibility tests then
sample a heap together with each value. That is more expensive, but still
local. End-to-end T2 stays the backstop.

### 8.4 Non-termination and faults

`Timeout` is safe at every type, but it is also useless as evidence. A rule
whose tests only time out is reported as **unconfirmed**, not as sound.
`Fault`s are the language's documented allowances, so the type system
doesn't need to rule them out. This is inty's ground rule 1: the language's
documented contract is the theorem, so the discovered system is neither
stronger nor weaker than what the language promises.

### 8.5 Abrupt completions and exit types

An uncaught `throw`, `break` or `continue` is allowed, as a fault is (the
Lean model's `Result.Abrupt`). So a construct that never completes
normally is of every type: `throw : (a) -> b`. A `catch` binds a value
from no child, so it binds `unknown` (`Top`): the type of every value,
which is no value's own type.

A `return` is different: it is safe only where an enclosing frame says
what it may carry. So every judgement gets an **exit type**, as inty's
`HasType` has its `R`. A child's exit type is the node's unless its premise
says otherwise, and a rule may fix the node's. Probing tells which: a
returning child in each position shows whether the `return` goes through
the node or is caught (a function's body's, by the call). Whether the node
starts one shows too. Then the search finds:

```
return : (a) -> b (return a)
func1  : ([x0: a, x1: T3<a -> b>] b (return b)) -> T3<a -> b>
```

At the top there is nothing to return from: the exit type is `never`.

### 8.6 Unions

A rule's variable may stand for a union of types where the attacks don't
break the rule when it does: `cond : (a, b, b) -> b` with `b` as
`T0 | T1`, but not `== : (a, a) -> T2` when `1 == "a"` is stuck. The
checker widens a variable to a union when a child doesn't fit it. It does
so only for a variable at the top of two or more children's types, and in
no other premise, since a child typed against a structure holding it saw
it narrower.

### 8.7 Narrowing

A branch of a `typeof` test binds the tested value, but only some sorts'
values reach it. Probing finds which. The checker meets the bound
variable's type with them, so `x : T0 | T1` is `T0` in the one branch and
`T1` in the other, and `never` (which fits anything) where none reaches.

---

## 9. Connecting tysearch to inty

tysearch stays independent: it has its own Cargo workspace, no dependency on
`inty`, and is excluded from the root workspace. Adapters connect it to
inty:

- **The Lean model as an oracle.** `inty-model` reads one wire-format term
  per line (`lean/Inty/Wire.lean`, s-expressions with de Bruijn indices) and
  prints a verdict: `type …;value …`, `reject;stuck typeMismatch`, and so
  on. An adapter crate implements `Language` by printing terms in that
  format and parsing the half of the verdict after `;`. The model's own
  type is never shown to the search; it is used only for comparison.
- **`dynamics` as an oracle.** An adapter crate depends on `inty` by path
  and runs `dynamics::run_to_end`. This is the same semantics, at a
  different level (the shared AST after lowering).
- **Node as a third oracle**, as the differential tests already do. Where
  Node and the model differ, the type system should be learned from the
  model, since that is inty's contract. The difference itself is worth
  reporting.
- **Corpora.** The 1242 programs of the model corpus serve as the weighted
  positive set.
- **Comparison.** Compare the discovered system with inty's on the corpora,
  and report the symmetric difference with minimal witnesses:
  - *inty types it, but tysearch refutes the rule involved*: a candidate
    soundness bug in inty, with a stuck program as the witness.
  - *tysearch types it, but inty rejects it*: a gap in permissiveness, or a
    deliberate choice (such as "declared, not guessed" unions). Either way
    it gets a test that pins it down.
- **The operator catalog.** At L0, a discovered rule for an operator is a
  `TypingArm`. A catalog generated from the semantics can be checked
  against the handwritten one in `src/operators`. That is the
  generalisation of Cimini-Blame mentioned in §2.2.

The prototype's `core` language is a first-order slice of the model's
operators. It already recovers `Plus`, `===` at any two types, `typeof` at
any type, and `if : (boolean, a, a) -> a`.

---

## 10. Roadmap

Each milestone ends with the rediscovered system checked end to end, plus a
test that pins it.

| Milestone | Scope | Exit criterion |
|---|---|---|
| **M0** (done) | L0, a black-box `Language` trait, fingerprint sorts, T0 and T1, a weighted cover, anti-unified classes, an end-to-end check | TAPL ch. 8 exactly. `Plus` on `core`. 0 typed terms stuck up to size 6. Correct even when learning from size-2 terms |
| M1 (done) | L1: binders, closing substitutions, `→` with a bounded logical relation, unification checker | The model's functions, calls and `const` (ITERATIONS.md, iteration 1) |
| M2 (done) | L2: generalisation policies, judged by whether a value is in all instances of its type at once; Kripke monotonicity for state; T2 typed generation | HM `let`. The value restriction, both in `refs` and in the model (iterations 3 and 4) |
| M3 (in part) | L3: field labels as eliminators; containers | Records, and reads overloaded as `HasProp` (iteration 5); arrays (iteration 6) |
| M3s (done) | Statements: abrupt completions, `unknown`, exit types (§8.5) | The Lean model's `throw`, `try`, loops (iteration 7) and `return` with its `R` (iteration 8) |
| M4 | inty adapters (model wire format, `dynamics`); the corpus; comparison report | A diff of the discovered system against `HasType` on the model's fragment, with every disagreement explained or filed |
| M5 (in part) | Subtyping from the fingerprint order (done: iteration 2); unions, for the variables the attacks allow (done: iteration 9); the Pareto frontier in output | `Int <: Float`, `cond : (a, b, b) -> b` with `b` a union (done); a frontier plot for `core`, from unions to no unions |
| M6 | T4: Lean export of `HasType`, with a proof template | Soundness of the M1 system proved in Lean |

---

## 11. Risks and open questions

- **Sampling can miss a counterexample.** Mitigations: probes and samples
  spread over each sort, from smallest to largest; held-out checks on larger
  sizes; T2 typed generation; and, for the systems that matter, T3 and T4.
  Every result states which tiers it passed.
- **Probe bias in fingerprints.** If no probe makes a context reject a
  value, two sorts merge. Mitigation: refine iteratively. Re-fingerprint
  with probes drawn from every sort found, until the partition is stable.
  The prototype uses one round.
- **Value-determinacy** (§7) fails for languages with effects, where a
  subterm also changes the store. T2 detects this, and L5's worlds handle
  it.
- **Combinatorial growth** at L1 and above. Mitigations: proposals from data
  (§6.3), generality pruning (§5.2), and search per constructor wherever
  locality holds.
- **Is description length the right notion of simple?** The smallest rule
  set is not always the one a designer would write. The frontier, and the
  comparison against a reference, keep a person in the loop.
- **What the corpus is for.** Without a corpus, permissiveness is measured
  over sort tuples and enumerated terms, which is uniform and unbiased.
  With one, it is weighted towards real code. Both are reported.

---

## 12. The prototype today

*This section shows iteration 0's output. For the current state, see
ITERATIONS.md:*

- *functions, state, objects, arrays and statements in the model of inty's;*
- *the language suite (unityped, products, subtyping, coercion, ML
  references);*
- *the value restriction.*

```sh
cd tysearch
cargo run --release -- arith            # TAPL ch. 3 language
cargo run --release -- core             # first-order slice of inty's model
cargo run --release -- core --learn 2   # sound from compatibility testing alone
cargo test --release
```

`arith`:

```
sorts (values that get stuck in the same immediate contexts):
  T0 = {true, false, ...}
  T1 = {0, 1, 2, 3, ...}

rules:
  true : T0
  false : T0
  zero : T1
  succ : (T1) -> T1
  pred : (T1) -> T1
  iszero : (T1) -> T0
  if : (T0, a, a) -> a

end-to-end check on all 3873 terms of size <= 6:
  safe terms:           654
  typed terms:          232
  typed but unsound:    0
  safe but untyped:     422 (35.5% of safe terms typed)
    e.g. if(true, true, zero)
```

`core`:

```
rules:
  + : (T1, T1) -> T1
  + : (T0, T0) -> T0
    = class: + : (a, a) -> a  where a in {T0, T1}
  - : (T0, T0) -> T0
  < : (T0, T0) -> T2
  === : (a, b) -> T2
  typeof : (a) -> T1
  length : (T1) -> T0
  if : (T2, a, a) -> a
  (and the literals)

end-to-end check on all 128898 terms of size <= 6:
  typed but unsound:    0
  safe but untyped:     4832 (67.4% of safe terms typed)
    e.g. if(true, 0, "")
```

The "safe but untyped" witnesses are where this system's simplicity costs
permissiveness. They are what L4's union types would buy back, for a cost
in description length.

---

## Sources

- P. Cousot, [Types as abstract interpretations](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL97.shtml), POPL 1997.
- P. K. Kalita, S. K. Muduli, L. D'Antoni, T. Reps, S. Roy, [Synthesizing abstract transformers](https://arxiv.org/abs/2105.00493), OOPSLA 2022.
- C. Nandi, M. Willsey, et al., [Rewrite rule inference using equality saturation](https://arxiv.org/abs/2108.10436), OOPSLA 2021.
- A. Cropper, R. Morel, [Learning programs by learning from failures](https://arxiv.org/abs/2005.02259), Machine Learning 2021.
- P. Garg, C. Löding, P. Madhusudan, D. Neider, [ICE: a robust framework for learning invariants](https://www.springerprofessional.de/en/ice-a-robust-framework-for-learning-invariants/2198224), CAV 2014.
- M. Cimini, J. G. Siek, [The Gradualizer](https://popl16.sigplan.org/details/POPL-2016-papers/39/The-Gradualizer-a-methodology-and-algorithm-for-generating-gradual-type-systems), POPL 2016.
- M. Cimini, D. Miller, J. G. Siek, [Well-typed languages are sound](https://arxiv.org/abs/1611.05105), arXiv 2016.
- J. Pombrio, S. Krishnamurthi, [Inferring type rules for syntactic sugar](https://cs.brown.edu/~sk/Publications/Papers/Published/pk-resuarging-types/), PLDI 2018.
- C. Hritcu et al., [Testing noninterference, quickly](https://arxiv.org/abs/1409.0393), ICFP 2013.
- J. An, A. Chaudhuri, J. S. Foster, M. Hicks, *Dynamic inference of static types for Ruby*, POPL 2011.
- L. Lampropoulos, Z. Paraskevopoulou, B. C. Pierce, *Generating good generators for inductive relations*, POPL 2018.
- C. Klein et al., *Run your research*, POPL 2012.
- B. C. Pierce, *Types and Programming Languages*, MIT Press 2002, chapters 3 and 8.
