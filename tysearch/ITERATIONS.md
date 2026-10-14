# Iterations

Each iteration extends the language under test toward inty's Lean model
(`src/langs/model.rs`), then improves the search until it finds the typing
rules. It ends with a test in `tests/discover.rs` that pins the rules on
several seeds and checks that no typed term gets stuck. Each iteration notes
what made the search fail on the new features and what fixed it, and how the
rules found differ from the model's `HasType` (`lean/Inty/Typing.lean`).

## 0. First-order operators

**Model.** Literals, `+` on numbers or strings, `-`, `<`, `===`, `typeof`,
`length`, and a conditional on booleans (`src/langs/core.rs`), plus TAPL's
arithmetic language (`src/langs/arith.rs`).

**Search.** Sorts from fingerprints, then schemas enumerated per
constructor, refuted by observation and by sampled compatibility tests,
then a weighted cover.

**Found.** TAPL chapter 8's rules. inty's `Plus` class, as two rules for
`+` that anti-unify to `(a, a) -> a`.

## 1. Functions, calls and `const`

**Model.** On top of iteration 0, the model's own:

- `undefined` and `null`;
- `!`, `typeof` and unary `-`;
- `*`;
- a conditional that reads its test by truthiness;
- `const` bindings;
- functions of one and two parameters, which can call themselves;
- calls that ignore extra arguments and get stuck on missing ones.

The binders use de Bruijn indices.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| Closures that get stuck inside their body split the function sort | Fingerprints count only the context's own step, so stuck reports `root` |
| No sort for functions of a given type | A sort is *refined* when what its eliminator gives depends on the member: `T3<A -> R>` is the closures that, called with an `A`, give an `R`. That is a logical relation, tested by sampling |
| Bound variables typed freely, so `func1` could type its recursive self at anything (unsound in general) | **Binder flow.** Probe where each bound variable's value comes from: make the child the variable and see where its value comes out. `const`'s `x0` is child 0's value. `func1`'s `x0` is its call's argument, and `x1` is the function itself. Bound types are then tied to their sources |
| Enumerating every generalisation of every instance exploded (19,060 candidates for `===`) | Candidates come from lgg (Plotkin) of pairs and triples of instances; lgg climbing from seeds in each shape group (Golem); and top-down enumeration of every rule with at most one sort constant |
| Instances paired a function's type with arguments of other types | Instances are drawn from every combination of the children's types, ranked by alignment: how many positions mention each type |
| Junk rules no observation contradicted | Before a rule joins the cover, `falsify` attacks its compatibility lemma (CEGIS). It instantiates the rule's variables, takes children meeting the premises from the whole pool, and runs the node |
| Spurious refutations | Premises and conclusions use the same samples. The value that actually flows into a bound variable is always among them |
| Samples of a function type all behaved alike | Samples are spread over behaviours: one per distinct reaction to probe arguments |
| Selection skewed by the many kinds of closure | Observations are weighted so each tuple of child sorts counts once. Among rules gaining a good share, the simplest wins, and every rule must gain at least 15% |
| `app1 : (T3<T2 -> T1>, a) -> T1` (unsound, but its smallest counterexample has about 10 nodes) | **Faithfulness.** A rule for a refined sort's eliminator may only use what the refinement means: `app1 : (T3<a -> b>, a) -> b` |
| 10× too slow | Removed the evaluation cache: hashing a term and its environment cost more than running it |
| The same seed gave different results | A `HashMap`'s iteration order fed the random choices |

**Found** (the same on seeds 1 to 6):

```
num : T0    str : T1    true, false, undefined, null : T2
! : (a) -> T2               typeof : (a) -> T1        neg : (T0) -> T0
+ : (T0, T0) -> T0          + : (T1, T1) -> T1        (class: (a, a) -> a)
- , * : (T0, T0) -> T0      < : (T0, T0) -> T2        === : (a, b) -> T2
cond : (a, b, b) -> b
const : (a, [x0: a] b) -> b
func1 : ([x0: a, x1: T3<a -> b>] b) -> T3<a -> b>
func2 : ([x0: a, x1: b, x2: T4<a, b -> c>] c) -> T4<a, b -> c>
app1 : (T3<a -> b>, a) -> b
app2 : (T4<a, b -> c>, a, b) -> c
```

T3 and T4 are `(a) => b` and `(a, b) => c`. No typed term gets stuck,
among all terms up to size 4 and 20,000 random ones up to size 9.

**Differences from inty's `HasType`.** All of them are sound in the
semantics:

- **T2 merges `boolean` with `undefined` and `null`.** No operator in this
  fragment is stuck on one and not the other. Sorts distinguish only what
  eliminators distinguish.
- **`cond : (T3<a -> b>, c, d) -> c`** (and the same for T4): a function
  is always truthy.
- **`app2 : (T3<a -> b>, a, c) -> b`:** a call ignores extra arguments, as
  the model's semantics does. inty's typing rule requires one argument per
  parameter.
- **`const` is monomorphic.** The model generalises a `const` whose
  initialiser is a syntactic value. That is next.

## 2. A suite of languages with other kinds of type system

The search has to work for languages whose type systems differ in kind
from inty's, not only for inty's model. Each language here is pinned by
a test, and every change to the search runs against all of them.

| Language | Type system found |
|---|---|
| `unityped`: nothing ever gets stuck | One sort; every safe term typed |
| `pairs`: products, `fst` and `snd` | `pair : (a, b) -> T2{fst: -> a, snd: -> b}`, which is `a × b`; `fst` gives `a` and `snd` gives `b` |
| `subtyping`: integers and floats, only integers count repetitions | `Int <: Float`; `+ : (Float, Float) -> Float` and `+ : (Int, Int) -> Int`; `floor : (Float) -> Int`; `repeat : (Str, Int) -> Str` |
| `coerce`: JavaScript's `+` and `-` | Booleans and `null` form the top sort (they are accepted only where everything is); `+ : (a, a) -> a` at the join, `+ : (a, Str) -> Str` and `(Str, a) -> Str`; `- : (a, b) -> Num` |

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| `snd` untypable: a pair was refined by `fst` alone | A sort is refined by every eliminator whose result depends on the member, and its type's parameters are each eliminator's in turn. An eliminator that only repeats another with extra arguments ignored (a two-argument call of a one-parameter function) is dropped |
| Overloads where subtyping would do: `+` and `<` each had four rules on numbers | **Subtyping from the fingerprints.** `s <: t` when `s` gets stuck in no context that accepts `t`. With subtyping, a sort's type includes its subsorts' values, and samples include them. The checker accepts a child below its premise, and widens a variable to the join. The search runs with and without subtyping, and keeps the system with the shorter description (counting each subtype pair) |
| With subtyping, `+ : (Int, Int) -> Int` was dropped, because `+ : (Float, Float) -> Float` already covered those runs | Selection counts precision: a rule gains where it gives a strictly more specific type than the rules chosen so far |
| `coerce`'s overloads each gained 11%, under the 15% bar | The bar is now 10%. The model's rules are unchanged |

**inty's model under the same search.** The fingerprints order its sorts:
booleans with nothing are the top, since they are accepted only by
operators that take anything. But the system with subtyping is longer (65
against 59), so the search keeps the one without, as before.

## 3. State and let-polymorphism

**Model.** Variables live in cells, as in the Lean model's environment.
`const` becomes `let`, since the model types the two alike. There is now
assignment `x = e`, which closures see, and `e₁; e₂`. The suite gains `refs`:
ML's `ref`, `get` and `set`, with `let` and functions.

**Generalisation is a policy per binder.** For each bound variable whose
value is a child's, the choice is to generalise that child's type never,
only when the child is a syntactic value (one that runs none of its
children: a constructor that, given children that would get stuck, still
gives a value), or always. A generalisable variable may also be used
monomorphically, and only a monomorphic one may be assigned, as in the Lean
model.

A policy is judged semantically. Take a child term whose type has free
variables. Its value must be in every instance of that type at once. The
test (`poly_member`) uses the value again and again, each time at a random
instance, through any rule that takes that instance: a call, but also a
store into a reference. It never starts over, and checks each result
against its instance.

- A pure value passes.
- A reference, or a closure over a fresh cell, fails once a use at one
  instance sees what a use at another stored.

The search keeps the most permissive policy that no tested term refutes.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| Closures with cells were never equal, so the function sort was refined by `app2` too | `Language::same`: a structural comparison to a bounded depth |
| Tests stored into the pool's references (`ref 0` came to hold a function) | Every run gets copies with cells of their own (`Language::isolate`). The tests about state share explicitly (`eval_shared`) |
| `set : (Ref<a>, b) -> b` passed every local test | **Kripke monotonicity.** A run must leave the values it was given in their types: checked for the children `falsify` gives a node, for the variables a premise binds, and for the arguments when testing a refined type's members. The result: `set : (T3< -> a>, a) -> a`, invariant |
| A function counted as taking `Ref<num>` though it stored a boolean there | The same check, in membership |
| Generated programs never used a generalised variable at two types, so no policy could be justified | Policies are judged by the semantic test above, not by generated programs |
| A sampled `g : ((bool) => a) => num` calls its argument on 0, and refuted generalising a function that diverges | The polymorphism test samples only first-order values for the other children |
| A string doubled through recursion ran out of memory | Strings past 4096 characters count as running out of fuel, as in the Lean model's driver |
| Minutes spent forgetting what was known of values a run had changed | The membership memo is keyed by value first, so forgetting is a single removal. Only a value that actually changed is re-checked |

**Found.**

- **`refs`:** exactly ML's system. Formation and use of references are
  `ref : (a) -> T3< -> a>`, `get : (T3< -> a>) -> a` and
  `set : (T3< -> a>, a) -> a`. `let` uses the **value restriction**:
  "always" is refuted by `ref((x) => 1)`, typed `Ref<(a) => num>`, whose
  value is not in all those instances at once.
- **`model`:** the rules of iteration 1, with `let` in place of `const`,
  and `seq : (a, b) -> b`. No typed term gets stuck, among all terms up to
  size 4, 20,000 random ones, and about 1,500 generated well typed.

**Known gap.** In the model, `let` generalises always, where inty
generalises only syntactic values. In the model, generalising a non-value
is unsound only through a closure over a fresh cell that hands back at one
instance what it stored at another:

```
let c = (x) => x in (p) => { let old = c; c = p; old }
```

The semantic test refutes it
(`tests/discover.rs: model_value_restriction_counterexample`). But it has
ten nodes, and neither random generation (60,000 terms) nor exhaustive
enumeration (too slow beyond size 5) reaches it. With references the
counterexample is three nodes, and the search finds the restriction.

## 4. The model's value restriction

**Gap closed.** In iteration 3, `let` in the model generalised always,
because no generated initialiser was a counterexample. The search now aims
its tests at state that outlives an initialiser:

- **Shape.** A binder whose variable takes a child's value (`let`), bound to
  a small value whose type shares a variable between positions (behaves
  parametrically, like `(x) => x`), and whose body makes a refined value (a
  function).
- **Bodies.** Every body up to size 6 built from the constructors that
  commit to no sort (the ones that move state around rather than compute on
  it), kept only if it both writes and reads the binder's cell: state can
  leak between instances only that way.
- **Screen.** All 15,000 such terms get a quick interleaved-instances test
  (6 uses each); the plain candidates get the full one (16 uses), with
  separate allowances for values and non-values.

**Found.** "Always" is refuted by a counterexample the search built:

```
let c = (x) => x in (flag, p) => flag ? c : (c = p)
```

Its type `(bool, (a) => a) => (a) => a` has a free variable, but a call at
one instance stores a function that a call at another hands back. So `let`
generalises syntactic values only, which is inty's rule (`Expr.IsValue` in
`lean/Inty/Typing.lean`'s `let_`). The rules are otherwise unchanged, and no
typed term gets stuck.

**Also fixed.**

- Cells printed their contents in `Debug`, and a closure stored in a cell it
  captures is a cycle. The result was a stack overflow when printing.

## 5. Objects

**Model.** Following the Lean model's `obj`, `get` and `set`, with the
labels `x` and `y`:

- the literals `{x}`, `{y}` and `{x,y}`;
- the reads `.x` and `.y`, stuck when the property is missing;
- the stores `.x =` and `.y =`, which need the property to exist.

Objects live in cells, and `===` compares them by identity.

**Found.**

- **Records.** Each set of labels is a sort, refined by its reads: `{x,y}`
  makes a `T7{.x: -> a, .y: -> b}`, which is `{x: a, y: b}`.
- **Reads.** `.x` is overloaded on the objects that have `x`:
  `(T5< -> a>) -> a` and `(T7{.x: -> a, .y: -> b}) -> a`. Their lgg is
  `.x : (c) -> a` where `c` has `x: a`, which is inty's `HasProp x`
  constraint, here over a finite set of labels.
- **Stores.** `.x=` keeps the property's type:
  `(T7{.x: -> a, .y: -> b}, a) -> a`. The monotonicity check refutes a
  store of any other type.
- **Truthiness.** A conditional on an object takes its first branch, since
  objects are truthy, as functions are.

No typed term gets stuck.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| No rule for stores. The invariant rule was a candidate, but the gain bar was relative to everything coverable, which counted what non-invariant rules (refuted later, by monotonicity) covered | A rule's bar is relative to the best rule chosen so far (20%). The first needs 5% of what the standing candidates cover |
| Junk `app2 : (T3<T2 -> T0>, a, b) -> T0` came back | **Aliases.** An eliminator dropped from a refinement because it only repeats another with extra arguments ignored (`app2` on a one-parameter function) is recorded, and held to the same faithfulness: its leading arguments have the parameters' types |

## 6. Arrays

**Model.** The literals `[a]` and `[a,b]`, and the Lean model's `index` and
`setIndex`:

- `idx` reads an element of an array or a character of a string, and
  faults out of bounds. On an object it reads a property by name, or gives
  `undefined`.
- `idx=` stores into an array, in bounds or just past the end (a push), and
  faults further out.

Property stores now add a missing property, as the Lean `setProp` does.

**Found.**

- **Arrays.** T7 is the arrays, refined by `idx`: `[a,b] : (a, a) -> T7<T0 -> a>`,
  which is `a[]`, indexed by numbers. The search finds that the two
  elements must share a type.
- **Reads.** `idx : (T7<a -> b>, a) -> b`. Strings indexed by numbers give
  strings, `(T1, T0) -> T1`.
- **Objects by key.** `idx` gives T2 on an object, by number or by string.
  That is sound here only because no term can build the string `"x"` or
  `"y"`: the literals are `""` and `"a"`, and no `typeof` name holds an
  `x` or a `y`. The closed world shows through.
- **Stores.** `idx= : (T7<a -> b>, a, b) -> b`, invariant, like the
  property stores.
- **Truthiness.** A conditional on an array takes its first branch.

No typed term gets stuck.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| Numbers were refined by `idx`: as indices, 0 and 1 differ in whether they fault | Faults count as no behaviour when refining. A fault is allowed, so it tells nothing about a member's type |
| `[a,b]` typed `[1, "s"]` as an array of numbers: the samples of T0 had no 1, so index 1 was never read | A base sort's samples are its smallest members, then one from the far end |
| `[a,b] : (a, a) -> T7<T0 -> a>` was never proposed: a refined head counted as one constant only with variable parameters | `simple_rules` also takes unrefined sorts as a refined head's parameters |
| `app2 : (T4<a, b -> c>, a, b) -> c` lost out at the 20%-of-best bar. Two-argument calls are rare among the observations | A simple rule (at most one constant) that types what no chosen rule does needs only the first rule's small share (0.5%). A gain in precision alone still needs the 20% bar: without that, `coerce` took `+ : (T0, a) -> a`, sound only because T2 is the top, in place of `+ : (a, T1) -> T1` |
| Results changed with the set of constructors searched | Each constructor's search draws from its own random stream |
| The search with subtyping redid every constructor | It keeps the search of each constructor whose rules mention no widened sort |

Also new: `TYSEARCH_ONLY='app2|[a,b]'` searches just those constructors.
Constructor names have commas in them, hence the `|`.

## 7. Statements: `throw`, `try`, loops

**Model.** As the Lean model's `throw_`, `tryCatch`, `while_`, `break_` and
`continue_`:

- `throw e` throws any value.
- `try body catch handler` runs `handler` with the thrown value as `var 0`.
- `while (c) body` reads `c` by truthiness, and gives `undefined`. Each
  iteration takes a tick of fuel.
- `break` and `continue` reach their loop.

Uncaught, each is allowed, as a fault is: the Lean model's
`Result.Abrupt`. Abrupt completions travel as faults, and `throw`'s
carries its value.

**Found.** The Lean model's rules exactly:

```
throw : (a) -> b
try   : (a, [x0: unknown] a) -> a
while : (a, b) -> T2
break : a
continue : a
```

`unknown` is new: the type of every value, about which nothing can be
assumed. It is inty's rigid `unknown`. No typed term gets stuck.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| `throw`, `break` and `continue` had no rule: they never give a value, so no observation supports a result type | A construct that never completes normally, only abruptly, gets `c : (a, …) -> z`, its result free, if the attacks don't break it |
| `try : (a, [x0: a] b) -> a`: the binder probe saw the node's value equal the body's, and took `x0` to be the body's value. The handler never ran | A probe counts only if the child ran: the node must change when another term replaces it |
| `try`'s bodies never threw: closed children came from values only | The pools get the smallest closed term for each kind of fault: one per thrown value, `break`, out of bounds. Observations and attacks draw from them, since a fault is in every type |
| No type for what a `catch` binds: any type variable is refuted, rightly | `Top` (`unknown`): in the universe, but never a child's own type. A binder of no known source is observed at `Top` |
| Junk `try` rules (`[x0: T4<b, c -> d>] a`, a handler that's an object) survived the attacks. Open terms are of size 3 at most, so no handler calls a two-argument `x0`. The handlers that fit were those that only fault, and those refute nothing | Attacks try **uses** of each bound variable first: a context its sort is accepted in and another sort is not (`app2(x0, 0, 1)`, `neg(x0)`). Then the children of nodes the rule covers. Children that only fault are skipped |
| The value restriction's hand-built counterexample stopped being refuted. `throw`, `while` and the like were among the uses that test a value at many instances, and they tell nothing about its type, so they crowded out the uses that do | A use must have a result that depends on the value's type: its type is not a bare variable, or that variable is in the result |

## 8. `return`, and exit types

**Model.** The Lean model's `ret`: `return e` completes abruptly with `e`'s
value, and a call turns its body's `return` into its value. At the top,
with nothing to return from, it is as wrong as getting stuck. So the
black box gets a new outcome, `Return(v)`, safe only where an enclosing
frame's type says what it may carry.

**Found.** The Lean model's `ret`, and its functions' `R`:

```
return : (a) -> b (return a)
func1  : ([x0: a, x1: T3<a -> b>] b (return b)) -> T3<a -> b>
func2  : ([x0: a, x1: b, x2: T4<a, b -> c>] c (return c)) -> T4<a, b -> c>
```

Every other rule passes its exit type down unchanged, so it shows none. No
typed term gets stuck or returns at the top.

**How.**

- **Exit types in the rule format.** A premise may give its child an exit
  type of its own, and a rule may fix the node's. The checker threads an
  exit type through each judgement, `never` at the top.
- **Exit flow, by probing.** A returning term in each position shows
  whether its `return` goes through the node or is caught. `func1(return
  0)` gives a function, not a `return`. A node that returns with values
  and variables for children starts one. Only those positions get an exit
  type to search for.
- **Observations record exits:** the types every value a child returns is
  in. A node's `return` refutes a rule unless every exit type the
  premises allow holds the value.
- **Attacks** draw closed children that return, where the value fits the
  exit type. They count open children that return, not only those that
  complete, as children that can break a rule. `func1`'s body getting an
  exit type unrelated to its result was refuted only after that.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| No `return` term reached the pools: the abrupt pool was capped at 8, filled by `break`, `continue` and throws | A few of each kind (fault reason, or `return`) |
| A full run of `func1` alone took minutes: generated programs nest functions deeply, and judging `T3<a -> T3<b -> …>>` runs 3^depth calls | Fewer runs where the result's type is itself a function's |
| `try : (a, [x0: b] a) -> a`, unsound, beat `[x0: unknown]` in one run. Attacks drew 2 random abrupt terms per instantiation, and with returns and breaks in the pool a throw came up about half the time | One abrupt term of each kind per closed child |
| `idx : (T1, T0) -> T1` came and went. `idx` on a string and a number has 4 nodes, of which one gives a value, and random tuples of groups found 3 | Stratified observation goes through every tuple of groups, each with its share of the nodes |

## 9. Unions

**Goal.** `cond(c, 0, "a")` is safe, and inty types it `number | string`;
the search typed it not at all. Same for `[1, "a"]`, and a `try` whose
body and handler differ.

**Found.** The rules don't change. What's new is which of their variables
may stand for a **union** of types. In the model, every one may, as in
inty: `cond : (a, b, b) -> b` types `cond(c, 0, "a")` as `T0 | T1`. In
`core`, whose new `==` compares two values of one type, one may not:

```
== : (a, a) -> T2  (a may not be a union)
```

`1 == "a"` is stuck. Of the model's safe terms, 68.5% are typed, up from
63.5%. None gets stuck.

**How.**

- **Union types** `T0 | T1` in the type language. A value is in one if
  it's in a member.
- **Which variables.** The attacks try each variable as each union of two
  sorts. It may stand for a union if none breaks the rule.
- **The checker.**
  - A child may have a type below a ground premise: `T1` fits `T0 | T1`.
  - A child that doesn't fit a variable widens it to the union. That
    needs a variable at the top of two or more children's types, and in
    no other premise, bound directly to a type by the rule's own children,
    with no other variable bound to it. Otherwise a function's parameter,
    already used as a number, could be widened behind its use's back.
  - A rule whose variable may not be a union doesn't apply where it would
    be one.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| `core`'s `==` came out as three overloads, not `(a, a) -> T2`: the attacks instantiated `a` to `unknown`, and two unknowns may differ | `unknown` is in the universe only if something binds a value of no known source (the model's `catch`); a rule's variables range over it only then |
| `==(if(false, false, 0), false)` was typed and got stuck. At first only the variables the checker could widen were tested, so `==`'s `a` became a union through a child that was one | Every variable is tested, and the checker refuses a union where the attacks did |

## 10. Narrowing by `typeof`

**Model.** The Lean model's `caseTag e₁ .typeOf t e₂ e₃` for `t` of
`"number"` and `"string"`: `e₃` if `e₁`'s `typeof` is `t`, else `e₂`, each
with the value as `var 0`. This is JavaScript's
`typeof x === "number" ? … : …`.

**Found.**

```
typeof=number : (a, [x0: a] b, [x0: a] b) -> b
typeof=number child 1, x0: Child(0), reached by T1, T2, …, T8 only
typeof=number child 2, x0: Child(0), reached by T0 only
```

The rule is plain. The narrowing is a fact about the construct, found by
probing: which sorts' values reach each branch. The checker meets the
bound variable's type with them. With `x : T0 | T1`,
`typeof x === "number" ? -x : x[0]` is typed `T0 | T1`: the one branch
sees `x : T0`, the other `x : T1`. A branch no value of the type reaches
binds `never`, which fits anything. This is inty's flow typing.

**How.**

- **Reach, by probing.** Give the tested child a member of each sort, and
  see whether the branch runs: the node changes when the branch does
  something else.
- **Observation and attacks** run each branch under the narrowed type, so
  a branch that only strings reach is judged on strings. If no value
  reaches it, anything will do.

**What broke, and what fixed it:**

| Problem | Fix |
|---|---|
| The then-branch's `x0` had no source: the probes drew the tested child from all ~110 representatives, few of them numbers, so the branch hardly ran | Probes draw a sort first, then a member, and sample until 12 trials ran the child |
| T8 seemed to reach the number branch: two runs that each `return` a new array compared unequal | `same_outcome` compares returned values as it does values |
| Junk `typeof=number : (a, [x0: a] T7<a -> b>, [x0: a] c) -> c`. A branch no value reaches has every type, so matching branched on its 57 types past the cap of 32 before reaching the branch that fixed `b`. So the plain rule matched nothing there | Matching takes the most constrained child first |

## Next

- **Keys:** a string literal `"x"`, so that `idx` on objects by string
  has no one result type. inty gives literal string types for keys.
- **Sums:** `unwrap` (`undefined`/`null`), and `caseTag` on a field.
  Booleans, `undefined` and `null` are one sort in the model so far: no
  context tells them apart, and branching is no context.
- **Records with width subtyping in the suite:** order refined sorts by
  their fingerprints too.
