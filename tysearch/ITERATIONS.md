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

## Next

- **Reach the model's value restriction:** generation aimed at state that
  outlives its initialiser, or a symbolic argument.
- **Statements:** `return`, `throw`, `try` and loops, with faults and
  abrupt completions.
- **Objects and arrays:** refinement by an eliminator per field label, which
  gives rows. Records with width subtyping go in the suite too.
- **Speed:** the model takes about three minutes now, mostly attacking
  rules under the state checks.
