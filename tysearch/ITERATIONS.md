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

## Next

- **A suite of languages with different kinds of type system**, so the
  search is judged on all of them and can't overfit to inty's model:
  - subtyping (integers and floats, with only integers as indices);
  - implicit coercion (a JavaScript-like `+`);
  - a unityped control language where nothing gets stuck;
  - later, records with width subtyping.
- **Let-polymorphism**, then mutable `let` and assignment: the value
  restriction (DESIGN.md §8.2).
- **Statements:** `return`, `throw`, `try` and loops, with faults and
  abrupt completions.
- **Objects and arrays:** refinement indexed by a field label (rows).
