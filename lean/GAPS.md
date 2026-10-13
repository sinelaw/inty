# Intentional gaps between the model and inty

The model is meant to cover what inty implements ([ROADMAP.md](ROADMAP.md)).
A few things inty has are left out of it on purpose. This file lists them,
with why. They are not work to do: each is a decision, and changing it is a
change to this list.

The other differences are not here:

- Features the model doesn't cover *yet* are in the roadmap's phases.
- Disagreements to fix, in inty or the model, are in the divergence table
  of [README.md](README.md) ("Differential testing") and in
  `crates/inty/tests/model_corpus/known.txt`.
- Where the model's interpreter, like inty's `dynamics`, differs from
  JavaScript is in [README.md](README.md) ("Where the interpreter isn't
  JavaScript").

| inty has | the model | why |
|---|---|---|
| Number literal types: `/** const n: 1 \| 2 */`, `g(4)` rejected for a `1 \| 2 \| 3` parameter | no number literal types | Rarely used, and enums are written with strings. A number's literal type would need a payload with decidable equality, which Lean's `Float` doesn't have. |
| Boolean literal types as types of their own: `/** const t: true */` used where a `Boolean` is expected, `true \| false` | a boolean literal type (`Con.boolLit`), made by checking `true` or `false` against it, for a variant's tag: `{ok: true, value: T} \| {ok: false, error: E}`, built by a tagged object literal and taken apart by `x.ok === true`. A value of one isn't injected into `Boolean` (a `"s"` is into `String`), and there are no unions of them | Tagging a result by a boolean is the one use real programs have. |
| Widening a literal type where it synthesises a type: an unannotated binding, an operand, a call argument, the join of `c ? t : "b"` with `t: "a"` | no widening: a literal synthesises its base type; a string literal type is made only by checking against it, and goes where a `String` does by injection in check mode; branches have one type unless an annotation is pushed into them | Widening is a function on types that doesn't commute with substitution: inty accepts `app1(k, "a")` and rejects `app2("a", k)` with `function app1(f, x) { return f(x); }`, `function app2(x, f) { return f(x); }` and `k` taking `"a"`. The model stays independent of the order of inference. |
| Reading a field every arm of a discriminated union has, without a test of the tag: `v.id` on `{kind: "a", id: Number} \| {kind: "b", id: Number}` | a variant's fields are read once a test of its tag takes it apart | An instance of `HasProp` on a variant would have to look inside each case for the field, and a case can be a type variable that a substitution later makes a record. Deciding the constraint would then have to wait on a known first argument, which only `Merge` does, with machinery of its own; deciding without waiting loses completeness of inference. A program tests the tag first. |
| The value of a program: its last expression statement is typed, but not one inside a `try` block | the program's value is typed throughout, a `try` block's last expression included | Programs don't use their completion value. The differential test puts the difference down to a `try` ending the program. |
| Keyword arguments in calls (`infer_keyword_call`) | none | Python only. The model types the shared AST of the JavaScript fragment. |
| Lowering from Python and Lua onto the shared AST | none | The model types the AST after lowering. Lowering is tested by running lowered programs against CPython and Lua instead ([ROADMAP.md](ROADMAP.md), "Frontends"). |
| The Go backend's integer analysis (`crates/inty-go/src/kinds.rs`) | none | It is outside the type system: it can't reject a program, and only chooses how a number is represented. |
