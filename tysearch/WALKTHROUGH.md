# How a program worked out the type rules of a JavaScript-like language

Type checkers usually come with rules written by people. Here, a program
had to work them out by itself, for a small language much like JavaScript,
starting from almost nothing. This page follows one real session of
tysearch, step by step. It is for anyone; no type theory needed.

| | |
|---|---|
| **It gets** | An interpreter for the language, and nothing else. It can run any program and see what happens: a result, a crash, or an allowed error such as an index out of range. |
| **It must** | Produce rules that say, *before* running a program, "this one is safe". The more safe programs they approve, the better. |
| **It must never** | Approve a program that crashes, like `1 + "a"`. |

## First, it gets to know the values

It tries every small value in small situations: add 1 to it, call it, read
`.x` from it, and so on. Values that crash in exactly the same situations
get grouped together. That gives it nine kinds of value, without being told
any of them:

- numbers: `0`, `1`, `-1`
- strings: `""`, `"a"`
- `true`, `false`, `null` (this language treats them alike)
- functions of one argument
- functions of two arguments
- objects with `x`: `{x: 1}`
- objects with `y`: `{y: 1}`
- objects with `x` and `y`
- arrays: `[1]`

## Then it climbs, one rung at a time

It starts with the simplest kind of rules and tries one new ability at a
time. Each try means a full search for rules, then checking them on about
60,000 safe programs, plus some that crash. An ability stays only if it
approves more of them, or as many with fewer rules, and still never
approves a crash.

The percentage on each rung is the share of safe programs its rules
approve.

### Rung 0, the start: fixed rules only (10.8%)

Every rule names exact kinds: "`+` takes two numbers". It knows nothing
about functions yet. It needs 527 rules, because comparing with `===`
needs a separate rule for every pair of kinds.

It can check: `1 + 1`, `"a" + "a"`.

### Rung 1, kept: "any kind" placeholders (28.0%)

Rules may say "any kind" (a type variable): "`===` compares any two
values". The 527 rules shrink to 44, and approvals nearly triple.

### Rung 2, kept: knowing what's inside (31.7%)

"Object with x" becomes "object whose x is a number". "Function" becomes
"function from number to string". "Array" becomes "array of strings".

Now it can also check: `({x: 1}).x + 1`, `[1, 1][0] + 1`.

### Rung 3, kept, the biggest jump: variables inside code (55.0%)

Rules for things that name a value: function parameters, `let`, and the
`e` in `catch (e)`. Something thrown could be anything, so it learns that
`e` is "unknown".

Now it can also check: `((x) => x + 1)(1)`,
`try { throw 1 } catch (e) { typeof e }`.

> **Tried and dropped:** functions you can use at several types (generic
> `let`). They approved a few more programs, but not enough to count.

### Rung 4, kept: tracking `return` (63.4%)

A `return` sends a value out of the function it's in. So the rules have to
know what the function is expected to give back.

Now it can also check: `((x) => { return x + 1 })(1)`.

> **Tried and dropped:** "a number is also an ok string" style rules
> (subtyping). Nothing in this language works that way.

### Rung 5, kept: "this or that" types (70.0%)

When the two sides of `c ? a : b` differ, the result is "number or string"
(a union type).

Now it can also check: `typeof (true ? 1 : "a")`.

> **Tried and dropped:** narrowing (knowing `x` is a number inside
> `if (typeof x === "number")`), generic `let` again, and both in pairs.
> Each approved a few more programs, but too few to count.

### Cleanup: could any ability go?

Finally it tries removing each ability it kept, in case a later one made
an earlier one unnecessary. Every removal approved fewer programs. So all
five stay.

## What it never did

At every one of the 20 tries, including those it dropped, it approved no
crashing program. These two were rejected every time:

| Program | What happens |
|---|---|
| `1 + "a"` | crashes: can't add a number and a string |
| `({x: 1}).y` | crashes: the object has no `y` |

The final rules were checked on 99,963 programs, 61,174 of them safe. They
approved 42,697 of the safe ones, and not one that crashes.

## Still out of reach

- `let id = (x) => x; id(1); id("a")`: safe, but rejected. Using one
  function at two types needs generic `let`, which didn't make the cut in
  this session.
- `let x = true ? 1 : "a"; typeof x === "number" ? -x : x[0]`: safe, but
  rejected. This needs narrowing, which was also tried and dropped.
- `(true ? 1 : "a") + 1`: rejected on purpose. It happens to work, but the
  rules can't know the condition is `true`. Had it been `false`, it would
  add a string to a number and crash. A checker has to be careful like
  this.

## Where this came from

One run of `cargo run --release --example climb_walkthrough`, which took
77 minutes, recorded in [ITERATIONS.md](ITERATIONS.md). The percentages are
shares of safe programs: every small program, 20,000 random ones, and
programs the rules on each rung generated, kept so that later rungs are
judged on them too.

Since this run, the bar for keeping an ability is lower (one more program
in 2,000 approved, from one in 500), so generic `let` and narrowing may
make the cut in later runs. Running the example again shows the current
climb, each step as it finishes.
