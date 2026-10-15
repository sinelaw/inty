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

The programs grow as it climbs. Each try also writes programs that only
its new rules would approve, and runs them. If they work, they count for
the new ability, and every later try is judged on them too. If they crash,
they count against it. That is how an ability that matters only in
particular programs, like using one function at two types, gets noticed.

The percentage on each rung is the share of safe programs its rules
approve. Each rung also shows a program it still rejects although it runs
fine: the smallest it could find, so they start obvious and get obscure.

### Rung 0, the start: fixed rules only (10.8%)

Every rule names exact kinds: "`+` takes two numbers". It knows nothing
about functions yet. It needs 527 rules, because comparing with `===`
needs a separate rule for every pair of kinds.

It can check: `1 + 1`, `"a" + "a"`.

Still rejects: `0 === 0`. One fixed rule per pair of kinds makes 81 rules
for `===`; it found 76, and "number `===` number" wasn't one of them.

### Rung 1, kept: "any kind" placeholders (28.4%)

Rules may say "any kind" (a type variable): "`===` compares any two
values". The 527 rules shrink to 44, and approvals nearly triple.

Still rejects: `({x: 0}).x`. It knows this is an object with `x`, but not
what `x` holds, so not what reading it gives.

### Rung 2, kept: knowing what's inside (32.3%)

"Object with x" becomes "object whose x is a number". "Function" becomes
"function from number to string". "Array" becomes "array of strings".

Now it can also check: `({x: 1}).x + 1`, `[1, 1][0] + 1`.

Still rejects: `(x) => 0`. It has no rule for a parameter yet.

### Rung 3, kept, the biggest jump: variables inside code (55.7%)

Rules for things that name a value: function parameters, `let`, and the
`e` in `catch (e)`. Something thrown could be anything, so it learns that
`e` is "unknown".

Now it can also check: `((x) => x + 1)(1)`,
`try { throw 1 } catch (e) { typeof e }`.

Still rejects: `let id = (x) => x; id(1); id("a")`. `id` is used once with
a number and once with a string. Rungs 4 and 5 fix this together.

### Rung 4, kept: one function, many types (56.0%)

A value bound by `let` may be used at different types each time, if it is
a plain value like a function (generic `let`). It approved 76 programs
nothing else could.

Still rejects: `(x) => (y) => 0`, a function that makes a function. Its
rules for functions say what they return one kind at a time: one rule for
"returns a number", one for "returns a string", one for "returns
true/false/null". None says "returns a function".

### Rung 5, kept: tracking `return` (64.2%)

A `return` sends a value out of the function it's in. So the rules have to
know what the function is expected to give back.

Now it can also check: `((x) => { return x + 1 })(1)`, and
`let id = (x) => x; id(1); id("a")`. That one needed both rungs 4 and 5.
Until `return` is tracked, a function's body could hand back something
other than its last value. So the rules can't say "the identity gives back
whatever it gets", only "number to number", "string to string", and so on,
separately. Rung 5 replaces those three rules with one, "returns whatever
its body gives back", and that also covers `(x) => (y) => 0`.

Still rejects: `[0, ""]`. An array of numbers, or of strings, it can
describe; one that holds both, it can't.

> **Tried and dropped:** "a number is also an ok string" style rules
> (subtyping). Nothing in this language works that way.

### Rung 6, kept: "this or that" types (70.6%)

When the two sides of `c ? a : b` differ, the result is "number or string"
(a union type).

Now it can also check: `typeof (true ? 1 : "a")`, `[0, ""]`.

Still rejects: `-(typeof 0 === "number" ? 0 : "")`. The `""` can never be
the answer, since `0` is a number. But the rules see "number or string",
and `-` needs a number.

### Rung 7, kept: knowing what a `typeof` test tells you (70.9%)

Inside `if (typeof x === "number")`, `x` is a number, even if it could
otherwise be a string (narrowing).

Now it can also check: `let x = true ? 1 : "a"; typeof x === "number" ? -x : x[0]`,
and `-(typeof 0 === "number" ? 0 : "")`: a branch the test rules out
doesn't count.

Still rejects: `function f(x) { return f }`, a function that returns
itself. Its type would be "a function returning a function returning a
function...", forever, and the rules can't write that down.

> **Tried and dropped:** subtyping again.

### Cleanup: could any ability go?

Finally it tries removing each ability it kept, in case a later one made
an earlier one unnecessary. Every removal approved fewer programs, or
needed more rules. So all seven stay.

## What it never did

At every one of the 17 tries, including those it dropped, it approved no
crashing program. These two were rejected every time:

| Program | What happens |
|---|---|
| `1 + "a"` | crashes: can't add a number and a string |
| `({x: 1}).y` | crashes: the object has no `y` |

The final rules were checked on 99,950 programs, 61,159 of them safe. They
approved 42,751 of the safe ones, and not one that crashes.

## Still out of reach

`(true ? 1 : "a") + 1` is rejected on purpose. It happens to work, but the
rules can't know the condition is `true`. Had it been `false`, it would
add a string to a number and crash. A checker has to be careful like this.

## Where this came from

One run of `cargo run --release --example climb_walkthrough`, which took
163 minutes, recorded in [ITERATIONS.md](ITERATIONS.md) (iterations 13 and
14). The programs each rung still rejects are the smallest safe ones it
rejects, from every program of up to five pieces. The
percentages are shares of safe programs: every small program, 20,000
random ones, and the programs each try wrote, kept so that later tries are
judged on them too.
