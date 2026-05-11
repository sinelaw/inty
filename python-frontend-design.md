# Python-syntax frontend for inty — design exploration

**Verdict.** "Typed-Python lite" is feasible and showcases the new presence
polymorphism nicely. **Real Python is not** — it needs at least three
orthogonal type-system extensions (dunder dispatch, inheritance/subtyping,
heterogeneous `**kwargs`). Pursue only if the goal is *Python-flavored
inty*, not *check-my-existing-Python*.

## Lowering strategy

Mapping against the existing AST (`parser/ast.rs`):

| Construct | Lowering | Status |
|---|---|---|
| literals/ident/arith/cmp | direct (`True/False/None`→`true/false/null`) | clean |
| `def f(...)` | `FunctionDecl` with one synthetic `args` param | resolver |
| `lambda`, `=`, `if/while/return/break/continue` | direct | clean |
| `for x in xs` | `ForOf` | needs iter stdlib |
| `try/except E as e`, `with` | `Try`+`Throw`/`finally` | flat only |
| `class C` (no inherit, no dunder) | record + factory function | desugar |
| comprehensions, f-strings | `.map().filter()`, `TemplateLiteral` | clean |
| `match Tag(a,b)` | `Switch` over tagged unions | structural only |
| `@decorator`, `*args` | `f=d(f)`, `Array` spread | clean |
| `**kwargs`, `yield`, async iter | — | **blocked** (see below) |

No new AST nodes are required for v0 if classes-without-inheritance desugar
to records.

## kwargs lowering (the central trick)

`def f(x, y=1, *, z=2): body` naïvely becomes
`function f(args /*: {x:T, y?:U, z?:V} */) { var x=args.x; var y=args.y;
var z=args.z; /*body*/ }`. This **breaks the instant the body reads `y`**:
per `optional_field_read_inside_body_forces_present`, reading `args.y`
pins its presence variable to `Pre`. Presence polymorphism is *type-level*
optionality, not value-level "absent means default."

Fix: **caller-side default injection**. Lower `f(1)` to
`f({x:1,y:1,z:2})`; the body always sees presence `Pre`. External callers
(other modules, JS interop) still see the optional row and benefit. Works
on 8/10 realistic signatures (`requests.get(url, params=…, timeout=…)`,
dataclass ctors, `print(*, sep, end)`). Breaks on `**kwargs` forwarding
(`def w(**kw): inner(**kw)`) — wrapper doesn't know `inner`'s signature.

## Name-resolution pass

`f(1,2)` needs `f`'s parameter order to rewrite into `f({x:1,y:2})`.
Aliasing (`g=f`) and imports make this a flow problem.

Shape: `inty-py` produces unresolved AST plus a per-module `DefTable:
name → ParamSpec { positional, defaults, has_star, has_starstar }`. A
resolver walks bindings, treats unannotated `f=g` as alias when `g ∈
DefTable`, and rewrites every `Call`. Cross-module: piggyback `modules.rs`
import resolution. Higher-order (`map(f, xs)`) **cannot** be rewritten;
restriction: a kwargs-def with defaults can't be passed first-class.

Cost: ~800–1200 LOC, similar to a mini module pass.

`*args` spreads `Array<T>`. `**kwargs` would spread `Map<T>` but `Map<T>`
is homogeneous, so **real-Python `**kw` is a soundness blocker**.

## Fits today

`def`+kwargs+defaults (with rewriting); tagged-union `match` over
dataclasses with a discriminant; f-strings, comprehensions, `for/while/if`,
flat `except`, decorators-as-wrappers.

## Won't work without new type-system work

1. **Dunder overloading.** `a+b → a.__add__(b)` needs user-defined `Plus`
   instances; today they're hard-wired in `classes/`. Blocker:
   `Decimal+Decimal`.
2. **Inheritance / exception hierarchies.** `except Exception:` catching
   `ValueError` needs nominal subtyping; inty omits `extends`. Blocker:
   `except (IOError, OSError)`.
3. **Heterogeneous `**kwargs`.** Mixed-type kw forwarding can't be
   `Map<T>`. Needs row-as-first-class-value. Blocker: `functools.partial`.
4. **Truthiness on containers.** `if xs:` on a list. Blocker: every
   empty-is-false idiom.
5. **Iterator/generator protocol.** `yield`/`__iter__` needs an effect
   type. Blocker: `yield from`.
6. **Protocols / multiple inheritance.** Structural subtyping at the
   class boundary.

## Recommended phasing

- **v0 (~2 weeks, `--frontend=py`):** `inty-py` crate, indent lexer, top-
  level `def`/class-as-record/`if`/`return`/literals/comprehensions/
  f-strings. Resolver with caller-side default injection. Goal: a 200-line
  hand-written demo, not real Python.
- **v1:** decorators-as-wrappers, `match`→tagged-union switch, flat
  `try/except`, `with` desugar. Still no inheritance, no dunder.
- **Hard stop before v2.** v2 means items 1–3 above; each is a real
  type-system project. Python becomes the tail wagging the dog.

## Honest take

Presence polymorphism makes kwargs+defaults sound and elegant. Everything
else fights inty's design. Build a demo, not a Django checker.


