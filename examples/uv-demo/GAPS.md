# Gaps found running `inty` on a real uv project

This is the companion write-up to the `authkit` demo. The project is a
small but realistic JWT auth toolkit (pydantic v2 models + validators +
enums, PyJWT, an argparse CLI, an exception hierarchy). It is **clean
under the real toolchain** — `ruff`, `ty`, and `pytest` all pass
(`make check`). We then pointed `inty` at the same sources the way `ty`
is run (`make inty` → `scripts/inty-check.sh`) and recorded where it
falls short.

The short version: on idiomatic, type-clean modern Python, **inty never
reaches the type-checking stage** — every file is rejected at parse /
import-resolution time. The type checker itself is fine (see Part C); the
gaps are in the language subset and the project/IO infrastructure around
it.

How `inty` was run, vs. how `ty` is run:

| | `ty` | `inty` |
|---|---|---|
| Invocation | `ty check` (whole project) | one file per process; we hand-rolled a `find ... | xargs` loop |
| Project discovery | reads `pyproject.toml`, finds the package root | none — we set `INTY_PYTHONPATH` by hand |
| Venv / third-party | auto-discovers `.venv` site-packages | none — we appended site-packages to `INTY_PYTHONPATH` by hand |
| Result | `All checks passed!` | 7/7 files failed before type-checking |

---

## Part A — Infra / CLI / polish gaps

### A1. No project / directory / venv mode

`ty check` discovers the project from `pyproject.toml`, finds the package
root and the `.venv`, and checks every module. `inty` takes **one file
per invocation** (`inty <file.py>`), has no directory walk, no
`pyproject.toml` awareness, and no venv discovery. Running it "like `ty`"
meant writing `scripts/inty-check.sh`: a `find` loop that checks files
one at a time and reconstructs the import search path by hand via
`INTY_PYTHONPATH=src:<site-packages>`.

*Suggested:* an `inty check [DIR]` subcommand that accepts a directory /
globs, reads `pyproject.toml` (at minimum `requires-python` and the
package root), auto-detects `.venv`, and prints one aggregate summary.

### A2. No opaque boundary for third-party packages — the degradation contract is unimplemented for `.py`

This is the headline infra gap. `docs/pyi-import-mapping.md` §6 promises a
"graceful-degradation floor" so that "point inty at a uv/venv project"
won't dead-end on third-party code. In practice it does:

```
$ inty -  <<< 'from pydantic import BaseModel'
Error: Unsupported construct: 'del' is not supported in the Python subset
  ╭─[ .../site-packages/pydantic/__init__.py:9:1 ]
9 │ del _ensure_pydantic_core_version
```

`inty` resolved `pydantic` to its real `__init__.py` and tried to
**type-infer the library's own implementation**, choking on the first
construct outside its subset (`del`). `import jwt` dies the same way
inside PyJWT's source. There is no "this is an installed dependency,
treat it as an opaque/declared interface" boundary:

- The degradation-to-opaque path exists only for `.pyi` stubs. A modern
  PEP 561 package (pydantic, pyjwt both ship `py.typed`, **zero `.pyi`**)
  has only inline-typed `.py`, which inty reads as checkable source.
- A genuinely unresolvable module is a hard error
  (`cannot resolve import "..."`), not an opaque fallback either.

*Suggested:* treat anything under a site-packages / `py.typed` root as a
**declaration source** — read only signatures/annotations (as the `.pyi`
reader already does), never infer the body — and fall back to an opaque
binding when a symbol can't be modelled. That is exactly the contract the
design doc already specifies; it just isn't wired for `.py` inputs.

> **Update — partially implemented (ty's flow, layer 0).** The import
> resolver now routes any `.py` under a PEP 561 `py.typed` package through
> the same declaration reader used for `.pyi` (`read_as_declarations` in
> `frontends/python/modules.rs`), and `from __future__ import …` is a
> recognized no-op. After this, `from pydantic import BaseModel` and
> `import jwt` **resolve** instead of dying on pydantic's `del`, and the
> import *surface* is real — `jwt.no_such_function` and `from pydantic
> import NoSuchName` are correctly flagged as missing exports. This is ty's
> **graceful-degradation floor**, and it is necessary, but it is **not
> sufficient** to get ty-level information. Three layers remain:
>
> 1. **Signature precision.** `jwt.encode(...) + 1` still does *not* error,
>    because `encode` (a module-level-assigned bound method) degrades to
>    *opaque* rather than `-> str`. The heuristic reader was tuned for
>    `.pyi` (bodies are `...`); on real `.py` it loses many signatures. ty
>    keeps them because it parses the whole file and consumes every
>    annotation. A faithful version needs declaration-lowering over inty's
>    *real* Python AST, not the line-skipping stub reader.
> 2. **Inheritance.** pydantic is still unusable: `class User(BaseModel)`
>    hits inty's `base classes / inheritance are not supported` rejection
>    (Part B) — a frontend gap independent of imports. Resolving the
>    `BaseModel` *name* doesn't help if you can't subclass it.
> 3. **PEP 681 `@dataclass_transform`.** Even with 1 and 2, `a.balance:
>    int` requires synthesizing `Model.__init__(...)` from the annotated
>    fields. ty special-cases the `dataclass_transform` marker that
>    pydantic's metaclass carries; inty has no analog. This is the specific
>    mechanism behind ty's precise `Account(owner: str, balance: int)`.

### A3. `from __future__ import annotations` is unresolvable

Every file in this project (and most modern Python) starts with it.
`inty` reported `cannot resolve import "__future__"`. **Fixed:**
`__future__` is now a recognized no-op pseudo-module (see A2's update).

### A4. The first parse-level error aborts the whole file

`inty` recovers from multiple *type* errors (a two-bad-line file reports
two), but a single *unsupported-construct* error stops parsing the file —
so each fix-and-rerun reveals only the next one. `ty` lists all
diagnostics at once (`Found 6 diagnostics`). For a subset this small, the
fix/re-run cycle is the dominant cost of trying inty on real code.

### A5. Misleading diagnostic on keyword-only `*`

```python
def issue(self, user, *, ttl_seconds=None) -> str:
```
is reported as `Unsupported construct: *args / **kwargs are not
supported`, pointing at the bare `*`. It is the PEP 3102 keyword-only
separator, not `*args`. The message should name the real construct.

### A6. No machine-readable output / error codes / aggregate summary

`ty` emits stable codes (`error[invalid-argument-type]`,
`error[missing-argument]`) and a `Found N diagnostics` tally suitable for
CI. `inty` prints prose diagnostics and a per-file `All checks passed: …`
line; there is no `--output-format`, no error codes, and (because there's
no project mode) no aggregate count across files.

---

## Part B — Language-subset gaps (the actual rejections)

Each row is a construct this project uses that `inty`'s Python frontend
rejects. The first four block essentially every real module.

| Construct | Used by | inty result |
|---|---|---|
| **Base classes / inheritance** | `class User(BaseModel)`, `class Role(StrEnum)`, `class AuthError(Exception)` | `base classes / inheritance are not supported` |
| **List / dict / set comprehensions** | `[Role(r) for r in args.roles]`, `[r.value for r in roles]` | `list comprehensions are not supported` (dict/set: "must be string or number literals") |
| **Generator expressions** | `", ".join(r.value for r in token.roles)` | `Unexpected token: found 'For'` |
| **Keyword-only params (`*` sep)** | `def issue(self, user, *, ttl_seconds=None)` | misreported as `*args / **kwargs` (A5) |
| **`*args` / `**kwargs`** | common library surface | `*args / **kwargs are not supported` |
| **Annotated attribute assignment** | `self._users: dict[str, User] = {}` | `Invalid assignment target` (`self.x = e` works; `self.x: T = e` doesn't) |
| **`del`** | (pydantic internals) | `'del' is not supported` |
| **`async def`** | common in real services | `'async' is not supported` |
| **`from __future__`** | every file | `cannot resolve import` (A3) |

The single highest-leverage item is **inheritance**. inty's stance
(instances are structural; compose explicitly) is defensible for plain
data classes, but `pydantic.BaseModel`, `enum.Enum`/`StrEnum`, and custom
`Exception` subclasses are *not optional* in real Python — they are how
you declare a model, an enum, and an error. Without a story for "subclass
a known base" (even a narrow, special-cased one for `BaseModel` / `Enum` /
`Exception`), no pydantic- or enum-using module can be checked.

### What already works (for contrast)

Not everything idiomatic is rejected — these all type-check cleanly:
method decorators (`@staticmethod`, `@property`), `with`, `try/except`,
`raise ... from`, `lambda`, `global`, nested/closure functions,
`X | None` unions, f-strings, list/dict literals and indexing, `for`
loops, list methods. The subset is real; it's the four big rejections
that put modern projects out of reach.

---

## Part C — The type checker itself is fine

To confirm the gaps are syntactic/infra and not in the inference engine,
here is the auth logic rewritten inside inty's subset (records instead of
pydantic models, explicit loops instead of comprehensions). inty infers
through records, calls, and loops and catches a genuine error:

```python
tok = issue(ada, 3600)            # {sub, roles, ttl: Number}
bad = tok["ttl"] + " seconds"     # Number + String
# → Error: Type mismatch: expected 'Number', found 'String'
```

So Part A and Part B are the whole story: widen the subset (or stub the
common bases) and add a third-party-as-declarations boundary, and inty's
existing checker would have real, idiomatic Python to work on.

---

## How `ty` handles `import pydantic` (the contrast in one place)

`ty` reads pydantic's **inline types** (it ships `py.typed`, no `.pyi`) as
a *declaration boundary* — consuming signatures/annotations only, never
inferring the library body — and falls back to the gradual `Unknown`/`Any`
type for anything it can't model, so an import never hard-errors. It also
implements PEP 681 `@dataclass_transform` (which pydantic's metaclass
carries), so it **synthesizes** `Account.__init__(owner: str, balance:
int)` from the model fields:

```
reveal_type(a.balance)   # int
Account(owner="ada", balance="x")  # error[invalid-argument-type]: Expected `int`
Account(owner="ada")               # error[missing-argument]: required `balance`
```

inty's design doc already describes the equivalent boundary (read stubs as
declarations; opaque-fallback the rest); the gap is that it's implemented
for `.pyi` only, while real packages ship inline-typed `.py`.
