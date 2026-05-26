# Importing `.pyi` stubs: mapping Python's type system onto inty

> Status: design note. No code yet. This document classifies every major
> Python typing construct by **how hard it is to bring into inty's type
> system when reading a `.pyi` stub** (typeshed, PEP 561 `py.typed`
> packages, or hand-written stubs).
>
> Companion to the import-resolution design (see the module-resolution
> notes). Resolution answers *"which file does `import a.b.c` point at?"*.
> This document answers *"once we've found a `.pyi`, what of it can we
> actually represent?"*.

## 1. Why this is the crux

inty's whole proposition is **full inference with no `any`** (README §"Strict
by Design"). It can already *follow* imports — the module machinery in
`crates/inty/src/modules.rs` (cycle detection, export tables, `Type::Module`)
is language-agnostic and reusable. The hard part is not plumbing; it is that
the community's type information for the stdlib and third-party packages lives
in `.pyi` files written against a **nominal, class-and-subtyping-based,
gradually-typed** type system, while inty is **structural, row-polymorphic,
Rank-1, with no subtyping, no `any`, and a closed set of type classes**.

So the question "support imports" reduces to a translation problem with three
possible outcomes per construct:

- **Bucket A — Direct translation.** The Python concept is the same concept
  inty already has, written differently. Translation is a spelling change.
- **Bucket B — Mechanical transformation (lossy but faithful enough).** The
  concept has no 1:1 equivalent, but a deterministic rewrite (flatten,
  erase, desugar) lands it in inty's world with acceptable, well-understood
  loss of precision.
- **Bucket C — Hard gap.** The concept depends on a feature inty
  deliberately does not have (nominal identity, `any`, intersections,
  higher-rank/higher-kinded types, user-defined type classes). No faithful
  translation exists; these require either a type-system extension or the
  graceful-degradation fallback (bind the symbol opaquely so the importer
  never errors — see §6).

## 2. The two type systems at a glance

inty's relevant capabilities (from `crates/inty/src/types/ty.rs`, the type
parser `crates/inty/src/infer/type_parser.rs`, and the README):

| inty has | inty does **not** have |
| --- | --- |
| Primitives `Number, String, Boolean, Null, Undefined, Regex` | An `any`/`unknown` type (rejected by the type parser) |
| `Array<T>` (`T[]`), `Map<V>` (string-keyed), `Promise<T>` | Distinct numeric types (one `Number` = f64) |
| Closed unions `A \| B`, literal types `"a" \| 42 \| true` | Intersection types (`A & B` is rejected) |
| Structural rows `{x: T, y?: U}`, open/closed, presence vars | Width **subtyping** (only unification + row polymorphism) |
| Rank-1 parametric polymorphism `<T>(T) => T` | Rank-2+ / higher-kinded types (Rank-1 restriction enforced) |
| Function types with optional trailing params `(a, b?) => R` | Variadic generics, `*args`/`**kwargs` in type position |
| Generic structural type aliases `type Pair<T> = {...}` | **Nominal** user types (`Type::Named` is recursion-only, not user-declarable) |
| Equi-recursive `this` rows (method chaining / `return self`) | Inheritance, `super`, `static` members |
| Closed type classes `Plus`, `Indexable` (inferred, not declared) | User-defined type classes / instances (operator dunders) |
| Nominal identity for **modules** only (by source path) | `isinstance`-style nominal class distinctions |

The single most important consequence: **inty has no nominal typing for
values and no subtyping.** Python's type system is built on both. That one
fact is the source of most Bucket C entries.

## 3. Bucket A — Direct translations (spelling change)

These map cleanly. A `.pyi` reader emits the inty annotation on the right.

| Python | inty | Notes |
| --- | --- | --- |
| `str` | `String` | |
| `bool` | `Boolean` | |
| `None` | `Null` | Python `None` is inty `Null`, **not** `Undefined`. See the `Optional` caveat in §4. |
| `Optional[T]` / `T \| None` | `T \| Null` | Use the explicit `\| Null` form, **not** the `T?` sugar (which adds `Undefined`). |
| `Union[A, B, C]` | `A \| B \| C` | inty normalises/dedups unions; semantically equivalent. |
| `Literal["a", "b"]` | `"a" \| "b"` | First-class literal-union support, including narrowing/exhaustiveness. |
| `Literal[1, 2]`, `Literal[True]` | `1 \| 2`, `true` | |
| `list[T]` / `List[T]` / `Sequence[T]`* | `T[]` | *`Sequence`/`Iterable` only insofar as the stub exposes list-like reads; see §5. |
| `dict[str, V]` / `Mapping[str, V]` | `Map<V>` | **String keys only** — `Map` is string-keyed. Non-`str` keys → Bucket C. |
| `Callable[[A, B], R]` | `(A, B) => R` | |
| `def f(x: A, y: B) -> R` | `(A, B) => R` / `function f(x: A, y: B) => R` | |
| `def f(x: A, y: B = ...) -> R` | `(x: A, y?: B) => R` | Default/optional **trailing** params → presence-polymorphic params (`FuncParam::optional`). |
| `TypedDict` (total) | `{k: T, ...}` (closed row) | TypedDicts are structural in Python too — excellent fit. |
| `TypedDict` (`total=False` / `NotRequired`) | `{k?: T, ...}` | Optional fields → presence variables. |
| `Protocol` (methods + attrs) | row of fields, open or closed | The standout fit: structural interface ↦ structural row. See §5 for variance/nominal caveats. |
| `TypeVar('T')` used Rank-1 | `<T>` quantifier | `def f[T](x: T) -> T` ↦ `<T>(T) => T`. |
| `type X = ...` / `TypeAlias` | `type X<...> = ...` | inty aliases are structural & generic — same semantics. |
| Recursive type alias / forward ref `"Node"` | recursive row (`Type::Named` / equi-recursive) | inty represents μ-types natively. |
| `Final[T]`, `ClassVar[T]`, `Annotated[T, ...]`, `InitVar[T]` | `T` (erase the wrapper) | Pure metadata for inty's purposes. |

## 4. Bucket B — Mechanical transformation (lossy, but deterministic)

No 1:1 equivalent, but a fixed rewrite produces a usable inty type. Each entry
notes **the rewrite** and **what precision is lost**.

### 4.1 Classes → callable rows (constructor) + instance rows

inty already lowers JS `class` to a **factory function returning a closed row**
of methods + fields, and models constructors-with-statics as **callable rows**
(README §"Callable Rows"; `core.d.js` `String`). The same encoding carries a
`.pyi` class:

- **Instance type** = closed row of the instance attributes + methods
  (`@property` → plain field, exactly as JS getters lower).
- **Class object** (`type[Foo]`, the thing you call and that holds
  `@classmethod`/`@staticmethod`) = a **callable row**: a keyless call
  signature `(args) => InstanceRow` plus the class/static methods as named
  fields.

```python
# stub
class Counter:
    def __init__(self, start: int) -> None: ...
    def inc(self) -> int: ...
    @classmethod
    def zero(cls) -> "Counter": ...
```
```javascript
// emitted inty stub
/** const Counter: {
      (Number) => {inc: () => Number},   // call = __init__ → instance row
      zero: () => {inc: () => Number}     // classmethod as static field
    } */
```

- **`Self` / `def copy(self) -> Self`** rides inty's equi-recursive `this`
  rows (the method-chaining mechanism) — `return self` already types in inty.
- **Lost:** nominal identity (see §5.1), `__slots__` exactness nuances, and
  the distinction between the class object and `type[Foo]` in generic
  position.

### 4.2 Inheritance → flatten the MRO

inty has no `extends`. The rewrite **inlines** every inherited attribute and
method into the subclass's instance row and class-object row, walking the MRO.

- **Works because** rows are structural: a flattened `Dog` row that contains
  all of `Animal`'s fields *is* usable everywhere `Animal`'s fields are read.
- **Lost:** `super()` calls (irrelevant to a stub's surface types);
  `isinstance(x, Animal)` as a **nominal** test (Bucket C, §5.1); and the
  `object` base balloons every row with `__eq__`, `__hash__`, … — the reader
  should **prune** universal `object` members to keep rows readable.

### 4.3 Variance → erase

`TypeVar('T', covariant=True)` / `contravariant=True` annotations are dropped.
inty has no subtyping, so declared variance has no target concept. In practice
benign: row polymorphism + unification already give inty its flexibility. Some
assignments Python would accept/reject on variance grounds will differ, but
inside a stub boundary this rarely surfaces.

### 4.4 Constrained `TypeVar` → union; bounded `TypeVar` → erase or open row

- `TypeVar('A', int, str)` (value-constrained) → approximate the parameter as
  `Number | String`. Lossy: the constraint that *one consistent* member is
  chosen per call isn't enforced, but the surface is right.
- `TypeVar('T', bound=Base)` (upper-bounded) → no upper-bound mechanism (no
  subtyping). If `Base` is protocol-like, emit an **open row** carrying
  `Base`'s members (`{...Base | ρ}`); otherwise erase the bound to a plain
  `<T>`. Lost: the "must be a subtype of `Base`" guarantee.

### 4.5 `NewType('UserId', int)` → base type

Erase to `Number`. inty has no nominal types, so the distinct-from-`int`
guarantee is lost. Low severity in practice.

### 4.6 Enums → literal union (+ synthesized accessors)

`class Color(Enum): RED = 1; GREEN = 2` → values map to `1 | 2`; if member
access is needed, emit a row `{RED: 1, GREEN: 2}` for the class object. Lost:
the nominal `Color` type and `.name`/`.value`/iteration semantics beyond the
literal values.

### 4.7 Homogeneous/variadic tuple → array

`tuple[T, ...]` → `T[]`. (Fixed heterogeneous tuples are Bucket C, §5.4.)

### 4.8 `@property`/`@cached_property` → field

Direct (matches JS getter lowering). Setters are accepted but don't add the
field independently (same rule as inty's JS `set`).

## 5. Bucket C — Hard gaps (need more than a type translation)

These depend on features inty intentionally lacks. For each: why it can't be
translated, and the **best available mitigation** short of a type-system
change.

### 5.1 Nominal identity / `isinstance` distinctions — *the big one*

Two Python classes with identical structure (`class Dog: name: str` vs
`class Cat: name: str`) are **distinct types**; inty unifies them structurally,
so it cannot tell them apart, and `isinstance`-based narrowing against a class
has no target. `NewType`, `Enum`, distinct exception classes, and "two empty
marker classes" all collapse.

- **Mitigation:** synthesize a **phantom discriminant field** per class
  (`{__class__: "Dog", name: String}`) so that classes participate in inty's
  *discriminated-union narrowing* (README §"Sum Types"). This recovers the
  common case — distinguishing members of a union by tag — but is a
  convention, not true nominality, and balloons every row with a tag field.
- **Otherwise:** a genuine fix is a nominal-type feature (inty has the
  machinery shape for it — `Type::Module` is already nominal-by-name, and
  `Type::Named` exists for recursion — but exposing user-declarable nominal
  types is a type-system decision, not a stub-reader trick).

### 5.2 `Any` — pervasive, and fundamentally unrepresentable

typeshed is saturated with `Any` (`**kwargs: Any`, untyped returns, escape
hatches). inty's type parser **rejects `any` outright**. `Any` is gradual:
it simultaneously accepts every type *and* produces every type, unsoundly.
inty has no such element.

- **Best approximations, all imperfect:**
  - *Input position* (`def f(x: Any)`) → a fresh quantified `<T>` per binding:
    "accepts anything." Reasonable.
  - *Output/field position* (`-> Any`, `attr: Any`) → a fresh type variable
    is wrong: it would either over-constrain (if shared) or silently unify
    with the first use (if per-use). There is no sound choice.
- **Mitigation:** when a stub symbol's type is `Any`-dominated, **bind it
  opaquely** (the graceful-degradation contract, §6) rather than forcing a
  variable. `Any` is the main reason whole-stub faithful translation is
  impossible and the opaque fallback is mandatory.

### 5.3 `@overload` — intersection types

An overload set is an intersection of function types
(`(int)->int ∧ (str)->str`). inty has **no intersection type** (`A & B` is
rejected) and no overload resolution.

- **Mitigation:** collapse to a single principal signature — either union the
  corresponding parameters/returns (`(Number | String) => Number | String`,
  lossy and over-permissive) or pick the first/widest overload. Neither
  preserves the input→output correlation. True support needs intersections.

### 5.4 Fixed heterogeneous tuples & variadic generics

`tuple[int, str]`, `TypeVarTuple`, `Unpack`, `Concatenate`, `ParamSpec` have
no analog: inty has no fixed-arity heterogeneous product type and is Rank-1
with no variadic generics.

- **Mitigation:** `tuple[A, B]` → a closed row `{"0": A, "1": B}` *only if*
  the stub uses it by-field; indexed access `t[0]` won't type (the
  `Indexable` class is closed and demands a uniform element type). `ParamSpec`
  / `TypeVarTuple` → fall back to opaque or a non-generic approximation.

### 5.5 User-defined operator/iteration protocols (`__add__`, `__getitem__`, `__iter__`, `__enter__`, …)

inty's type classes (`Plus`, `Indexable`) are a **closed, built-in set with no
user-declarable instances** (`crates/inty/src/classes/instances.rs`). A `.pyi`
class that defines `__add__` cannot be registered as a `Plus` instance;
`__getitem__` can't make it `Indexable`; `__iter__` can't make it iterable in a
`for` loop.

- **Mitigation:** expose the dunder as an ordinary method field
  (`{__add__: (Other) => R}`) so explicit calls type, but `x + y`,
  `x[i]`, and `for v in x` over a user type won't dispatch. A real fix is
  opening the type-class system to user instances — a significant extension.

### 5.6 Higher-rank / higher-kinded / `Callable[..., R]`

Rank-2 callables (a parameter that is itself polymorphic), higher-kinded
generics (generic over a type constructor), and `Callable[..., R]`
(arbitrary-arity) exceed inty's Rank-1 restriction (enforced;
`TypeError::Rank1Restriction`).

- **Mitigation:** monomorphise at a chosen instantiation, or opaque fallback.

### 5.7 Dynamic attribute access (`__getattr__`/`__setattr__`)

A class with `__getattr__` exposes statically-unknown attributes. inty's
closest tool is an **open row** or `Map<V>`, both of which lose per-attribute
typing.

- **Mitigation:** open row when the value type is uniform; otherwise opaque.

### 5.8 Numeric tower & `bytes`

One inty `Number` (f64) absorbs `int`/`float` (collapse — usually fine), but
`complex`, `Decimal`, `Fraction` have no faithful home, and **`bytes`/
`bytearray`/`memoryview`** have no analog. `int`-only operations (bitwise,
arbitrary precision, use as `dict`/sequence index) silently behave as `Number`.

- **Mitigation:** map `int`/`float` → `Number`; `bytes`/`complex`/etc. →
  opaque (or a documented `Map`/`Array<Number>` approximation for `bytes`).

### 5.9 Nominal exception hierarchies & `try/except`

`except ValueError` is a nominal subclass test. With structural-only types and
no inheritance identity, matching an exception by class isn't representable
beyond the flattened-structure approximation (§4.2) and loses subclass
matching.

## 6. Cross-cutting: the degradation contract

Buckets A and B let a stub reader translate the bulk of well-typed,
structural Python surface. Bucket C and the `Any` problem guarantee that **some
symbols in almost every real stub cannot be faithfully represented.** The
design must therefore never turn an unrepresentable stub symbol into a hard
error for the *importer*. Instead:

- A symbol whose type lands in Bucket C (or is `Any`-dominated) is bound as an
  **opaque module export**: it resolves, member access yields fresh type
  variables, and no error is raised at the import site. Precision is reduced
  only for values flowing across that one binding.
- This is the same graceful-degradation floor described in the import-
  resolution design. It keeps "point inty at a uv/venv project" from dead-
  ending on `numpy`, `Any`, or an overloaded stdlib function.

Coverage then improves **monotonically**: as more constructs move from "opaque"
to a Bucket A/B translation, precision rises with no change to the user's
workflow and no re-architecture.

## 7. Cross-cutting: conditional & versioned stubs (resolution, not typing)

typeshed stubs branch on `sys.version_info`/`sys.platform` and use
`@type_check_only`, `if TYPE_CHECKING:`, and a `VERSIONS` file gating which
modules exist per Python version. These are **resolution-time** concerns, not
type-mapping ones: the reader needs a configured target Python version to pick
the right branch (exactly as `ty`/pyright do). Listed here so it isn't
mistaken for a type-system gap — it belongs in the module-resolver design.

## 8. Recommendation

1. **Build the `.pyi` reader to cover Buckets A and B**, in roughly that
   priority: primitives/unions/optionals/literals → `Protocol`s and
   `TypedDict`s (inty's best fits) → functions/callables → classes-as-callable-
   rows with **MRO flattening** and **variance/`Final`/`Annotated` erasure**.
2. **Treat every Bucket C construct and every `Any`-dominated symbol as an
   opaque export** (§6) — never an importer-facing error.
3. **Adopt the phantom-discriminant convention (§5.1)** as the pragmatic
   stand-in for nominal identity, and revisit a real nominal-type feature only
   if the loss proves painful in practice.
4. **Defer, as genuine type-system extensions** (not stub-reader work):
   user-defined type classes (§5.5), intersection/overload support (§5.3),
   and nominal value types (§5.1). Each is a deliberate addition to inty's
   core, weighed against its "small, strict, structural" philosophy.

The headline: **Protocols, TypedDicts, unions, literals, generics (Rank-1),
and functions translate cleanly; classes and inheritance translate
mechanically with known loss; nominal identity, `Any`, overloads, and
user-defined operator protocols are the irreducible gaps that the opaque
fallback exists to absorb.**
