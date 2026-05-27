# Curated Python builtins prelude for inty.
#
# Signatures are *inspired by* typeshed but written against inty's native
# primitives: `int`/`float` -> Number, `str` -> String, `bool` -> Boolean,
# `list[T]` -> Array<T>. Builtins inty cannot model precisely — variadics
# (`print`, `min`), heavy overloads, gradual `Any` — are exposed opaquely
# (a `forall a. a` binding) so calls type-check without false positives,
# matching the graceful-degradation contract for unmodellable imports.
#
# This file is loaded into every Python program's value namespace. It is
# NOT typeshed; see issue #55.

T = TypeVar("T")
U = TypeVar("U")

# --- precisely-modellable free functions ---
# (`object` parameters lower to a fresh variable, so these accept any
# argument while still constraining their result type.)

def len(x: object) -> int: ...
def abs(x: float) -> float: ...
def round(x: float) -> int: ...
def str(x: object) -> str: ...
def repr(x: object) -> str: ...
def int(x: object) -> int: ...
def float(x: object) -> float: ...
def bool(x: object) -> bool: ...
def ord(c: str) -> int: ...
def chr(i: int) -> str: ...
def hex(i: int) -> str: ...
def hash(x: object) -> int: ...
def input(prompt: str = ...) -> str: ...
def range(start: int, stop: int = ..., step: int = ...) -> list[int]: ...
def open(path: str) -> object: ...

# --- generic sequence builtins ---
# Modelled precisely with type variables, for the forms with a fixed
# arity. The input is `list[T]` (inty's array); these consume the result
# by iterating, so returning a list rather than a lazy iterator is
# faithful. `filter`'s predicate is typed `object` (not a strict
# `Callable`) so the `filter(None, xs)` idiom still type-checks while the
# result keeps the element type.

def sorted(xs: list[T]) -> list[T]: ...
def reversed(xs: list[T]) -> list[T]: ...
def any(xs: list[T]) -> bool: ...
def all(xs: list[T]) -> bool: ...
def sum(xs: list[float], start: float = ...) -> float: ...
def filter(f: object, xs: list[T]) -> list[T]: ...

# --- variadic / heavily-overloaded builtins ---
# inty has no variadic arity or tuple type, so these are exposed opaquely
# (accept any call, produce a fresh result) rather than wrongly
# constrained: `map` and `min`/`max` are variadic (`map(f, *iters)`,
# `min(a, b, …)`); `zip`/`enumerate` yield tuples; the rest are
# iterator-protocol / constructors.

print: object
map: object
min: object
max: object
enumerate: object
zip: object
iter: object
next: object
list: object
dict: object
set: object
tuple: object
type: object
getattr: object
setattr: object
hasattr: object
issubclass: object
format: object
# `isinstance` is provided by `builtins::initial_env` with a precise
# signature and flow-sensitive narrowing (issue #40); not redefined here.

# --- module-level magic globals ---
# Present in every module's namespace at runtime.
__name__: str
__file__: str
__doc__: str

# --- builtin exception classes ---
# Exposed opaquely: they're used both as constructors (`raise Foo("…")`)
# and as `except` targets, and inty doesn't model an exception hierarchy.
# Opaque values accept either use without false positives.
BaseException: object
Exception: object
ValueError: object
TypeError: object
KeyError: object
IndexError: object
AttributeError: object
RuntimeError: object
NotImplementedError: object
StopIteration: object
StopAsyncIteration: object
FileNotFoundError: object
FileExistsError: object
IsADirectoryError: object
NotADirectoryError: object
PermissionError: object
OSError: object
IOError: object
ImportError: object
ModuleNotFoundError: object
NameError: object
ZeroDivisionError: object
ArithmeticError: object
OverflowError: object
AssertionError: object
KeyboardInterrupt: object
SystemExit: object
LookupError: object
UnicodeDecodeError: object
UnicodeEncodeError: object
TimeoutError: object
ConnectionError: object
RecursionError: object
Warning: object
DeprecationWarning: object
UserWarning: object
