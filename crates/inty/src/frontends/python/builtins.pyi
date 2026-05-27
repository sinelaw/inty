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

# --- variadic / heavily-overloaded builtins ---
# inty has no variadic arity, so these are exposed opaquely (accept any
# call, produce a fresh result) rather than wrongly constrained.

print: object
min: object
max: object
sum: object
sorted: object
reversed: object
enumerate: object
zip: object
map: object
filter: object
any: object
all: object
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
