# Built-in `typing` module stub for inty.
#
# `typing`'s members are *type constructors*, recognised structurally by
# the type-expression parser (`type_expr`): `List[int]` → `int[]`,
# `Optional[T]` → `T | None`, `Dict[str, V]` → `Map<V>`, `Literal[…]`,
# `Callable[…]`, etc. — the same whether written bare (`from typing import
# List`) or qualified (`typing.List`). This stub exists so the *import*
# resolves and the names are bound as values (used opaquely, e.g.
# `T = TypeVar("T")`); the type-level meaning comes from `type_expr`.
#
# Exposed opaquely (`object` → a fresh variable), so any value-level use
# type-checks without imposing a constraint.

Any: object
List: object
Dict: object
Set: object
FrozenSet: object
Tuple: object
Optional: object
Union: object
Callable: object
Type: object
Sequence: object
MutableSequence: object
Iterable: object
Iterator: object
Mapping: object
MutableMapping: object
Literal: object
Final: object
ClassVar: object
Annotated: object
Protocol: object
Generic: object
TypeVar: object
ParamSpec: object
TypeVarTuple: object
TypeAlias: object
NamedTuple: object
TypedDict: object
NewType: object
NoReturn: object
Never: object
Self: object
overload: object
final: object
cast: object
runtime_checkable: object
get_args: object
get_origin: object
get_type_hints: object
TYPE_CHECKING: object
