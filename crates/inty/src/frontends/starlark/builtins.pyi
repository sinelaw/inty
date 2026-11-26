# Starlark builtins that the Python prelude (`python/builtins.pyi`) does
# not provide. `fail` takes any arguments and never returns; `fail(…)` as a
# statement is lowered to a `throw`. `struct(k = v, …)` is lowered to a
# record by the parser; the binding covers any other use of the name.
fail: object
struct: object
dir: object
