# `Literal[...]` constrains a value to a fixed set of strings. The
# alias makes the set reusable; passing a value outside the set is a
# type error — caught here, not as a `ValueError` at runtime.

BumpType = Literal["patch", "minor", "major"]

def next_version(kind: BumpType) -> BumpType:
    return kind

a = next_version("patch")
b = next_version("minor")
c = next_version("major")

# Try this — uncomment to see the alias enforce its set:
# d = next_version("majr")   # error!
