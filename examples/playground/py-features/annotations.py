# Type annotations are enforced as constraints, not discarded. A
# program whose values match its annotations type-checks. Annotations
# inty doesn't model (e.g. `SomeProtocol`) impose no constraint, so they
# never cause a false positive.

def add_one(x: int) -> int:
    return x + 1

def greet(name: str) -> str:
    return "hi " + name

def total(xs: list[int]) -> int:
    s = 0
    for v in xs:
        s = s + v
    return s

count: int = 5
label: str = "app"
r = add_one(10)
m = total([1, 2, 3])

class Counter:
    def __init__(self):
        self.v = 0
    def scaled(self, k: int) -> int:
        return self.v * k

c = Counter()
out = c.scaled(3)

# Unmodelled annotation: lowers to a fresh variable, constrains nothing.
def use(p: SomeProtocol):
    return 1

ignored = use("anything")
also = use(42)
