# Functions are first-class. `compose` is fully polymorphic — inty
# infers `compose<a, b, c>((b) => c, (a) => b) => ((a) => c)`.

def compose(f, g):
    def composed(x):
        return f(g(x))
    return composed

def double(n):
    return n * 2

def inc(n):
    return n + 1

f = compose(double, inc)
m = f(3)              # (3 + 1) * 2 == 8

# Same compose, different types — strings flow through fine.
def loud(s):
    return s + "!"
def repeat(s):
    return s + s

g = compose(loud, repeat)
hi = g("yo")          # "yoyo!"
