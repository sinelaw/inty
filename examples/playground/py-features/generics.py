# A function that doesn't constrain its inputs becomes polymorphic.
# Inty infers `id<a>(a) => a` — one definition, every call site
# instantiates at its own type.

def id(x):
    return x

def pair(a, b):
    return [a, b]

n = id(42)               # Number
s = id("hello")          # String

nums  = pair(1, 2)       # list[Number]
words = pair("hi", "yo") # list[String]
