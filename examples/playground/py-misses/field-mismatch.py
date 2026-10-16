# `__init__` ties each field to its initial type. `self.name` is a
# `String`, and `+` needs both sides to match, so `shout` only takes
# a String — passing a Number is a type error, by design.

class Greeter:
    def __init__(self, name):
        self.name = name
    def shout(self, times):
        return self.name + times   # fixes `times` to String

g = Greeter("ada")
out = g.shout(3)   # String + Number — rejected
