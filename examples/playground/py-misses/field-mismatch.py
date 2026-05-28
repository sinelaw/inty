# `__init__` ties each field to its initial type. Inside any method
# that reads `self.name`, the field is a `String` — adding a Number
# to it is a type error, by design.

class Greeter:
    def __init__(self, name):
        self.name = name
    def shout(self, times):
        return self.name + times   # String + Number — rejected

g = Greeter("ada")
out = g.shout(3)
