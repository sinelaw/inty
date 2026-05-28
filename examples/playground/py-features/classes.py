# A class lowers to a factory function returning a row of methods +
# fields. `__init__` pins the field types; methods read them through
# `self`. Different classes are distinct nominal brands even when
# their shape is identical.

class Counter:
    def __init__(self, start):
        self.value = start
    def inc(self):
        self.value = self.value + 1
        return self.value
    def get(self):
        return self.value

c = Counter(0)
a = c.inc()
b = c.inc()
v = c.get()

# Try this — fields keep the type fixed by __init__:
# c.value = "oops"   # error!
