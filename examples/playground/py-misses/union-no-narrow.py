# A union value has only the methods common to *all* its branches.
# A brand-specific method requires an `isinstance` check first —
# without one, inty rejects the access.

class Dog:
    def __init__(self):
        self.legs = 4
    def bark(self):
        return "woof"

class Cat:
    def __init__(self):
        self.legs = 4
    def meow(self):
        return "miaow"

animal = Dog() if True else Cat()

# No narrowing yet — `bark` exists on Dog only.
sound = animal.bark()
