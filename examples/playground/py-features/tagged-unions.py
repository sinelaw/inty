# A union of two brands. The brand-specific methods are only safe
# to call inside the matching `isinstance` branch — outside it,
# inty rejects the access.

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

# Each branch narrows `animal` to a single brand, so the brand-
# specific method type-checks here.
if isinstance(animal, Dog):
    dog_sound = animal.bark()
else:
    cat_sound = animal.meow()

# Try this — uncomment to see narrowing in action:
# leak = animal.bark()   # error!
