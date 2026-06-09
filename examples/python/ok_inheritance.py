# Single inheritance. `class Sub(Base):` lowers to a factory that
# constructs and spreads a base instance, so the base's fields and methods
# are inherited via inty's structural row merge. `super().__init__(...)`
# drives the base construction; `super().m(...)` calls the base method.
#
# Inheritance here is structural: a subclass instance carries every field of
# its base, so a function that reads a base field accepts a subclass without
# any subtyping rule — it's plain row polymorphism.


class Animal:
    def __init__(self, name):
        self.name = name

    def describe(self):
        return self.name


class Dog(Animal):
    def __init__(self, name, breed):
        super().__init__(name)  # base constructor: sets self.name
        self.breed = breed

    def describe(self):  # override
        return super().describe() + " the dog"

    def loud_name(self):
        return self.name + "!"  # direct access to an inherited field


d = Dog("Rex", "lab")
a = d.describe()  # String  (Dog's override, which calls super().describe())
b = d.loud_name()  # String  (reads inherited `name`)
c = d.breed  # String  (own field)
e = d.name  # String  (inherited field)


# Structural subsumption: a function reading `.name` accepts any subclass,
# because the subclass row carries the inherited field.
def greet(x):
    return x.name


g = greet(d)  # String — a Dog flows where a "thing with .name" is expected
