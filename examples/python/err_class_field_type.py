# A field's declared type is enforced: assigning a value that doesn't
# match the annotation in `__init__` is a type error.

class Box:
    size: int

    def __init__(self):
        # `size` was declared `int`; a string assignment is rejected.
        self.size = "big"
