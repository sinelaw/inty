# Two classes with the *same shape* are still different types —
# nominal typing. Trying to use one where the other is expected is
# rejected even when the fields and methods match exactly.

class Meters:
    def __init__(self, n):
        self.value = n

class Seconds:
    def __init__(self, n):
        self.value = n

distance = Meters(100)
distance = Seconds(60)   # different brand — rejected
