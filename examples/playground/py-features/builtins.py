# Inty's Python prelude types core builtins precisely. `abs` is
# `(Number) -> Number`, `range` produces something you can iterate
# over as Number, `sorted` is generic over the element type.

x = abs(-7)                 # Number
total = sum([1, 2, 3])      # Number

words = sorted(["pear", "apple", "fig"])
first = words[0]            # String

count = 0
for i in range(10):
    count = count + i

label = str(count)          # Number -> String
yes = all([True, True])     # Bool
