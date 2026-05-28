# Inty exposes the Python `list` method surface — not the JavaScript
# one. The methods you'd reach for at the REPL all type-check.

xs = [3, 1, 4, 1, 5]
xs.append(9)
xs.extend([2, 6])
xs.insert(0, 0)

n = xs.count(1)       # how many 1s
i = xs.index(4)       # first position of 4

xs.sort()
xs.reverse()
last = xs.pop()       # Number

ys = ["banana", "apple", "cherry"]
ys.sort()
top = ys[0]           # String
