# Tuples are typed positionally. Returning one and destructuring it
# at the call site preserves each element's type — `q` is a Number,
# `r` is a Number, and the program type-checks across the seam.

def divmod_pair(a, b):
    return (a // b, a % b)

q, r = divmod_pair(17, 5)
total = q + r

# A heterogeneous tuple keeps each slot's type distinct.
def labelled(n, name):
    return (n, name + "!")

count, tag = labelled(3, "items")
ok = count + 1
caption = tag + " ok"
