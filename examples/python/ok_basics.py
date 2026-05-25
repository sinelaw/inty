# Functions, assignment, arithmetic, string concatenation and a
# for-each loop over a list. Types are inferred throughout.

def add(a, b):
    return a + b

def double(n):
    return n * 2

total = 0
for i in [1, 2, 3, 4, 5]:
    total = total + add(i, double(i))

label = "total = " + "done"
