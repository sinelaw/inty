# Control flow: if/elif/else, a while loop, and a conditional
# expression. All branches of `classify` return strings.

def classify(n):
    if n < 0:
        return "negative"
    elif n == 0:
        return "zero"
    else:
        return "positive"

label = classify(5)

i = 0
while i < 5:
    i = i + 1

sign = "pos" if i > 0 else "nonpos"
