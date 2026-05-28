# A function that doesn't `return` anything returns `None`, not the
# value of its last expression statement. Using that None as if it
# were a Number is a bug Python only spots when the addition runs.

def log(msg):
    f"[log] {msg}"     # no `return` — the value is thrown away

x = log("starting") + 1
