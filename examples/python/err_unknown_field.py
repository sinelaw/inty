# The dict literal gives `p` a closed shape `{"x", "y"}`. Reading a key
# it doesn't have is a type error.

p = {"x": 1, "y": 2}
bad = p["z"]
