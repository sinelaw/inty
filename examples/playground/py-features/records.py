# Dicts with string-literal keys are records: `d["field"]` lowers to a
# field read, so structural typing applies just like in JavaScript.

def make_point(x, y):
    return {"x": x, "y": y}

def length_squared(p):
    return p["x"] * p["x"] + p["y"] * p["y"]

origin = make_point(0, 0)
p = make_point(3, 4)
d = length_squared(p)

config = {"name": "app", "version": 1, "enabled": True}
title = config["name"]
