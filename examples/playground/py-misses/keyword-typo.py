# Keyword arguments resolve by name against the callee's parameter
# list. A misspelt keyword has no matching parameter — caught here,
# not as a TypeError at runtime.

def make_user(name, age):
    return {"name": name, "age": age}

# `nme` is a typo for `name`. Python runs it as a TypeError; inty
# rejects it statically.
u = make_user(nme="ada", age=36)
