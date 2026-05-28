# An annotation referring to a name that isn't a primitive, type
# alias, declared type variable, or class in scope is a hard error
# (catches typos like `-> blabla` and unimported types). Stub gaps
# (typeshed / `.pyi`) still degrade silently — this strict check
# applies only to user-authored `.py` annotations.

def total_price(quantity: int, price: int) -> blabla:
    return f"total: {quantity * price}"

t = total_price(3, 10)
