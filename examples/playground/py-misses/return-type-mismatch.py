# A `-> int` annotation is enforced. Returning a String from a
# function the type system promised would yield an `int` is rejected.

def total_price(quantity: int, price: int) -> int:
    # Easy to swap by accident when refactoring.
    return f"total: {quantity * price}"

t = total_price(3, 10)
