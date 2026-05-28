# inty rejects mixing operand types: `+` requires both operands to
# share one type. This is a type error, by design.

x = 1 + "oops"
