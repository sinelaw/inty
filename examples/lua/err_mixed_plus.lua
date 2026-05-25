-- inty rejects mixing operand types: `+` (and Lua's `..`, which lowers
-- to it) requires both operands to share one type. This is a type
-- error, by design.

local x = 1 + "oops"
