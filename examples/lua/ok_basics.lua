-- Functions, locals, arithmetic, string concatenation and a numeric
-- for loop. Everything here is inferred — no annotations.

local function add(a, b)
  return a + b
end

local function double(n)
  return n * 2
end

local sum = 0
for i = 1, 10 do
  sum = sum + add(i, double(i))
end

-- `..` is string concatenation; it lowers to `+` (the Plus type class
-- on strings), so mixing a string with a number is still rejected.
local label = "sum = " .. "done"
