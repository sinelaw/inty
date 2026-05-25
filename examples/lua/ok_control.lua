-- Control flow: if/elseif/else, while, and repeat/until. The branches
-- of `classify` all return strings, so its return type is inferred as a
-- single String.

local function classify(n)
  if n < 0 then
    return "negative"
  elseif n == 0 then
    return "zero"
  else
    return "positive"
  end
end

local label = classify(5)

local i = 0
while i < 5 do
  i = i + 1
end

local j = 0
repeat
  j = j + 1
until j >= 3
