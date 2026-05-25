-- The table literal gives `p` a closed shape `{x, y}`. Reading a field
-- it doesn't have is a type error.

local p = {x = 1, y = 2}
local bad = p.z
