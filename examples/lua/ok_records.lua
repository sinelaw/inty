-- Tables used as records. Field access works through both `t.field`
-- and the string-literal form `t["field"]` (both lower to a field
-- read), and structural typing means a function that reads `.x`/`.y`
-- accepts any table carrying them.

local function makePoint(x, y)
  return {x = x, y = y}
end

local function lengthSquared(p)
  return p.x * p.x + p.y * p.y
end

local origin = makePoint(0, 0)
local p = makePoint(3, 4)
local d = lengthSquared(p)

local config = {name = "app", version = 1, enabled = true}
local title = config.name
local ver = config["version"]
