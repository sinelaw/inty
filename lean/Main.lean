import Inty.Wire

/-- Read core programs in the wire format, one per line, and print the
model's verdicts for each, one line per program. -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimRight
  unless line.isEmpty do
    -- Fuel bounds recursion depth. Kept low: a recursive call that
    -- doubles a string (`f(x + x)`) grows it exponentially in the depth.
    stdout.putStrLn (Inty.Wire.verdict 40 line)
    stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
