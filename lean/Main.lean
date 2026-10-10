import Inty.Wire

/-- Read core programs in the wire format, one per line, and print the
model's verdicts for each, one line per program. -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAsciiEnd.toString
  unless line.isEmpty do
    -- The clock bounds the number of calls. Kept low: a call that doubles
    -- a string (`f(x + x)`) grows it exponentially in the number of calls,
    -- and 2^24 characters is the most we can afford. Longer runs time out
    -- here and aren't compared.
    stdout.putStrLn (Inty.Wire.verdict 24 line)
    stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
