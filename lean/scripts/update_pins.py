#!/usr/bin/env python3
"""Regenerate the `Generated` section of Inty/Statements.lean from what
scripts/PrintPins.lean prints. Run from lean/ after `lake build`."""
import subprocess
import sys

HEADER = '''/-! ## The typing rules and the interpreter

Every rule of the typing judgement (`HasTypeS`), of literals' and
operators' types (`LitTy`, `UnOpTy`, `BinOpTyS`), of an object literal's
case (`ObjCase`) and of syntactic values (`Expr.IsValue`); every defining
equation of the interpreter (`run` and the functions it calls, down to a
literal's and an operator's value) and of what the rules' side conditions
are made of (`Expr.writes`, `Annotated`, `EntailsS`, `Ty.whnf`, the scope
checks, ...), restated; and how many rules each family has and equations
each function, so a rule or an equation changed, added or dropped breaks
the build here until this section changes too, where a review sees it.
(Printed by `scripts/PrintPins.lean`; `scripts/update_pins.py` puts it
here.) -/

'''

out = subprocess.run(
    ["lake", "env", "lean", "scripts/PrintPins.lean"],
    capture_output=True, text=True, check=False,
)
if out.returncode != 0 or "error:" in out.stdout:
    sys.exit(out.stdout + out.stderr)

path = "Inty/Statements.lean"
src = open(path).read()
start = src.index("/-! ## The typing rules")
end = src.index("end Generated")
open(path, "w").write(src[:start] + HEADER + out.stdout.rstrip() + "\n\n" + src[end:])
