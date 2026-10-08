import Inty.Infer
import Inty.Semantics

/-!
# Wire format for differential testing

The Rust side generates core programs, writes each one for inty as
JavaScript and for this model as an s-expression, one program per line:

```
(num M E)   M × 10^-E      (str s:abc)   a string, `s:` then [a-z]*
(bool true) (undef) (null) (var i)       (func BODY)   (app F A)
(let E₁ E₂) (cond C T E)   (not E) (typeof E) (neg E)  (plus A B) (minus A B)
```

`inty-model` (`Main.lean`) answers each line with the model's verdicts, as
`verdict` prints them. The parser and printer aren't part of what is proved;
they only carry programs and answers across.
-/

namespace Inty.Wire

open Inty

/-- Split a line into `(`, `)` and atoms. -/
def tokenize (s : String) : List String :=
  let spaced := s.replace "(" " ( " |>.replace ")" " ) "
  spaced.splitOn " " |>.filter (· ≠ "")

mutual
/-- Parse one expression from the front of the tokens. -/
partial def parseExpr : List String → Option (Expr × List String)
  | "(" :: tag :: rest => do
    let (e, rest) ← parseForm tag rest
    match rest with
    | ")" :: rest => some (e, rest)
    | _ => none
  | _ => none

partial def parseForm (tag : String) (ts : List String) : Option (Expr × List String) :=
  match tag, ts with
  | "num", m :: e :: rest => do
    let m ← m.toNat?
    let e ← e.toNat?
    some (.lit (.number (Float.ofScientific m true e)), rest)
  | "str", s :: rest =>
    if s.startsWith "s:" then some (.lit (.string (s.drop 2).toString), rest) else none
  | "bool", "true" :: rest => some (.lit (.boolean true), rest)
  | "bool", "false" :: rest => some (.lit (.boolean false), rest)
  | "undef", rest => some (.lit .undefined, rest)
  | "null", rest => some (.lit .null, rest)
  | "var", i :: rest => do some (.var (← i.toNat?), rest)
  | "func", rest => do
    let (b, rest) ← parseExpr rest
    some (.func b, rest)
  | "app", rest => do
    let (f, rest) ← parseExpr rest
    let (a, rest) ← parseExpr rest
    some (.app f a, rest)
  | "let", rest => do
    let (e₁, rest) ← parseExpr rest
    let (e₂, rest) ← parseExpr rest
    some (.let_ e₁ e₂, rest)
  | "cond", rest => do
    let (c, rest) ← parseExpr rest
    let (t, rest) ← parseExpr rest
    let (e, rest) ← parseExpr rest
    some (.cond c t e, rest)
  | "not", rest => do let (e, rest) ← parseExpr rest; some (.unop .not e, rest)
  | "typeof", rest => do let (e, rest) ← parseExpr rest; some (.unop .typeof e, rest)
  | "neg", rest => do let (e, rest) ← parseExpr rest; some (.unop .neg e, rest)
  | "plus", rest => do
    let (a, rest) ← parseExpr rest
    let (b, rest) ← parseExpr rest
    some (.binop .plus a b, rest)
  | "minus", rest => do
    let (a, rest) ← parseExpr rest
    let (b, rest) ← parseExpr rest
    some (.binop .minus a b, rest)
  | _, _ => none
end

/-- Parse a whole line. -/
def parse (s : String) : Option Expr :=
  match parseExpr (tokenize s) with
  | some (e, []) => some e
  | _ => none

def tyWire : Ty → String
  | .number => "number"
  | .string => "string"
  | .boolean => "boolean"
  | .undefined => "undefined"
  | .null => "null"
  | .arrow .. => "fun"
  | .var _ => "var"

/-- Whether a pending `Plus` constraint could still hold: it is on a type
variable, or on an instance. -/
def satisfiable : Ty → Bool
  | .var _ => true
  | τ => τ.isPlusInst

/-- Inference's verdict: `type T`; `ambiguous`, when a `Plus` constraint on
a type variable is left that nothing resolves; or `reject`, which includes a
`Plus` constraint no type could satisfy (on `undefined`, or on a function). -/
def inferVerdict (e : Expr) : String :=
  match infer [] e 0 with
  | none => "reject"
  | some o =>
    if o.plus.all Ty.isPlusInst then s!"type {tyWire o.τ}"
    else if o.plus.all satisfiable then "ambiguous"
    else "reject"

def valueWire : Value → String
  | .number n => s!"num {n.toBits}"
  | .string s => s!"str s:{s}"
  | .boolean b => s!"bool {b}"
  | .undefined => "undef"
  | .null => "null"
  | .closure .. => "fun"

def stuckWire : Stuck → String
  | .undefinedVariable => "undefinedVariable"
  | .notCallable => "notCallable"
  | .typeMismatch => "typeMismatch"

/-- The interpreter's verdict: `value V`, `stuck R`, or `timeout`. -/
def evalVerdict (fuel : Nat) (e : Expr) : String :=
  match eval fuel [] e with
  | .ok v => s!"value {valueWire v}"
  | .stuck s => s!"stuck {stuckWire s}"
  | .timeout => "timeout"

/-- The answer to one line. -/
def verdict (fuel : Nat) (line : String) : String :=
  match parse line with
  | none => "error unparsable"
  | some e => s!"{inferVerdict e};{evalVerdict fuel e}"

#guard verdict 100 "(app (func (var 0)) (num 15 1))" ==
  s!"type number;value num {(1.5 : Float).toBits}"
#guard verdict 100 "(plus (num 1 0) (str s:a))" == "reject;stuck typeMismatch"
#guard verdict 100 "(not (func (plus (var 0) (var 0))))" == "ambiguous;value bool false"
#guard verdict 100 "(let (func (var 0)) (app (var 0) (str s:)))" == "type string;value str s:"
#guard verdict 100 "(app (num 1 0" == "error unparsable"

end Inty.Wire
