import Inty.Infer
import Inty.Semantics

/-!
# Wire format for differential testing

The Rust side generates core programs, writes each one for inty as
JavaScript and for this model as an s-expression, one program per line:

```
(num M E)   M × 10^-E      (str s:abc)   a string, `s:` then [a-z]*
(bool true) (undef) (null) (var i)  (func N BODY)  (app F A₀ A₁ …)
(let E₁ E₂) (cond C T E)   (not E) (typeof E) (neg E)  (plus A B) (minus A B)
(ret E)     (throw E)      (seq A B)
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
  | "func", n :: rest => do
    let n ← n.toNat?
    let (b, rest) ← parseExpr rest
    some (.func n b, rest)
  | "app", rest => do
    let (f, rest) ← parseExpr rest
    let (args, rest) ← parseMany rest
    some (.app f args, rest)
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
  | "ret", rest => do let (e, rest) ← parseExpr rest; some (.ret e, rest)
  | "throw", rest => do let (e, rest) ← parseExpr rest; some (.throw_ e, rest)
  | "seq", rest => do
    let (a, rest) ← parseExpr rest
    let (b, rest) ← parseExpr rest
    some (.seq a b, rest)
  | _, _ => none

/-- Parse expressions up to a closing `)`, which is left in place. -/
partial def parseMany : List String → Option (List Expr × List String)
  | ")" :: rest => some ([], ")" :: rest)
  | ts => do
    let (e, rest) ← parseExpr ts
    let (es, rest) ← parseMany rest
    some (e :: es, rest)
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
  | .fn .. => "fun"
  | .var _ => "var"

/-- Inference's verdict: `type T`, or `reject`, which includes a constraint
no type could satisfy (`Plus` on `undefined`, or on a function). A
constraint left on a type variable is satisfiable, and inty leaves it in
place; `T` keeps the variable, as inty's type does. -/
def inferVerdict (e : Expr) : String :=
  match infer [] none e 0 with
  | none => "reject"
  | some o =>
    if o.preds.all Pred.satisfiable then s!"type {tyWire o.τ}" else "reject"

def valueWire : Value → String
  | .number n => s!"num {n.toBits}"
  | .string s => s!"str s:{s}"
  | .boolean b => s!"bool {b}"
  | .undefined => "undef"
  | .null => "null"
  | .closure .. | .prim _ => "fun"

def stuckWire : Stuck → String
  | .undefinedVariable => "undefinedVariable"
  | .notCallable => "notCallable"
  | .typeMismatch => "typeMismatch"
  | .arityMismatch => "arityMismatch"

/-- The interpreter's verdict: `value V`, `stuck R`, or `timeout`. -/
def evalVerdict (clock : Nat) (e : Expr) : String :=
  match eval clock [] e with
  | .ok v => s!"value {valueWire v}"
  | .stuck s => s!"stuck {stuckWire s}"
  | .timeout => "timeout"
  | .thrown v => s!"thrown {valueWire v}"
  -- Only inside a function; at the top level the typing rules rule it out.
  | .returned v => s!"returned {valueWire v}"

/-- The answer to one line. -/
def verdict (clock : Nat) (line : String) : String :=
  match parse line with
  | none => "error unparsable"
  | some e => s!"{inferVerdict e};{evalVerdict clock e}"

#guard verdict 100 "(app (func 1 (var 0)) (num 15 1))" ==
  s!"type number;value num {(1.5 : Float).toBits}"
#guard verdict 100 "(plus (num 1 0) (str s:a))" == "reject;stuck typeMismatch"
#guard verdict 100 "(not (func 1 (plus (var 0) (var 0))))" == "type boolean;value bool false"
#guard verdict 100 "(let (func 1 (var 0)) (app (var 0) (str s:)))" == "type string;value str s:"
#guard verdict 100 "(app (func 2 (var 1)) (num 1 0) (str s:a))" == "type string;value str s:a"
#guard verdict 100 "(app (func 0 (var 1)))" == "type undefined;value undef"
#guard verdict 100 "(app (func 2 (var 1)) (num 1 0))" == "reject;stuck arityMismatch"
#guard verdict 100 "(app (num 1 0" == "error unparsable"
#guard verdict 100 "(app (func 1 (seq (ret (str s:a)) (str s:b))) (null))" == "type string;value str s:a"
#guard verdict 100 "(throw (num 1 0))" == s!"type var;thrown num {(1 : Float).toBits}"
#guard verdict 100 "(ret (num 1 0))" == "reject;returned num 4607182418800017408"

end Inty.Wire
