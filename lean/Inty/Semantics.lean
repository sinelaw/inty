import Inty.Syntax

/-!
# Operational semantics

A definitional interpreter with fuel, in the style of Amin and Rompf, "Type
Soundness Proofs with Definitional Interpreters" (POPL 2017). It is the Lean
counterpart of `src/dynamics`: closures capture their
definition-time environment, evaluation is bounded by fuel, and anything that
goes wrong is an explicit `stuck` result, never a crash.

Being a plain function, `eval` runs (`#eval`), so the model can serve as a
test oracle against the Rust implementation.
-/

namespace Inty

/-- Runtime values, mirroring `dynamics::Value`. -/
inductive Value where
  | number (n : Float)
  | string (s : String)
  | boolean (b : Bool)
  | undefined
  | null
  /-- A closure over its definition-time environment. -/
  | closure (env : List Value) (body : Expr)
  deriving Repr

/-- A runtime environment: the value of each variable, innermost first. -/
abbrev Env := List Value

/-- Why evaluation got stuck, mirroring `dynamics::step::Stuck`. A
well-typed program never produces one. -/
inductive Stuck where
  | undefinedVariable
  | notCallable
  | typeMismatch
  deriving DecidableEq, Repr

/-- The outcome of running with a given amount of fuel. `timeout` is
`Stuck::FuelExhausted`, which is not a soundness violation. -/
inductive Result where
  | ok (v : Value)
  | stuck (s : Stuck)
  | timeout
  deriving Repr

/-- JavaScript truthiness, as `dynamics::Value::truthy`. -/
def Value.truthy : Value → Bool
  | .number n => n != 0 && !n.isNaN
  | .string s => !s.isEmpty
  | .boolean b => b
  | .undefined | .null => false
  | .closure .. => true

/-- JavaScript `typeof`, as `dynamics::Value::type_string`. -/
def Value.typeString : Value → String
  | .number _ => "number"
  | .string _ => "string"
  | .boolean _ => "boolean"
  | .undefined => "undefined"
  | .null => "object"
  | .closure .. => "function"

def Lit.eval : Lit → Value
  | .number n => .number n
  | .string s => .string s
  | .boolean b => .boolean b
  | .undefined => .undefined
  | .null => .null

def UnOp.eval : UnOp → Value → Result
  | .not, v => .ok (.boolean !v.truthy)
  | .typeof, v => .ok (.string v.typeString)
  | .neg, .number n => .ok (.number (-n))
  | .neg, _ => .stuck .typeMismatch

def BinOp.eval : BinOp → Value → Value → Result
  | .plus, .number a, .number b => .ok (.number (a + b))
  | .plus, .string a, .string b => .ok (.string (a ++ b))
  | .minus, .number a, .number b => .ok (.number (a - b))
  | _, _, _ => .stuck .typeMismatch

/-- Evaluate with `fuel` steps of recursion. -/
def eval : Nat → Env → Expr → Result
  | 0, _, _ => .timeout
  | fuel + 1, env, e =>
    match e with
    | .lit l => .ok l.eval
    | .var i =>
      match env[i]? with
      | some v => .ok v
      | none => .stuck .undefinedVariable
    | .func body => .ok (.closure env body)
    -- The callee, then the argument, then the call, as in `dynamics`: a
    -- callee that isn't a function is found out only at the call.
    | .app f a =>
      match eval fuel env f with
      | .ok vf =>
        match eval fuel env a with
        | .ok va =>
          match vf with
          | .closure cenv body => eval fuel (va :: vf :: cenv) body
          | _ => .stuck .notCallable
        | r => r
      | r => r
    | .let_ e₁ e₂ =>
      match eval fuel env e₁ with
      | .ok v => eval fuel (v :: env) e₂
      | r => r
    | .cond c t e =>
      match eval fuel env c with
      | .ok v => if v.truthy then eval fuel env t else eval fuel env e
      | r => r
    | .unop op e =>
      match eval fuel env e with
      | .ok v => op.eval v
      | r => r
    | .binop op e₁ e₂ =>
      match eval fuel env e₁ with
      | .ok v₁ =>
        match eval fuel env e₂ with
        | .ok v₂ => op.eval v₁ v₂
        | r => r
      | r => r

end Inty
