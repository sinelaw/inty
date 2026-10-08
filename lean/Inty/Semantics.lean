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
`Stuck::FuelExhausted`, which is not a soundness violation. `returned` and
`thrown` are abrupt completions, as `dynamics::StmtOutcome::{Return,
Throw}`: a call turns a `returned` into its value, and a `thrown` propagates
to the top, where `dynamics` reports it as `Stuck::UncaughtThrow`. -/
inductive Result where
  | ok (v : Value)
  | stuck (s : Stuck)
  | timeout
  | returned (v : Value)
  | thrown (v : Value)
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

/-- Continue with `k` on a value; any other outcome (stuck, out of fuel,
returned, thrown) passes through unchanged. -/
def Result.bind (r : Result) (k : Value → Result) : Result :=
  match r with
  | .ok v => k v
  | r => r

/-- A call's result: a `return` from the body is the call's value. -/
def Result.catchReturn : Result → Result
  | .returned v => .ok v
  | r => r

@[simp] theorem Result.ok_bind (v : Value) (k : Value → Result) : (Result.ok v).bind k = k v := rfl
@[simp] theorem Result.stuck_bind (s : Stuck) (k : Value → Result) :
    (Result.stuck s).bind k = .stuck s := rfl
@[simp] theorem Result.timeout_bind (k : Value → Result) : Result.timeout.bind k = .timeout := rfl
@[simp] theorem Result.returned_bind (v : Value) (k : Value → Result) :
    (Result.returned v).bind k = .returned v := rfl
@[simp] theorem Result.thrown_bind (v : Value) (k : Value → Result) :
    (Result.thrown v).bind k = .thrown v := rfl

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
      (eval fuel env f).bind fun vf =>
      (eval fuel env a).bind fun va =>
      match vf with
      | .closure cenv body => (eval fuel (va :: vf :: cenv) body).catchReturn
      | _ => .stuck .notCallable
    | .let_ e₁ e₂ => (eval fuel env e₁).bind fun v => eval fuel (v :: env) e₂
    | .cond c t e =>
      (eval fuel env c).bind fun v => if v.truthy then eval fuel env t else eval fuel env e
    | .unop op e => (eval fuel env e).bind op.eval
    | .binop op e₁ e₂ =>
      (eval fuel env e₁).bind fun v₁ => (eval fuel env e₂).bind fun v₂ => op.eval v₁ v₂
    | .ret e => (eval fuel env e).bind .returned
    | .throw_ e => (eval fuel env e).bind .thrown
    | .seq e₁ e₂ => (eval fuel env e₁).bind fun _ => eval fuel env e₂

end Inty
