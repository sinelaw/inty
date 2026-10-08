import Inty.Syntax

/-!
# Operational semantics

A definitional interpreter with a clock, in the style of Amin and Rompf,
"Type Soundness Proofs with Definitional Interpreters" (POPL 2017), and of
CakeML's functional big-step semantics (Owens et al., ESOP 2016). It is the
Lean counterpart of `src/dynamics`: closures capture their definition-time
environment, and anything that goes wrong is an explicit `stuck` result,
never a crash.

The clock bounds the number of calls. Each call takes one tick, and `run`
returns what is left, which the rest of the program continues with; out of
ticks, a call is a `timeout`. Counting calls rather than recursion depth is
what lets the clock serve as the step index of the logical relation in
`Inty.Soundness`: a value computed with `k` ticks left is good for `k` more.

Being a plain function, `eval` runs (`#eval`), so the model can serve as a
test oracle against the Rust implementation.
-/

namespace Inty

/-- Native functions: values a program can call that no expression of the
calculus denotes. Their types come from what they do, not from a typing
derivation (`Inty.Soundness`). -/
inductive Prim where
  /-- `Math.abs`, on numbers. -/
  | abs
  /-- `Boolean`: truthiness. -/
  | truthy
  deriving DecidableEq, Repr

/-- Runtime values, mirroring `dynamics::Value`. -/
inductive Value where
  | number (n : Float)
  | string (s : String)
  | boolean (b : Bool)
  | undefined
  | null
  /-- A closure over its definition-time environment. -/
  | closure (env : List Value) (body : Expr)
  /-- A native function, `dynamics::Value::Builtin`. -/
  | prim (p : Prim)
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

/-- The outcome of running with a given clock. `timeout` (out of clock) is
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
  | .closure .. | .prim _ => true

/-- JavaScript `typeof`, as `dynamics::Value::type_string`. -/
def Value.typeString : Value → String
  | .number _ => "number"
  | .string _ => "string"
  | .boolean _ => "boolean"
  | .undefined => "undefined"
  | .null => "object"
  | .closure .. | .prim _ => "function"

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

def Prim.apply : Prim → Value → Result
  | .abs, .number n => .ok (.number n.abs)
  | .abs, _ => .stuck .typeMismatch
  | .truthy, v => .ok (.boolean v.truthy)

/-- A call's result: a `return` from the body is the call's value. -/
def Result.catchReturn : Result → Result
  | .returned v => .ok v
  | r => r

/-- Continue with `k` on a value and the clock left; any other outcome
(stuck, out of clock, returned, thrown) stops there, with its clock. -/
def bindC (p : Result × Nat) (k : Value → Nat → Result × Nat) : Result × Nat :=
  match p with
  | (.ok v, c) => k v c
  | p => p

@[simp] theorem ok_bindC (v : Value) (c : Nat) (k : Value → Nat → Result × Nat) :
    bindC (.ok v, c) k = k v c := rfl

private theorem lex_of_le {c c' s s' : Nat} (hc : c' ≤ c) (hs : s' < s) :
    Prod.Lex (· < ·) (· < ·) (c', s') (c, s) := by
  rcases Nat.lt_or_eq_of_le hc with h | rfl
  · exact .left _ _ h
  · exact .right _ hs

/-- Run with `clock` calls to spare; the result, and the calls still to
spare. A clock coming back from a subterm is clamped to the clock it was
given (`min c clock`), which it never exceeds (`run_clock_le`); that is
CakeML's `fix_clock`, there for the termination proof. -/
def run (clock : Nat) (env : Env) (e : Expr) : Result × Nat :=
  match e with
  | .lit l => (.ok l.eval, clock)
  | .var i =>
    match env[i]? with
    | some v => (.ok v, clock)
    | none => (.stuck .undefinedVariable, clock)
  | .func body => (.ok (.closure env body), clock)
  -- The callee, then the argument, then the call, as in `dynamics`: a
  -- callee that isn't a function is found out only at the call.
  | .app f a =>
    bindC (run clock env f) fun vf c₁ =>
    bindC (run (min c₁ clock) env a) fun va c₂ =>
    match vf with
    | .closure cenv body =>
      match _h : min c₂ clock with
      | 0 => (.timeout, 0)
      | c + 1 =>
        let p := run c (va :: vf :: cenv) body
        (p.1.catchReturn, p.2)
    | .prim p => (p.apply va, min c₂ clock)
    | _ => (.stuck .notCallable, min c₂ clock)
  | .let_ e₁ e₂ =>
    bindC (run clock env e₁) fun v c₁ => run (min c₁ clock) (v :: env) e₂
  | .cond c t e =>
    bindC (run clock env c) fun v c₁ =>
      if v.truthy then run (min c₁ clock) env t else run (min c₁ clock) env e
  | .unop op e => bindC (run clock env e) fun v c₁ => (op.eval v, c₁)
  | .binop op e₁ e₂ =>
    bindC (run clock env e₁) fun v₁ c₁ =>
    bindC (run (min c₁ clock) env e₂) fun v₂ c₂ => (op.eval v₁ v₂, c₂)
  | .ret e => bindC (run clock env e) fun v c₁ => (.returned v, c₁)
  | .throw_ e => bindC (run clock env e) fun v c₁ => (.thrown v, c₁)
  | .seq e₁ e₂ => bindC (run clock env e₁) fun _ c₁ => run (min c₁ clock) env e₂
termination_by (clock, sizeOf e)
decreasing_by
  all_goals first
    | exact lex_of_le (Nat.le_refl _) (by simp <;> omega)
    | exact lex_of_le (Nat.min_le_right _ _) (by simp <;> omega)
    | exact .left _ _ (show _ < clock by omega)

/-- Calling `vf` on `va` with `c` calls to spare. -/
def call (c : Nat) (vf va : Value) : Result × Nat :=
  match vf, c with
  | .closure _ _, 0 => (.timeout, 0)
  | .closure cenv body, c + 1 =>
    let p := run c (va :: vf :: cenv) body
    (p.1.catchReturn, p.2)
  | .prim p, c => (p.apply va, c)
  | _, c => (.stuck .notCallable, c)

/-- `run` on a call, without the termination proof's dependent match. -/
theorem run_app (clock : Nat) (env : Env) (f a : Expr) :
    run clock env (.app f a) =
      bindC (run clock env f) fun vf c₁ =>
      bindC (run (min c₁ clock) env a) fun va c₂ => call (min c₂ clock) vf va := by
  rw [run]
  congr 1; funext vf c₁; congr 1; funext va c₂
  generalize min c₂ clock = m
  cases vf <;> cases m <;> rfl

/-- The result of running with `clock` calls to spare. -/
def eval (clock : Nat) (env : Env) (e : Expr) : Result := (run clock env e).1

end Inty
