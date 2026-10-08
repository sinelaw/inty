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
  /-- A closure over its definition-time environment, of `arity`
  parameters. The environment holds the variables' cells, so the closure
  sees later assignments to them, as in JavaScript. -/
  | closure (env : List Nat) (arity : Nat) (body : Expr)
  /-- A native function, `dynamics::Value::Builtin`. -/
  | prim (p : Prim)
  /-- An object: the cell holding its properties, as `dynamics`'
  `Value::Object`. -/
  | obj (ℓ : Nat)
  /-- What an object's cell holds, `dynamics`' `Cell::Object`: its
  properties' values, the latest first. No program has it as a value. -/
  | fields (fs : List (String × Value))
  deriving Repr

/-- A runtime environment: the cell of each variable, innermost first. As in
`dynamics` (`RuntimeEnv`), every binding is a cell, `const` or not. -/
abbrev Env := List Nat

/-- The heap: the value in each cell. A cell is never freed. -/
abbrev Heap := List Value

/-- Why evaluation got stuck, mirroring `dynamics::step::Stuck`. A
well-typed program never produces one. -/
inductive Stuck where
  | undefinedVariable
  | notCallable
  | typeMismatch
  /-- A call with too few arguments, `Stuck::ArityMismatch`. JavaScript
  leaves missing ones `undefined`; inty's semantics, like its typing,
  requires them. Extra ones are ignored, as in JavaScript. -/
  | arityMismatch
  /-- Reading or writing a property of something that isn't an object,
  `Stuck::NotIndexable`. -/
  | notIndexable
  /-- A property the object doesn't have, `Stuck::PropertyNotFound`. -/
  | propertyNotFound
  /-- Writing a property of something that isn't an object,
  `Stuck::BadAssignmentTarget`. -/
  | badAssignmentTarget
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
  /-- `break;`, on its way to its loop. -/
  | broke
  /-- `continue;`, on its way to its loop. -/
  | continued
  deriving Repr

/-- JavaScript truthiness, as `dynamics::Value::truthy`. -/
def Value.truthy : Value → Bool
  | .number n => n != 0 && !n.isNaN
  | .string s => !s.isEmpty
  | .boolean b => b
  | .undefined | .null => false
  | .closure .. | .prim _ | .obj _ | .fields _ => true

/-- JavaScript `typeof`, as `dynamics::Value::type_string`. -/
def Value.typeString : Value → String
  | .number _ => "number"
  | .string _ => "string"
  | .boolean _ => "boolean"
  | .undefined => "undefined"
  | .null | .obj _ | .fields _ => "object"
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

def Prim.apply : Prim → List Value → Result
  | .abs, [.number n] => .ok (.number n.abs)
  | .abs, [_] => .stuck .typeMismatch
  | .truthy, [v] => .ok (.boolean v.truthy)
  | _, _ => .stuck .arityMismatch

/-- Reading the property `l` of `v`, as `dynamics::step::read_member`. A
string has properties of its own (`length`, its methods), which come with
the standard library; any other is not found. -/
def Value.getProp (h : Heap) (l : String) : Value → Result
  | .obj ℓ =>
    match h[ℓ]? with
    | some (.fields fs) =>
      match fs.lookup l with
      | some v => .ok v
      | none => .stuck .propertyNotFound
    | _ => .stuck .notIndexable
  | .string _ => .stuck .propertyNotFound
  | _ => .stuck .notIndexable

/-- Storing `v` in the property `l` of `o`, which it adds if `o` hasn't it,
as in JavaScript and `dynamics`: the outcome and the heap. -/
def Value.setProp (o : Value) (h : Heap) (l : String) (v : Value) : Result × Heap :=
  match o with
  | .obj ℓ =>
    match h[ℓ]? with
    | some (.fields fs) => (.ok v, h.set ℓ (.fields ((l, v) :: fs.filter (·.1 != l))))
    | _ => (.stuck .badAssignmentTarget, h)
  | _ => (.stuck .badAssignmentTarget, h)

/-- An object literal's cell: its fields, the later of two with one label
first, as in JavaScript. -/
def objFields (ls : List String) (vs : List Value) : Value := .fields (ls.zip vs).reverse

/-- A call's result: a `return` from the body is the call's value. -/
def Result.catchReturn : Result → Result
  | .returned v => .ok v
  | r => r

/-- What running gives: the outcome, the clock left, and the heap. -/
abbrev Ran := Result × Nat × Heap

/-- Continue with `k` on a value, the clock left and the heap; any other
outcome (stuck, out of clock, returned, thrown) stops there. -/
def bindC (p : Ran) (k : Value → Nat → Heap → Ran) : Ran :=
  match p with
  | (.ok v, c, h) => k v c h
  | p => p

@[simp] theorem ok_bindC (v : Value) (c : Nat) (h : Heap) (k : Value → Nat → Heap → Ran) :
    bindC (.ok v, c, h) k = k v c h := rfl

private theorem lex_of_le {c c' s s' : Nat} (hc : c' ≤ c) (hs : s' < s) :
    Prod.Lex (· < ·) (· < ·) (c', s') (c, s) := by
  rcases Nat.lt_or_eq_of_le hc with h | rfl
  · exact .left _ _ h
  · exact .right _ hs

/-- What running arguments gives: their values or the outcome that stopped
them, the clock left, and the heap. -/
abbrev RanArgs := Except Result (List Value) × Nat × Heap

/-- Continue with `k` on the values of a list of arguments, the clock left
and the heap; an argument that doesn't give a value stops there. -/
def bindArgs (p : RanArgs) (k : List Value → Nat → Heap → Ran) : Ran :=
  match p with
  | (.ok vs, c, h) => k vs c h
  | (.error r, c, h) => (r, c, h)

/-- A call's environment: cells for the arguments, the function itself and
`this`, stored after the heap `h`, then the closure's. -/
def callEnv (h : Heap) (n : Nat) (cenv : Env) : Env := List.range' h.length (n + 2) ++ cenv

mutual
/-- Run with `clock` calls to spare, in `env`, on the heap `heap`: the
outcome, the calls still to spare, and the heap after. A clock coming back
from a subterm is clamped to the clock it was given (`min c clock`), which
it never exceeds (`run_clock_le`); that is CakeML's `fix_clock`, there for
the termination proof. -/
def run (clock : Nat) (env : Env) (heap : Heap) (e : Expr) : Ran :=
  match e with
  | .lit l => (.ok l.eval, clock, heap)
  | .var i =>
    match env[i]? with
    | some ℓ =>
      match heap[ℓ]? with
      | some v => (.ok v, clock, heap)
      | none => (.stuck .undefinedVariable, clock, heap)
    | none => (.stuck .undefinedVariable, clock, heap)
  | .func n body => (.ok (.closure env n body), clock, heap)
  -- The callee, then the arguments in order, then the call, as in
  -- `dynamics`: a callee that isn't a function is found out only at the
  -- call. A call outside any receiver has `this` `undefined`. A call
  -- takes a tick, a native one too. Extra arguments are ignored, as in
  -- JavaScript and `dynamics`; missing ones are an error.
  | .app f args =>
    bindC (run clock env heap f) fun vf c₁ h₁ =>
    bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ =>
    match vf with
    | .closure cenv n body =>
      if n ≤ vs.length then
        match _h : min c₂ clock with
        | 0 => (.timeout, 0, h₂)
        | c + 1 =>
          let p := run c (callEnv h₂ n cenv) (h₂ ++ vs.take n ++ [vf, .undefined]) body
          (p.1.catchReturn, p.2)
      else (.stuck .arityMismatch, min c₂ clock, h₂)
    | .prim p =>
      match min c₂ clock with
      | 0 => (.timeout, 0, h₂)
      | c + 1 => (p.apply vs, c, h₂)
    | _ => (.stuck .notCallable, min c₂ clock, h₂)
  | .let_ _ e₁ e₂ =>
    bindC (run clock env heap e₁) fun v c₁ h₁ =>
      run (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) e₂
  | .assign i e =>
    bindC (run clock env heap e) fun v c₁ h₁ =>
      match env[i]? with
      | some ℓ => if ℓ < h₁.length then (.ok v, c₁, h₁.set ℓ v)
        else (.stuck .undefinedVariable, c₁, h₁)
      | none => (.stuck .undefinedVariable, c₁, h₁)
  | .cond c t e =>
    bindC (run clock env heap c) fun v c₁ h₁ =>
      if v.truthy then run (min c₁ clock) env h₁ t else run (min c₁ clock) env h₁ e
  | .unop op e => bindC (run clock env heap e) fun v c₁ h₁ => (op.eval v, c₁, h₁)
  | .binop op e₁ e₂ =>
    bindC (run clock env heap e₁) fun v₁ c₁ h₁ =>
    bindC (run (min c₁ clock) env h₁ e₂) fun v₂ c₂ h₂ => (op.eval v₁ v₂, c₂, h₂)
  | .ret e => bindC (run clock env heap e) fun v c₁ h₁ => (.returned v, c₁, h₁)
  | .throw_ e => bindC (run clock env heap e) fun v c₁ h₁ => (.thrown v, c₁, h₁)
  | .seq e₁ e₂ => bindC (run clock env heap e₁) fun _ c₁ h₁ => run (min c₁ clock) env h₁ e₂
  -- Each iteration takes a tick, so a loop runs out of clock, as a
  -- recursive function does. A `break` leaves the loop with `undefined`.
  | .while_ test body =>
    bindC (run clock env heap test) fun v c₁ h₁ =>
      if v.truthy then
        match run (min c₁ clock) env h₁ body with
        | (.ok _, c₂, h₂) | (.continued, c₂, h₂) =>
          match _h : min c₂ clock with
          | 0 => (.timeout, 0, h₂)
          | c + 1 => run c env h₂ (.while_ test body)
        | (.broke, c₂, h₂) => (.ok .undefined, c₂, h₂)
        | p => p
      else (.ok .undefined, c₁, h₁)
  | .break_ => (.broke, clock, heap)
  | .continue_ => (.continued, clock, heap)
  -- The caught value goes in a new cell.
  | .tryCatch body handler =>
    match run clock env heap body with
    | (.thrown v, c₁, h₁) => run (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) handler
    | p => p
  -- Out of clock or stuck, the program stops there, as `dynamics` does: a
  -- stuck program is not a JavaScript exception.
  | .tryFinally body fin =>
    match run clock env heap body with
    | (.timeout, c₁, h₁) => (.timeout, c₁, h₁)
    | (.stuck s, c₁, h₁) => (.stuck s, c₁, h₁)
    | (r, c₁, h₁) =>
      match run (min c₁ clock) env h₁ fin with
      | (.ok _, c₂, h₂) => (r, c₂, h₂)
      | p => p
  -- The fields in order, then a cell for each.
  | .obj ls es =>
    bindArgs (runArgs clock env heap es) fun vs c₁ h₁ =>
      (.ok (.obj h₁.length), c₁, h₁ ++ [objFields ls vs])
  | .get e l => bindC (run clock env heap e) fun v c₁ h₁ => (v.getProp h₁ l, c₁, h₁)
  -- The object, then the value, as in JavaScript.
  | .set e l v =>
    bindC (run clock env heap e) fun vo c₁ h₁ =>
    bindC (run (min c₁ clock) env h₁ v) fun vv c₂ h₂ =>
      let p := vo.setProp h₂ l vv
      (p.1, c₂, p.2)
termination_by (clock, sizeOf e)
decreasing_by
  all_goals first
    | exact lex_of_le (Nat.le_refl _) (by simp <;> omega)
    | exact lex_of_le (Nat.min_le_right _ _) (by simp <;> omega)
    | exact .left _ _ (show _ < clock by omega)

/-- Run a list of arguments in order: their values, or the first outcome
that isn't one. -/
def runArgs (clock : Nat) (env : Env) (heap : Heap) (args : List Expr) : RanArgs :=
  match args with
  | [] => (.ok [], clock, heap)
  | e :: es =>
    match run clock env heap e with
    | (.ok v, c₁, h₁) =>
      match runArgs (min c₁ clock) env h₁ es with
      | (.ok vs, c₂, h₂) => (.ok (v :: vs), c₂, h₂)
      | (.error r, c₂, h₂) => (.error r, c₂, h₂)
    | (r, c₁, h₁) => (.error r, c₁, h₁)
termination_by (clock, sizeOf args)
decreasing_by
  all_goals first
    | exact lex_of_le (Nat.le_refl _) (by simp <;> omega)
    | exact lex_of_le (Nat.min_le_right _ _) (by simp <;> omega)
end

/-- Calling `vf` on `args`, with `this` bound to `thisv`, with `c` calls to
spare, on the heap `h`. -/
def call (c : Nat) (h : Heap) (vf thisv : Value) (args : List Value) : Ran :=
  match vf with
  | .closure cenv n body =>
    if n ≤ args.length then
      match c with
      | 0 => (.timeout, 0, h)
      | c + 1 =>
        let p := run c (callEnv h n cenv) (h ++ args.take n ++ [vf, thisv]) body
        (p.1.catchReturn, p.2)
    else (.stuck .arityMismatch, c, h)
  | .prim p =>
    match c with
    | 0 => (.timeout, 0, h)
    | c + 1 => (p.apply args, c, h)
  | _ => (.stuck .notCallable, c, h)

/-- `run` on a call, without the termination proof's dependent match. -/
theorem run_app (clock : Nat) (env : Env) (heap : Heap) (f : Expr) (args : List Expr) :
    run clock env heap (.app f args) =
      bindC (run clock env heap f) fun vf c₁ h₁ =>
      bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ =>
        call (min c₂ clock) h₂ vf .undefined vs := by
  rw [run]
  congr 1; funext vf c₁ h₁; congr 1; funext vs c₂ h₂
  generalize min c₂ clock = m
  cases vf <;> simp only [call] <;> try rfl
  split <;> try rfl
  cases m <;> rfl

/-- What a loop does after its test and body, given what the body gave:
loop again (`k`) with a tick less, leave it, or stop there. -/
def loopNext (clock : Nat) (p : Ran) (k : Nat → Heap → Ran) : Ran :=
  match p with
  | (.ok _, c₂, h₂) | (.continued, c₂, h₂) =>
    match min c₂ clock with
    | 0 => (.timeout, 0, h₂)
    | c + 1 => k c h₂
  | (.broke, c₂, h₂) => (.ok .undefined, c₂, h₂)
  | p => p

/-- `run` on a loop, without the termination proof's dependent match. -/
theorem run_while (clock : Nat) (env : Env) (heap : Heap) (test body : Expr) :
    run clock env heap (.while_ test body) =
      bindC (run clock env heap test) fun v c₁ h₁ =>
        if v.truthy then
          loopNext clock (run (min c₁ clock) env h₁ body) fun c h₂ =>
            run c env h₂ (.while_ test body)
        else (.ok .undefined, c₁, h₁) := by
  rw [run]
  congr 1; funext v c₁ h₁
  split
  · simp only [loopNext]
    split <;> try rfl
    all_goals (rename_i c₂ h₂ _; generalize min c₂ clock = m; cases m <;> rfl)
  · rfl

/-- The result of running with `clock` calls to spare. -/
def eval (clock : Nat) (env : Env) (heap : Heap) (e : Expr) : Result := (run clock env heap e).1

end Inty
