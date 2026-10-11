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

/-- How an object holds a property: an own value, an own getter, or, for
a class's instance, a method or a getter on its prototype, which a spread
doesn't copy. -/
inductive MemberKind where
  | data
  | getter
  | method
  | protoGetter
  deriving DecidableEq, Repr

/-- Whether a member is the object's own property, which a spread copies,
not one on its prototype. -/
def MemberKind.isOwn : MemberKind → Bool
  | .data | .getter => true
  | .method | .protoGetter => false

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
  /-- A function whose `this` is `thisv` whatever it is called on: a
  class's arrow field, whose `this` is the instance. -/
  | bound (f : Value) (thisv : Value)
  /-- An object: the cell holding its properties, as `dynamics`'
  `Value::Object`. -/
  | obj (ℓ : Nat)
  /-- What an object's cell holds, `dynamics`' `Cell::Object`: its
  properties, each with how it holds it, the latest first. No program has
  it as a value. -/
  | fields (fs : List (String × MemberKind × Value))
  /-- An array: the cell holding its elements, `Value::Array`. -/
  | arr (ℓ : Nat)
  /-- What an array's cell holds, `Cell::Array`. No program has it as a
  value. -/
  | items (vs : List Value)
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
  /-- Spreading something that isn't an object: `dynamics` reports
  `Stuck::NotImplemented` (JavaScript spreads a primitive's own
  properties, which a number hasn't). -/
  | notSpreadable
  /-- Storing to a property that only has a getter, which throws a
  `TypeError` in strict code. -/
  | readOnly
  deriving DecidableEq, Repr

/-- A fault inty documents as allowed: the program stops there, and it is
no soundness violation (`Stuck::OutOfBounds`). -/
inductive Fault where
  /-- An element read at an index the array or string hasn't, or a store
  past an array's end. -/
  | outOfBounds
  deriving DecidableEq, Repr

/-- The outcome of running with a given clock. `timeout` (out of clock) is
`Stuck::FuelExhausted`, which is not a soundness violation. `returned` and
`thrown` are abrupt completions, as `dynamics::StmtOutcome::{Return,
Throw}`: a call turns a `returned` into its value, and a `thrown` propagates
to the top, where `dynamics` reports it as `Stuck::UncaughtThrow`. -/
inductive Result where
  | ok (v : Value)
  | stuck (s : Stuck)
  /-- A documented fault: allowed, and not stuck. -/
  | fault (f : Fault)
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
  | .closure .. | .prim _ | .bound .. | .obj _ | .fields _ | .arr _ | .items _ => true

/-- JavaScript `typeof`, as `dynamics::Value::type_string`. -/
def Value.typeString : Value → String
  | .number _ => "number"
  | .string _ => "string"
  | .boolean _ => "boolean"
  | .undefined => "undefined"
  | .null | .obj _ | .fields _ | .arr _ | .items _ => "object"
  | .closure .. | .prim _ | .bound .. => "function"

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

/-- What reading a property finds: a value, a getter to call (with the
object as `this`), or an outcome that stops there. -/
inductive Read where
  | value (v : Value)
  | getter (g : Value)
  | fail (r : Result)

/-- What reading the property `l` of an object with the properties `fs`
finds. -/
def readMember (fs : List (String × MemberKind × Value)) (l : String) : Option Read :=
  match fs.lookup l with
  | some (.data, v) | some (.method, v) => some (.value v)
  | some (.getter, g) | some (.protoGetter, g) => some (.getter g)
  | none => none

/-- Reading the property `l` of `v`, as `dynamics::step::read_member`. An
array and a string have their `length`; their methods come with the
standard library, and any other property is not found. -/
def Value.read (h : Heap) (l : String) : Value → Read
  | .obj ℓ =>
    match h[ℓ]? with
    | some (.fields fs) => (readMember fs l).getD (.fail (.stuck .propertyNotFound))
    | _ => .fail (.stuck .notIndexable)
  | .arr ℓ =>
    match h[ℓ]? with
    | some (.items vs) =>
      if l = "length" then .value (.number vs.length.toFloat)
      else .fail (.stuck .propertyNotFound)
    | _ => .fail (.stuck .notIndexable)
  | .string s =>
    if l = "length" then .value (.number s.length.toFloat) else .fail (.stuck .propertyNotFound)
  | _ => .fail (.stuck .notIndexable)

/-- A number as an index: a non-negative integer, as `dynamics`'
`array_index` (`n as usize`, checked to give `n` back). -/
def _root_.Float.toIndex? (n : Float) : Option Nat :=
  if n.toUInt64.toFloat == n then some n.toUInt64.toNat else none

/-- Reading `o[i]`, as `dynamics::step::read_index`: an array's or a
string's element (a fault at an index it hasn't), an object's property by a
string (or `undefined`; a label is never a number's digits, so a number
reads `undefined` too). -/
def Value.index (h : Heap) : Value → Value → Read
  | .arr ℓ, .number n =>
    match h[ℓ]? with
    | some (.items vs) =>
      match n.toIndex?.bind (vs[·]?) with
      | some v => .value v
      | none => .fail (.fault .outOfBounds)
    | _ => .fail (.stuck .notIndexable)
  | .string s, .number n =>
    match n.toIndex?.bind (s.toList[·]?) with
    | some c => .value (.string (String.singleton c))
    | none => .fail (.fault .outOfBounds)
  | .obj ℓ, .string k =>
    match h[ℓ]? with
    | some (.fields fs) => (readMember fs k).getD (.value .undefined)
    | _ => .fail (.stuck .notIndexable)
  | .obj ℓ, .number _ =>
    match h[ℓ]? with
    | some (.fields _) => .value .undefined
    | _ => .fail (.stuck .notIndexable)
  | _, _ => .fail (.stuck .notIndexable)

/-- The properties `fs` with each `l` holding `v`, as data, in its place. -/
def replaceField (fs : List (String × MemberKind × Value)) (l : String) (v : Value) :
    List (String × MemberKind × Value) :=
  fs.map fun p => if p.1 == l then (l, .data, v) else p

/-- Storing `v` in the property `l` of `o`, as in JavaScript and
`dynamics`: an own property that holds a value keeps its place (which a
spread copies in); one `o` hasn't (or a prototype's method) is added as
its newest own property; a property with only a getter takes no store.
The outcome and the heap. -/
def Value.setProp (o : Value) (h : Heap) (l : String) (v : Value) : Result × Heap :=
  match o with
  | .obj ℓ =>
    match h[ℓ]? with
    | some (.fields fs) =>
      match fs.lookup l with
      | some (.getter, _) | some (.protoGetter, _) => (.stuck .readOnly, h)
      | some (.data, _) => (.ok v, h.set ℓ (.fields (replaceField fs l v)))
      | _ => (.ok v, h.set ℓ (.fields ((l, .data, v) :: fs.filter (·.1 != l))))
    | _ => (.stuck .badAssignmentTarget, h)
  | _ => (.stuck .badAssignmentTarget, h)

/-- Storing `v` at `o[i]`, as `dynamics::step::write_place`: an array's
element in bounds, or just past the end (a push), and a fault further; an
object's property by a string. The outcome and the heap. -/
def Value.setIndex (o : Value) (h : Heap) (i v : Value) : Result × Heap :=
  match o, i with
  | .arr ℓ, .number n =>
    match h[ℓ]? with
    | some (.items vs) =>
      match n.toIndex? with
      | some k =>
        if k < vs.length then (.ok v, h.set ℓ (.items (vs.set k v)))
        else if k = vs.length then (.ok v, h.set ℓ (.items (vs ++ [v])))
        else (.fault .outOfBounds, h)
      | none => (.fault .outOfBounds, h)
    | _ => (.stuck .badAssignmentTarget, h)
  | .obj ℓ, .string k => Value.setProp (.obj ℓ) h k v
  | _, _ => (.stuck .badAssignmentTarget, h)

/-- How an object literal holds a field written as `k`: a method is an
own property holding the function, as JavaScript makes it. -/
def FieldKind.member : FieldKind → MemberKind
  | .data | .method => .data
  | .getter => .getter

/-- Labelled items with each label once, at its first occurrence, holding
its last occurrence's item: an object literal's properties, where a later
definition of a label replaces an earlier one in its place, as in
JavaScript. -/
def mergeLabels {α : Type} : List (String × α) → List (String × α)
  | [] => []
  | (l, a) :: xs =>
    let m := mergeLabels xs
    (l, (m.lookup l).getD a) :: m.filter (·.1 != l)

/-- An object literal's cell: its fields, newest first (so a spread copies
them in the order they were made), a label defined twice where it was
first, with its last value, as in JavaScript. -/
def objFields (ls : List String) (ks : List FieldKind) (vs : List Value) : Value :=
  .fields (mergeLabels (ls.zip ((ks.map FieldKind.member).zip vs))).reverse

/-- A class instance's members, from the values of its fields (`vs`, in
order), the instance `self` (an arrow field's `this`), and the
environment: each member's label, how the instance holds it, and its
value; `none` if a member that isn't a field isn't a function. -/
def clsMembers (env : Env) (self : Value) :
    List String → List Expr → List ClassKind → List Value →
      Option (List (String × MemberKind × Value))
  | l :: ls, _ :: es, .data :: ks, v :: vs =>
    (clsMembers env self ls es ks vs).map ((l, .data, v) :: ·)
  | l :: ls, .func n b :: es, .arrow :: ks, vs =>
    (clsMembers env self ls es ks vs).map ((l, .data, .bound (.closure env n b) self) :: ·)
  | l :: ls, .func n b :: es, .method :: ks, vs =>
    (clsMembers env self ls es ks vs).map ((l, .method, .closure env n b) :: ·)
  | l :: ls, .func n b :: es, .getter :: ks, vs =>
    (clsMembers env self ls es ks vs).map ((l, .protoGetter, .closure env n b) :: ·)
  | [], [], [], [] => some []
  | _, _, _, _ => none

/-- Labelled items with each label once, at its first occurrence (which a
lookup finds): an object's properties, without those a later definition
replaced. -/
def dedupLabels {α : Type} : List (String × α) → List (String × α)
  | [] => []
  | (l, a) :: xs => (l, a) :: (dedupLabels xs).filter (·.1 != l)

/-- Whether a value is an object (a function or an array too), which a
constructor's `return` gives `new` instead of the object it made. -/
def Value.isObject : Value → Bool
  | .obj _ | .arr _ | .closure .. | .prim _ | .bound .. => true
  | _ => false

/-- Whether `new` can call a value: a closure, a `function` or a
constructor. A native function isn't a constructor, and neither is an
arrow field's closure bound to its instance: `new` on one throws a
`TypeError` in JavaScript. -/
def Value.isCtor : Value → Bool
  | .closure .. => true
  | _ => false

/-- What `new` calls: the value if it is a constructor, else `undefined`,
which isn't callable, so that `new` on a function that isn't a
constructor is stuck as a call of something that isn't a function is. -/
def Value.asCtor (v : Value) : Value := if v.isCtor then v else .undefined

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

theorem lex3_left {c c' a a' b b' : Nat} (h : c' < c) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (c', a', b') (c, a, b) := .left _ _ h

theorem lex3_of {c c' a a' b b' : Nat} (hc : c' ≤ c) (h : a' < a ∨ (a' = a ∧ b' < b)) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (c', a', b') (c, a, b) := by
  rcases Nat.lt_or_eq_of_le hc with hc | rfl
  · exact .left _ _ hc
  · refine .right _ ?_
    rcases h with h | ⟨rfl, h⟩
    · exact .left _ _ h
    · exact .right _ h

/-- What running arguments gives: their values or the outcome that stopped
them, the clock left, and the heap. -/
abbrev RanArgs := Except Result (List Value) × Nat × Heap

/-- Continue with `k` on the values of a list of arguments, the clock left
and the heap; an argument that doesn't give a value stops there. -/
def bindArgs (p : RanArgs) (k : List Value → Nat → Heap → Ran) : Ran :=
  match p with
  | (.ok vs, c, h) => k vs c h
  | (.error r, c, h) => (r, c, h)

/-- What copying an object's own properties gives: them, or the outcome
that stopped a getter, the clock left, and the heap. -/
abbrev RanFields := Except Result (List (String × MemberKind × Value)) × Nat × Heap

/-- Continue with `k` on copied properties. -/
def bindFields (p : RanFields) (k : List (String × MemberKind × Value) → Nat → Heap → Ran) :
    Ran :=
  match p with
  | (.ok fs, c, h) => k fs c h
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
  | .ctor n body => (.ok (.closure env n body), clock, heap)
  -- The callee, then the arguments in order, then the call, as in
  -- `dynamics`: a callee that isn't a function is found out only at the
  -- call. A call outside any receiver has `this` `undefined`.
  | .app f args =>
    bindC (run clock env heap f) fun vf c₁ h₁ =>
    bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ =>
      call (min c₂ clock) h₂ vf .undefined vs
  -- `new f(…)`: as a call, with a new object as `this`, which is the
  -- result unless the call gives an object; stuck if `f` isn't a
  -- constructor (`Value.asCtor`).
  | .new_ f args =>
    bindC (run clock env heap f) fun vf c₁ h₁ =>
    bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ =>
      match call (min c₂ clock) (h₂ ++ [.fields []]) vf.asCtor (.obj h₂.length) vs with
      | (.ok v, c₃, h₃) => (.ok (if v.isObject then v else .obj h₂.length), c₃, h₃)
      | p => p
  | .let_ _ _ e₁ e₂ =>
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
  -- Out of clock, stuck or at a fault, the program stops there, as
  -- `dynamics` does: none is a JavaScript exception.
  | .tryFinally body fin =>
    match run clock env heap body with
    | (.timeout, c₁, h₁) => (.timeout, c₁, h₁)
    | (.stuck s, c₁, h₁) => (.stuck s, c₁, h₁)
    | (.fault f, c₁, h₁) => (.fault f, c₁, h₁)
    | (r, c₁, h₁) =>
      match run (min c₁ clock) env h₁ fin with
      | (.ok _, c₂, h₂) => (r, c₂, h₂)
      | p => p
  -- The fields in order, then a cell for them.
  | .obj ls es ks =>
    bindArgs (runArgs clock env heap es) fun vs c₁ h₁ =>
      (.ok (.obj h₁.length), c₁, h₁ ++ [objFields ls ks vs])
  -- The fields' initialisers in order, each seeing the fields before it;
  -- then the instance's cell.
  | .cls ls es ks =>
    bindArgs (runInits clock env heap es ks) fun vs c₁ h₁ =>
      match clsMembers env (.obj h₁.length) ls es ks vs with
      | some fs => (.ok (.obj h₁.length), c₁, h₁ ++ [.fields fs.reverse])
      | none => (.stuck .typeMismatch, c₁, h₁)
  | .get e l =>
    bindC (run clock env heap e) fun vo c₁ h₁ => getter (min c₁ clock) h₁ vo (vo.read h₁ l)
  -- The object, then the value, as in JavaScript.
  | .set e l v =>
    bindC (run clock env heap e) fun vo c₁ h₁ =>
    bindC (run (min c₁ clock) env h₁ v) fun vv c₂ h₂ =>
      let p := vo.setProp h₂ l vv
      (p.1, c₂, p.2)
  -- Each operand's own properties are copied once it is evaluated (a
  -- getter's value, called then), as in JavaScript and `dynamics`, then a
  -- new cell holds them: `e₂`'s first, so a lookup finds them before
  -- `e₁`'s.
  | .spread e₁ e₂ =>
    bindC (run clock env heap e₁) fun v₁ c₁ h₁ =>
    bindFields (own (min c₁ clock) h₁ v₁) fun fs₁ c₂ h₂ =>
    bindC (run (min c₂ clock) env h₂ e₂) fun v₂ c₃ h₃ =>
    bindFields (own (min c₃ clock) h₃ v₂) fun fs₂ c₄ h₄ =>
      (.ok (.obj h₄.length), c₄, h₄ ++ [.fields (fs₂ ++ fs₁)])
  -- The elements in order, then a cell for them.
  | .arr es =>
    bindArgs (runArgs clock env heap es) fun vs c₁ h₁ =>
      (.ok (.arr h₁.length), c₁, h₁ ++ [.items vs])
  | .index e i =>
    bindC (run clock env heap e) fun vo c₁ h₁ =>
    bindC (run (min c₁ clock) env h₁ i) fun vi c₂ h₂ => getter (min c₂ clock) h₂ vo (vo.index h₂ vi)
  -- The container, the index, then the value, as in JavaScript.
  | .setIndex e i v =>
    bindC (run clock env heap e) fun vo c₁ h₁ =>
    bindC (run (min c₁ clock) env h₁ i) fun vi c₂ h₂ =>
    bindC (run (min c₂ clock) env h₂ v) fun vv c₃ h₃ =>
      let p := vo.setIndex h₃ vi vv
      (p.1, c₃, p.2)
  -- The receiver, its property, the arguments, then the call, with `this`
  -- the receiver.
  | .mcall e l args =>
    bindC (run clock env heap e) fun vo c₁ h₁ =>
    bindC (getter (min c₁ clock) h₁ vo (vo.read h₁ l)) fun vf c₂ h₂ =>
    bindArgs (runArgs (min c₂ clock) env h₂ args) fun vs c₃ h₃ =>
      call (min c₃ clock) h₃ vf vo vs
termination_by (clock, 2 * sizeOf e, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
    | exact lex3_left (by omega)

/-- Calling `vf` on `args`, with `this` bound to `thisv` (unless `vf` has a
`this` of its own), with `clock` calls to spare, on the heap `h`. A call
takes a tick, a native one too. Extra arguments are ignored, as in
JavaScript and `dynamics`; missing ones are an error. -/
def call (clock : Nat) (h : Heap) (vf thisv : Value) (args : List Value) : Ran :=
  match vf with
  | .closure cenv n body => callClosure clock h vf cenv n body thisv args
  | .bound (.closure cenv n body) t =>
    callClosure clock h (.closure cenv n body) cenv n body t args
  | .prim p =>
    match clock with
    | 0 => (.timeout, 0, h)
    | c + 1 => (p.apply args, c, h)
  | _ => (.stuck .notCallable, clock, h)
termination_by (clock, 0, 1)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

/-- Calling the closure `vf`, of `n` parameters, its environment `cenv`
and its body `body`, with `this` bound to `thisv`. -/
def callClosure (clock : Nat) (h : Heap) (vf : Value) (cenv : Env) (n : Nat) (body : Expr)
    (thisv : Value) (args : List Value) : Ran :=
  if n ≤ args.length then
    match clock with
    | 0 => (.timeout, 0, h)
    | c + 1 =>
      let p := run c (callEnv h n cenv) (h ++ args.take n ++ [vf, thisv]) body
      (p.1.catchReturn, p.2)
  else (.stuck .arityMismatch, clock, h)
termination_by (clock, 0, 0)
decreasing_by all_goals exact lex3_left (by omega)

/-- What a read gives: the value found, or what calling the getter found
gives, with the object `vo` as `this`. -/
def getter (clock : Nat) (h : Heap) (vo : Value) : Read → Ran
  | .value v => (.ok v, clock, h)
  | .getter g => call clock h g vo []
  | .fail r => (r, clock, h)
termination_by (clock, 0, 2)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

/-- An object's own properties, what a spread copies, in the order they
were made: each read as it is reached (a getter called with the object as
`this`), as JavaScript's `CopyDataProperties` does, so that a getter's
store to a later property is seen; `notSpreadable` for what isn't an
object. -/
def own (clock : Nat) (h : Heap) (v : Value) : RanFields :=
  match v with
  | .obj ℓ =>
    match h[ℓ]? with
    | some (.fields fs) =>
      match copyOwn clock h v (dedupLabels fs).reverse with
      | (.ok cs, c, h') => (.ok cs.reverse, c, h')
      | p => p
    | _ => (.error (.stuck .notSpreadable), clock, h)
  | _ => (.error (.stuck .notSpreadable), clock, h)
termination_by (clock, 1, 0)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inl (by omega))

/-- `own`, for the properties `fs` (in the order they were made) of the
object `vo`: each own one read from the heap as it is then. -/
def copyOwn (clock : Nat) (h : Heap) (vo : Value) (fs : List (String × MemberKind × Value)) :
    RanFields :=
  match fs with
  | [] => (.ok [], clock, h)
  | (l, m, _) :: fs =>
    if m.isOwn then
      match getter clock h vo (vo.read h l) with
      | (.ok v, c₁, h₁) =>
        match copyOwn (min c₁ clock) h₁ vo fs with
        | (.ok cs, c, h') => (.ok ((l, .data, v) :: cs), c, h')
        | p => p
      | (r, c₁, h₁) => (.error r, c₁, h₁)
    else copyOwn clock h vo fs
termination_by (clock, 0, 3 + fs.length)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by simp <;> omega⟩)
    | exact lex3_of (Nat.min_le_right _ _) (.inr ⟨rfl, by simp <;> omega⟩)

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
termination_by (clock, 2 * sizeOf args, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))

/-- Run a class's field initialisers in order, each seeing the fields
before it (in a new cell each, the latest first): their values, or the
first outcome that isn't one. Its other members are functions, made with
the instance. -/
def runInits (clock : Nat) (env : Env) (heap : Heap) (es : List Expr) (ks : List ClassKind) :
    RanArgs :=
  match es, ks with
  | e :: es, .data :: ks =>
    match run clock env heap e with
    | (.ok v, c₁, h₁) =>
      match runInits (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) es ks with
      | (.ok vs, c₂, h₂) => (.ok (v :: vs), c₂, h₂)
      | (.error r, c₂, h₂) => (.error r, c₂, h₂)
    | (r, c₁, h₁) => (.error r, c₁, h₁)
  | _ :: es, _ :: ks => runInits clock env heap es ks
  | _, _ => (.ok [], clock, heap)
termination_by (clock, 2 * sizeOf es, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
end

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
