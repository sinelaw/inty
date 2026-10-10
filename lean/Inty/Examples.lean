import Inty.Builtins

/-!
# Examples

Small programs, each with its typing derivation and its evaluation. The
`#guard`s run the interpreter at build time.
-/

namespace Inty.Examples

open Inty

def num (n : Float) : Expr := .lit (.number n)
def str (s : String) : Expr := .lit (.string s)

/-- Whether a result is the string `s`. -/
def isString (s : String) : Result → Bool
  | .ok (.string t) => t == s
  | _ => false

/-- `const double = function (x) { return x + x; }; double("ab")` -/
def double : Expr :=
  .let_ false (.func 1 (.binop .plus (.var 0) (.var 0))) (.app (.var 0) [str "ab"])

-- One derivation types `double` monomorphically, at `String → String`.
example : HasType L [] [] none double .string :=
  .let_mono (τ₁ := .fn .undefined [.string] .string)
    (.func rfl (.binop (.plus (.of_inst .plusString)) (.var_mono rfl) (.var_mono rfl)))
    (.app (.var_mono rfl) rfl (by simp; exact .lit .string))

#guard isString "abab" (eval 10 [] [] double)

/-- `+` is overloaded, but each use picks one instance: the same function body
also types at `Number`. -/
example : HasType L [] [] none (.func 1 (.binop .plus (.var 0) (.var 0)))
    (.fn .undefined [.number] .number) :=
  .func rfl (.binop (.plus (.of_inst .plusNumber)) (.var_mono rfl) (.var_mono rfl))

/-- Let-polymorphism:
`const id = function (x) { return x; }; const n = id(1); id("a")` -/
def polyId : Expr :=
  .let_ false (.func 1 (.var 0))
    (.let_ false (.app (.var 0) [num 1])
      (.app (.var 1) [str "a"]))

/-- `id`'s scheme, `∀ θ α. this: θ, (α) => α`. -/
def idScheme : Scheme := ⟨2, .fn (.bound 0) [.bound 1] (.bound 1), []⟩

-- `id` is used at `Number → Number` and at `String → String`.
example : HasType L [] [] none polyId .string :=
  .let_ idScheme [] (fun _ _ => .func rfl (.var_mono rfl)) (.inr ⟨.func, rfl⟩)
    (fun _ h => by simp [idScheme] at h)
    (.let_mono
      (.app (.var (s := idScheme) (τs := [.undefined, .number]) rfl rfl nofun) rfl
        (by simp; exact .lit .number))
      (.app (.var (s := idScheme) (τs := [.undefined, .string]) rfl rfl nofun) rfl
        (by simp; exact .lit .string)))

#guard isString "a" (eval 10 [] [] polyId)

/-- A constrained scheme:
`const double = function (x) { return x + x; }; const n = double(1); double("a")` -/
def polyDouble : Expr :=
  .let_ false (.func 1 (.binop .plus (.var 0) (.var 0)))
    (.let_ false (.app (.var 0) [num 1])
      (.app (.var 1) [str "a"]))

/-- `double`'s scheme, `∀ θ α. Plus α ⇒ this: θ, (α) => α`, inty's
`<a> where Plus a => (a) => a`. -/
def doubleScheme : Scheme := ⟨2, .fn (.bound 0) [.bound 1] (.bound 1), [⟨.plus, [.bound 1]⟩]⟩

-- The body is typed assuming `Plus α`; each use establishes it.
example : HasType L [] [] none polyDouble .string :=
  .let_ doubleScheme []
    (fun m _ => .func rfl (.binop (.plus (.inr (by simp [Scheme.openPreds, Scheme.instPreds,
      doubleScheme, varBlock, PPred.inst, PTy.inst, List.range']))) (.var_mono rfl)
      (.var_mono rfl)))
    (.inr ⟨.func, rfl⟩) (fun p hp => by
      simp [doubleScheme] at hp; subst hp; exact .inl ⟨by decide, rfl, 1, by decide, [], rfl⟩)
    (.let_mono
      (.app (.var (s := doubleScheme) (τs := [.undefined, .number]) rfl rfl (fun c hc => by
        simp [Scheme.instPreds, doubleScheme, PPred.inst, PTy.inst] at hc; subst hc
        exact .of_inst .plusNumber))
        rfl (by simp; exact .lit .number))
      (.app (.var (s := doubleScheme) (τs := [.undefined, .string]) rfl rfl (fun c hc => by
        simp [Scheme.instPreds, doubleScheme, PPred.inst, PTy.inst] at hc; subst hc
        exact .of_inst .plusString))
        rfl (by simp; exact .lit .string)))

#guard isString "aa" (eval 20 [] [] polyDouble)

/-- The value restriction: `id(id)` is not a syntactic value, so a `const`
bound to it gets a monomorphic scheme. -/
example : ¬ (Expr.app (.var 0) [.var 0]).IsValue := nofun

/-- A recursive function:
`function f(n) { return n ? f(n - 1) : "done"; }; f(3)` -/
def countdown : Expr :=
  .app (.func 1 (.cond (.var 0) (.app (.var 1) [.binop .minus (.var 0) (num 1)])
    (str "done")))
    [num 3]

example : HasType L [] [] none countdown .string :=
  .app
    (.func (θ := .undefined) (τs := [.number]) (ρ := .string) rfl (.cond (.var_mono rfl)
      (.app (.var_mono rfl) rfl (by simp; exact .binop .minus (.var_mono rfl) (.lit .number)))
      (.lit .string)))
    rfl (by simp; exact .lit .number)

#guard isString "done" (eval 20 [] [] countdown)
-- With too little clock it times out, which is not a soundness violation.
#guard match eval 3 [] [] countdown with | .timeout => true | _ => false

/-- `1 + "a"`: inty rejects it, and the semantics gets stuck on it. -/
def mixedPlus : Expr := .binop .plus (num 1) (str "a")

example : ¬ HasType L [] [] none mixedPlus τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top
      obtain ⟨_, e₂, h₂⟩ := h₂.top
      cases h₁ with
      | lit hl =>
        cases hl
        cases h₂ with
        | lit hl => cases hl; exact absurd (e₁.trans e₂.symm) (fun h => by cases TyEq.con h)

#guard match eval 10 [] [] mixedPlus with | .stuck .typeMismatch => true | _ => false

/-- A test may have any type and is read by truthiness:
`"" ? 1 : 2` is `2`. -/
example : HasType L [] [] none (.cond (str "") (num 1) (num 2)) .number :=
  .cond (.lit .string) (.lit .number) (.lit .number)

#guard match eval 10 [] [] (.cond (str "") (num 1) (num 2)) with
  | .ok (.number n) => n == 2
  | _ => false

-- `1(y)` with `y` unbound: the argument is evaluated before the callee is
-- found not to be a function, as in `dynamics`, so it gets stuck on `y`.
#guard match eval 10 [] [] (.app (num 1) [.var 5]) with
  | .stuck .undefinedVariable => true
  | _ => false

/-! ## Inference

`inferProgram` runs at build time. Each type it finds is a valid typing, by
`inferProgram_sound`. -/

#guard inferProgram double == some .string
#guard inferProgram polyId == some .string
#guard inferProgram countdown == some .string
#guard inferProgram mixedPlus == none
-- `id`'s scheme quantifies each of its variables once: `∀ θ α. this: θ, (α) => α`.
#guard (letScheme true [] none (.fn (.var 0) [.var 1] (.var 1)) []).1.arity == 2
-- `id` alone gets the most general type: its `this`, and its parameter's
-- type for its result.
#guard inferProgram (.func 1 (.var 0)) == some (.fn (.var 0) [.var 1] (.var 1))
-- Two parameters, and `this` (`var 3` in a two-parameter body), which a
-- call outside a receiver makes `undefined`.
#guard inferProgram (.app (.func 2 (.var 3)) [num 1, str "a"]) == some .undefined
#guard inferProgram (.app (.func 2 (.var 1)) [num 1]) == none
-- A `const` generalises `double` with its `Plus` constraint, so it is used
-- at both instances; a use at `Boolean` is rejected.
#guard inferProgram polyDouble == some .string
#guard inferProgram (.let_ false (.func 1 (.binop .plus (.var 0) (.var 0)))
  (.app (.var 0) [.lit (.boolean true)])) == none
-- `const x = function () { const g = function (y) { return y; }; return g + g; }; 1`:
-- `x`'s scheme would carry `Plus` on a function type, which can't hold, so
-- it is an error when `x` is generalised, though nothing uses `x`.
#guard inferProgram (.let_ false (.func 0 (.let_ false (.func 1 (.var 0)) (.binop .plus (.var 0) (.var 0))))
  (num 1)) == none
-- At the top level, nothing resolves the constraint of an unused `+`. inty
-- leaves it on its type variable and accepts the program, and so does
-- inference here: a constraint on a type variable can't fail
-- (`HoldsOrVar`).
#guard inferProgram (.func 1 (.binop .plus (.var 0) (.var 0))) ==
  some (.fn (.var 0) [.var 1] (.var 1))

-- Each of these types is a valid typing, by `inferProgram_sound`. (A proof
-- by `decide` would have the kernel run inference, which it can't do in
-- reasonable memory on types with nested lists; the `#guard`s run it
-- compiled.)

/-! ## `let` and assignment -/

/-- `let x = 1; x = x - 1; x` -/
def countDown : Expr :=
  .let_ true (num 1) (.seq (.assign 0 (.binop .minus (.var 0) (num 1))) (.var 0))

#guard match eval 10 [] [] countDown with | .ok (.number n) => n == 0 | _ => false
#guard inferProgram countDown == some .number

/-- A closure sees a later assignment to a variable it captured:
`let x = 1; const f = function () { return x; }; x = 2; f()` is `2`. -/
def captured : Expr :=
  .let_ true (num 1)
    (.let_ false (.func 0 (.var 2)) (.seq (.assign 1 (num 2)) (.app (.var 0) [])))

#guard match eval 10 [] [] captured with | .ok (.number n) => n == 2 | _ => false
#guard inferProgram captured == some .number

-- Assigning to a `const` is rejected, though it would be type-safe.
#guard inferProgram (.let_ false (num 1) (.assign 0 (num 2))) == none
-- Assigning a value of another type is rejected.
#guard inferProgram (.let_ true (num 1) (.assign 0 (str "a"))) == none

/-- A `let` that is written has one type: `let id = function (x) { return x; };
id = id; id(1); id("a")` is rejected, and without the assignment it is
accepted. -/
def reassignedId (written : Bool) : Expr :=
  .let_ true (.func 1 (.var 0))
    (.seq (if written then .assign 0 (.var 0) else .lit .undefined)
      (.seq (.app (.var 0) [num 1]) (.app (.var 0) [str "a"])))

#guard inferProgram (reassignedId true) == none
#guard inferProgram (reassignedId false) == some .string

/-! ## Loops and exceptions -/

/-- `let i = 3; let s = 0; while (i) { s = s + i; i = i - 1; } s` -/
def sumDown : Expr :=
  .let_ true (num 3) (.let_ true (num 0)
    (.seq (.while_ (.var 1)
      (.seq (.assign 0 (.binop .plus (.var 0) (.var 1)))
        (.assign 1 (.binop .minus (.var 1) (num 1)))))
      (.var 0)))

#guard match eval 20 [] [] sumDown with | .ok (.number n) => n == 6 | _ => false
#guard inferProgram sumDown == some .number

/-- `let i = 0; while (true) { i = i + 1; if (i - 3) {} else { break; } } i` -/
def breakOut : Expr :=
  .let_ true (num 0)
    (.seq (.while_ (.lit (.boolean true))
      (.seq (.assign 0 (.binop .plus (.var 0) (num 1)))
        (.cond (.binop .minus (.var 0) (num 3)) (.lit .undefined) .break_)))
      (.var 0))

#guard match eval 20 [] [] breakOut with | .ok (.number n) => n == 3 | _ => false
#guard inferProgram breakOut == some .number
-- An endless loop runs out of clock, as an endless recursion does.
#guard match eval 50 [] [] (.while_ (.lit (.boolean true)) (.lit .undefined)) with
  | .timeout => true | _ => false

-- `break;` outside a loop is rejected, as JavaScript rejects it.
#guard inferProgram .break_ == none
#guard inferProgram (.while_ (num 1) (.func 0 .break_)) == none

/-- `try { throw "x"; } catch (e) { typeof e }`: anything can be thrown, so
the caught value can be tested but not used at a type. -/
def caught : Expr := .tryCatch (.throw_ (str "x")) (.unop .typeof (.var 0))

#guard isString "string" (eval 10 [] [] caught)
#guard inferProgram caught == some .string
-- `try { throw "s"; } catch (e) { e - 1 }` is rejected: `e` could be a string.
#guard inferProgram (.tryCatch (.throw_ (str "s")) (.binop .minus (.var 0) (num 1))) == none

/-- `let x = 1; try { x = 2; } finally { x = 3; } x` -/
def finallyRuns : Expr :=
  .let_ true (num 1)
    (.seq (.tryFinally (.assign 0 (num 2)) (.assign 0 (num 3))) (.var 0))

#guard match eval 10 [] [] finallyRuns with | .ok (.number n) => n == 3 | _ => false
#guard inferProgram finallyRuns == some .number
-- A `throw` in the body still runs `finally`, and goes on after it.
#guard match eval 10 [] [] (.tryFinally (.throw_ (num 1)) (num 2)) with
  | .thrown (.number n) => n == 1 | _ => false

/-! ## Statements -/

/-- `function f(x) { if (x) { return "pos"; } else { throw x; } }`, applied
to `1`: an early `return` and a `throw`, each standing for any type. -/
def early : Expr :=
  .app (.func 1 (.cond (.var 0) (.ret (str "pos")) (.throw_ (.var 0)))) [num 1]

example : HasType L [] [] none early .string :=
  .app (.func (θ := .undefined) (τs := [.number]) (ρ := .string) rfl
      (.cond (.var_mono rfl) (.ret (.lit .string)) (.throw_ (.var_mono rfl))))
    rfl (by simp; exact .lit .number)

#guard isString "pos" (eval 10 [] [] early)
#guard inferProgram early == some .string
-- `0` takes the other branch: the `throw` reaches the top.
#guard match eval 10 [] [] (.app (.func 1 (.cond (.var 0) (.ret (str "pos")) (.throw_ (.var 0))))
    [num 0]) with
  | .thrown (.number n) => n == 0
  | _ => false

/-- `return` outside a function is rejected. -/
example : ¬ HasType L [] [] none (.ret (num 1)) τ := fun h => by
  obtain ⟨_, -, h⟩ := h.top; cases h

/-! ## Builtins

With the builtins in scope, `Boolean` is variable 0 and `Math.abs` variable
1. -/

/-- `Math.abs(-2)` -/
def absNeg : Expr := .app (.var 1) [.unop .neg (num 2)]

#guard match eval 1 builtinEnv builtinHeap absNeg with | .ok (.number n) => n == 2 | _ => false
#guard inferIn [] builtinCtx absNeg == some .number

-- So, by `inferIn_builtins_never_stuck`, it never gets stuck: `Math.abs` is
-- in the relation because of what it does (`Prim.abs_sound`), with no
-- derivation behind it.

/-- `Boolean` is polymorphic: `Boolean("") ? Boolean(0) : Boolean(Math.abs)`. -/
def truthiness : Expr :=
  .cond (.app (.var 0) [str ""]) (.app (.var 0) [num 0]) (.app (.var 0) [.var 1])

#guard match eval 3 builtinEnv builtinHeap truthiness with | .ok (.boolean b) => b | _ => false
#guard inferIn [] builtinCtx truthiness == some .boolean

-- `Math.abs("a")` is rejected, and would be stuck.
#guard inferIn [] builtinCtx (.app (.var 1) [str "a"]) == none
#guard match eval 1 builtinEnv builtinHeap (.app (.var 1) [str "a"]) with
  | .stuck .typeMismatch => true | _ => false

/-! ## Methods and recursive types -/

/-- `function () { this.value = this.value + 1; return this; }`: inside a
function of no parameters, `var 1` is `this`. -/
def incBody : Expr :=
  .seq (.set (.var 1) "value" (.binop .plus (.get (.var 1) "value") (num 1))) (.ret (.var 1))

/-- `const c = {value: 0, inc: function () {…}}`. -/
def counter : Expr := .obj ["value", "inc"] [num 0, .func 0 incBody]

/-- `c.inc().inc().value`: `inc`'s `this` is the receiver's type, which holds
`inc`, so it is recursive (`μt. {value: Number, inc: (this: t) => t}`), and
the chain types as inty's does. -/
def chained : Expr := .let_ false counter (.get (.mcall (.mcall (.var 0) "inc" []) "inc" []) "value")

#guard inferProgram chained == some .number
#guard match eval 20 [] [] chained with | .ok (.number n) => n == 2 | _ => false

-- `(0, c.inc)()`: a call outside a receiver gives `inc` an `undefined`
-- `this`, which has no `value`.
#guard inferProgram (.let_ false counter (.app (.get (.var 0) "inc") [])) == none

-- A method that doesn't use `this` can be called outside its object.
#guard inferProgram (.let_ false (.obj ["m"] [.func 0 (num 1)]) (.app (.get (.var 0) "m") [])) ==
  some .number

-- `function f(x) { return f; }; f(1)(2) - 1`: `f` returns itself, a
-- recursive function type, so `f(1)(2)` is `f`, not a number.
#guard inferProgram (.let_ false (.func 1 (.var 1))
  (.binop .minus (.app (.app (.var 0) [num 1]) [num 2]) (num 1))) == none

end Inty.Examples
