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
  .let_ (.func (.binop .plus (.var 0) (.var 0))) (.app (.var 0) (str "ab"))

-- One derivation types `double` monomorphically, at `String → String`.
example : HasType [] [] none double .string :=
  .let_mono (τ₁ := .arrow .string .string)
    (.func (.binop (.plus (.inl .plusString)) (.var_mono rfl) (.var_mono rfl)))
    (.app (.var_mono rfl) (.lit .string))

#guard isString "abab" (eval 10 [] double)

/-- `+` is overloaded, but each use picks one instance: the same function body
also types at `Number`. -/
example : HasType [] [] none (.func (.binop .plus (.var 0) (.var 0)))
    (.arrow .number .number) :=
  .func (.binop (.plus (.inl .plusNumber)) (.var_mono rfl) (.var_mono rfl))

/-- Let-polymorphism:
`const id = function (x) { return x; }; const n = id(1); id("a")` -/
def polyId : Expr :=
  .let_ (.func (.var 0))
    (.let_ (.app (.var 0) (num 1))
      (.app (.var 1) (str "a")))

/-- `id`'s scheme, `∀ α. α → α`. -/
def idScheme : Scheme := ⟨1, .arrow (.bound 0) (.bound 0), []⟩

-- `id` is used at `Number → Number` and at `String → String`.
example : HasType [] [] none polyId .string :=
  .let_ idScheme [] (fun _ _ => .func (.var_mono rfl)) (.inr .func)
    (.let_mono
      (.app (.var (s := idScheme) (τs := [.number]) rfl rfl nofun) (.lit .number))
      (.app (.var (s := idScheme) (τs := [.string]) rfl rfl nofun) (.lit .string)))

#guard isString "a" (eval 10 [] polyId)

/-- A constrained scheme:
`const double = function (x) { return x + x; }; const n = double(1); double("a")` -/
def polyDouble : Expr :=
  .let_ (.func (.binop .plus (.var 0) (.var 0)))
    (.let_ (.app (.var 0) (num 1))
      (.app (.var 1) (str "a")))

/-- `double`'s scheme, `∀ α. Plus α ⇒ α → α`, inty's
`<a> where Plus a => (a) => a`. -/
def doubleScheme : Scheme := ⟨1, .arrow (.bound 0) (.bound 0), [⟨.plus, [.bound 0]⟩]⟩

-- The body is typed assuming `Plus α`; each use establishes it.
example : HasType [] [] none polyDouble .string :=
  .let_ doubleScheme []
    (fun m _ => .func (.binop (.plus (.inr (by simp [Scheme.openPreds, Scheme.instPreds,
      doubleScheme, varBlock, PPred.inst, PTy.inst]))) (.var_mono rfl) (.var_mono rfl)))
    (.inr .func)
    (.let_mono
      (.app (.var (s := doubleScheme) (τs := [.number]) rfl rfl (fun c hc => by
        simp [Scheme.instPreds, doubleScheme, PPred.inst, PTy.inst] at hc; subst hc
        exact .inl .plusNumber))
        (.lit .number))
      (.app (.var (s := doubleScheme) (τs := [.string]) rfl rfl (fun c hc => by
        simp [Scheme.instPreds, doubleScheme, PPred.inst, PTy.inst] at hc; subst hc
        exact .inl .plusString))
        (.lit .string)))

#guard isString "aa" (eval 20 [] polyDouble)

/-- The value restriction: `id(id)` is not a syntactic value, so a `const`
bound to it gets a monomorphic scheme. -/
example : ¬ (Expr.app (.var 0) (.var 0)).IsValue := nofun

/-- A recursive function:
`function f(n) { return n ? f(n - 1) : "done"; }; f(3)` -/
def countdown : Expr :=
  .app (.func (.cond (.var 0) (.app (.var 1) (.binop .minus (.var 0) (num 1)))
    (str "done")))
    (num 3)

example : HasType [] [] none countdown .string :=
  .app
    (.func (.cond (.var_mono rfl)
      (.app (.var_mono rfl) (.binop .minus (.var_mono rfl) (.lit .number)))
      (.lit .string)))
    (.lit .number)

#guard isString "done" (eval 20 [] countdown)
-- With too little clock it times out, which is not a soundness violation.
#guard match eval 3 [] countdown with | .timeout => true | _ => false

/-- `1 + "a"`: inty rejects it, and the semantics gets stuck on it. -/
def mixedPlus : Expr := .binop .plus (num 1) (str "a")

example : ¬ HasType [] [] none mixedPlus τ := by
  intro h
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ => cases h₁ with | lit hl => cases hl; cases h₂ with | lit hl => cases hl

#guard match eval 10 [] mixedPlus with | .stuck .typeMismatch => true | _ => false

/-- A test may have any type and is read by truthiness:
`"" ? 1 : 2` is `2`. -/
example : HasType [] [] none (.cond (str "") (num 1) (num 2)) .number :=
  .cond (.lit .string) (.lit .number) (.lit .number)

#guard match eval 10 [] (.cond (str "") (num 1) (num 2)) with
  | .ok (.number n) => n == 2
  | _ => false

-- `1(y)` with `y` unbound: the argument is evaluated before the callee is
-- found not to be a function, as in `dynamics`, so it gets stuck on `y`.
#guard match eval 10 [] (.app (num 1) (.var 5)) with
  | .stuck .undefinedVariable => true
  | _ => false

/-! ## Inference

`inferProgram` runs at build time. Each type it finds is a valid typing, by
`inferProgram_sound`. -/

#guard inferProgram double == some .string
#guard inferProgram polyId == some .string
#guard inferProgram countdown == some .string
#guard inferProgram mixedPlus == none
-- `id`'s scheme quantifies its one variable once: `∀ α. α → α`.
#guard (letScheme (.func (.var 0)) [] none (.arrow (.var 0) (.var 0)) []).1.arity == 1
-- `id` alone gets the most general type, `α → α`.
#guard inferProgram (.func (.var 0)) == some (.arrow (.var 0) (.var 0))
-- A `const` generalises `double` with its `Plus` constraint, so it is used
-- at both instances; a use at `Boolean` is rejected.
#guard inferProgram polyDouble == some .string
#guard inferProgram (.let_ (.func (.binop .plus (.var 0) (.var 0)))
  (.app (.var 0) (.lit (.boolean true)))) == none
-- At the top level, nothing resolves the constraint of an unused `+`.
#guard inferProgram (.func (.binop .plus (.var 0) (.var 0))) == none

example : HasType [] [] none polyId .string := inferProgram_sound (by decide)

/-! ## Statements -/

/-- `function f(x) { if (x) { return "pos"; } else { throw x; } }`, applied
to `1`: an early `return` and a `throw`, each standing for any type. -/
def early : Expr :=
  .app (.func (.cond (.var 0) (.ret (str "pos")) (.throw_ (.var 0)))) (num 1)

example : HasType [] [] none early .string :=
  .app (.func (.cond (.var_mono rfl) (.ret (.lit .string)) (.throw_ (.var_mono rfl))))
    (.lit .number)

#guard isString "pos" (eval 10 [] early)
#guard inferProgram early == some .string
-- `0` takes the other branch: the `throw` reaches the top.
#guard match eval 10 [] (.app (.func (.cond (.var 0) (.ret (str "pos")) (.throw_ (.var 0))))
    (num 0)) with
  | .thrown (.number n) => n == 0
  | _ => false

/-- `return` outside a function is rejected. -/
example : ¬ HasType [] [] none (.ret (num 1)) τ := nofun

/-! ## Builtins

With the builtins in scope, `Boolean` is variable 0 and `Math.abs` variable
1. -/

/-- `Math.abs(-2)` -/
def absNeg : Expr := .app (.var 1) (.unop .neg (num 2))

#guard match eval 1 builtinEnv absNeg with | .ok (.number n) => n == 2 | _ => false
#guard inferIn builtinCtx absNeg == some .number

/-- Its inferred type makes it safe: `Math.abs` is in the relation because of
what it does (`Prim.abs_sound`), with no derivation behind it. -/
example : ∀ clock s, eval clock builtinEnv absNeg ≠ .stuck s :=
  inferIn_builtins_never_stuck (τ := .number) (by decide)

/-- `Boolean` is polymorphic: `Boolean("") ? Boolean(0) : Boolean(Math.abs)`. -/
def truthiness : Expr :=
  .cond (.app (.var 0) (str "")) (.app (.var 0) (num 0)) (.app (.var 0) (.var 1))

#guard match eval 1 builtinEnv truthiness with | .ok (.boolean b) => b | _ => false
#guard inferIn builtinCtx truthiness == some .boolean

-- `Math.abs("a")` is rejected, and would be stuck.
#guard inferIn builtinCtx (.app (.var 1) (str "a")) == none
#guard match eval 1 builtinEnv (.app (.var 1) (str "a")) with
  | .stuck .typeMismatch => true | _ => false

end Inty.Examples
