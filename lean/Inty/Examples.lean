import Inty.Soundness

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

example : HasType [] double .string :=
  .let_ (τ₁ := .arrow .string .string)
    (.func (.binop (.plus .string) (.var rfl) (.var rfl)))
    (.app (.var rfl) (.lit .string))

#guard isString "abab" (eval 10 [] double)

/-- `+` is overloaded, but each use picks one instance: the same function body
also types at `Number`. -/
example : HasType [] (.func (.binop .plus (.var 0) (.var 0)))
    (.arrow .number .number) :=
  .func (.binop (.plus .number) (.var rfl) (.var rfl))

/-- A recursive function:
`function f(n) { return n ? f(n - 1) : "done"; }; f(3)` -/
def countdown : Expr :=
  .app (.func (.cond (.var 0) (.app (.var 1) (.binop .minus (.var 0) (num 1)))
    (str "done")))
    (num 3)

example : HasType [] countdown .string :=
  .app
    (.func (.cond (.var rfl) (.app (.var rfl) (.binop .minus (.var rfl) (.lit .number)))
      (.lit .string)))
    (.lit .number)

#guard isString "done" (eval 20 [] countdown)
-- With too little fuel it times out, which is not a soundness violation.
#guard match eval 3 [] countdown with | .timeout => true | _ => false

/-- `1 + "a"`: inty rejects it, and the semantics gets stuck on it. -/
def mixedPlus : Expr := .binop .plus (num 1) (str "a")

example : ¬ HasType [] mixedPlus τ := by
  intro h
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ => cases h₁ with | lit hl => cases hl; cases h₂ with | lit hl => cases hl

#guard match eval 10 [] mixedPlus with | .stuck .typeMismatch => true | _ => false

/-- A test may have any type and is read by truthiness:
`"" ? 1 : 2` is `2`. -/
example : HasType [] (.cond (str "") (num 1) (num 2)) .number :=
  .cond (.lit .string) (.lit .number) (.lit .number)

#guard match eval 10 [] (.cond (str "") (num 1) (num 2)) with
  | .ok (.number n) => n == 2
  | _ => false

end Inty.Examples
