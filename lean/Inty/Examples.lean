import Inty.Builtins

/-!
# Examples

Small programs, each with its typing derivation and its evaluation. The
`#guard`s run the interpreter at build time. In the JavaScript each is
written as, a function's `return` is its body's value: a function in the
calculus gives back the value its body ends with, or the one a `return`
gives.
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
  .let_ false none (.func 1 (.binop .plus (.var 0) (.var 0))) (.app (.var 0) [str "ab"])

-- One derivation types `double` monomorphically, at `String → String`.
example : HasType L [] [] none .synth .synth double .string :=
  .let_mono (τ₁ := .fn .undefined [.string] .string)
    (.func rfl (.binop (.plus (.of_inst .plusString)) (.var_mono rfl) (.var_mono rfl)))
    (.app (.var_mono rfl) rfl (by simp; exact .lit .string))

#guard isString "abab" (eval 10 [] [] double)

/-- `+` is overloaded, but each use picks one instance: the same function body
also types at `Number`. -/
example : HasType L [] [] none .synth .synth (.func 1 (.binop .plus (.var 0) (.var 0)))
    (.fn .undefined [.number] .number) :=
  .func rfl (.binop (.plus (.of_inst .plusNumber)) (.var_mono rfl) (.var_mono rfl))

/-- Let-polymorphism:
`const id = function (x) { return x; }; const n = id(1); id("a")` -/
def polyId : Expr :=
  .let_ false none (.func 1 (.var 0))
    (.let_ false none (.app (.var 0) [num 1])
      (.app (.var 1) [str "a"]))

/-- `id`'s scheme, `∀ θ α. this: θ, (α) => α`. -/
def idScheme : Scheme := ⟨2, .fn (.bound 0) [.bound 1] (.bound 1), []⟩

-- `id` is used at `Number → Number` and at `String → String`.
example : HasType L [] [] none .synth .synth polyId .string :=
  .let_ idScheme [] (fun _ _ => .func rfl (.var_mono rfl)) (.inr ⟨.func, rfl⟩)
    (fun _ h => by simp [idScheme] at h) (fun _ h => by cases h)
    (.let_mono
      (.app (.var (s := idScheme) (τs := [.undefined, .number]) rfl rfl nofun) rfl
        (by simp; exact .lit .number))
      (.app (.var (s := idScheme) (τs := [.undefined, .string]) rfl rfl nofun) rfl
        (by simp; exact .lit .string)))

#guard isString "a" (eval 10 [] [] polyId)

/-- A constrained scheme:
`const double = function (x) { return x + x; }; const n = double(1); double("a")` -/
def polyDouble : Expr :=
  .let_ false none (.func 1 (.binop .plus (.var 0) (.var 0)))
    (.let_ false none (.app (.var 0) [num 1])
      (.app (.var 1) [str "a"]))

/-- `double`'s scheme, `∀ θ α. Plus α ⇒ this: θ, (α) => α`, inty's
`<a> where Plus a => (a) => a`. -/
def doubleScheme : Scheme := ⟨2, .fn (.bound 0) [.bound 1] (.bound 1), [⟨.plus, [.bound 1]⟩]⟩

-- The body is typed assuming `Plus α`; each use establishes it.
example : HasType L [] [] none .synth .synth polyDouble .string :=
  .let_ doubleScheme []
    (fun m _ => .func rfl (.binop (.plus (.of_mem (by simp [Scheme.openPreds, Scheme.instPreds,
      doubleScheme, varBlock, PPred.inst, PTy.inst, List.range']))) (.var_mono rfl)
      (.var_mono rfl)))
    (.inr ⟨.func, rfl⟩) (fun p hp => by
      simp [doubleScheme] at hp; subst hp; exact .inl ⟨by decide, rfl, 1, by decide, [], rfl⟩)
    (fun _ h => by cases h)
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

example : HasType L [] [] none .synth .synth countdown .string :=
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

example : ¬ HasType L [] [] none .synth .synth mixedPlus τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top_synth
      obtain ⟨_, e₂, h₂⟩ := h₂.top_synth
      cases h₁ with
      | lit hl =>
        cases hl
        cases h₂ with
        | lit hl => cases hl; exact absurd (e₁.trans e₂.symm) (fun h => by cases TyEq.con h)

#guard match eval 10 [] [] mixedPlus with | .stuck .typeMismatch => true | _ => false

/-- A test may have any type and is read by truthiness:
`"" ? 1 : 2` is `2`. -/
example : HasType L [] [] none .synth .synth (.cond (str "") (num 1) (num 2)) .number :=
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
#guard inferProgram (.let_ false none (.func 1 (.binop .plus (.var 0) (.var 0)))
  (.app (.var 0) [.lit (.boolean true)])) == none
-- `const x = function () { const g = function (y) { return y; }; return g + g; }; 1`:
-- `x`'s scheme would carry `Plus` on a function type, which can't hold, so
-- it is an error when `x` is generalised, though nothing uses `x`.
#guard inferProgram (.let_ false none (.func 0 (.let_ false none (.func 1 (.var 0)) (.binop .plus (.var 0) (.var 0))))
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
  .let_ true none (num 1) (.seq (.assign 0 (.binop .minus (.var 0) (num 1))) (.var 0))

#guard match eval 10 [] [] countDown with | .ok (.number n) => n == 0 | _ => false
#guard inferProgram countDown == some .number

/-- A closure sees a later assignment to a variable it captured:
`let x = 1; const f = function () { return x; }; x = 2; f()` is `2`. -/
def captured : Expr :=
  .let_ true none (num 1)
    (.let_ false none (.func 0 (.var 2)) (.seq (.assign 1 (num 2)) (.app (.var 0) [])))

#guard match eval 10 [] [] captured with | .ok (.number n) => n == 2 | _ => false
#guard inferProgram captured == some .number

-- Assigning to a `const` is rejected, though it would be type-safe.
#guard inferProgram (.let_ false none (num 1) (.assign 0 (num 2))) == none
-- Assigning a value of another type is rejected.
#guard inferProgram (.let_ true none (num 1) (.assign 0 (str "a"))) == none

/-- A `let` that is written has one type: `let id = function (x) { return x; };
id = id; id(1); id("a")` is rejected, and without the assignment it is
accepted. -/
def reassignedId (written : Bool) : Expr :=
  .let_ true none (.func 1 (.var 0))
    (.seq (if written then .assign 0 (.var 0) else .lit .undefined)
      (.seq (.app (.var 0) [num 1]) (.app (.var 0) [str "a"])))

#guard inferProgram (reassignedId true) == none
#guard inferProgram (reassignedId false) == some .string

/-! ## Loops and exceptions -/

/-- `let i = 3; let s = 0; while (i) { s = s + i; i = i - 1; } s` -/
def sumDown : Expr :=
  .let_ true none (num 3) (.let_ true none (num 0)
    (.seq (.while_ (.var 1)
      (.seq (.assign 0 (.binop .plus (.var 0) (.var 1)))
        (.assign 1 (.binop .minus (.var 1) (num 1)))))
      (.var 0)))

#guard match eval 20 [] [] sumDown with | .ok (.number n) => n == 6 | _ => false
#guard inferProgram sumDown == some .number

/-- `let i = 0; while (true) { i = i + 1; if (i - 3) {} else { break; } } i` -/
def breakOut : Expr :=
  .let_ true none (num 0)
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
  .let_ true none (num 1)
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

example : HasType L [] [] none .synth .synth early .string :=
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
example : ¬ HasType L [] [] none .synth .synth (.ret (num 1)) τ := fun h => by
  obtain ⟨_, -, h⟩ := h.top_synth; cases h

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
def counter : Expr := .obj ["value", "inc"] [num 0, .func 0 incBody] [.data, .data]

/-- `c.inc().inc().value`: `inc`'s `this` is the receiver's type, which holds
`inc`, so it is recursive (`μt. {value: Number, inc: (this: t) => t}`), and
the chain types as inty's does. -/
def chained : Expr := .let_ false none counter (.get (.mcall (.mcall (.var 0) "inc" []) "inc" []) "value")

#guard inferProgram chained == some .number
#guard match eval 20 [] [] chained with | .ok (.number n) => n == 2 | _ => false

-- `(0, c.inc)()`: a call outside a receiver gives `inc` an `undefined`
-- `this`, which has no `value`.
#guard inferProgram (.let_ false none counter (.app (.get (.var 0) "inc") [])) == none

-- A method that doesn't use `this` can be called outside its object.
#guard inferProgram (.let_ false none (.obj ["m"] [.func 0 (num 1)] [.data]) (.app (.get (.var 0) "m") [])) ==
  some .number

/-! A method written `inc() {…}` runs as `inc: function () {…}` does, but
its `this` is the literal's type, as inty types it (`shared_this`). -/

/-- `const c = {value: 0, inc() {…}}`. -/
def counterM : Expr := .obj ["value", "inc"] [num 0, .func 0 incBody] [.data, .method]

#guard inferProgram (.let_ false none counterM (.get (.mcall (.mcall (.var 0) "inc" []) "inc" []) "value"))
  == some .number

-- Even a method that doesn't use `this` needs its object as the receiver.
#guard inferProgram (.let_ false none (.obj ["m"] [.func 0 (num 1)] [.method]) (.app (.get (.var 0) "m") []))
  == none

-- `({v: "s", m: o.m}).m()`, `o` being `{v: 1, m() { return this.v; }}`: the
-- other object isn't of `o`'s type, so the call is rejected, though it
-- would run; with `m: function () {…}` it is accepted.
#guard inferProgram (.let_ false none (.obj ["v", "m"] [num 1, .func 0 (.get (.var 1) "v")] [.data, .method])
  (.mcall (.obj ["v", "m"] [str "s", .get (.var 0) "m"] [.data, .data]) "m" [])) == none
#guard inferProgram (.let_ false none (.obj ["v", "m"] [num 1, .func 0 (.get (.var 1) "v")] [.data, .data])
  (.mcall (.obj ["v", "m"] [str "s", .get (.var 0) "m"] [.data, .data]) "m" [])) == some .string

/-! A getter, `get g() {…}`, runs when its property is read, with the
object as `this`; a store to it is rejected, and would throw. -/

/-- `{v: 1, get twice() { return this.v + this.v; }}`. -/
def withGetter : Expr :=
  .obj ["v", "twice"] [num 1, .func 0 (.ret (.binop .plus (.get (.var 1) "v") (.get (.var 1) "v")))]
    [.data, .getter]

#guard inferProgram (.let_ false none withGetter (.get (.var 0) "twice")) == some .number
#guard match eval 20 [] [] (.let_ false none withGetter (.get (.var 0) "twice")) with
  | .ok (.number n) => n == 2 | _ => false
#guard inferProgram (.let_ false none withGetter (.set (.var 0) "twice" (num 3))) == none
#guard match eval 20 [] [] (.let_ false none withGetter (.set (.var 0) "twice" (num 3))) with
  | .stuck .readOnly => true | _ => false
-- A spread copies what the getter gives, as a field that holds a value.
#guard inferProgram (.let_ false none withGetter
  (.set (.spread (.obj [] [] []) (.var 0)) "twice" (num 3))) == some .number

/-- `class C { constructor(v) { this.v = v; } get() { return this.v; } }`:
a constructor returning the instance, a field `v` and a method `get` on
the prototype. -/
def classC : Expr :=
  .ctor 1 (.ret (.cls ["v", "get"] [.var 0, .func 0 (.get (.var 1) "v")] [.data, .method]))

#guard inferProgram (.let_ false none classC (.mcall (.new_ (.var 0) [num 1]) "get" [])) == some .number
#guard match eval 20 [] [] (.let_ false none classC (.mcall (.new_ (.var 0) [str "a"]) "get" [])) with
  | .ok (.string s) => s == "a" | _ => false
-- A class is called with `new`.
#guard inferProgram (.let_ false none classC (.mcall (.app (.var 0) [num 1]) "get" [])) == none
-- A spread copies an instance's own fields, not its prototype's methods.
#guard inferProgram (.let_ false none classC
  (.mcall (.spread (.new_ (.var 0) [num 1]) (.obj ["w"] [num 2] [.data])) "get" [])) == none
#guard inferProgram (.let_ false none classC
  (.get (.spread (.new_ (.var 0) [num 1]) (.obj ["w"] [num 2] [.data])) "v")) == some .number
-- A method isn't a field one can store to.
#guard inferProgram (.let_ false none classC
  (.set (.new_ (.var 0) [num 1]) "get" (.func 0 (num 1)))) == none

/-- `class D { a = 1; b = this.a + 1; f = () => this.b; }`: a field's
initialiser reads the fields before it (as variables, `this.a` being the
latest), and an arrow field's `this` is the instance, whatever it is
called on. -/
def classD : Expr :=
  .ctor 0 (.ret (.cls ["a", "b", "f"]
    [num 1, .binop .plus (.var 0) (num 1), .func 0 (.ret (.get (.var 1) "b"))] [.data, .data, .arrow]))

#guard inferProgram (.let_ false none classD (.app (.get (.new_ (.var 0) []) "f") [])) == some .number
#guard match eval 20 [] [] (.let_ false none classD (.app (.get (.new_ (.var 0) []) "f") [])) with
  | .ok (.number n) => n == 2 | _ => false
-- An arrow function isn't a constructor: `new` on an arrow field throws a
-- `TypeError` in JavaScript, and is stuck here (`Value.asCtor`). Its `this`
-- is `NotNew`, so it isn't typed.
#guard inferProgram (.let_ false none classD (.new_ (.get (.new_ (.var 0) []) "f") [])) == none
#guard match eval 20 [] [] (.let_ false none classD (.new_ (.get (.new_ (.var 0) []) "f") [])) with
  | .stuck _ => true | _ => false
-- A field's initialiser is an expression, outside the constructor's body:
-- a `return` in it (which JavaScript has no syntax for) isn't typed.
#guard inferProgram (.let_ false none (.ctor 0 (.cls ["a"] [.ret (num 1)] [.data]))
  (.get (.new_ (.var 0) []) "a")) == none
-- Read off its instance, it is called on that instance, or outside one.
#guard inferProgram (.let_ false none classD
  (.binop .plus (.mcall (.new_ (.var 0) []) "f" []) (.app (.get (.new_ (.var 0) []) "f") [])))
    == some .number

/-- A getter that stores `v` to `this.a` and gives `0`. -/
def storesA (v : Float) : Expr := .func 0 (.seq (.set (.var 1) "a" (num v)) (num 0))

/-- `{...o}.a`, for `o` the innermost variable. -/
def spreadA : Expr := .get (.spread (.obj [] [] []) (.var 0)) "a"

-- A spread copies an object's properties in the order they were made,
-- running a getter when it reaches it, as JavaScript does: a property
-- stored to keeps its place, one added comes last, and a label defined
-- twice in a literal is where it was first, with its last value.
-- `{get b() { this.a = 5; … }, a: 1}`: the getter runs first.
#guard match eval 20 [] [] (.let_ false none
    (.obj ["b", "a"] [storesA 5, num 1] [.getter, .data]) spreadA) with
  | .ok (.number n) => n == 5 | _ => false
-- `{a: 1, get g() { this.a = 9; … }}; o.a = 2`: `a` is still first.
#guard match eval 20 [] [] (.let_ false none
    (.obj ["a", "g"] [num 1, storesA 9] [.data, .getter])
    (.seq (.set (.var 0) "a" (num 2)) spreadA)) with
  | .ok (.number n) => n == 2 | _ => false
-- `{a: 1, get g() { this.a = 9; … }, a: 3}`: `a` is first, `3`.
#guard match eval 20 [] [] (.let_ false none
    (.obj ["a", "g", "a"] [num 1, storesA 9, num 3] [.data, .getter, .data]) spreadA) with
  | .ok (.number n) => n == 3 | _ => false
-- `{get g() { this.a = 9; … }}; o.a = 2`: `a` comes after the getter.
#guard match eval 20 [] [] (.let_ false none
    (.obj ["g"] [storesA 9] [.getter])
    (.seq (.set (.var 0) "a" (num 2)) spreadA)) with
  | .ok (.number n) => n == 9 | _ => false

-- `function f(x) { return f; }; f(1)(2) - 1`: `f` returns itself, a
-- recursive function type, so `f(1)(2)` is `f`, not a number.
#guard inferProgram (.let_ false none (.func 1 (.var 1))
  (.binop .minus (.app (.app (.var 0) [num 1]) [num 2]) (num 1))) == none

end Inty.Examples
