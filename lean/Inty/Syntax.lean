import Inty.Types

/-!
# Syntax of the core calculus

The core calculus is the fragment of inty's shared AST (`src/ast`)
that this formalization covers so far. Each frontend lowers onto that AST, so
the calculus is language-agnostic in the same way.

Variables are de Bruijn indices: `var 0` is the innermost binder. The
environment of the semantics and the context of the typing judgement are both
lists indexed the same way, so terms are never substituted into.
-/

namespace Inty

/-- Literals. Numbers are IEEE doubles, as in JavaScript and in
`dynamics::Value::Number(f64)`. -/
inductive Lit where
  | number (n : Float)
  | string (s : String)
  | boolean (b : Bool)
  | undefined
  | null
  deriving Repr

/-- Unary operators, a subset of `ast::UnaryOp`. -/
inductive UnOp where
  /-- `!e`: truthiness negation, defined on every type. -/
  | not
  /-- `typeof e`: defined on every type. -/
  | typeof
  /-- `-e`: `Number` only. -/
  | neg
  deriving DecidableEq, Repr

/-- Binary operators, a subset of `ast::BinOp`. -/
inductive BinOp where
  /-- `+`: any instance of the `Plus` class (`Number`, `String`). -/
  | plus
  /-- `-`: `Number` only. -/
  | minus
  deriving DecidableEq, Repr

/-- Expressions. -/
inductive Expr where
  | lit (l : Lit)
  | var (i : Nat)
  /-- A named function of `arity` parameters,
  `function f(x₀, …, xₙ₋₁) { body }`. Inside `body`, `var i` is the
  parameter `xᵢ` for `i < n`, `var n` is the function itself, so functions
  can recurse, as JavaScript's named function expressions can, and
  `var (n + 1)` is `this`. -/
  | func (arity : Nat) (body : Expr)
  /-- A call `f(a₀, …)`, outside any receiver: `this` is `undefined`. -/
  | app (f : Expr) (args : List Expr)
  /-- `const x = e₁; e₂` (`mutable` false) or `let x = e₁; e₂` (`mutable`
  true), with `x` as `var 0` in `e₂`. `x` is generalised when `e₁` is a
  syntactic value and `e₂` never assigns to it. -/
  | let_ (mutable : Bool) (e₁ e₂ : Expr)
  /-- `x = e`, for the variable `var i`: `e`'s value, stored in `x`. -/
  | assign (i : Nat) (e : Expr)
  /-- `c ? t : e`. The test may have any type and is read by truthiness, as
  in `dynamics::Value::truthy`. -/
  | cond (c t e : Expr)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  /-- `return e;`: leaves the enclosing function with `e`'s value. -/
  | ret (e : Expr)
  /-- `throw e;`. -/
  | throw_ (e : Expr)
  /-- `e₁; e₂`: `e₁` for its effects, then `e₂`. -/
  | seq (e₁ e₂ : Expr)
  /-- `while (c) body`; it completes with `undefined`. -/
  | while_ (c body : Expr)
  /-- `break;`, out of the innermost loop. -/
  | break_
  /-- `continue;`, to the innermost loop's next test. -/
  | continue_
  /-- `try { body } catch (e) { handler }`, with `e` as `var 0` in
  `handler`. -/
  | tryCatch (body handler : Expr)
  /-- `try { body } finally { fin }`: `fin` runs however `body` completes,
  and its own abrupt completion, if any, wins. -/
  | tryFinally (body fin : Expr)
  deriving Repr

/-- Syntactic values, which the value restriction lets a `const` generalise:
`is_syntactic_value` in `src/infer/features/bindings.rs`. -/
inductive Expr.IsValue : Expr → Prop where
  | lit : Expr.IsValue (.lit l)
  | var : Expr.IsValue (.var i)
  | func : Expr.IsValue (.func n body)

/-- Induction on `Expr`, with a hypothesis for each argument of a call. -/
theorem Expr.ind {motive : Expr → Prop} (lit : ∀ l, motive (.lit l))
    (var : ∀ i, motive (.var i)) (func : ∀ n body, motive body → motive (.func n body))
    (app : ∀ f args, motive f → (∀ a ∈ args, motive a) → motive (.app f args))
    (let_ : ∀ m e₁ e₂, motive e₁ → motive e₂ → motive (.let_ m e₁ e₂))
    (assign : ∀ i e, motive e → motive (.assign i e))
    (cond : ∀ c t e, motive c → motive t → motive e → motive (.cond c t e))
    (unop : ∀ op e, motive e → motive (.unop op e))
    (binop : ∀ op e₁ e₂, motive e₁ → motive e₂ → motive (.binop op e₁ e₂))
    (ret : ∀ e, motive e → motive (.ret e)) (throw_ : ∀ e, motive e → motive (.throw_ e))
    (seq : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (.seq e₁ e₂))
    (while_ : ∀ c body, motive c → motive body → motive (.while_ c body))
    (break_ : motive .break_) (continue_ : motive .continue_)
    (tryCatch : ∀ body handler, motive body → motive handler → motive (.tryCatch body handler))
    (tryFinally : ∀ body fin, motive body → motive fin → motive (.tryFinally body fin)) :
    ∀ e, motive e
  | .lit l => lit l
  | .var i => var i
  | .func n body => func n body (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally body)
  | .app f args =>
    app f args (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally f)
      (fun a _ => Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally a)
  | .let_ m e₁ e₂ =>
    let_ m e₁ e₂ (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₁)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₂)
  | .cond c t e =>
    cond c t e (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally c)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally t)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e)
  | .assign i e => assign i e (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e)
  | .unop op e => unop op e (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e)
  | .binop op e₁ e₂ =>
    binop op e₁ e₂ (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₁)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₂)
  | .ret e => ret e (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e)
  | .throw_ e => throw_ e (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e)
  | .seq e₁ e₂ =>
    seq e₁ e₂ (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₁)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally e₂)
  | .while_ c body =>
    while_ c body
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally c)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally body)
  | .break_ => break_
  | .continue_ => continue_
  | .tryCatch body handler =>
    tryCatch body handler
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally body)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally handler)
  | .tryFinally body fin =>
    tryFinally body fin
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally body)
      (Expr.ind lit var func app let_ assign cond unop binop ret throw_ seq while_ break_ continue_
        tryCatch tryFinally fin)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)

mutual
/-- Whether `e` assigns to the variable `var i` (in a function in it, too). -/
def Expr.writes (i : Nat) : Expr → Bool
  | .lit _ | .var _ => false
  | .func n body => body.writes (i + n + 2)
  | .app f args => f.writes i || Expr.writesList i args
  | .let_ _ e₁ e₂ => e₁.writes i || e₂.writes (i + 1)
  | .assign j e => j == i || e.writes i
  | .cond c t e => c.writes i || t.writes i || e.writes i
  | .unop _ e | .ret e | .throw_ e => e.writes i
  | .binop _ e₁ e₂ | .seq e₁ e₂ | .while_ e₁ e₂ | .tryFinally e₁ e₂ => e₁.writes i || e₂.writes i
  | .break_ | .continue_ => false
  | .tryCatch body handler => body.writes i || handler.writes (i + 1)
/-- `writes`, for a list of arguments. -/
def Expr.writesList (i : Nat) : List Expr → Bool
  | [] => false
  | e :: es => e.writes i || Expr.writesList i es
end

mutual
/-- Whether every assignment is to a variable `mutables` says is mutable: a
`let` or a parameter, not a `const`, a function's own name (which a named
function expression binds immutably) or `this`. inty rejects assigning to
a `const` (`check_assignment_target`). It is a scope check beside the
typing rules, not one of them: the assignment would be type-safe. -/
def Expr.assignsMutable (mutables : List Bool) : Expr → Bool
  | .lit _ | .var _ => true
  | .func n body => body.assignsMutable (List.replicate n true ++ false :: false :: mutables)
  | .app f args => f.assignsMutable mutables && Expr.assignsMutableList mutables args
  | .let_ m e₁ e₂ => e₁.assignsMutable mutables && e₂.assignsMutable (m :: mutables)
  | .assign j e => mutables[j]? == some true && e.assignsMutable mutables
  | .cond c t e => c.assignsMutable mutables && t.assignsMutable mutables &&
      e.assignsMutable mutables
  | .unop _ e | .ret e | .throw_ e => e.assignsMutable mutables
  | .binop _ e₁ e₂ | .seq e₁ e₂ | .while_ e₁ e₂ | .tryFinally e₁ e₂ =>
    e₁.assignsMutable mutables && e₂.assignsMutable mutables
  | .break_ | .continue_ => true
  -- What a `catch` binds can be assigned.
  | .tryCatch body handler =>
    body.assignsMutable mutables && handler.assignsMutable (true :: mutables)
/-- `assignsMutable`, for a list of arguments. -/
def Expr.assignsMutableList (mutables : List Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.assignsMutable mutables && Expr.assignsMutableList mutables es
end

mutual
/-- Whether every `break` and `continue` is inside a loop (`inLoop`) of the
same function: JavaScript rejects the program otherwise. -/
def Expr.jumpsInLoop (inLoop : Bool) : Expr → Bool
  | .lit _ | .var _ => true
  | .func _ body => body.jumpsInLoop false
  | .app f args => f.jumpsInLoop inLoop && Expr.jumpsInLoopList inLoop args
  | .let_ _ e₁ e₂ | .binop _ e₁ e₂ | .seq e₁ e₂ | .tryCatch e₁ e₂ | .tryFinally e₁ e₂ =>
    e₁.jumpsInLoop inLoop && e₂.jumpsInLoop inLoop
  | .assign _ e | .unop _ e | .ret e | .throw_ e => e.jumpsInLoop inLoop
  | .cond c t e => c.jumpsInLoop inLoop && t.jumpsInLoop inLoop && e.jumpsInLoop inLoop
  | .while_ c body => c.jumpsInLoop inLoop && body.jumpsInLoop true
  | .break_ | .continue_ => inLoop
/-- `jumpsInLoop`, for a list of arguments. -/
def Expr.jumpsInLoopList (inLoop : Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.jumpsInLoop inLoop && Expr.jumpsInLoopList inLoop es
end

/-- The checks beside the typing rules, both of scope: assignments only to
mutable variables, `break` and `continue` only in loops. -/
def Expr.scoped (mutables : List Bool) (e : Expr) : Bool :=
  e.assignsMutable mutables && e.jumpsInLoop false

end Inty
