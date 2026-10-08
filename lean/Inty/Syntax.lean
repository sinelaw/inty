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
  /-- `const x = e₁; e₂`, with `x` as `var 0` in `e₂`. `x` is generalised
  when `e₁` is a syntactic value. -/
  | let_ (e₁ e₂ : Expr)
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
    (let_ : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (.let_ e₁ e₂))
    (cond : ∀ c t e, motive c → motive t → motive e → motive (.cond c t e))
    (unop : ∀ op e, motive e → motive (.unop op e))
    (binop : ∀ op e₁ e₂, motive e₁ → motive e₂ → motive (.binop op e₁ e₂))
    (ret : ∀ e, motive e → motive (.ret e)) (throw_ : ∀ e, motive e → motive (.throw_ e))
    (seq : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (.seq e₁ e₂)) : ∀ e, motive e
  | .lit l => lit l
  | .var i => var i
  | .func n body => func n body (Expr.ind lit var func app let_ cond unop binop ret throw_ seq body)
  | .app f args =>
    app f args (Expr.ind lit var func app let_ cond unop binop ret throw_ seq f)
      (fun a _ => Expr.ind lit var func app let_ cond unop binop ret throw_ seq a)
  | .let_ e₁ e₂ =>
    let_ e₁ e₂ (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₁)
      (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₂)
  | .cond c t e =>
    cond c t e (Expr.ind lit var func app let_ cond unop binop ret throw_ seq c)
      (Expr.ind lit var func app let_ cond unop binop ret throw_ seq t)
      (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e)
  | .unop op e => unop op e (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e)
  | .binop op e₁ e₂ =>
    binop op e₁ e₂ (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₁)
      (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₂)
  | .ret e => ret e (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e)
  | .throw_ e => throw_ e (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e)
  | .seq e₁ e₂ =>
    seq e₁ e₂ (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₁)
      (Expr.ind lit var func app let_ cond unop binop ret throw_ seq e₂)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)

end Inty
