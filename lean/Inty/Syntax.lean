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
  /-- A named function of one parameter, `function f(x) { return body; }`.
  Inside `body`, `var 0` is the parameter and `var 1` is the function itself,
  so functions can recurse, as JavaScript's named function expressions can. -/
  | func (body : Expr)
  | app (f a : Expr)
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
  | func : Expr.IsValue (.func body)

end Inty
