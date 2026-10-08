import Inty.Syntax

/-!
# Declarative typing

`HasType Γ e τ` is the specification the inference engine (`src/infer`)
implements: it says which types an expression may have, not how to find one.
Inference soundness and completeness against it is a later layer.

The operator rules are split out as `UnOpTy` / `BinOpTy`, one constructor per
typing arm, mirroring the operator catalog in `src/operators`. Type-class
instances are `PlusInst`, mirroring the instance tables in `src/classes`.
-/

namespace Inty

/-- A typing context: the type of each variable, innermost first. -/
abbrev Ctx := List Ty

/-- Instances of the `Plus` class: the types `+` is defined on. -/
inductive PlusInst : Ty → Prop where
  | number : PlusInst .number
  | string : PlusInst .string

/-- The type of a literal. Literal types (`42`, `"err"`) come later; for now a
literal has its base type, as after widening. -/
inductive LitTy : Lit → Ty → Prop where
  | number : LitTy (.number n) .number
  | string : LitTy (.string s) .string
  | boolean : LitTy (.boolean b) .boolean
  | undefined : LitTy .undefined .undefined
  | null : LitTy .null .null

/-- Typing arms of the unary operators: operand type, result type. -/
inductive UnOpTy : UnOp → Ty → Ty → Prop where
  | not : UnOpTy .not τ .boolean
  | typeof : UnOpTy .typeof τ .string
  | neg : UnOpTy .neg .number .number

/-- Typing arms of the binary operators: operand types, result type. Both
operands of `+` have the same type, one instance of `Plus`: inty's `+` never
mixes a `Number` with a `String`. -/
inductive BinOpTy : BinOp → Ty → Ty → Ty → Prop where
  | plus : PlusInst τ → BinOpTy .plus τ τ τ
  | minus : BinOpTy .minus .number .number .number

/-- The typing judgement. -/
inductive HasType : Ctx → Expr → Ty → Prop where
  | lit : LitTy l τ → HasType Γ (.lit l) τ
  | var : Γ[i]? = some τ → HasType Γ (.var i) τ
  | func : HasType (τ₁ :: .arrow τ₁ τ₂ :: Γ) body τ₂ →
      HasType Γ (.func body) (.arrow τ₁ τ₂)
  | app : HasType Γ f (.arrow τ₁ τ₂) → HasType Γ a τ₁ →
      HasType Γ (.app f a) τ₂
  | let_ : HasType Γ e₁ τ₁ → HasType (τ₁ :: Γ) e₂ τ₂ →
      HasType Γ (.let_ e₁ e₂) τ₂
  /-- Both branches have one type, as in Hindley–Milner: inty doesn't guess
  that disagreeing branches form a union. -/
  | cond : HasType Γ c τc → HasType Γ t τ → HasType Γ e τ →
      HasType Γ (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasType Γ e τ₁ →
      HasType Γ (.unop op e) τ
  | binop : BinOpTy op τ₁ τ₂ τ → HasType Γ e₁ τ₁ → HasType Γ e₂ τ₂ →
      HasType Γ (.binop op e₁ e₂) τ

end Inty
