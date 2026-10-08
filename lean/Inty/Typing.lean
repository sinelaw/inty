import Inty.Syntax
import Inty.Types

/-!
# Declarative typing

`HasType Γ e τ` is the specification the inference engine (`src/infer`)
implements: it says which types an expression may have, not how to find one.
Inference soundness and completeness against it is a later layer.

The operator rules are split out as `UnOpTy` / `BinOpTy`, one constructor per
operator rule, mirroring the operator catalog in `src/operators`. Type-class
instances are `PlusInst`, mirroring the instance tables in `src/classes`.
-/

namespace Inty

/-- A typing context: the type scheme of each variable, innermost first. -/
abbrev Ctx := List Scheme

/-- Instances of the `Plus` class: the types `+` is defined on. -/
inductive PlusInst : Ty → Prop where
  | number : PlusInst .number
  | string : PlusInst .string

/-- The type of a literal: its base type. Literal types (`42`, `"err"`) come
later, and so does `Int`: inty types an integral literal as `Int` or
`Number`, and this calculus folds both into `number`. -/
inductive LitTy : Lit → Ty → Prop where
  | number : LitTy (.number n) .number
  | string : LitTy (.string s) .string
  | boolean : LitTy (.boolean b) .boolean
  | undefined : LitTy .undefined .undefined
  | null : LitTy .null .null

/-- Typing rules of the unary operators: operand type, result type. -/
inductive UnOpTy : UnOp → Ty → Ty → Prop where
  | not : UnOpTy .not τ .boolean
  | typeof : UnOpTy .typeof τ .string
  | neg : UnOpTy .neg .number .number

/-- Typing rules of the binary operators: operand types, result type. Both
operands of `+` have the same type, one instance of `Plus`: inty's `+` never
mixes a `Number` with a `String`. -/
inductive BinOpTy : BinOp → Ty → Ty → Ty → Prop where
  | plus : PlusInst τ → BinOpTy .plus τ τ τ
  | minus : BinOpTy .minus .number .number .number

/-- The typing judgement. -/
inductive HasType : Ctx → Expr → Ty → Prop where
  | lit : LitTy l τ → HasType Γ (.lit l) τ
  /-- A variable has any instance of its scheme. -/
  | var : Γ[i]? = some s → τs.length = s.arity →
      HasType Γ (.var i) (s.inst τs)
  | func : HasType (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ) body τ₂ →
      HasType Γ (.func body) (.arrow τ₁ τ₂)
  | app : HasType Γ f (.arrow τ₁ τ₂) → HasType Γ a τ₁ →
      HasType Γ (.app f a) τ₂
  /-- `const x = e₁; e₂` gives `x` a scheme `s`. The first premise says `e₁`
  has every opening of `s` at fresh type variables: `m` ranges over all
  starting points above a finite set `L`, which is how a locally nameless
  development says "for fresh variables" (cofinite quantification). It
  implies the usual side condition, that the generalised variables don't
  occur free in `Γ`. Under the value restriction only a syntactic value
  generalises; anything else gets a scheme of arity 0. -/
  | let_ (s : Scheme) (L : List Nat) :
      (∀ m, (∀ a ∈ L, a < m) → HasType Γ e₁ (s.open m)) →
      s.arity = 0 ∨ e₁.IsValue →
      HasType (s :: Γ) e₂ τ₂ →
      HasType Γ (.let_ e₁ e₂) τ₂
  /-- Both branches have one type, as in Hindley–Milner: inty doesn't guess
  that disagreeing branches form a union. -/
  | cond : HasType Γ c τc → HasType Γ t τ → HasType Γ e τ →
      HasType Γ (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasType Γ e τ₁ →
      HasType Γ (.unop op e) τ
  | binop : BinOpTy op τ₁ τ₂ τ → HasType Γ e₁ τ₁ → HasType Γ e₂ τ₂ →
      HasType Γ (.binop op e₁ e₂) τ

/-- A variable whose scheme is a monotype has that type. -/
theorem HasType.var_mono (h : Γ[i]? = some (Scheme.mono τ)) :
    HasType Γ (.var i) τ := by
  simpa using HasType.var (τs := []) h rfl

/-- A monomorphic `const`. -/
theorem HasType.let_mono (h₁ : HasType Γ e₁ τ₁)
    (h₂ : HasType (.mono τ₁ :: Γ) e₂ τ₂) : HasType Γ (.let_ e₁ e₂) τ₂ :=
  .let_ (.mono τ₁) [] (fun _ _ => by simpa [Scheme.open] using h₁) (.inl rfl) h₂

end Inty
