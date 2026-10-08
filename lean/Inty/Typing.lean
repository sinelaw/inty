import Inty.Syntax
import Inty.Types

/-!
# Declarative typing

`HasType C Γ e τ` is the specification the inference engine (`src/infer`)
implements: it says which types an expression may have, not how to find one.
`C` lists the types assumed to be `Plus` instances: a polymorphic function
whose body uses `+` on its parameter is typed assuming its scheme's
constraints, and each use of it must establish them.

The operator rules are split out as `UnOpTy` / `BinOpTy`, one constructor per
operator rule, mirroring the operator catalog in `src/operators`. Type-class
instances are `PlusInst`, mirroring the instance tables in `src/classes`.
-/

namespace Inty

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

/-- `τ` is a `Plus` instance, or assumed to be one. -/
def Entails (C : List Ty) (τ : Ty) : Prop := PlusInst τ ∨ τ ∈ C

/-- Typing rules of the binary operators under assumptions `C`: operand
types, result type. Both operands of `+` have the same type, one instance of
`Plus`: inty's `+` never mixes a `Number` with a `String`. -/
inductive BinOpTy (C : List Ty) : BinOp → Ty → Ty → Ty → Prop where
  | plus : Entails C τ → BinOpTy C .plus τ τ τ
  | minus : BinOpTy C .minus .number .number .number

/-- The typing judgement: under the `Plus` assumptions `C` and the context
`Γ`, `e` has type `τ`. -/
inductive HasType : List Ty → Ctx → Expr → Ty → Prop where
  | lit : LitTy l τ → HasType C Γ (.lit l) τ
  /-- A variable has any instance of its scheme whose constraints hold. -/
  | var : Γ[i]? = some s → τs.length = s.arity →
      (∀ c ∈ s.instPlus τs, Entails C c) →
      HasType C Γ (.var i) (s.inst τs)
  | func : HasType C (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ) body τ₂ →
      HasType C Γ (.func body) (.arrow τ₁ τ₂)
  | app : HasType C Γ f (.arrow τ₁ τ₂) → HasType C Γ a τ₁ →
      HasType C Γ (.app f a) τ₂
  /-- `const x = e₁; e₂` gives `x` a scheme `s`. The first premise says `e₁`
  has every opening of `s` at fresh type variables, assuming the opened
  constraints: `m` ranges over all starting points above a finite set `L`,
  which is how a locally nameless development says "for fresh variables"
  (cofinite quantification). It implies the usual side condition, that the
  generalised variables don't occur free in `Γ`. Under the value restriction
  only a syntactic value generalises; anything else gets a scheme with no
  quantified variables and no constraints. -/
  | let_ (s : Scheme) (L : List Nat) :
      (∀ m, (∀ a ∈ L, a < m) → HasType (C ++ s.openPlus m) Γ e₁ (s.open m)) →
      (s.arity = 0 ∧ s.plus = []) ∨ e₁.IsValue →
      HasType C (s :: Γ) e₂ τ₂ →
      HasType C Γ (.let_ e₁ e₂) τ₂
  /-- Both branches have one type, as in Hindley–Milner: inty doesn't guess
  that disagreeing branches form a union. -/
  | cond : HasType C Γ c τc → HasType C Γ t τ → HasType C Γ e τ →
      HasType C Γ (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasType C Γ e τ₁ →
      HasType C Γ (.unop op e) τ
  | binop : BinOpTy C op τ₁ τ₂ τ → HasType C Γ e₁ τ₁ → HasType C Γ e₂ τ₂ →
      HasType C Γ (.binop op e₁ e₂) τ

/-- A variable whose scheme is a monotype has that type. -/
theorem HasType.var_mono (h : Γ[i]? = some (Scheme.mono τ)) :
    HasType C Γ (.var i) τ := by
  simpa using HasType.var (C := C) (τs := []) h rfl (by simp [Scheme.instPlus, Scheme.mono])

/-- A monomorphic `const`. -/
theorem HasType.let_mono (h₁ : HasType C Γ e₁ τ₁)
    (h₂ : HasType C (.mono τ₁ :: Γ) e₂ τ₂) : HasType C Γ (.let_ e₁ e₂) τ₂ :=
  .let_ (.mono τ₁) [] (fun _ _ => by simpa [Scheme.open, Scheme.openPlus,
    Scheme.instPlus, Scheme.mono, Scheme.inst] using h₁) (.inl ⟨rfl, rfl⟩) h₂

end Inty
