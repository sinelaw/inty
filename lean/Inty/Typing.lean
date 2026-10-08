import Inty.Syntax
import Inty.Classes

/-!
# Declarative typing

`HasType L C Γ R e τ` is the specification the inference engine (`src/infer`)
implements: it says which types an expression may have, not how to find one.
`C` lists the class constraints assumed to hold: a polymorphic function
whose body uses `+` on its parameter is typed assuming its scheme's
constraints (`Plus a`), and each use of it must establish them.

The operator rules are split out as `UnOpTy` / `BinOpTy`, one constructor per
operator rule, mirroring the operator catalog in `src/operators`. Class
instances and entailment are in `Inty.Classes`.
-/

namespace Inty

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

/-- Typing rules of the binary operators under assumptions `C`: operand
types, result type. Both operands of `+` have the same type, one instance of
`Plus`: inty's `+` never mixes a `Number` with a `String`. -/
inductive BinOpTy (C : List Pred) : BinOp → Ty → Ty → Ty → Prop where
  | plus : Entails C ⟨.plus, [τ]⟩ → BinOpTy C .plus τ τ τ
  | minus : BinOpTy C .minus .number .number .number

/-- A scheme's constraints are on its quantified variables: `Plus a`, as in
`<a> where Plus a => …`, or `HasProp l a σ`, as in
`<a, b> where a has {name: b} => …`. inty decides a constraint on a type
already known when it generalises (`InferState::generalize`), so no scheme
carries one that could fail at a use; and a `HasProp` whose receiver the
environment fixes fixes its field type too (`env_fixed_vars`), so it stays
outside the scheme.

A `Merge` is different: its decision waits for the operand's presence,
which a later substitution may decide, so it stays in the scheme as it is
whatever its presence, as long as it mentions one of the scheme's
variables in the arguments that determine its result. (Deciding it when
the presence is known would make the rule depend on when that is, which
no rule closed under substitution can.) -/
def Scheme.Simple (s : Scheme) : Prop :=
  ∀ p ∈ s.preds, (∃ i < s.arity,
    p = ⟨.plus, [.bound i]⟩ ∨ ∃ l σ, p = ⟨.hasProp l, [.bound i, σ]⟩) ∨
    ∃ q τ t r, p = ⟨.merge, [q, τ, t, r]⟩ ∧ ∃ i ∈ q.bvs ++ τ.bvs ++ t.bvs, i < s.arity

/-- The typing judgement: with records over the program's labels `L`, under
the class assumptions `C`, the context `Γ` and the enclosing function's
return type `R` (`none` at the top level), `e` has type `τ`. -/
inductive HasType (L : List String) : List Pred → Ctx → Option Ty → Expr → Ty → Prop where
  | lit : LitTy l τ → HasType L C Γ R (.lit l) τ
  /-- A variable has any instance of its scheme whose constraints hold. -/
  | var : Γ[i]? = some s → τs.length = s.arity →
      (∀ c ∈ s.instPreds τs, Entails C c) →
      HasType L C Γ R (.var i) (s.inst τs)
  /-- A function's body sees its parameters, itself and `this`, and returns
  `ρ`, by `return` or as its value. -/
  | func : τs.length = n →
      HasType L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) body ρ →
      HasType L C Γ R (.func n body) (.fn θ τs ρ)
  /-- A call has one argument per parameter, each of its parameter's type. A
  call outside any receiver binds `this` to `undefined`, so the function's
  `this` type must be `undefined`: inty unifies it with `Undefined`
  (`src/infer/features/functions.rs`), which rejects a detached method. -/
  | app : HasType L C Γ R f (.fn .undefined τs ρ) → args.length = τs.length →
      (∀ p ∈ args.zip τs, HasType L C Γ R p.1 p.2) →
      HasType L C Γ R (.app f args) ρ
  /-- `const x = e₁; e₂` or `let x = e₁; e₂` gives `x` a scheme `s`. The
  first premise says `e₁` has every opening of `s` at fresh type variables,
  assuming the opened constraints: `m` ranges over all starting points
  above a finite set `F`, which is how a locally nameless development says
  "for fresh variables" (cofinite quantification). It implies the usual
  side condition, that the generalised variables don't occur free in `Γ`.
  Only a syntactic value generalises (the value restriction), and only if
  `e₂` never assigns to `x`: a `let` that is written has one type, which
  each assignment must have. Otherwise `s` quantifies nothing and has no
  constraints. Its constraints are on its quantified variables
  (`Scheme.Simple`). -/
  | let_ (s : Scheme) (F : List Nat) :
      (∀ m, (∀ a ∈ F, a < m) → HasType L (C ++ s.openPreds m) Γ R e₁ (s.open m)) →
      (s.arity = 0 ∧ s.preds = []) ∨ (e₁.IsValue ∧ e₂.writes 0 = false) → s.Simple →
      HasType L C (s :: Γ) R e₂ τ₂ →
      HasType L C Γ R (.let_ mb e₁ e₂) τ₂
  /-- `x = e` stores a value of `x`'s type, which is a monotype: a binding
  that is assigned is never generalised. Its value is the assignment's.
  (That `x` is a `let` or a parameter, not a `const`, is checked apart,
  by `Expr.assignsMutable`.) -/
  | assign : Γ[i]? = some s → s.arity = 0 → s.preds = [] → HasType L C Γ R e (s.inst []) →
      HasType L C Γ R (.assign i e) (s.inst [])
  /-- Both branches have one type, as in Hindley–Milner: inty doesn't guess
  that disagreeing branches form a union. -/
  | cond : HasType L C Γ R c τc → HasType L C Γ R t τ → HasType L C Γ R e τ →
      HasType L C Γ R (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasType L C Γ R e τ₁ →
      HasType L C Γ R (.unop op e) τ
  | binop : BinOpTy C op τ₁ τ₂ τ → HasType L C Γ R e₁ τ₁ → HasType L C Γ R e₂ τ₂ →
      HasType L C Γ R (.binop op e₁ e₂) τ
  /-- `return e;` gives the enclosing function's return type; it doesn't
  complete, so it may stand for any type. -/
  | ret : HasType L C Γ (some τr) e τr → HasType L C Γ (some τr) (.ret e) τ
  /-- `throw e;` throws any value and doesn't complete. -/
  | throw_ : HasType L C Γ R e τe → HasType L C Γ R (.throw_ e) τ
  | seq : HasType L C Γ R e₁ τ₁ → HasType L C Γ R e₂ τ → HasType L C Γ R (.seq e₁ e₂) τ
  /-- `while (c) body`: any test, read by truthiness; it completes with
  `undefined` (`infer_stmt_while`). -/
  | while_ : HasType L C Γ R c τc → HasType L C Γ R body τb → HasType L C Γ R (.while_ c body) .undefined
  /-- `break;` and `continue;` don't complete, so they stand for any type.
  (That they are in a loop is checked apart, by `Expr.jumpsInLoop`.) -/
  | break_ : HasType L C Γ R .break_ τ
  | continue_ : HasType L C Γ R .continue_ τ
  /-- `try { body } catch (e) { handler }`: anything can be thrown, so `e`
  has the opaque type `unknown` (inty's rigid type variable). -/
  | tryCatch : HasType L C Γ R body τ → HasType L C (.mono .unknown :: Γ) R handler τ →
      HasType L C Γ R (.tryCatch body handler) τ
  /-- `try { body } finally { fin }` has `body`'s type; `fin`'s value is
  dropped. -/
  | tryFinally : HasType L C Γ R body τ → HasType L C Γ R fin τf →
      HasType L C Γ R (.tryFinally body fin) τ
  /-- An object literal has a record type over the program's labels, with
  its fields present (`objSlots`). -/
  | obj : τs.length = ls.length → absent.length = L.length → (∀ l ∈ ls, l ∈ L) →
      es.length = ls.length → (∀ p ∈ es.zip τs, HasType L C Γ R p.1 p.2) →
      HasType L C Γ R (.obj ls es) (.record L (objSlots L ls τs absent))
  /-- `e.l` reads a field of `e`'s type, `HasProp l τ σ`: a present field of
  a record, or what a scheme's constraint promises. -/
  | get : HasType L C Γ R e τ → Entails C ⟨.hasProp l, [τ, σ]⟩ →
      HasType L C Γ R (.get e l) σ
  /-- `e.l = v` stores a value of the field's type, which is the
  assignment's. -/
  | set : HasType L C Γ R e τ → Entails C ⟨.hasProp l, [τ, σ]⟩ → HasType L C Γ R v σ →
      HasType L C Γ R (.set e l v) σ
  /-- `{...e₁, ...e₂}`: `e₂`'s slot for each label, with presence `p` and
  type `τ`, merged over `e₁`'s slot `s` gives the result's slot `r`
  (`Merge p τ s r`): `e₂`'s field if it has one, `e₁`'s if not. -/
  | spread : ps.length = L.length → τs.length = L.length → ss.length = L.length →
      rs.length = L.length →
      HasType L C Γ R e₁ (.record L ss) →
      HasType L C Γ R e₂ (.record L (List.zipWith Ty.slot ps τs)) →
      (∀ p ∈ mergePreds ps τs ss rs, Entails C p) →
      HasType L C Γ R (.spread e₁ e₂) (.record L rs)

/-- A variable whose scheme is a monotype has that type. -/
theorem HasType.var_mono (h : Γ[i]? = some (Scheme.mono τ)) :
    HasType L C Γ R (.var i) τ := by
  simpa using HasType.var (C := C) (R := R) (τs := []) h rfl (by simp [Scheme.instPreds, Scheme.mono])

/-- A monomorphic `const`. -/
theorem HasType.let_mono (h₁ : HasType L C Γ R e₁ τ₁)
    (h₂ : HasType L C (.mono τ₁ :: Γ) R e₂ τ₂) : HasType L C Γ R (.let_ mb e₁ e₂) τ₂ :=
  .let_ (.mono τ₁) [] (fun _ _ => by simpa [Scheme.open, Scheme.openPreds,
    Scheme.instPreds, Scheme.mono, Scheme.inst] using h₁) (.inl ⟨rfl, rfl⟩)
    (fun _ h => by simp [Scheme.mono] at h) h₂

end Inty
