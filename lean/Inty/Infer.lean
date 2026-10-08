import Inty.Unify
import Inty.Classes
import Inty.Syntax

/-!
# Type inference

Algorithm W (Damas and Milner) for the calculus: an executable function that
finds a type, where `HasType` only says which types are valid. It mirrors the
structure of `src/infer`, minus its destructive unification and constraint
solver.

Unification is in `Inty.Unify`, proved sound and most general. Class
constraints are not solved as they arise:

- `+` records the constraint `Plus τ` on its operand type `τ`.
  A `const` that generalises a variable takes the constraints mentioning it
  into its scheme (inty's `<a> where Plus a => …`), and each use of the
  `const` instantiates them again. The rest stay pending until the whole
  program is checked.
-/

namespace Inty

/-- The type of a literal, as `LitTy`. -/
def Lit.ty : Lit → Ty
  | .number _ => .number
  | .string _ => .string
  | .boolean _ => .boolean
  | .undefined => .undefined
  | .null => .null

/-- Decides `Expr.IsValue`. -/
def Expr.isValue : Expr → Bool
  | .lit _ | .var _ | .func _ _ => true
  | _ => false

/-- The result of inferring an expression: a substitution to apply to the
context, the expression's type, the class constraints it needs,
and the next unused type variable. -/
structure Out where
  σ : Subst
  τ : Ty
  preds : List Pred
  next : Nat

/-- A return type, substituted. -/
def Ret.subst (σ : Subst) (R : Option Ty) : Option Ty := R.map (·.subst σ)

/-- The free type variables of a return type. -/
def Ret.ftv (R : Option Ty) : List Nat := (R.map Ty.ftv).getD []

@[simp] theorem Ret.subst_none (σ : Subst) : Ret.subst σ none = none := rfl
@[simp] theorem Ret.subst_some (σ : Subst) (τ : Ty) :
    Ret.subst σ (some τ) = some (τ.subst σ) := rfl
@[simp] theorem Ret.subst_nil (R : Option Ty) : Ret.subst [] R = R := by
  cases R <;> simp
@[simp] theorem Ret.subst_compose (σ₂ σ₁ : Subst) (R : Option Ty) :
    Ret.subst (Subst.compose σ₂ σ₁) R = Ret.subst σ₂ (Ret.subst σ₁ R) := by
  cases R <;> simp

theorem Ret.subst_congr {σ σ' : Subst} {R : Option Ty}
    (h : ∀ a ∈ Ret.ftv R, σ.find a = σ'.find a) : Ret.subst σ R = Ret.subst σ' R := by
  cases R with
  | none => rfl
  | some τ => simp only [Ret.subst_some, Option.some.injEq]; exact Ty.subst_congr (by simpa [Ret.ftv] using h)

/-- The scheme a `const` gives its variable, and the constraints left
pending. A syntactic value generalises the variables of its type that
neither the context nor the enclosing function's return type mentions, each once, taking along the constraints that mention
them. -/
def letScheme (e₁ : Expr) (Γ₁ : Ctx) (R₁ : Option Ty) (τ₁ : Ty) (preds : List Pred) :
    Scheme × List Pred :=
  if e₁.isValue then
    let ᾱ := (τ₁.ftv.filter (fun a => a ∉ ctxFtv Γ₁ ++ Ret.ftv R₁)).eraseDups
    (generalize ᾱ τ₁ (preds.filter (fun c => c.ftv.any (· ∈ ᾱ))),
      preds.filter (fun c => !c.ftv.any (· ∈ ᾱ)))
  else (.mono τ₁, preds)

/-- The result of inferring a list of arguments: a substitution, each
argument's type under it, the class constraints, and the next unused type
variable. -/
structure OutArgs where
  σ : Subst
  τs : List Ty
  preds : List Pred
  next : Nat

mutual
/-- Algorithm W. `R` is the enclosing function's return type (`none` at the
top level) and `n` the first unused type variable. -/
def infer : Ctx → Option Ty → Expr → Nat → Option Out
  | _, _, .lit l, n => some ⟨[], l.ty, [], n⟩
  | Γ, _, .var i, n =>
    match Γ[i]? with
    | some s => some ⟨[], s.open n, s.openPreds n, n + s.arity⟩
    | none => none
  -- `this` is the variable `n`, the parameters `n + 1, …`, and the result
  -- the variable after them.
  | Γ, _, .func k body, n =>
    let θ := Ty.var n
    let τs := varBlock (n + 1) k
    let ρ := Ty.var (n + 1 + k)
    match infer (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) body
        (n + 2 + k) with
    | none => none
    | some o =>
      match unify (ρ.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        let σ := Subst.compose σ' o.σ
        some ⟨σ, (Ty.fn θ τs ρ).subst σ, o.preds.map (·.subst σ'), o.next⟩
  -- A call outside any receiver: the callee's `this` is `undefined`.
  | Γ, R, .app f args, n =>
    match infer Γ R f n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) args o₁.next with
      | none => none
      | some o₂ =>
        let β := Ty.var o₂.next
        match unify (o₁.τ.subst o₂.σ) (.fn .undefined o₂.τs β) with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), β.subst σ₃,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst σ₃), o₂.next + 1⟩
  | Γ, R, .let_ e₁ e₂, n =>
    match infer Γ R e₁ n with
    | none => none
    | some o₁ =>
      let Γ₁ := Ctx.subst o₁.σ Γ
      let (s, rest) := letScheme e₁ Γ₁ (Ret.subst o₁.σ R) o₁.τ o₁.preds
      match infer (s :: Γ₁) (Ret.subst o₁.σ R) e₂ o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.preds,
          o₂.next⟩
  | Γ, R, .cond c t e, n =>
    match infer Γ R c n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) t o₁.next with
      | none => none
      | some o₂ =>
        match infer (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) (Ret.subst o₂.σ (Ret.subst o₁.σ R)) e
            o₂.next with
        | none => none
        | some o₃ =>
          match unify (o₂.τ.subst o₃.σ) o₃.τ with
          | none => none
          | some σ₄ =>
            some ⟨Subst.compose σ₄ (Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ)),
              o₃.τ.subst σ₄,
              ((o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst o₃.σ) ++ o₃.preds).map
                (·.subst σ₄),
              o₃.next⟩
  | Γ, R, .unop op e, n =>
    match infer Γ R e n with
    | none => none
    | some o =>
      match op with
      | .not => some ⟨o.σ, .boolean, o.preds, o.next⟩
      | .typeof => some ⟨o.σ, .string, o.preds, o.next⟩
      | .neg =>
        match unify o.τ .number with
        | none => none
        | some σ' => some ⟨Subst.compose σ' o.σ, .number, o.preds.map (·.subst σ'), o.next⟩
  | Γ, R, .binop op e₁ e₂, n =>
    match infer Γ R e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) e₂ o₁.next with
      | none => none
      | some o₂ =>
        let σ₂₁ := Subst.compose o₂.σ o₁.σ
        let preds := o₁.preds.map (·.subst o₂.σ) ++ o₂.preds
        match op with
        | .plus =>
          match unify (o₁.τ.subst o₂.σ) o₂.τ with
          | none => none
          | some σ₃ =>
            some ⟨Subst.compose σ₃ σ₂₁, o₂.τ.subst σ₃,
              (preds ++ [(⟨.plus, [o₂.τ]⟩ : Pred)]).map (·.subst σ₃), o₂.next⟩
        | .minus =>
          match unify (o₁.τ.subst o₂.σ) .number with
          | none => none
          | some σ₃ =>
            match unify (o₂.τ.subst σ₃) .number with
            | none => none
            | some σ₄ =>
              some ⟨Subst.compose σ₄ (Subst.compose σ₃ σ₂₁), .number,
                (preds.map (·.subst σ₃)).map (·.subst σ₄), o₂.next⟩
  -- `return e;` unifies `e`'s type with the function's; it has any type,
  -- a fresh variable.
  | _, none, .ret _, _ => none
  | Γ, some τr, .ret e, n =>
    match infer Γ (some τr) e n with
    | none => none
    | some o =>
      match unify (τr.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        some ⟨Subst.compose σ' o.σ, .var o.next, o.preds.map (·.subst σ'), o.next + 1⟩
  | Γ, R, .throw_ e, n =>
    match infer Γ R e n with
    | none => none
    | some o => some ⟨o.σ, .var o.next, o.preds, o.next + 1⟩
  | Γ, R, .seq e₁ e₂, n =>
    match infer Γ R e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) e₂ o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩

/-- Infer a list of arguments, left to right, threading the substitution. -/
def inferArgs : Ctx → Option Ty → List Expr → Nat → Option OutArgs
  | _, _, [], n => some ⟨[], [], [], n⟩
  | Γ, R, a :: as, n =>
    match infer Γ R a n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) as o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ :: o₂.τs,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
end

/-- Infer the type of a program in a context with no free type variables,
such as the builtins'. Every constraint left must be satisfiable: an
instance, or a constraint on a type variable, which inty leaves in place
and which the program's type here defaults (`defaultSubst`). -/
def inferIn (Γ : Ctx) (e : Expr) : Option Ty :=
  match infer Γ none e 0 with
  | none => none
  | some o =>
    if o.preds.all Pred.satisfiable then some (o.τ.subst (defaultSubst o.preds)) else none

/-- Infer the type of a closed program. -/
def inferProgram (e : Expr) : Option Ty := inferIn [] e

end Inty
