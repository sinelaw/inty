import Inty.Subst
import Inty.Syntax

/-!
# Type inference

Algorithm W (Damas and Milner) for the calculus: an executable function that
finds a type, where `HasType` only says which types are valid. It mirrors the
structure of `src/infer`, minus its destructive unification and constraint
solver.

Two simplifications, both safe for soundness:

- Unification is bounded by fuel (`unifyFuel`), so it is total without a
  termination proof. Completeness, the next step, needs that proof.
- `+` records a constraint that its operand type is an instance of `Plus`.
  A `const` that generalises a variable takes the constraints mentioning it
  into its scheme (inty's `<a> where Plus a => …`), and each use of the
  `const` instantiates them again. The rest stay pending until the whole
  program is checked.
-/

namespace Inty

/-- Robinson unification: a substitution that makes `τ₁` and `τ₂` equal. -/
def unify : Nat → Ty → Ty → Option Subst
  | 0, _, _ => none
  | fuel + 1, τ₁, τ₂ =>
    match τ₁, τ₂ with
    | .var a, .var b => if a = b then some [] else some [(a, .var b)]
    | .var a, τ => if a ∈ τ.ftv then none else some [(a, τ)]
    | τ, .var a => if a ∈ τ.ftv then none else some [(a, τ)]
    | .arrow d₁ c₁, .arrow d₂ c₂ =>
      match unify fuel d₁ d₂ with
      | none => none
      | some σ₁ =>
        match unify fuel (c₁.subst σ₁) (c₂.subst σ₁) with
        | none => none
        | some σ₂ => some (Subst.compose σ₂ σ₁)
    | τ₁, τ₂ => if τ₁ = τ₂ then some [] else none

/-- How deep unification may recurse. -/
def unifyFuel : Nat := 1000

/-- The type of a literal, as `LitTy`. -/
def Lit.ty : Lit → Ty
  | .number _ => .number
  | .string _ => .string
  | .boolean _ => .boolean
  | .undefined => .undefined
  | .null => .null

/-- Decides `Expr.IsValue`. -/
def Expr.isValue : Expr → Bool
  | .lit _ | .var _ | .func _ => true
  | _ => false

/-- The result of inferring an expression: a substitution to apply to the
context, the expression's type, the types that must be `Plus` instances,
and the next unused type variable. -/
structure Out where
  σ : Subst
  τ : Ty
  plus : List Ty
  next : Nat

/-- The scheme a `const` gives its variable, and the constraints left
pending. A syntactic value generalises the variables of its type that the
context doesn't mention, each once, taking along the constraints that mention
them. -/
def letScheme (e₁ : Expr) (Γ₁ : Ctx) (τ₁ : Ty) (plus : List Ty) : Scheme × List Ty :=
  if e₁.isValue then
    let ᾱ := (τ₁.ftv.filter (fun a => a ∉ ctxFtv Γ₁)).eraseDups
    (generalize ᾱ τ₁ (plus.filter (fun c => c.ftv.any (· ∈ ᾱ))),
      plus.filter (fun c => !c.ftv.any (· ∈ ᾱ)))
  else (.mono τ₁, plus)

/-- Algorithm W. `n` is the first unused type variable. -/
def infer : Ctx → Expr → Nat → Option Out
  | _, .lit l, n => some ⟨[], l.ty, [], n⟩
  | Γ, .var i, n =>
    match Γ[i]? with
    | some s => some ⟨[], s.open n, s.openPlus n, n + s.arity⟩
    | none => none
  | Γ, .func body, n =>
    let α := Ty.var n
    let β := Ty.var (n + 1)
    match infer (.mono α :: .mono (.arrow α β) :: Γ) body (n + 2) with
    | none => none
    | some o =>
      match unify unifyFuel (β.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        let σ := Subst.compose σ' o.σ
        some ⟨σ, (Ty.arrow α β).subst σ, o.plus.map (·.subst σ'), o.next⟩
  | Γ, .app f a, n =>
    match infer Γ f n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) a o₁.next with
      | none => none
      | some o₂ =>
        let β := Ty.var o₂.next
        match unify unifyFuel (o₁.τ.subst o₂.σ) (.arrow o₂.τ β) with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), β.subst σ₃,
            (o₁.plus.map (·.subst o₂.σ) ++ o₂.plus).map (·.subst σ₃), o₂.next + 1⟩
  | Γ, .let_ e₁ e₂, n =>
    match infer Γ e₁ n with
    | none => none
    | some o₁ =>
      let Γ₁ := Ctx.subst o₁.σ Γ
      let (s, rest) := letScheme e₁ Γ₁ o₁.τ o₁.plus
      match infer (s :: Γ₁) e₂ o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.plus,
          o₂.next⟩
  | Γ, .cond c t e, n =>
    match infer Γ c n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) t o₁.next with
      | none => none
      | some o₂ =>
        match infer (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) e o₂.next with
        | none => none
        | some o₃ =>
          match unify unifyFuel (o₂.τ.subst o₃.σ) o₃.τ with
          | none => none
          | some σ₄ =>
            some ⟨Subst.compose σ₄ (Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ)),
              o₃.τ.subst σ₄,
              ((o₁.plus.map (·.subst o₂.σ) ++ o₂.plus).map (·.subst o₃.σ) ++ o₃.plus).map
                (·.subst σ₄),
              o₃.next⟩
  | Γ, .unop op e, n =>
    match infer Γ e n with
    | none => none
    | some o =>
      match op with
      | .not => some ⟨o.σ, .boolean, o.plus, o.next⟩
      | .typeof => some ⟨o.σ, .string, o.plus, o.next⟩
      | .neg =>
        match unify unifyFuel o.τ .number with
        | none => none
        | some σ' => some ⟨Subst.compose σ' o.σ, .number, o.plus.map (·.subst σ'), o.next⟩
  | Γ, .binop op e₁ e₂, n =>
    match infer Γ e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) e₂ o₁.next with
      | none => none
      | some o₂ =>
        let σ₂₁ := Subst.compose o₂.σ o₁.σ
        let plus := o₁.plus.map (·.subst o₂.σ) ++ o₂.plus
        match op with
        | .plus =>
          match unify unifyFuel (o₁.τ.subst o₂.σ) o₂.τ with
          | none => none
          | some σ₃ =>
            some ⟨Subst.compose σ₃ σ₂₁, o₂.τ.subst σ₃,
              (plus ++ [o₂.τ]).map (·.subst σ₃), o₂.next⟩
        | .minus =>
          match unify unifyFuel (o₁.τ.subst o₂.σ) .number with
          | none => none
          | some σ₃ =>
            match unify unifyFuel (o₂.τ.subst σ₃) .number with
            | none => none
            | some σ₄ =>
              some ⟨Subst.compose σ₄ (Subst.compose σ₃ σ₂₁), .number,
                (plus.map (·.subst σ₃)).map (·.subst σ₄), o₂.next⟩

/-- Whether a type is, as it stands, an instance of `Plus`. -/
def Ty.isPlusInst : Ty → Bool
  | .number | .string => true
  | _ => false

/-- Infer the type of a closed program. Every `+` must end up at an instance
of `Plus`. -/
def inferProgram (e : Expr) : Option Ty :=
  match infer [] e 0 with
  | none => none
  | some o => if o.plus.all Ty.isPlusInst then some o.τ else none

end Inty
