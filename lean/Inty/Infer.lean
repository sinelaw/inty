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

- `+` records the constraint `Plus τ` on its operand type `τ`, and a
  property read or write `HasProp l τ σ` on its receiver's.
- Before a `const` or `let` generalises, the constraints on known types are
  decided (`improveAll`). It then takes the constraints mentioning the
  variables it quantifies into its scheme (inty's `<a> where Plus a => …`),
  and each use instantiates them again. The rest stay pending until the
  whole program is checked.
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

/-- Whether a scheme's constraint is on one of its `k` quantified variables
(`Scheme.Simple`). -/
def PPred.isSimple (k : Nat) : PPred → Bool
  | ⟨.merge, [q, τ, t, _]⟩ => (q.bvs ++ τ.bvs ++ t.bvs).any (· < k)
  | ⟨.merge, _⟩ => false
  | ⟨c, .bound i :: rest⟩ => decide (i < k) && decide (rest.length + 1 = c.arity)
  | _ => false

/-! ## Constraints whose arguments determine one another

A `HasProp`'s receiver determines its field's type (a functional
dependency). Such a constraint on a known type is decided, improving the
types (`Pred.improve`), and one on a type variable waits. -/

/-- What a constraint on a known type comes to: `keep` it (it is on a type
variable, or its class has no dependency), it `fail`s, or it holds exactly
when two types are equal (`eq`). -/
inductive Improve where
  | keep
  | fail
  | eq (τ₁ τ₂ : Ty)

/-- Deciding a constraint whose first argument is known, as inty's
`resolve_has_prop` and `resolve_indexable`: a record's field `l` must be
present, at the type the read gives; an array's or a string's `length` is
a number; an array's element has the array's type, a string's character
is a string; a store into an array or an object holds. A `Merge`'s
presence decides it: the operand's field if present, the slot written over
if absent. -/
def Pred.decide : Cls → Ty → List Ty → Improve
  | .hasProp l, .record ls slots, [σ] =>
    match Ty.field l ls slots with
    | some s => .eq s (.slot .pre σ)
    | none => .fail
  | .hasProp l, .array _, [σ] => if l = "length" then .eq σ .number else .fail
  | .hasProp l, .string, [σ] => if l = "length" then .eq σ .number else .fail
  | .indexable, .array τ, [i, e] => .eq (.tuple [i, e]) (.tuple [.number, τ])
  | .indexable, .string, [i, e] => .eq (.tuple [i, e]) (.tuple [.number, .string])
  -- (An instance holds: a trivial equation drops it.)
  | .indexWrite, .array _, [] => .eq .number .number
  | .fieldWrite, .record _ _, [] => .eq .number .number
  | .merge, .pre, [τ, _, r] => .eq r (.slot .pre τ)
  | .merge, .abs, [_, s, r] => .eq r s
  | _, _, _ => .fail

/-- A constraint of the class `c` on the arguments `args`: on a type
variable it waits (if it has the class's arity), on a known type it is
decided. -/
def Pred.improveArgs (c : Cls) : List Ty → Improve
  | .var _ :: rest => if rest.length + 1 = c.arity then .keep else .fail
  | t :: rest => Pred.decide c t rest
  | [] => .fail

/-- Deciding a constraint on a known type. A `Plus` waits until the end
(`Pred.settled`). A `Merge` is decided only at the top level (`top`): where
a binding generalises, it stays as it is, so that the decision doesn't
depend on whether its presence is known by then (see `Scheme.Simple`). -/
def Pred.improve (top : Bool) (p : Pred) : Improve :=
  match p.cls with
  | .plus => .keep
  | .merge => if top then Pred.improveArgs .merge p.args else .keep
  | c => Pred.improveArgs c p.args

/-- The arguments a constraint's determining arguments fix: a constraint's
first argument fixes the rest (a `HasProp`'s receiver its field's type, an
`Indexable`'s container its index and element), and a `Merge`'s operand
slot and the slot it is written over fix the result. -/
def Pred.fundep : Pred → Option (List Ty × List Ty)
  | ⟨.plus, _⟩ => none
  | ⟨.merge, [q, τ, t, r]⟩ => some ([q, τ, t], [r])
  | ⟨.merge, _⟩ => none
  | ⟨_, c :: rest⟩ => some ([c], rest)
  | ⟨_, []⟩ => none

/-- Decide the first constraint that can be decided: `none` if one fails,
`some none` if none can be, or the equation it comes to and the others. -/
def improveOne (top : Bool) : List Pred → Option (Option ((Ty × Ty) × List Pred))
  | [] => some none
  | p :: ps =>
    match p.improve top with
    | .fail => none
    | .eq τ₁ τ₂ => some (some ((τ₁, τ₂), ps))
    | .keep =>
      match improveOne top ps with
      | none => none
      | some none => some none
      | some (some (e, rest)) => some (some (e, p :: rest))

/-- Decide the constraints on known types, repeatedly (deciding one can make
another's receiver known), as inty's `simplify_has_props`: the
substitution the improvements come to, and the constraints left. -/
def improveAll (top : Bool) : Nat → List Pred → Option (Subst × List Pred)
  | 0, ps => some ([], ps)
  | k + 1, ps =>
    match improveOne top ps with
    | none => none
    | some none => some ([], ps)
    | some (some ((τ₁, τ₂), rest)) =>
      match unify τ₁ τ₂ with
      | none => none
      | some σ =>
        match improveAll top k (rest.map (·.subst σ)) with
        | none => none
        | some (σ', ps') => some (Subst.compose σ' σ, ps')

/-- Whether the variables `fixed` fix a constraint's determining arguments. -/
def Pred.fires (fixed : List Nat) (p : Pred) : Bool :=
  match p.fundep with
  | some (ds, _) => (ds.flatMap Ty.ftv).all (· ∈ fixed)
  | none => false

/-- The variables a constraint's determining arguments fix. -/
def Pred.fixes (p : Pred) : List Nat :=
  match p.fundep with
  | some (_, rs) => rs.flatMap Ty.ftv
  | none => []

/-- Close `fixed` under the dependencies of `preds`: a constraint whose
determining arguments are fixed fixes the rest, and is then set aside. -/
def fixLoop : Nat → List Pred → List Nat → List Nat
  | 0, _, fixed => fixed
  | k + 1, preds, fixed =>
    if (preds.filter (Pred.fires fixed)).isEmpty then fixed
    else fixLoop k (preds.filter (fun p => !p.fires fixed))
      (fixed ++ (preds.filter (Pred.fires fixed)).flatMap Pred.fixes)

/-- The variables the environment fixes, through the constraints'
dependencies (inty's `env_fixed_vars`). -/
def fixedVars (preds : List Pred) (env : List Nat) : List Nat :=
  fixLoop preds.length preds env

/-- The variables a `const` or `let` quantifies: every variable of its type
and of the constraints that the environment doesn't fix (through the
constraints' dependencies, inty's `env_fixed_vars`). inty starts from the
type's variables and adds those of the constraints on them; a constraint
none of whose variables the type reaches, it leaves pending instead. Such a
constraint's variables appear in no type, then or later, so it stays on
type variables either way, where it can't fail: the two accept the same
programs, and only the schemes they print differ. -/
def genVars (Γ₁ : Ctx) (R₁ : Option Ty) (τ₁ : Ty) (preds : List Pred) : List Nat :=
  ((τ₁.ftv ++ preds.flatMap Pred.ftv).filter
    (· ∉ fixedVars preds (ctxFtv Γ₁ ++ Ret.ftv R₁))).eraseDups

/-- Whether a binding generalises: its initialiser is a syntactic value and
the rest of its scope never assigns to it. -/
def Expr.generalises (e₁ e₂ : Expr) : Bool := e₁.isValue && !e₂.writes 0

/-- The scheme a `const` or `let` gives its variable, and the constraints
left pending. When it generalises (`gen`), it quantifies `genVars`, taking
along the constraints that mention them. -/
def letScheme (gen : Bool) (Γ₁ : Ctx) (R₁ : Option Ty) (τ₁ : Ty) (preds : List Pred) :
    Scheme × List Pred :=
  if gen then
    let ᾱ := genVars Γ₁ R₁ τ₁ preds
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

section
variable (L : List String)

mutual
/-- Algorithm W, with records over the labels `L`. `R` is the enclosing
function's return type (`none` at the top level) and `n` the first unused
type variable. -/
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
  -- The constraints on known types are decided first, as inty's
  -- `simplify_has_props` does before it generalises.
  | Γ, R, .let_ _ e₁ e₂, n =>
    match infer Γ R e₁ n with
    | none => none
    | some o₁ =>
      match improveAll false o₁.preds.length o₁.preds with
      | none => none
      | some (σi, preds₁) =>
        let σ₁ := Subst.compose σi o₁.σ
        let Γ₁ := Ctx.subst σ₁ Γ
        let R₁ := Ret.subst σ₁ R
        let (s, rest) := letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ (o₁.τ.subst σi) preds₁
        -- A constraint the scheme would carry on a type already known is
        -- decided now, as inty's `generalize` does: it can't hold.
        if s.preds.all (PPred.isSimple s.arity) then
          match infer (s :: Γ₁) R₁ e₂ o₁.next with
          | none => none
          | some o₂ =>
            some ⟨Subst.compose o₂.σ σ₁, o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
        else none
  -- `x = e`: `x`'s scheme is a monotype, which `e`'s type is unified with.
  | Γ, R, .assign i e, n =>
    match Γ[i]? with
    | none => none
    | some s =>
      if s.arity = 0 ∧ s.preds = [] then
        match infer Γ R e n with
        | none => none
        | some o =>
          match unify ((s.inst []).subst o.σ) o.τ with
          | none => none
          | some σ' =>
            some ⟨Subst.compose σ' o.σ, (s.inst []).subst (Subst.compose σ' o.σ),
              o.preds.map (·.subst σ'), o.next⟩
      else none
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
  | Γ, R, .while_ c body, n =>
    match infer Γ R c n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) body o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, .undefined, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
          o₂.next⟩
  -- `break` and `continue` have any type, a fresh variable.
  | _, _, .break_, n | _, _, .continue_, n => some ⟨[], .var n, [], n + 1⟩
  -- The caught value has the opaque type `unknown`; both branches have one
  -- type.
  | Γ, R, .tryCatch body handler, n =>
    match infer Γ R body n with
    | none => none
    | some o₁ =>
      match infer (.mono .unknown :: Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) handler o₁.next with
      | none => none
      | some o₂ =>
        match unify (o₁.τ.subst o₂.σ) o₂.τ with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), o₂.τ.subst σ₃,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst σ₃), o₂.next⟩
  | Γ, R, .tryFinally body fin, n =>
    match infer Γ R body n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) fin o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
          o₂.next⟩
  -- An object literal over the labels `L`: its fields present, the other
  -- labels absent, at fresh types.
  | Γ, R, .obj ls es, n =>
    if ls.all (· ∈ L) ∧ es.length = ls.length then
      match inferArgs Γ R es n with
      | none => none
      | some o =>
        some ⟨o.σ, .record L (objSlots L ls o.τs (varBlock o.next L.length)), o.preds,
          o.next + L.length⟩
    else none
  -- `e.l` on a receiver of any type: `HasProp l τ β`, for a fresh `β`.
  | Γ, R, .get e l, n =>
    match infer Γ R e n with
    | none => none
    | some o => some ⟨o.σ, .var o.next, o.preds ++ [⟨.hasProp l, [o.τ, .var o.next]⟩], o.next + 1⟩
  -- `e.l = v`: `HasProp l τ ρ`, `ρ` being `v`'s type.
  | Γ, R, .set e l v, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) v o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
            [⟨.hasProp l, [o₁.τ.subst o₂.σ, o₂.τ]⟩, ⟨.fieldWrite, [o₁.τ.subst o₂.σ]⟩],
          o₂.next⟩
  -- `{...e₁, ...e₂}`: `e₁` a record, `e₂` a record each of whose slots is
  -- a presence and a type, and a `Merge` for each label, all at fresh
  -- variables after `e₂`'s: the slots written over, the presences, the
  -- types, and the result's slots.
  | Γ, R, .spread e₁ e₂, n =>
    match infer Γ R e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) e₂ o₁.next with
      | none => none
      | some o₂ =>
        let k := L.length
        let ss := varBlock o₂.next k
        let ps := varBlock (o₂.next + k) k
        let τs := varBlock (o₂.next + 2 * k) k
        let rs := varBlock (o₂.next + 3 * k) k
        match unify (o₁.τ.subst o₂.σ) (.record L ss) with
        | none => none
        | some σ₃ =>
          match unify (o₂.τ.subst σ₃) ((Ty.record L (List.zipWith Ty.slot ps τs)).subst σ₃) with
          | none => none
          | some σ₄ =>
            let σ₄₃ := Subst.compose σ₄ σ₃
            some ⟨Subst.compose σ₄₃ (Subst.compose o₂.σ o₁.σ), (Ty.record L rs).subst σ₄₃,
              (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++ mergePreds ps τs ss rs).map
                (·.subst σ₄₃),
              o₂.next + 4 * k⟩
  -- `[e₀, …]`: one type for the elements, a fresh variable.
  | Γ, R, .arr es, n =>
    match inferArgs Γ R es n with
    | none => none
    | some o =>
      match unify (.tuple o.τs) (.tuple (List.replicate o.τs.length (.var o.next))) with
      | none => none
      | some σ' =>
        some ⟨Subst.compose σ' o.σ, (Ty.array (.var o.next)).subst σ', o.preds.map (·.subst σ'),
          o.next + 1⟩
  -- `e[i]`: `Indexable τ ι β`, for a fresh `β`.
  | Γ, R, .index e i, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) i o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, .var o₂.next,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
            [⟨.indexable, [o₁.τ.subst o₂.σ, o₂.τ, .var o₂.next]⟩],
          o₂.next + 1⟩
  -- `e[i] = v`: `Indexable τ ι ρ` and `IndexWrite τ`, `ρ` being `v`'s type.
  | Γ, R, .setIndex e i v, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) i o₁.next with
      | none => none
      | some o₂ =>
        match infer (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) (Ret.subst o₂.σ (Ret.subst o₁.σ R)) v
            o₂.next with
        | none => none
        | some o₃ =>
          let τc := (o₁.τ.subst o₂.σ).subst o₃.σ
          some ⟨Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ), o₃.τ,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst o₃.σ) ++ o₃.preds ++
              [⟨.indexable, [τc, o₂.τ.subst o₃.σ, o₃.τ]⟩, ⟨.indexWrite, [τc]⟩],
            o₃.next⟩

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

end

/-- Infer the type of a program in a context with no free type variables,
such as the builtins', none of whose variables is mutable, with records
over the labels `L`. It must pass the scope checks (`Expr.scoped`): it
assigns only to its own `let`s and parameters, and has `break` and
`continue` only in loops. The constraints on known types are decided
(`improveAll`), and every one left must be settled: an instance, or on a
type variable (`HoldsOrVar`), which inty leaves in place. -/
def inferIn (L : List String) (Γ : Ctx) (e : Expr) : Option Ty :=
  if e.scoped (Γ.map fun _ => false) then
    match infer L Γ none e 0 with
    | none => none
    | some o =>
      match improveAll true o.preds.length o.preds with
      | none => none
      | some (σi, preds) => if preds.all Pred.settled then some (o.τ.subst σi) else none
  else none

mutual
/-- The property labels a program mentions: the labels its records have
slots for. -/
def Expr.labels : Expr → List String
  | .lit _ | .var _ | .break_ | .continue_ => []
  | .func _ b | .ret b | .throw_ b | .unop _ b | .assign _ b => b.labels
  | .app f args => f.labels ++ Expr.labelsList args
  | .let_ _ a b | .binop _ a b | .seq a b | .while_ a b | .tryCatch a b | .tryFinally a b =>
    a.labels ++ b.labels
  | .cond a b c => a.labels ++ b.labels ++ c.labels
  | .obj ls es => ls ++ Expr.labelsList es
  | .get e l => l :: e.labels
  | .set e l v => l :: (e.labels ++ v.labels)
  | .spread a b | .index a b => a.labels ++ b.labels
  | .arr es => Expr.labelsList es
  | .setIndex a b c => a.labels ++ b.labels ++ c.labels
/-- `labels`, for a list of expressions. -/
def Expr.labelsList : List Expr → List String
  | [] => []
  | e :: es => e.labels ++ Expr.labelsList es
end

/-- Infer the type of a closed program, with records over its labels. -/
def inferProgram (e : Expr) : Option Ty := inferIn e.labels.eraseDups [] e

end Inty
