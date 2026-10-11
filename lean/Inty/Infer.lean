import Inty.TreeVars
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
  | .lit _ | .var _ | .func _ _ | .ctor _ _ => true
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

/-- The tree variables of a return type. -/
def Ret.tv (R : Option Ty) : List Nat := (R.map Ty.tv).getD []

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
  | ⟨.merge, [q, κ, τ, t, _]⟩ => (List.range k).any fun i => [q, κ, τ, t].any (·.treeBound k i)
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

/-- What a spread copies of the slot `s` it doesn't write over, as the slot
`r` (`SlotCopy`): it waits while `s`'s presence, or its kind if present, is
a type variable. (Each is looked at unfolded.) -/
def Pred.decideCopy (s r : Ty) : Improve :=
  match s.whnf with
  | .slot p k τ =>
    match p.whnf, k.whnf with
    | .pre, .data => .eq r s
    | .pre, .getter => .eq r (.slot .pre .data τ)
    | .pre, .proto => .eq r .absSlot
    | .abs, _ => .eq r s
    | .var _, _ => .keep
    | .pre, .var _ => .keep
    | _, _ => .fail
  | .var _ => .keep
  | _ => .fail

/-- A `Merge` whose operand's field is present, of the kind `k` and type
`τ`, over the slot `s`: a field that holds a value or a getter is copied as
one that holds a value; a prototype member isn't. It waits while `k` is a
type variable. -/
def Pred.decidePre (k τ s r : Ty) : Improve :=
  match k.whnf with
  | .data | .getter => .eq r (.slot .pre .data τ)
  | .proto => Pred.decideCopy s r
  | .var _ => .keep
  | _ => .fail

/-- Deciding a constraint whose first argument is known, as inty's
`resolve_has_prop` and `resolve_indexable`: a record's field `l` must be
present, of the kind and at the type the read gives; an array's or a
string's `length` is a number, which a getter gives; an array's element
has the array's type, a string's character is a string; a store into an
array holds. A `Merge`'s presence and kind decide it, and if the operand
doesn't write over the slot, that slot (`Pred.decideCopy`). The known type
is taken as it is; `Pred.decide` unfolds it first. -/
def Pred.decide₀ : Cls → Ty → List Ty → Improve
  | .hasProp l, .record ls slots, [κ, σ] =>
    match Ty.field l ls slots with
    | some s => .eq s (.slot .pre κ σ)
    | none => .fail
  | .hasProp l, .array _, [κ, σ] =>
    if l = "length" then .eq (.tuple [κ, σ]) (.tuple [.getter, .number]) else .fail
  | .hasProp l, .string, [κ, σ] =>
    if l = "length" then .eq (.tuple [κ, σ]) (.tuple [.getter, .number]) else .fail
  | .indexable, .array τ, [i, e] => .eq (.tuple [i, e]) (.tuple [.number, τ])
  | .indexable, .string, [i, e] => .eq (.tuple [i, e]) (.tuple [.number, .string])
  -- (An instance holds: a trivial equation drops it.)
  | .indexWrite, .array _, [] => .eq .number .number
  | .merge, .pre, [k, τ, s, r] => Pred.decidePre k τ s r
  | .merge, .abs, [_, _, s, r] => Pred.decideCopy s r
  | _, _, _ => .fail

/-- `Pred.decide₀` on the known type unfolded (`Ty.whnf`): a property of a
recursive type is one of its unfolding, as inty's `resolve_has_prop`
unrolls a `Type::Named` receiver. -/
def Pred.decide (c : Cls) (t : Ty) (rest : List Ty) : Improve := Pred.decide₀ c t.whnf rest

/-- A constraint of the class `c` on the arguments `args`: on a type
variable it waits (if it has the class's arity), on a known type it is
decided. -/
def Pred.improveArgs (c : Cls) : List Ty → Improve
  | t :: rest =>
    if t.whnf.isVar then (if rest.length + 1 = c.arity then .keep else .fail)
    else Pred.decide c t rest
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
  | ⟨.merge, [q, κ, τ, t, r]⟩ => some ([q, κ, τ, t], [r])
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

/-- Whether the variables `fixed` fix a constraint's determining arguments
(their tree variables, `Ty.tv`). -/
def Pred.fires (fixed : List Nat) (p : Pred) : Bool :=
  match p.fundep with
  | some (ds, _) => (ds.flatMap Ty.tv).all (· ∈ fixed)
  | none => false

/-- The variables a constraint's determining arguments fix. -/
def Pred.fixes (p : Pred) : List Nat :=
  match p.fundep with
  | some (_, rs) => rs.flatMap Ty.tv
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
programs, and only the schemes they print differ.

The variables are the trees' (`Ty.tv`): a variable that a recursive type of
the environment mentions only in an equation its unfolding never reaches
isn't one of the environment's, and is quantified. -/
def genVars (Γ₁ : Ctx) (R₁ : Option Ty) (τ₁ : Ty) (preds : List Pred) : List Nat :=
  ((τ₁.tv ++ preds.flatMap Pred.tv).filter
    (· ∉ fixedVars preds (ctxTv Γ₁ ++ Ret.tv R₁))).eraseDups

/-- A constraint on a type whose head is a variable, as one on the
variable. -/
def Pred.normHead (p : Pred) : Pred :=
  match p.args with
  | t :: rest => if t.whnf.isVar then ⟨p.cls, t.whnf :: rest⟩ else p
  | [] => p

/-- Whether a binding generalises: its initialiser is a syntactic value and
the rest of its scope never assigns to it. -/
def Expr.generalises (e₁ e₂ : Expr) : Bool := e₁.isValue && !e₂.writes 0

/-- The scheme a `const` or `let` gives its variable, and the constraints
left pending. When it generalises (`gen`), it quantifies `genVars`, taking
along the constraints that mention them, each on its head's variable
(`Pred.normHead`). -/
def letScheme (gen : Bool) (Γ₁ : Ctx) (R₁ : Option Ty) (τ₁ : Ty) (preds : List Pred) :
    Scheme × List Pred :=
  if gen then
    let ᾱ := genVars Γ₁ R₁ τ₁ preds
    (generalize ᾱ τ₁ ((preds.filter (fun c => c.tv.any (· ∈ ᾱ))).map Pred.normHead),
      preds.filter (fun c => !c.tv.any (· ∈ ᾱ)))
  else (.mono τ₁, preds)

/-- An object literal's fields' slots, from their kinds, expressions and
types (as `FieldSlot`), and the `this` type of each method and getter;
`none` if one of those isn't a function expression, or a getter has
parameters. -/
def fieldSlots : List FieldKind → List Expr → List Ty → Option (List Ty × List Ty)
  | [], [], [] => some ([], [])
  | .data :: ks, _ :: es, τ :: τs =>
    (fieldSlots ks es τs).map fun (θs, ss) => (θs, .slot .pre .data τ :: ss)
  | .method :: ks, .func _ _ :: es, .fn θ τs' ρ :: τs =>
    (fieldSlots ks es τs).map fun (θs, ss) => (θ :: θs, .slot .pre .data (.fn θ τs' ρ) :: ss)
  | .getter :: ks, .func 0 _ :: es, .fn θ [] σ :: τs =>
    (fieldSlots ks es τs).map fun (θs, ss) => (θ :: θs, .slot .pre .getter σ :: ss)
  | _, _, _ => none

/-- A class's members' slots, from their kinds, expressions and types (as
`MemberSlot`), and the `this` type of each that isn't a field holding a
value, which must be a function expression (a getter's of no parameters);
an arrow field's slot has any `this`, a fresh variable from `n`. The
slots, the `this` types, and the next unused variable. -/
def memberSlots : List ClassKind → List Expr → List Ty → Nat → Option (List Ty × List Ty × Nat)
  | [], [], [], n => some ([], [], n)
  | .data :: ks, _ :: es, τ :: τs, n =>
    (memberSlots ks es τs n).map fun (θs, ss, n') => (θs, .slot .pre .data τ :: ss, n')
  | .arrow :: ks, .func _ _ :: es, .fn θ τs' ρ :: τs, n =>
    (memberSlots ks es τs (n + 1)).map fun (θs, ss, n') =>
      (θ :: θs, .slot .pre .data (.fn (.var n) τs' ρ) :: ss, n')
  | .method :: ks, .func _ _ :: es, .fn θ τs' ρ :: τs, n =>
    (memberSlots ks es τs n).map fun (θs, ss, n') =>
      (θ :: θs, .slot .pre .proto (.fn θ τs' ρ) :: ss, n')
  | .getter :: ks, .func 0 _ :: es, .fn θ [] σ :: τs, n =>
    (memberSlots ks es τs n).map fun (θs, ss, n') => (θ :: θs, .slot .pre .proto σ :: ss, n')
  | _, _, _, _ => none

/-- Unify each `this` type `θs` with the record type `T`: with each other,
then with `T`, which makes it recursive (inty's `shared_this`). -/
def unifyThis (θs : List Ty) (T : Ty) : Option Subst :=
  match θs with
  | [] => some []
  | θ :: θs =>
    match unify (.tuple (θ :: θs)) (.tuple (List.replicate (θs.length + 1) θ)) with
    | none => none
    | some σ₁ =>
      match unify (θ.subst σ₁) (T.subst σ₁) with
      | none => none
      | some σ₂ => some (Subst.compose σ₂ σ₁)

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
  -- An object literal over the labels `L`: its fields present, each as
  -- its kind says, the other labels absent. A method's and a getter's
  -- `this` is the literal's type (`unifyThis`).
  | Γ, R, .obj ls es ks, n =>
    if ls.all (· ∈ L) ∧ es.length = ls.length ∧ ks.length = ls.length then
      match inferArgs Γ R es n with
      | none => none
      | some o =>
        match fieldSlots ks es o.τs with
        | none => none
        | some (θs, ss) =>
          let T := Ty.record L (objSlots L ls ss)
          match unifyThis θs T with
          | none => none
          | some σ' => some ⟨Subst.compose σ' o.σ, T.subst σ', o.preds.map (·.subst σ'), o.next⟩
    else none
  -- A class's instance: its fields' initialisers, each seeing the fields
  -- before it, and its other members, functions whose `this` is the
  -- instance.
  | Γ, R, .cls ls es ks, n =>
    if ls.all (· ∈ L) ∧ ls.Nodup ∧ es.length = ls.length ∧ ks.length = ls.length then
      match inferMembers Γ [] R es ks n with
      | none => none
      | some o =>
        match memberSlots ks es o.τs o.next with
        | none => none
        | some (θs, ss, n') =>
          let T := Ty.record L (objSlots L ls ss)
          match unifyThis θs T with
          | none => none
          | some σ' => some ⟨Subst.compose σ' o.σ, T.subst σ', o.preds.map (·.subst σ'), n'⟩
    else none
  -- A constructor: a function whose `this` is what `new` makes.
  | Γ, _, .ctor k body, n =>
    let τs := varBlock n k
    let ρ := Ty.var (n + k)
    match infer (τs.map .mono ++ .mono (.fn .newTarget τs ρ) :: .mono .newTarget :: Γ) (some ρ)
        body (n + 1 + k) with
    | none => none
    | some o =>
      match unify (ρ.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        let σ := Subst.compose σ' o.σ
        some ⟨σ, (Ty.fn .newTarget τs ρ).subst σ, o.preds.map (·.subst σ'), o.next⟩
  -- `new f(…)`: `f` a constructor, which gives a record, over fresh slots.
  | Γ, R, .new_ f args, n =>
    match infer Γ R f n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) args o₁.next with
      | none => none
      | some o₂ =>
        let ρ := Ty.record L (varBlock o₂.next L.length)
        match unify (o₁.τ.subst o₂.σ) (.fn .newTarget o₂.τs ρ) with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), ρ.subst σ₃,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst σ₃), o₂.next + L.length⟩
  -- `e.l` on a receiver of any type: `HasProp l τ κ β`, for a fresh `κ`
  -- and `β`.
  | Γ, R, .get e l, n =>
    match infer Γ R e n with
    | none => none
    | some o =>
      some ⟨o.σ, .var (o.next + 1),
        o.preds ++ [⟨.hasProp l, [o.τ, .var o.next, .var (o.next + 1)]⟩], o.next + 2⟩
  -- `e.l = v`: `HasProp l τ data ρ`, `ρ` being `v`'s type.
  | Γ, R, .set e l v, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) v o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++ [⟨.hasProp l, [o₁.τ.subst o₂.σ, .data, o₂.τ]⟩],
          o₂.next⟩
  -- `{...e₁, ...e₂}`: `e₁` a record, `e₂` a record each of whose slots is
  -- a presence, a kind and a type, and a `Merge` for each label, all at
  -- fresh variables after `e₂`'s: the slots written over, the presences,
  -- the kinds, the types, and the result's slots.
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
        let ks := varBlock (o₂.next + 2 * k) k
        let τs := varBlock (o₂.next + 3 * k) k
        let rs := varBlock (o₂.next + 4 * k) k
        match unify (o₁.τ.subst o₂.σ) (.record L ss) with
        | none => none
        | some σ₃ =>
          match unify (o₂.τ.subst σ₃) ((Ty.record L (slots3 ps ks τs)).subst σ₃) with
          | none => none
          | some σ₄ =>
            let σ₄₃ := Subst.compose σ₄ σ₃
            some ⟨Subst.compose σ₄₃ (Subst.compose o₂.σ o₁.σ), (Ty.record L rs).subst σ₄₃,
              (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++ mergePreds ps ks τs ss rs).map
                (·.subst σ₄₃),
              o₂.next + 5 * k⟩
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
  -- `e.l(args)`: `HasProp l τ κ (this: τ, (τs) => β)`, the method's `this`
  -- being the receiver's type (inty's `method_receiver`), for a fresh `κ`
  -- and `β`.
  | Γ, R, .mcall e l args, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) args o₁.next with
      | none => none
      | some o₂ =>
        let τ := o₁.τ.subst o₂.σ
        some ⟨Subst.compose o₂.σ o₁.σ, .var (o₂.next + 1),
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
            [⟨.hasProp l, [τ, .var o₂.next, .fn τ o₂.τs (.var (o₂.next + 1))]⟩],
          o₂.next + 2⟩

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

/-- Infer a class's members, left to right, threading the substitution: a
field's initialiser sees the types `Δ` of the fields before it, the latest
first; the other members see `Γ`. -/
def inferMembers : Ctx → List Ty → Option Ty → List Expr → List ClassKind → Nat → Option OutArgs
  | _, _, _, [], [], n => some ⟨[], [], [], n⟩
  | Γ, Δ, R, e :: es, .data :: ks, n =>
    match infer (Δ.map .mono ++ Γ) R e n with
    | none => none
    | some o₁ =>
      match inferMembers (Ctx.subst o₁.σ Γ) (o₁.τ :: Δ.map (·.subst o₁.σ)) (Ret.subst o₁.σ R) es
          ks o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ :: o₂.τs,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
  | Γ, Δ, R, e :: es, _ :: ks, n =>
    match infer Γ R e n with
    | none => none
    | some o₁ =>
      match inferMembers (Ctx.subst o₁.σ Γ) (Δ.map (·.subst o₁.σ)) (Ret.subst o₁.σ R) es ks
          o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ :: o₂.τs,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
  | _, _, _, _, _, _ => none
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
  | .obj ls es _ | .cls ls es _ => ls ++ Expr.labelsList es
  | .ctor _ b => b.labels
  | .new_ f args => f.labels ++ Expr.labelsList args
  | .get e l => l :: e.labels
  | .set e l v => l :: (e.labels ++ v.labels)
  | .spread a b | .index a b => a.labels ++ b.labels
  | .arr es => Expr.labelsList es
  | .setIndex a b c => a.labels ++ b.labels ++ c.labels
  | .mcall e l args => l :: (e.labels ++ Expr.labelsList args)
/-- `labels`, for a list of expressions. -/
def Expr.labelsList : List Expr → List String
  | [] => []
  | e :: es => e.labels ++ Expr.labelsList es
end

/-- Infer the type of a closed program, with records over its labels. -/
def inferProgram (e : Expr) : Option Ty := inferIn e.labels.eraseDups [] e

end Inty
