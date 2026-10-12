import Inty.Typing
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

- `+` records the constraint `Plus τ` on its operand type `τ`; a property
  read or write, `HasProp l τ k σ` on its receiver's; a spread, a `Merge`
  per label; an index, `Indexable` (and `IndexWrite` for a store); an arrow
  field, `NotNew` on its `this`.
- Before a `const` or `let` generalises, the constraints on known types are
  decided (`improveAll`), but a `Plus`, which waits until the end
  (`Pred.settled`), and a `Merge`, which only the top level decides. It
  then takes the constraints mentioning the variables it quantifies into
  its scheme (inty's `<a> where Plus a => …`), and each use instantiates
  them again. The rest stay pending until the whole program is checked.
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

/-- An `Inject T τ` whose `τ` is known (unfolded): the heads decide which
instance it can be, and into a variant told apart by `typeof` the tag of
`τ`'s head which case. (`T` is an annotation's type, without variables.) -/
def Pred.decideInject (τ T : Ty) : Improve :=
  if T.ftv = [] then
    match T.whnf with
    | .app (.maybe z) [σ] =>
      match τ with
      | .app c args =>
        if c = .maybe z then .eq τ T
        else if c = z.con ∧ args = [] then .eq .number .number
        else .eq τ σ
      | _ => .eq τ T
    -- Into a variant told apart by `typeof`, its case of the tag `τ`'s
    -- head's values have.
    | .app (.variant .typeOf ts) Rs =>
      match τ with
      | .app c _ =>
        match c.typeTag with
        | some t =>
          if ts.Nodup then
            match firstIdx t ts with
            | some i =>
              match Rs[i]? with
              | some R => .eq τ R
              | none => .fail
            | none => .fail
          else .fail
        | none => .eq τ T
      | _ => .eq τ T
    | _ => .eq τ T
  else .fail

/-- A `Strip τ σ` whose `τ` is known (unfolded): a sum's value type, or `τ`
itself; `Null` and `Undefined` have no value but nothing. -/
def Pred.decideStrip (t σ : Ty) : Improve :=
  match t with
  | .app (.maybe _) [σ'] => .eq σ σ'
  | .app c args =>
    match c with
    | .maybe _ | .null | .undefined => .fail
    | _ => .eq σ (.app c args)
  | _ => .fail

/-- A `Case_{l,t}` on a variant tagged by `l'` with the tags `ts` and the
cases `Ps`: the case of the tag `t` and the rest, if the tags differ. -/
def Pred.decideCase (d : Disc) (t : String) (d' : Disc) (ts : List String) (Ps : List Ty)
    (σ ρ : Ty) : Improve :=
  if d' = d ∧ ts.Nodup then
    match firstIdx t ts with
    | some i =>
      match Ps[i]? with
      | some P => .eq (.tuple [σ, ρ]) (.tuple [P, variantRest d (ts.eraseIdx i) (Ps.eraseIdx i)])
      | none => .fail
    | none => .fail
  else .fail

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
  | .notNew, .app c _, [] => if c = .newTarget ∨ c.isRigid then .fail else .eq .number .number
  | .merge, .pre, [k, τ, s, r] => Pred.decidePre k τ s r
  | .merge, .abs, [_, _, s, r] => Pred.decideCopy s r
  | .inject T, τ, [] => Pred.decideInject τ T
  | .strip, t, [σ] => Pred.decideStrip t σ
  | .caseTag d t, .app (.variant d' ts) Ps, [σ, ρ] => Pred.decideCase d t d' ts Ps σ ρ
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

/-- `NotNew` on each of the variables from `n` up to `n'`: what
`memberSlots` gives a class's arrow fields' `this` types, as `new` on an
arrow function throws. -/
def notNewPreds (n n' : Nat) : List Pred :=
  (List.range' n (n' - n)).map fun a => ⟨.notNew, [.var a]⟩

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

/-- A function literal with `k` parameters checked against the expected
type `T`: `T` with its `this`, parameter and result types, if `T` is a
function type with `k` parameters (`HasTypeS.funcCheck`). -/
def funcTarget : Option Ty → Nat → Option (Ty × Ty × List Ty × Ty)
  | some T, k =>
    match T.whnf with
    | .fn θ τs ρ => if τs.length = k then some (T, θ, τs, ρ) else none
    | _ => none
  | none, _ => none

/-- An array literal checked against the expected type `T`: `T` with its
element type, if `T` is an array type (`HasTypeS.arrCheck`). -/
def arrTarget : Option Ty → Option (Ty × Ty)
  | some T =>
    match T.whnf with
    | .array σ => some (T, σ)
    | _ => none
  | none => none

/-- The record an object literal with the labels `ls` and the expressions
`es` is checked against, if `T` is expected of it: `T` itself, a record, or
the case of a variant `T` the literal's tag picks. -/
def objTarget (T : Ty) (ls : List String) (es : List Expr) : Option Ty :=
  match T.whnf with
  | .app (.record _) _ => some T
  | .app (.variant (.field l) ts) Ps =>
    match litTag l ls es with
    | some t =>
      match firstIdx t ts with
      | some i =>
        match Ps[i]? with
        | some P => if P.tagOf l = some t then some P else none
        | none => none
      | none => none
    | none => none
  | _ => none

/-- Whether checking `e` against `T` pushes `T` into it: into the branches
of `?:` and `unwrap`, a sequence's last statement, a `let`'s body, a `try`, a function
literal's body against a function type, an array literal's elements against
an array type; `return`, `break` and `continue` have any type. Any other
expression is synthesised, and its type injected into `T`. -/
def Expr.pushes (T : Ty) : Expr → Bool
  | .cond .. | .seq .. | .let_ .. | .tryCatch .. | .tryFinally .. | .ret _ | .break_
  | .continue_ | .unwrap .. | .caseTag .. => true
  | .lit (.string s) => decide (T.whnf = .strLit s)
  | .obj ls es ks =>
    (objTarget T ls es).isSome && decide ls.Nodup && decide (ks = ls.map fun _ => .data)
  | .func k _ => (funcTarget (some T) k).isSome
  | .arr _ => (arrTarget (some T)).isSome
  | _ => false

/-- The mode an expected type gives an expression. -/
def Ex.mode : Option Ty → Mode
  | some _ => .check
  | none => .synth

/-- The mode `infer` types `e` in, given the expected type `ex`: checked if
`e` takes it in (`Expr.pushes`). -/
def exMode : Option Ty → Expr → Mode
  | some T, e => if e.pushes T then .check else .synth
  | none, _ => .synth

/-- What inferring `e` against the expected type `ex` gives, at its call
site: unchanged if `e` takes `ex` in; otherwise `e`'s type `τ`, synthesised,
is dropped if `ex` is `unknown` (`HasTypeS.drop`), or else injected into
`ex`, a waiting constraint `Inject T τ` (`HasTypeS.inj`). -/
def checkEx : Option Ty → Expr → Out → Out
  | some T, e, o =>
    if e.pushes T then o
    else if T = .unknown then ⟨o.σ, T, o.preds, o.next⟩
    else ⟨o.σ, T, o.preds ++ [⟨.inject T, [o.τ]⟩], o.next⟩
  | none, _, o => o

@[simp] theorem checkEx_none (e : Expr) : checkEx none e = id := rfl

/-- An expected type, an annotation's, has no type variables. -/
def Ex.Closed (ex : Option Ty) : Prop := ∀ T ∈ ex, T.ftv = []

theorem Ex.Closed.none : Ex.Closed none := fun _ h => nomatch h

theorem Ex.Closed.some {T : Ty} (h : T.ftv = []) : Ex.Closed (some T) := fun _ hT => by
  cases hT; exact h

@[simp] theorem exMode_none (e : Expr) : exMode none e = .synth := rfl
@[simp] theorem Ex.mode_none : Ex.mode none = .synth := rfl

/-- An expression that never takes an expected type in is synthesised. -/
theorem exMode_synth {ex : Option Ty} {e : Expr} (h : ∀ T, e.pushes T = false) :
    exMode ex e = .synth := by
  cases ex <;> simp [exMode, h]

/-- An expression that always takes an expected type in is checked against
it, if there is one. -/
theorem exMode_pushes {ex : Option Ty} {e : Expr} (h : ∀ T, e.pushes T = true) :
    exMode ex e = Ex.mode ex := by
  cases ex <;> simp [exMode, Ex.mode, h]
@[simp] theorem Ex.mode_some (T : Ty) : Ex.mode (some T) = .check := rfl

/-- Checked `return`s are checked against a type with no type variables,
an annotation's part. -/
def RetOk (rm : Mode) (R : Option Ty) : Prop := rm = .check → Ex.Closed R

theorem RetOk.synth {R : Option Ty} : RetOk .synth R := nofun

theorem RetOk.check {τ : Ty} (h : τ.ftv = []) : RetOk .check (some τ) := fun _ => Ex.Closed.some h

theorem RetOk.subst {rm : Mode} {R : Option Ty} (h : RetOk rm R) (σ : Subst) :
    RetOk rm (Ret.subst σ R) := fun hm τ hτ => by
  cases R with
  | none => cases hτ
  | some τ₀ =>
    cases hτ
    have := h hm τ₀ rfl
    simp only [Ty.closed_subst this]; exact this

/-- A checked function's return type, with no type variables, is unchanged by
a substitution. -/
theorem RetOk.subst_eq {R : Option Ty} (h : RetOk .check R) (σ : Subst) : Ret.subst σ R = R := by
  cases R with
  | none => rfl
  | some τ => simp [Ty.closed_subst (h rfl τ rfl)]

/-- Proves `RetOk rm R'` for `R'` the return type `R` an assumption
`RetOk rm R` is about, substituted. -/
macro "ret_ok" : tactic =>
  `(tactic| (repeat (first | assumption | exact RetOk.synth | apply RetOk.subst)))

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
/-- Algorithm W, with records over the labels `L`, and bidirectional: `R`
is the enclosing function's return type (`none` at the top level), and
`rm` whether its `return`s are checked against it; `ex` is the type `e` is
checked against, if any, which `e` takes in if it can (`Expr.pushes`) and
otherwise ignores, its caller injecting its type (`checkEx`); `n` is the
first unused type variable. -/
def infer : Ctx → Option Ty → Mode → Option Ty → Expr → Nat → Option Out
  -- A string literal checked against its own string type has it.
  | _, _, _, ex, .lit l, n =>
    some ⟨[], (ex.filter fun T => (Expr.lit l).pushes T).getD l.ty, [], n⟩
  | Γ, _, _, _, .var i, n =>
    match Γ[i]? with
    | some s => some ⟨[], s.open n, s.openPreds n, n + s.arity⟩
    | none => none
  -- Checked against a function type with as many parameters, the body is
  -- checked against its result type. Otherwise `this` is the variable `n`,
  -- the parameters `n + 1, …`, and the result the variable after them.
  | Γ, _, _, ex, .func k body, n =>
    match funcTarget ex k with
    | some (T, θ, τs, ρ) =>
      match (infer (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .check (some ρ)
          body n).map (checkEx (some ρ) body) with
      | none => none
      | some o => some ⟨o.σ, T, o.preds, o.next⟩
    | none =>
      let θ := Ty.var n
      let τs := varBlock (n + 1) k
      let ρ := Ty.var (n + 1 + k)
      match infer (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .synth none body
          (n + 2 + k) with
      | none => none
      | some o =>
        match unify (ρ.subst o.σ) o.τ with
        | none => none
        | some σ' =>
          let σ := Subst.compose σ' o.σ
          some ⟨σ, (Ty.fn θ τs ρ).subst σ, o.preds.map (·.subst σ'), o.next⟩
  -- A call outside any receiver: the callee's `this` is `undefined`.
  | Γ, R, rm, _, .app f args, n =>
    match infer Γ R rm none f n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none args o₁.next with
      | none => none
      | some o₂ =>
        let β := Ty.var o₂.next
        match unify (o₁.τ.subst o₂.σ) (.fn .undefined o₂.τs β) with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), β.subst σ₃,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst σ₃), o₂.next + 1⟩
  -- An annotated binding: the initialiser is checked against the declared
  -- type, which has no variables, and which the variable gets.
  | Γ, R, rm, ex, .let_ _ (some a) e₁ e₂, n =>
    if a.arity = 0 ∧ a.preds = [] ∧ a.ftv = [] ∧ a.rkeys = [] then
      match (infer Γ R rm (some (a.inst [])) e₁ n).map (checkEx (some (a.inst [])) e₁) with
      | none => none
      | some o₁ =>
        match (infer (a :: Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex e₂ o₁.next).map
            (checkEx ex e₂) with
        | none => none
        | some o₂ =>
          some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
    -- A polymorphic annotation: the initialiser, a syntactic value, is
    -- checked against it at rigid type variables named apart from the
    -- context's, the constraints on known types are decided, and the rigid
    -- type variables must not escape, into the context or into the
    -- constraints left.
    else if 0 < a.arity ∧ a.preds = [] ∧ a.ftv = [] ∧ a.rkeys = [] ∧ Expr.generalises e₁ e₂ then
      let k := maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R)
      let T := a.inst (rigids k a.arity)
      match (infer Γ R rm (some T) e₁ n).map (checkEx (some T) e₁) with
      | none => none
      | some o₁ =>
        match improveAll false o₁.preds.length o₁.preds with
        | none => none
        | some (σi, preds₁) =>
          let σ₁ := Subst.compose σi o₁.σ
          if k ∈ ctxRkeys (Ctx.subst σ₁ Γ) ∨ k ∈ Ret.rkeys (Ret.subst σ₁ R) ∨
              k ∈ preds₁.flatMap Pred.rkeys then none
          else
            match (infer (a :: Ctx.subst σ₁ Γ) (Ret.subst σ₁ R) rm ex e₂ o₁.next).map
                (checkEx ex e₂) with
            | none => none
            | some o₂ =>
              some ⟨Subst.compose o₂.σ σ₁, o₂.τ, preds₁.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
    else none
  -- The constraints on known types are decided first, as inty's
  -- `simplify_has_props` does before it generalises.
  | Γ, R, rm, ex, .let_ _ none e₁ e₂, n =>
    match infer Γ R rm none e₁ n with
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
          match (infer (s :: Γ₁) R₁ rm ex e₂ o₁.next).map (checkEx ex e₂) with
          | none => none
          | some o₂ =>
            some ⟨Subst.compose o₂.σ σ₁, o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
        else none
  -- `x = e`: `x`'s scheme is a monotype, which `e`'s type is unified with.
  | Γ, R, rm, _, .assign i e, n =>
    match Γ[i]? with
    | none => none
    | some s =>
      if s.arity = 0 ∧ s.preds = [] then
        match infer Γ R rm none e n with
        | none => none
        | some o =>
          match unify ((s.inst []).subst o.σ) o.τ with
          | none => none
          | some σ' =>
            some ⟨Subst.compose σ' o.σ, (s.inst []).subst (Subst.compose σ' o.σ),
              o.preds.map (·.subst σ'), o.next⟩
      else none
  -- An expected type is pushed into both branches.
  | Γ, R, rm, ex, .cond c t e, n =>
    match infer Γ R rm none c n with
    | none => none
    | some o₁ =>
      match (infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex t o₁.next).map (checkEx ex t) with
      | none => none
      | some o₂ =>
        match (infer (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) (Ret.subst o₂.σ (Ret.subst o₁.σ R)) rm ex
            e o₂.next).map (checkEx ex e) with
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
  | Γ, R, rm, _, .unop op e, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o =>
      match op with
      | .not => some ⟨o.σ, .boolean, o.preds, o.next⟩
      | .typeof => some ⟨o.σ, .string, o.preds, o.next⟩
      | .neg =>
        match unify o.τ .number with
        | none => none
        | some σ' => some ⟨Subst.compose σ' o.σ, .number, o.preds.map (·.subst σ'), o.next⟩
  | Γ, R, rm, _, .binop op e₁ e₂, n =>
    match infer Γ R rm none e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none e₂ o₁.next with
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
  -- `return e;` unifies `e`'s type with the function's, or checks `e`
  -- against it; it has any type: the expected one, or a fresh variable.
  | _, none, _, _, .ret _, _ => none
  | Γ, some τr, .synth, ex, .ret e, n =>
    match infer Γ (some τr) .synth none e n with
    | none => none
    | some o =>
      match unify (τr.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        some ⟨Subst.compose σ' o.σ, ex.getD (.var o.next), o.preds.map (·.subst σ'), o.next + 1⟩
  | Γ, some τr, .check, ex, .ret e, n =>
    match (infer Γ (some τr) .check (some τr) e n).map (checkEx (some τr) e) with
    | none => none
    | some o => some ⟨o.σ, ex.getD (.var o.next), o.preds, o.next + 1⟩
  | Γ, R, rm, _, .throw_ e, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o => some ⟨o.σ, .var o.next, o.preds, o.next + 1⟩
  -- A statement's value is dropped: `e₁` is checked against `unknown`.
  | Γ, R, rm, ex, .seq e₁ e₂, n =>
    match (infer Γ R rm (some .unknown) e₁ n).map (checkEx (some .unknown) e₁) with
    | none => none
    | some o₁ =>
      match (infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex e₂ o₁.next).map (checkEx ex e₂) with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
  | Γ, R, rm, _, .while_ c body, n =>
    match infer Γ R rm none c n with
    | none => none
    | some o₁ =>
      match (infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm (some .unknown) body o₁.next).map
          (checkEx (some .unknown) body) with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, .undefined, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
          o₂.next⟩
  -- `break` and `continue` have any type: the expected one, or a fresh
  -- variable.
  | _, _, _, ex, .break_, n | _, _, _, ex, .continue_, n => some ⟨[], ex.getD (.var n), [], n + 1⟩
  -- The caught value has the opaque type `unknown`; both branches have one
  -- type.
  | Γ, R, rm, ex, .tryCatch body handler, n =>
    match (infer Γ R rm ex body n).map (checkEx ex body) with
    | none => none
    | some o₁ =>
      match (infer (.mono .unknown :: Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex handler
          o₁.next).map (checkEx ex handler) with
      | none => none
      | some o₂ =>
        match unify (o₁.τ.subst o₂.σ) o₂.τ with
        | none => none
        | some σ₃ =>
          some ⟨Subst.compose σ₃ (Subst.compose o₂.σ o₁.σ), o₂.τ.subst σ₃,
            (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst σ₃), o₂.next⟩
  | Γ, R, rm, ex, .tryFinally body fin, n =>
    match (infer Γ R rm ex body n).map (checkEx ex body) with
    | none => none
    | some o₁ =>
      match (infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm (some .unknown) fin o₁.next).map
          (checkEx (some .unknown) fin) with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
          o₂.next⟩
  -- An object literal over the labels `L`: its fields present, each as
  -- its kind says, the other labels absent. A method's and a getter's
  -- `this` is the literal's type (`unifyThis`).
  -- An object literal checked against a record, or a variant's case:
  -- each field against its type there, which must make that record.
  | Γ, R, rm, ex, .obj ls es ks, n =>
    match ex.filter fun T => (Expr.obj ls es ks).pushes T with
    | some T =>
      match objTarget T ls es with
      | some P =>
        match P.dataFields ls with
        | some τs =>
          if ls.all (· ∈ L) ∧ es.length = ls.length ∧
              (unify P (.record L (objSlots L ls (τs.map fun τ => .slot .pre .data τ)))).isSome then
            match inferFields Γ R rm es τs n with
            | none => none
            | some o => some ⟨o.σ, T, o.preds, o.next⟩
          else none
        | none => none
      | none => none
    | none =>
    if ls.all (· ∈ L) ∧ es.length = ls.length ∧ ks.length = ls.length then
      match inferArgs Γ R rm none es n with
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
  -- instance. None is in the enclosing function: no `return` leaves it.
  | Γ, _, _, _, .cls ls es ks, n =>
    if ls.all (· ∈ L) ∧ ls.Nodup ∧ es.length = ls.length ∧ ks.length = ls.length then
      match inferMembers Γ [] none es ks n with
      | none => none
      | some o =>
        match memberSlots ks es o.τs o.next with
        | none => none
        | some (θs, ss, n') =>
          let T := Ty.record L (objSlots L ls ss)
          match unifyThis θs T with
          | none => none
          | some σ' => some ⟨Subst.compose σ' o.σ, T.subst σ',
              (o.preds ++ notNewPreds o.next n').map (·.subst σ'), n'⟩
    else none
  -- A constructor: a function whose `this` is what `new` makes.
  | Γ, _, _, _, .ctor k body, n =>
    let τs := varBlock n k
    let ρ := Ty.var (n + k)
    match infer (τs.map .mono ++ .mono (.fn .newTarget τs ρ) :: .mono .newTarget :: Γ) (some ρ)
        .synth none body (n + 1 + k) with
    | none => none
    | some o =>
      match unify (ρ.subst o.σ) o.τ with
      | none => none
      | some σ' =>
        let σ := Subst.compose σ' o.σ
        some ⟨σ, (Ty.fn .newTarget τs ρ).subst σ, o.preds.map (·.subst σ'), o.next⟩
  -- `new f(…)`: `f` a constructor, which gives a record, over fresh slots.
  | Γ, R, rm, _, .new_ f args, n =>
    match infer Γ R rm none f n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none args o₁.next with
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
  | Γ, R, rm, _, .get e l, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o =>
      some ⟨o.σ, .var (o.next + 1),
        o.preds ++ [⟨.hasProp l, [o.τ, .var o.next, .var (o.next + 1)]⟩], o.next + 2⟩
  -- `e.l = v`: `HasProp l τ data ρ`, `ρ` being `v`'s type.
  | Γ, R, rm, _, .set e l v, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none v o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₂.τ,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++ [⟨.hasProp l, [o₁.τ.subst o₂.σ, .data, o₂.τ]⟩],
          o₂.next⟩
  -- `{...e₁, ...e₂}`: `e₁` a record, `e₂` a record each of whose slots is
  -- a presence, a kind and a type, and a `Merge` for each label, all at
  -- fresh variables after `e₂`'s: the slots written over, the presences,
  -- the kinds, the types, and the result's slots.
  | Γ, R, rm, _, .spread e₁ e₂, n =>
    match infer Γ R rm none e₁ n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none e₂ o₁.next with
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
  -- `[e₀, …]`: checked against an array type, each element is checked
  -- against its element type; otherwise one type for the elements, a fresh
  -- variable.
  | Γ, R, rm, ex, .arr es, n =>
    match arrTarget ex with
    | some (T, σ) =>
      match inferArgs Γ R rm (some σ) es n with
      | none => none
      | some o => some ⟨o.σ, T, o.preds, o.next⟩
    | none =>
      match inferArgs Γ R rm none es n with
      | none => none
      | some o =>
        match unify (.tuple o.τs) (.tuple (List.replicate o.τs.length (.var o.next))) with
        | none => none
        | some σ' =>
          some ⟨Subst.compose σ' o.σ, (Ty.array (.var o.next)).subst σ', o.preds.map (·.subst σ'),
            o.next + 1⟩
  -- `e[i]`: `Indexable τ ι β`, for a fresh `β`.
  | Γ, R, rm, _, .index e i, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none i o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, .var o₂.next,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
            [⟨.indexable, [o₁.τ.subst o₂.σ, o₂.τ, .var o₂.next]⟩],
          o₂.next + 1⟩
  -- `e[i] = v`: `Indexable τ ι ρ` and `IndexWrite τ`, `ρ` being `v`'s type.
  | Γ, R, rm, _, .setIndex e i v, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o₁ =>
      match infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none i o₁.next with
      | none => none
      | some o₂ =>
        match infer (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) (Ret.subst o₂.σ (Ret.subst o₁.σ R)) rm none v
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
  | Γ, R, rm, _, .mcall e l args, n =>
    match infer Γ R rm none e n with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm none args o₁.next with
      | none => none
      | some o₂ =>
        let τ := o₁.τ.subst o₂.σ
        some ⟨Subst.compose o₂.σ o₁.σ, .var (o₂.next + 1),
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
            [⟨.hasProp l, [τ, .var o₂.next, .fn τ o₂.τs (.var (o₂.next + 1))]⟩],
          o₂.next + 2⟩
  -- `unwrap e₁ e₂ e₃`: `Strip τ₁ β` for `e₁`'s type `τ₁` and a fresh `β`,
  -- the type of what `e₃` binds; an expected type is pushed into both
  -- branches, which have one type.
  | Γ, R, rm, ex, .unwrap e₁ e₂ e₃, n =>
    match infer Γ R rm none e₁ n with
    | none => none
    | some o₁ =>
      match (infer (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex e₂ o₁.next).map (checkEx ex e₂) with
      | none => none
      | some o₂ =>
        let β := Ty.var o₂.next
        match (infer (.mono β :: Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ))
            (Ret.subst o₂.σ (Ret.subst o₁.σ R)) rm ex e₃ (o₂.next + 1)).map (checkEx ex e₃) with
        | none => none
        | some o₃ =>
          match unify (o₂.τ.subst o₃.σ) o₃.τ with
          | none => none
          | some σ₄ =>
            some ⟨Subst.compose σ₄ (Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ)), o₃.τ.subst σ₄,
              ((o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
                [(⟨.strip, [o₁.τ.subst o₂.σ, β]⟩ : Pred)]).map (·.subst o₃.σ) ++ o₃.preds).map
                (·.subst σ₄),
              o₃.next⟩
  -- A variant taken apart by its tag: `e₂` sees `e₁`'s value as the rest
  -- (a fresh variable), `e₃` as the case of the tag (another), which
  -- `Case_{l,t}` relates to `e₁`'s type; an expected type is pushed into
  -- both branches.
  | Γ, R, rm, ex, .caseTag e₁ d t e₂ e₃, n =>
    match infer Γ R rm none e₁ n with
    | none => none
    | some o₁ =>
      let ρv := Ty.var o₁.next
      match (infer (.mono ρv :: Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex e₂ (o₁.next + 1)).map
          (checkEx ex e₂) with
      | none => none
      | some o₂ =>
        let σv := Ty.var o₂.next
        match (infer (.mono σv :: Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ))
            (Ret.subst o₂.σ (Ret.subst o₁.σ R)) rm ex e₃ (o₂.next + 1)).map (checkEx ex e₃) with
        | none => none
        | some o₃ =>
          match unify (o₂.τ.subst o₃.σ) o₃.τ with
          | none => none
          | some σ₄ =>
            some ⟨Subst.compose σ₄ (Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ)), o₃.τ.subst σ₄,
              ((o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
                [(⟨.caseTag d t, [o₁.τ.subst o₂.σ, σv, ρv.subst o₂.σ]⟩ : Pred)]).map
                  (·.subst o₃.σ) ++ o₃.preds).map (·.subst σ₄),
              o₃.next⟩

/-- Infer an object literal's fields, left to right, threading the
substitution, each checked against its own type. -/
def inferFields : Ctx → Option Ty → Mode → List Expr → List Ty → Nat → Option OutArgs
  | _, _, _, [], [], n => some ⟨[], [], [], n⟩
  | Γ, R, rm, e :: es, τ :: τs, n =>
    match (infer Γ R rm (some τ) e n).map (checkEx (some τ) e) with
    | none => none
    | some o₁ =>
      match inferFields (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm es τs o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ :: o₂.τs,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
  | _, _, _, _, _, _ => none

/-- Infer a list of arguments, left to right, threading the substitution,
each checked against `ex` if it is given. -/
def inferArgs : Ctx → Option Ty → Mode → Option Ty → List Expr → Nat → Option OutArgs
  | _, _, _, _, [], n => some ⟨[], [], [], n⟩
  | Γ, R, rm, ex, a :: as, n =>
    match (infer Γ R rm ex a n).map (checkEx ex a) with
    | none => none
    | some o₁ =>
      match inferArgs (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) rm ex as o₁.next with
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
    match infer (Δ.map .mono ++ Γ) R .synth none e n with
    | none => none
    | some o₁ =>
      match inferMembers (Ctx.subst o₁.σ Γ) (o₁.τ :: Δ.map (·.subst o₁.σ)) (Ret.subst o₁.σ R) es
          ks o₁.next with
      | none => none
      | some o₂ =>
        some ⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ :: o₂.τs,
          o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩
  | Γ, Δ, R, e :: es, _ :: ks, n =>
    match infer Γ R .synth none e n with
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
    match infer L Γ none .synth none e 0 with
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
  | .let_ _ _ a b | .binop _ a b | .seq a b | .while_ a b | .tryCatch a b | .tryFinally a b =>
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
  | .unwrap a b c => a.labels ++ b.labels ++ c.labels
  | .caseTag a (.field l) _ b c => l :: (a.labels ++ b.labels ++ c.labels)
  | .caseTag a .typeOf _ b c => a.labels ++ b.labels ++ c.labels
/-- `labels`, for a list of expressions. -/
def Expr.labelsList : List Expr → List String
  | [] => []
  | e :: es => e.labels ++ Expr.labelsList es
end

/-- Infer the type of a closed program, with records over its labels. -/
def inferProgram (e : Expr) : Option Ty := inferIn e.labels.eraseDups [] e

end Inty
