/-!
# Types and type schemes

Monotypes `Ty` may mention free type variables `var a`. A type scheme
`∀ α₀ … αₖ₋₁. τ` is a `Scheme` whose body is a `PTy`, where `bound i` refers to
the `i`-th quantified variable. Keeping bound and free variables in separate
syntax (a locally nameless representation) means substituting for free
variables can never capture a bound one, and a monotype can never contain a
dangling bound variable.
-/

namespace Inty

/-- Type constructors. Every type former is one, applied to its argument
types (`Ty.app`), so substitution, unification and their lemmas are written
once for all of them. -/
inductive Con where
  | number
  | string
  | boolean
  | undefined
  | null
  /-- What a `catch` binds: any value at all, since anything can be thrown.
  Nothing can be done with it but what any type allows: passing it on,
  testing it, `typeof`, rethrowing it. inty gives it a rigid type variable
  (a skolem). -/
  | unknown
  /-- A function, applied to the type of `this` in its body, its result's
  type, and its parameters' types (`Ty.fn`). In inty a function value is a
  row carrying a call signature (`Type::Func` inside a row); this is that
  signature alone. -/
  | fn
  /-- A record over the labels `labels`, applied to one slot per label
  (`Ty.record`). The typing rules use the program's labels (Rémy's flat
  rows): a record has a slot for every label of the program, saying whether
  the field is there. -/
  | record (labels : List String)
  /-- A record's slot, applied to a presence and the field's type
  (`types::FieldEntry`). -/
  | slot
  /-- The presence of a field that is there, `Presence::Pre`. -/
  | pre
  /-- The presence of a field that isn't, `Presence::Abs`. -/
  | abs
  /-- An array, applied to its element type (`Type::Array`). -/
  | array
  /-- A tuple, applied to its components' types. Inference uses it to state
  several equations as one (`unify` on two tuples). -/
  | tuple
  deriving DecidableEq, Repr

/-- Monotypes: a type variable, or a constructor applied to types. A type
variable stands for a type, a presence or a slot alike: the constructors
keep them apart. -/
inductive Ty where
  | var (a : Nat)
  | app (c : Con) (args : List Ty)
  deriving Repr

/-- The body of a type scheme: a monotype that may also mention the scheme's
quantified variables, `bound i`. -/
inductive PTy where
  | free (a : Nat)
  | bound (i : Nat)
  | app (c : Con) (args : List PTy)
  deriving Repr

/-! `Ty` and `PTy` nest lists, so Lean derives neither their equality test
nor their induction principles; they are below. The functions on them
recurse through a list by a mutual function on the list (`Ty.substs`), which
keeps them structural, so the kernel evaluates them (`by decide`), and a
simp lemma rewrites each list function to a `map`. -/

mutual
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .var a, .var b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .app c₁ a₁, .app c₂ a₂ =>
    if hc : c₁ = c₂ then
      match Ty.decEqs a₁ a₂ with
      | isTrue ha => isTrue (by subst hc ha; rfl)
      | isFalse ha => isFalse (by intro e; cases e; exact ha rfl)
    else isFalse (by intro e; cases e; exact hc rfl)
  | .var _, .app .. | .app .., .var _ => isFalse (by intro e; cases e)
def Ty.decEqs : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Ty.decEq a b, Ty.decEqs as bs with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
    | isFalse h, _ | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Ty := Ty.decEq

mutual
def PTy.decEq : (a b : PTy) → Decidable (a = b)
  | .free a, .free b | .bound a, .bound b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .app c₁ a₁, .app c₂ a₂ =>
    if hc : c₁ = c₂ then
      match PTy.decEqs a₁ a₂ with
      | isTrue ha => isTrue (by subst hc ha; rfl)
      | isFalse ha => isFalse (by intro e; cases e; exact ha rfl)
    else isFalse (by intro e; cases e; exact hc rfl)
  | .free _, .bound _ | .free _, .app .. | .bound _, .free _ | .bound _, .app ..
  | .app .., .free _ | .app .., .bound _ => isFalse (by intro e; cases e)
def PTy.decEqs : (a b : List PTy) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match PTy.decEq a b, PTy.decEqs as bs with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
    | isFalse h, _ | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq PTy := PTy.decEq

/-! Names for the types of each constructor, usable as patterns. -/

@[match_pattern] abbrev Ty.number : Ty := .app .number []
@[match_pattern] abbrev Ty.string : Ty := .app .string []
@[match_pattern] abbrev Ty.boolean : Ty := .app .boolean []
@[match_pattern] abbrev Ty.undefined : Ty := .app .undefined []
@[match_pattern] abbrev Ty.null : Ty := .app .null []
@[match_pattern] abbrev Ty.unknown : Ty := .app .unknown []
/-- `θ, (τs) => ρ`: `this` of type `θ`, parameters `τs`, result `ρ`. -/
@[match_pattern] abbrev Ty.fn (θ : Ty) (τs : List Ty) (ρ : Ty) : Ty := .app .fn (θ :: ρ :: τs)
@[match_pattern] abbrev Ty.record (ls : List String) (slots : List Ty) : Ty :=
  .app (.record ls) slots
@[match_pattern] abbrev Ty.slot (p τ : Ty) : Ty := .app .slot [p, τ]
@[match_pattern] abbrev Ty.pre : Ty := .app .pre []
@[match_pattern] abbrev Ty.abs : Ty := .app .abs []
@[match_pattern] abbrev Ty.array (τ : Ty) : Ty := .app .array [τ]
@[match_pattern] abbrev Ty.tuple (τs : List Ty) : Ty := .app .tuple τs

@[match_pattern] abbrev PTy.number : PTy := .app .number []
@[match_pattern] abbrev PTy.string : PTy := .app .string []
@[match_pattern] abbrev PTy.boolean : PTy := .app .boolean []
@[match_pattern] abbrev PTy.undefined : PTy := .app .undefined []
@[match_pattern] abbrev PTy.null : PTy := .app .null []
@[match_pattern] abbrev PTy.unknown : PTy := .app .unknown []
@[match_pattern] abbrev PTy.fn (θ : PTy) (τs : List PTy) (ρ : PTy) : PTy :=
  .app .fn (θ :: ρ :: τs)

/-- Induction on `Ty`, with a hypothesis for each argument type. -/
theorem Ty.ind {motive : Ty → Prop} (var : ∀ a, motive (.var a))
    (app : ∀ c args, (∀ p ∈ args, motive p) → motive (.app c args)) : ∀ τ, motive τ
  | .var a => var a
  | .app c args => app c args (fun p _ => Ty.ind var app p)
termination_by τ => sizeOf τ
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-- Induction on `PTy`, with a hypothesis for each argument type. -/
theorem PTy.ind {motive : PTy → Prop} (free : ∀ a, motive (.free a))
    (bound : ∀ i, motive (.bound i))
    (app : ∀ c args, (∀ p ∈ args, motive p) → motive (.app c args)) : ∀ p, motive p
  | .free a => free a
  | .bound i => bound i
  | .app c args => app c args (fun p _ => PTy.ind free bound app p)
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-- Type classes, as `classes::ClassName`. Their instances are in
`Inty.Classes`. -/
inductive Cls where
  /-- `Plus a`: the types `+` is defined on. -/
  | plus
  /-- `HasProp l a b` (`a has {l: b}` in inty's syntax): reading `.l` from
  a value of type `a` gives a `b`. It is what a property read on a value
  whose type isn't known yet records. -/
  | hasProp (l : String)
  /-- `Merge p τ s r`: a spread operand whose slot for some label has the
  presence `p` and the type `τ`, written over a slot `s`, gives the slot
  `r`: the operand's field if it has one, `s` if not. Its decision waits
  for `p`, so a spread of a row whose fields aren't known yet has a
  principal type. -/
  | merge
  /-- `Indexable c i e`: indexing a `c` by an `i` gives an `e` (`c[i]`):
  an array by a number, its element; a string by a number, a string. The
  container determines the rest. -/
  | indexable
  /-- `IndexWrite c`: an element of a `c` can be stored (`c[i] = v`): an
  array's, not a string's. -/
  | indexWrite
  /-- `FieldWrite r`: a property of an `r` can be stored (`r.p = v`): an
  object's, not an array's or a string's built-in one. -/
  | fieldWrite
  deriving DecidableEq, Repr

/-- How many types a class is applied to. -/
def Cls.arity : Cls → Nat
  | .plus | .indexWrite | .fieldWrite => 1
  | .hasProp _ => 2
  | .indexable => 3
  | .merge => 4

/-- A class constraint: a class applied to types, such as `Plus a`. -/
structure Pred where
  cls : Cls
  args : List Ty
  deriving DecidableEq, Repr

/-- A class constraint in a scheme, which may mention its quantified
variables. -/
structure PPred where
  cls : Cls
  args : List PTy
  deriving DecidableEq, Repr

/-- A type scheme `∀ α₀ … α_{arity-1}. preds ⇒ body`: `preds` are the class
constraints an instance must satisfy, as in inty's
`<a> where Plus a => (a, a) => a`. -/
structure Scheme where
  arity : Nat
  body : PTy
  preds : List PPred := []
  deriving DecidableEq, Repr

/-- A typing context: the type scheme of each variable, innermost first. -/
abbrev Ctx := List Scheme

mutual
/-- A monotype as a scheme body. -/
def Ty.toPTy : Ty → PTy
  | .var a => .free a
  | .app c args => .app c (Ty.toPTys args)
def Ty.toPTys : List Ty → List PTy
  | [] => []
  | τ :: τs => τ.toPTy :: Ty.toPTys τs
end

@[simp] theorem Ty.toPTys_eq (τs : List Ty) : Ty.toPTys τs = τs.map Ty.toPTy := by
  induction τs <;> simp_all [Ty.toPTys]

@[simp] theorem Ty.toPTy_app (c : Con) (args : List Ty) :
    (Ty.app c args).toPTy = .app c (args.map Ty.toPTy) := by simp [Ty.toPTy]

mutual
/-- Instantiate a scheme body: `bound i` becomes `τs[i]`. A well-formed scheme
only has `bound i` with `i < arity`; out of range gives `undefined`. -/
def PTy.inst (τs : List Ty) : PTy → Ty
  | .free a => .var a
  | .bound i => τs.getD i .undefined
  | .app c args => .app c (PTy.insts τs args)
def PTy.insts (τs : List Ty) : List PTy → List Ty
  | [] => []
  | p :: ps => p.inst τs :: PTy.insts τs ps
end

@[simp] theorem PTy.insts_eq (τs : List Ty) (ps : List PTy) :
    PTy.insts τs ps = ps.map (PTy.inst τs) := by
  induction ps <;> simp_all [PTy.insts]

@[simp] theorem PTy.inst_app (τs : List Ty) (c : Con) (args : List PTy) :
    (PTy.app c args).inst τs = .app c (args.map (·.inst τs)) := by simp [PTy.inst]

def PPred.inst (τs : List Ty) (p : PPred) : Pred := ⟨p.cls, p.args.map (·.inst τs)⟩

/-- A monotype as a scheme that quantifies nothing. -/
def Scheme.mono (τ : Ty) : Scheme := ⟨0, τ.toPTy, []⟩

def Scheme.inst (s : Scheme) (τs : List Ty) : Ty := s.body.inst τs

/-- The constraints of an instance. -/
def Scheme.instPreds (s : Scheme) (τs : List Ty) : List Pred := s.preds.map (·.inst τs)

/-- The type variables `m, m+1, …, m+k-1`. -/
def varBlock (m k : Nat) : List Ty := (List.range' m k).map .var

/-- Open a scheme with the type variables `m, m+1, …`, one per quantified
variable. -/
def Scheme.open (s : Scheme) (m : Nat) : Ty := s.inst (varBlock m s.arity)

/-- The constraints of a scheme opened at `m`. -/
def Scheme.openPreds (s : Scheme) (m : Nat) : List Pred := s.instPreds (varBlock m s.arity)

/-! ## Free type variables -/

mutual
def Ty.ftv : Ty → List Nat
  | .var a => [a]
  | .app _ args => Ty.ftvs args
def Ty.ftvs : List Ty → List Nat
  | [] => []
  | τ :: τs => τ.ftv ++ Ty.ftvs τs
end

@[simp] theorem Ty.ftvs_eq (τs : List Ty) : Ty.ftvs τs = τs.flatMap Ty.ftv := by
  induction τs <;> simp_all [Ty.ftvs]

@[simp] theorem Ty.ftv_var (a : Nat) : (Ty.var a).ftv = [a] := rfl
@[simp] theorem Ty.ftv_app (c : Con) (args : List Ty) :
    (Ty.app c args).ftv = args.flatMap Ty.ftv := by simp [Ty.ftv]

mutual
def PTy.ftv : PTy → List Nat
  | .free a => [a]
  | .bound _ => []
  | .app _ args => PTy.ftvs args
def PTy.ftvs : List PTy → List Nat
  | [] => []
  | p :: ps => p.ftv ++ PTy.ftvs ps
end

@[simp] theorem PTy.ftvs_eq (ps : List PTy) : PTy.ftvs ps = ps.flatMap PTy.ftv := by
  induction ps <;> simp_all [PTy.ftvs]

@[simp] theorem PTy.ftv_app (c : Con) (args : List PTy) :
    (PTy.app c args).ftv = args.flatMap PTy.ftv := by simp [PTy.ftv]

mutual
/-- A scheme body's quantified variables, as their indices. -/
def PTy.bvs : PTy → List Nat
  | .free _ => []
  | .bound i => [i]
  | .app _ args => PTy.bvss args
def PTy.bvss : List PTy → List Nat
  | [] => []
  | p :: ps => p.bvs ++ PTy.bvss ps
end

@[simp] theorem PTy.bvss_eq (ps : List PTy) : PTy.bvss ps = ps.flatMap PTy.bvs := by
  induction ps <;> simp_all [PTy.bvss]

@[simp] theorem PTy.bvs_app (c : Con) (args : List PTy) :
    (PTy.app c args).bvs = args.flatMap PTy.bvs := by simp [PTy.bvs]

def Pred.ftv (p : Pred) : List Nat := p.args.flatMap Ty.ftv

def PPred.ftv (p : PPred) : List Nat := p.args.flatMap PTy.ftv

def Scheme.ftv (s : Scheme) : List Nat := s.body.ftv ++ s.preds.flatMap PPred.ftv

def ctxFtv (Γ : List Scheme) : List Nat := Γ.flatMap Scheme.ftv

/-! ## Substitution of free type variables -/

/-- A finite substitution of types for type variables. -/
abbrev Subst := List (Nat × Ty)

def Subst.find : Subst → Nat → Option Ty
  | [], _ => none
  | (b, τ) :: σ, a => if a = b then some τ else Subst.find σ a

mutual
def Ty.subst (σ : Subst) : Ty → Ty
  | .var a => (σ.find a).getD (.var a)
  | .app c args => .app c (Ty.substs σ args)
def Ty.substs (σ : Subst) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.subst σ :: Ty.substs σ τs
end

@[simp] theorem Ty.substs_eq (σ : Subst) (τs : List Ty) :
    Ty.substs σ τs = τs.map (Ty.subst σ) := by
  induction τs <;> simp_all [Ty.substs]

@[simp] theorem Ty.subst_app (σ : Subst) (c : Con) (args : List Ty) :
    (Ty.app c args).subst σ = .app c (args.map (·.subst σ)) := by
  simp [Ty.subst]

theorem Ty.subst_fn (σ : Subst) (t : Ty) (ps : List Ty) (r : Ty) :
    (Ty.fn t ps r).subst σ = .fn (t.subst σ) (ps.map (·.subst σ)) (r.subst σ) := by
  simp

mutual
def PTy.subst (σ : Subst) : PTy → PTy
  | .free a => ((σ.find a).getD (.var a)).toPTy
  | .bound i => .bound i
  | .app c args => .app c (PTy.substs σ args)
def PTy.substs (σ : Subst) : List PTy → List PTy
  | [] => []
  | p :: ps => p.subst σ :: PTy.substs σ ps
end

@[simp] theorem PTy.substs_eq (σ : Subst) (ps : List PTy) :
    PTy.substs σ ps = ps.map (PTy.subst σ) := by
  induction ps <;> simp_all [PTy.substs]

@[simp] theorem PTy.subst_app (σ : Subst) (c : Con) (args : List PTy) :
    (PTy.app c args).subst σ = .app c (args.map (·.subst σ)) := by
  simp [PTy.subst]

def Pred.subst (σ : Subst) (p : Pred) : Pred := ⟨p.cls, p.args.map (·.subst σ)⟩

def PPred.subst (σ : Subst) (p : PPred) : PPred := ⟨p.cls, p.args.map (·.subst σ)⟩

def Scheme.subst (σ : Subst) (s : Scheme) : Scheme :=
  ⟨s.arity, s.body.subst σ, s.preds.map (·.subst σ)⟩

/-! ## Lemmas -/

@[simp] theorem Ty.toPTy_inst (τ : Ty) (τs : List Ty) : τ.toPTy.inst τs = τ := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.inst_app, List.map_map, Ty.app.injEq, true_and]
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left ih

@[simp] theorem Scheme.mono_inst (τ : Ty) (τs : List Ty) :
    (Scheme.mono τ).inst τs = τ := by
  simp [Scheme.mono, Scheme.inst]

@[simp] theorem Ty.toPTy_subst (σ : Subst) (τ : Ty) :
    τ.toPTy.subst σ = (τ.subst σ).toPTy := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.subst_app, Ty.subst_app, List.map_map, PTy.app.injEq, true_and]
    exact List.map_congr_left ih

@[simp] theorem Ty.toPTy_bvs (τ : Ty) : τ.toPTy.bvs = [] := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.bvs_app, List.flatMap_map, List.flatMap_eq_nil_iff]
    exact ih

/-- Substitution touches only the free variables. -/
@[simp] theorem PTy.bvs_subst (σ : Subst) (p : PTy) : (p.subst σ).bvs = p.bvs := by
  induction p using PTy.ind with
  | free a => simp [PTy.subst, PTy.bvs]
  | bound i => rfl
  | app c args ih =>
    simp only [PTy.subst_app, PTy.bvs_app, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih

@[simp] theorem Scheme.mono_subst (σ : Subst) (τ : Ty) :
    (Scheme.mono τ).subst σ = Scheme.mono (τ.subst σ) := by
  simp [Scheme.mono, Scheme.subst]

/-- Substitution commutes with instantiation. -/
theorem PTy.inst_subst (σ : Subst) (τs : List Ty) (p : PTy) :
    (p.inst τs).subst σ = (p.subst σ).inst (τs.map (·.subst σ)) := by
  induction p using PTy.ind with
  | free a => simp [PTy.inst, PTy.subst]; rfl
  | bound i =>
    simp only [PTy.inst, PTy.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases τs[i]? <;> rfl
  | app c args ih =>
    simp only [PTy.inst_app, PTy.subst_app, Ty.subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left ih

theorem Scheme.inst_subst (σ : Subst) (τs : List Ty) (s : Scheme) :
    (s.inst τs).subst σ = (s.subst σ).inst (τs.map (·.subst σ)) :=
  PTy.inst_subst σ τs s.body

theorem Scheme.inst_nil_subst (σ : Subst) (s : Scheme) :
    (s.inst []).subst σ = (s.subst σ).inst [] := by
  simpa using Scheme.inst_subst σ [] s

theorem PPred.inst_subst (σ : Subst) (τs : List Ty) (p : PPred) :
    (p.inst τs).subst σ = (p.subst σ).inst (τs.map (·.subst σ)) := by
  simp [PPred.inst, Pred.subst, PPred.subst, PTy.inst_subst]

theorem Scheme.instPreds_subst (σ : Subst) (τs : List Ty) (s : Scheme) :
    (s.instPreds τs).map (·.subst σ) = (s.subst σ).instPreds (τs.map (·.subst σ)) := by
  simp [Scheme.instPreds, Scheme.subst, PPred.inst_subst]

/-- A substitution that leaves alone every variable it doesn't map. -/
theorem Subst.find_none {σ : Subst} {a : Nat} (h : ∀ p ∈ σ, p.1 ≠ a) :
    σ.find a = none := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨b, τ⟩ := p
    have hb : a ≠ b := fun e => h (b, τ) List.mem_cons_self e.symm
    simp [Subst.find, hb, ih (fun q hq => h q (by simp [hq]))]

theorem Ty.subst_id {σ : Subst} {τ : Ty} (h : ∀ a ∈ τ.ftv, σ.find a = none) :
    τ.subst σ = τ := by
  induction τ using Ty.ind with
  | var a => simp [Ty.subst, h a (by simp)]
  | app c args ih =>
    simp only [Ty.ftv_app, List.mem_flatMap] at h
    simp only [Ty.subst_app, Ty.app.injEq, true_and]
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))

theorem PTy.subst_id {σ : Subst} {p : PTy} (h : ∀ a ∈ p.ftv, σ.find a = none) :
    p.subst σ = p := by
  induction p using PTy.ind with
  | free a => simp [PTy.subst, h a (by simp [PTy.ftv]), Ty.toPTy]
  | bound i => rfl
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at h
    simp only [PTy.subst_app, PTy.app.injEq, true_and]
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))

theorem Pred.subst_id {σ : Subst} {p : Pred} (h : ∀ a ∈ p.ftv, σ.find a = none) :
    p.subst σ = p := by
  obtain ⟨c, args⟩ := p
  simp only [Pred.subst, Pred.mk.injEq, true_and]
  conv => rhs; rw [← List.map_id args]
  exact List.map_congr_left (fun τ hτ =>
    Ty.subst_id (fun a ha => h a (List.mem_flatMap.mpr ⟨τ, hτ, ha⟩)))

theorem PPred.subst_id {σ : Subst} {p : PPred} (h : ∀ a ∈ p.ftv, σ.find a = none) :
    p.subst σ = p := by
  obtain ⟨c, args⟩ := p
  simp only [PPred.subst, PPred.mk.injEq, true_and]
  conv => rhs; rw [← List.map_id args]
  exact List.map_congr_left (fun q hq =>
    PTy.subst_id (fun a ha => h a (List.mem_flatMap.mpr ⟨q, hq, ha⟩)))

theorem ctx_subst_id {σ : Subst} {Γ : List Scheme}
    (h : ∀ a ∈ ctxFtv Γ, σ.find a = none) : Γ.map (Scheme.subst σ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    simp only [ctxFtv, List.flatMap_cons, List.mem_append] at h
    have hs : s.subst σ = s := by
      obtain ⟨k, p, ps⟩ := s
      simp only [Scheme.ftv, List.mem_append, List.mem_flatMap] at h
      simp only [Scheme.subst, Scheme.mk.injEq, true_and]
      refine ⟨PTy.subst_id (fun a ha => h a (.inl (.inl ha))), ?_⟩
      conv => rhs; rw [← List.map_id ps]
      exact List.map_congr_left (fun q hq =>
        PPred.subst_id (fun a ha => h a (.inl (.inr ⟨q, hq, ha⟩))))
    simp [hs, ih (fun a ha => h a (.inr (by simpa [ctxFtv] using ha)))]

/-- Substituting for variables below `m` commutes with opening at `m`. -/
theorem PTy.open_subst {σ : Subst} {m : Nat} (k : Nat) (p : PTy)
    (h : ∀ q ∈ σ, q.1 < m) : (p.inst (varBlock m k)).subst σ = (p.subst σ).inst (varBlock m k) := by
  simp only [varBlock, PTy.inst_subst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hm : m ≤ a := by
    obtain ⟨i, _, rfl⟩ := List.mem_range'.mp ha; omega
  have : σ.find a = none :=
    Subst.find_none (fun q hq e => by have := h q hq; omega)
  simp [Ty.subst, this]

theorem Scheme.open_subst {σ : Subst} {m : Nat} (s : Scheme)
    (h : ∀ p ∈ σ, p.1 < m) : (s.open m).subst σ = (s.subst σ).open m :=
  PTy.open_subst _ s.body h

theorem PPred.open_subst {σ : Subst} {m : Nat} (k : Nat) (p : PPred)
    (h : ∀ q ∈ σ, q.1 < m) :
    (p.inst (varBlock m k)).subst σ = (p.subst σ).inst (varBlock m k) := by
  simp only [PPred.inst, Pred.subst, PPred.subst, List.map_map, Pred.mk.injEq,
    true_and]
  exact List.map_congr_left (fun q _ => PTy.open_subst k q h)

theorem Scheme.openPreds_subst {σ : Subst} {m : Nat} (s : Scheme)
    (h : ∀ p ∈ σ, p.1 < m) : (s.openPreds m).map (·.subst σ) = (s.subst σ).openPreds m := by
  simp only [Scheme.openPreds, Scheme.instPreds, Scheme.subst, List.map_map]
  exact List.map_congr_left (fun p _ => PPred.open_subst _ p h)

/-- The substitution sending `m + i` to `τs[i]`. -/
def Subst.block (m : Nat) (τs : List Ty) : Subst :=
  (List.range' m τs.length).zip τs

theorem Subst.block_keys {m : Nat} {τs : List Ty} :
    ∀ p ∈ Subst.block m τs, m ≤ p.1 := by
  intro p hp
  have := (List.of_mem_zip hp).1
  obtain ⟨i, _, h⟩ := List.mem_range'.mp this; omega

theorem Subst.block_find (m : Nat) (τs : List Ty) :
    ∀ i, (Subst.block m τs).find (m + i) = τs[i]? := by
  induction τs generalizing m with
  | nil => intro i; rfl
  | cons τ τs ih =>
    intro i
    cases i with
    | zero => simp [Subst.block, List.range'_succ, Subst.find]
    | succ i =>
      have := ih (m + 1) i
      simp only [Subst.block, List.length_cons, List.range'_succ, List.zip_cons_cons,
        Subst.find] at this ⊢
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- Opening above the free variables, then substituting, is instantiation. -/
theorem PTy.open_block (p : PTy) {m : Nat} {τs : List Ty}
    (hm : ∀ a ∈ p.ftv, a < m) :
    (p.inst (varBlock m τs.length)).subst (Subst.block m τs) = p.inst τs := by
  induction p using PTy.ind with
  | free a =>
    have ha := hm a (by simp [PTy.ftv])
    have : (Subst.block m τs).find a = none :=
      Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
    simp [PTy.inst, Ty.subst, this]
  | bound i =>
    simp only [varBlock, PTy.inst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.block_find]
    · simp [hi]
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at hm
    simp only [PTy.inst_app, Ty.subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => hm a ⟨p, hp, ha⟩))

theorem Scheme.open_block (s : Scheme) {m : Nat} {τs : List Ty}
    (hm : ∀ a ∈ s.ftv, a < m) (hlen : τs.length = s.arity) :
    (s.open m).subst (Subst.block m τs) = s.inst τs := by
  simp only [Scheme.open, Scheme.inst, ← hlen]
  exact PTy.open_block _ (fun a ha => hm a (List.mem_append_left _ ha))

theorem PPred.open_block (p : PPred) {m : Nat} {τs : List Ty}
    (hm : ∀ a ∈ p.ftv, a < m) :
    (p.inst (varBlock m τs.length)).subst (Subst.block m τs) = p.inst τs := by
  simp only [PPred.inst, Pred.subst, List.map_map, Pred.mk.injEq, true_and]
  exact List.map_congr_left (fun q hq =>
    PTy.open_block q (fun a ha => hm a (List.mem_flatMap.mpr ⟨q, hq, ha⟩)))

theorem Scheme.openPreds_block (s : Scheme) {m : Nat} {τs : List Ty}
    (hm : ∀ a ∈ s.ftv, a < m) (hlen : τs.length = s.arity) :
    (s.openPreds m).map (·.subst (Subst.block m τs)) = s.instPreds τs := by
  simp only [Scheme.openPreds, Scheme.instPreds, List.map_map, ← hlen]
  exact List.map_congr_left (fun p hp => PPred.open_block p (fun a ha =>
    hm a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, ha⟩))))

/-- A bound above every element of a list. -/
def maxPlusOne (l : List Nat) : Nat := l.foldr (fun a m => max (a + 1) m) 0

theorem lt_maxPlusOne {l : List Nat} : ∀ a ∈ l, a < maxPlusOne l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro a ha
    simp only [maxPlusOne, List.foldr_cons] at *
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha; omega

end Inty
