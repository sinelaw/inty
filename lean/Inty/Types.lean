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

/-- Monotypes. A later layer adds rows, literal types and unions. -/
inductive Ty where
  | number
  | string
  | boolean
  | undefined
  | null
  /-- A function of one argument. In inty a function value is a row carrying
  a call signature (`Type::Func` inside a row); this is that signature alone. -/
  | arrow (dom cod : Ty)
  /-- A type variable. -/
  | var (a : Nat)
  deriving DecidableEq, Repr

/-- The body of a type scheme: a monotype that may also mention the scheme's
quantified variables, `bound i`. -/
inductive PTy where
  | number
  | string
  | boolean
  | undefined
  | null
  | arrow (dom cod : PTy)
  | free (a : Nat)
  | bound (i : Nat)
  deriving DecidableEq, Repr

/-- Type classes, as `classes::ClassName`. Their instances are in
`Inty.Classes`. -/
inductive Cls where
  /-- `Plus a`: the types `+` is defined on. -/
  | plus
  deriving DecidableEq, Repr

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

/-- A monotype as a scheme body. -/
def Ty.toPTy : Ty → PTy
  | .number => .number
  | .string => .string
  | .boolean => .boolean
  | .undefined => .undefined
  | .null => .null
  | .arrow d c => .arrow d.toPTy c.toPTy
  | .var a => .free a

/-- Instantiate a scheme body: `bound i` becomes `τs[i]`. A well-formed scheme
only has `bound i` with `i < arity`; out of range gives `undefined`. -/
def PTy.inst (τs : List Ty) : PTy → Ty
  | .number => .number
  | .string => .string
  | .boolean => .boolean
  | .undefined => .undefined
  | .null => .null
  | .arrow d c => .arrow (d.inst τs) (c.inst τs)
  | .free a => .var a
  | .bound i => τs.getD i .undefined

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

def Ty.ftv : Ty → List Nat
  | .arrow d c => d.ftv ++ c.ftv
  | .var a => [a]
  | _ => []

def PTy.ftv : PTy → List Nat
  | .arrow d c => d.ftv ++ c.ftv
  | .free a => [a]
  | _ => []

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

def Ty.subst (σ : Subst) : Ty → Ty
  | .arrow d c => .arrow (d.subst σ) (c.subst σ)
  | .var a => (σ.find a).getD (.var a)
  | τ => τ

def PTy.subst (σ : Subst) : PTy → PTy
  | .arrow d c => .arrow (d.subst σ) (c.subst σ)
  | .free a => ((σ.find a).getD (.var a)).toPTy
  | p => p

def Pred.subst (σ : Subst) (p : Pred) : Pred := ⟨p.cls, p.args.map (·.subst σ)⟩

def PPred.subst (σ : Subst) (p : PPred) : PPred := ⟨p.cls, p.args.map (·.subst σ)⟩

def Scheme.subst (σ : Subst) (s : Scheme) : Scheme :=
  ⟨s.arity, s.body.subst σ, s.preds.map (·.subst σ)⟩

/-! ## Lemmas -/

@[simp] theorem Ty.toPTy_inst (τ : Ty) (τs : List Ty) : τ.toPTy.inst τs = τ := by
  induction τ <;> simp_all [Ty.toPTy, PTy.inst]

@[simp] theorem Scheme.mono_inst (τ : Ty) (τs : List Ty) :
    (Scheme.mono τ).inst τs = τ := by
  simp [Scheme.mono, Scheme.inst]

@[simp] theorem Ty.toPTy_subst (σ : Subst) (τ : Ty) :
    τ.toPTy.subst σ = (τ.subst σ).toPTy := by
  induction τ <;> simp_all [Ty.toPTy, PTy.subst, Ty.subst]

@[simp] theorem Scheme.mono_subst (σ : Subst) (τ : Ty) :
    (Scheme.mono τ).subst σ = Scheme.mono (τ.subst σ) := by
  simp [Scheme.mono, Scheme.subst]

/-- Substitution commutes with instantiation. -/
theorem PTy.inst_subst (σ : Subst) (τs : List Ty) (p : PTy) :
    (p.inst τs).subst σ = (p.subst σ).inst (τs.map (·.subst σ)) := by
  induction p with
  | arrow d c ihd ihc => simp [PTy.inst, PTy.subst, Ty.subst, ihd, ihc]
  | free a => simp [PTy.inst, PTy.subst]; rfl
  | bound i =>
    simp only [PTy.inst, PTy.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases τs[i]? <;> rfl
  | _ => rfl

theorem Scheme.inst_subst (σ : Subst) (τs : List Ty) (s : Scheme) :
    (s.inst τs).subst σ = (s.subst σ).inst (τs.map (·.subst σ)) :=
  PTy.inst_subst σ τs s.body

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
  induction τ with
  | arrow d c ihd ihc =>
    simp only [Ty.ftv, List.mem_append] at h
    simp [Ty.subst, ihd (fun a ha => h a (.inl ha)), ihc (fun a ha => h a (.inr ha))]
  | var a => simp [Ty.subst, h a (by simp [Ty.ftv])]
  | _ => rfl

theorem PTy.subst_id {σ : Subst} {p : PTy} (h : ∀ a ∈ p.ftv, σ.find a = none) :
    p.subst σ = p := by
  induction p with
  | arrow d c ihd ihc =>
    simp only [PTy.ftv, List.mem_append] at h
    simp [PTy.subst, ihd (fun a ha => h a (.inl ha)), ihc (fun a ha => h a (.inr ha))]
  | free a => simp [PTy.subst, h a (by simp [PTy.ftv]), Ty.toPTy]
  | _ => rfl

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
  induction p with
  | arrow d c ihd ihc =>
    simp only [PTy.ftv, List.mem_append] at hm
    simp [PTy.inst, Ty.subst, ihd (fun a ha => hm a (.inl ha)),
      ihc (fun a ha => hm a (.inr ha))]
  | free a =>
    have ha := hm a (by simp [PTy.ftv])
    have : (Subst.block m τs).find a = none :=
      Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
    simp [PTy.inst, Ty.subst, this]
  | bound i =>
    simp only [varBlock, PTy.inst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.block_find]
    · simp [hi, Ty.subst]
  | _ => rfl

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
