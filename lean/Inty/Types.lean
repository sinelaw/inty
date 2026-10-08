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

/-- A type scheme `∀ α₀ … α_{arity-1}. body`. -/
structure Scheme where
  arity : Nat
  body : PTy
  deriving DecidableEq, Repr

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

/-- A monotype as a scheme that quantifies nothing. -/
def Scheme.mono (τ : Ty) : Scheme := ⟨0, τ.toPTy⟩

def Scheme.inst (s : Scheme) (τs : List Ty) : Ty := s.body.inst τs

/-- Open a scheme with the type variables `m, m+1, …`, one per quantified
variable. -/
def Scheme.open (s : Scheme) (m : Nat) : Ty :=
  s.inst ((List.range' m s.arity).map .var)

/-! ## Free type variables -/

def Ty.ftv : Ty → List Nat
  | .arrow d c => d.ftv ++ c.ftv
  | .var a => [a]
  | _ => []

def PTy.ftv : PTy → List Nat
  | .arrow d c => d.ftv ++ c.ftv
  | .free a => [a]
  | _ => []

def Scheme.ftv (s : Scheme) : List Nat := s.body.ftv

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

def Scheme.subst (σ : Subst) (s : Scheme) : Scheme := ⟨s.arity, s.body.subst σ⟩

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

theorem ctx_subst_id {σ : Subst} {Γ : List Scheme}
    (h : ∀ a ∈ ctxFtv Γ, σ.find a = none) : Γ.map (Scheme.subst σ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    simp only [ctxFtv, List.flatMap_cons, List.mem_append] at h
    have hs : s.subst σ = s := by
      cases s; simp only [Scheme.subst, Scheme.mk.injEq, true_and]
      exact PTy.subst_id (fun a ha => h a (.inl ha))
    simp [hs, ih (fun a ha => h a (.inr (by simpa [ctxFtv] using ha)))]

/-- Substituting for variables below `m` commutes with opening at `m`. -/
theorem Scheme.open_subst {σ : Subst} {m : Nat} (s : Scheme)
    (h : ∀ p ∈ σ, p.1 < m) : (s.open m).subst σ = (s.subst σ).open m := by
  simp only [Scheme.open, Scheme.inst_subst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hm : m ≤ a := by
    obtain ⟨i, _, rfl⟩ := List.mem_range'.mp ha; omega
  have : σ.find a = none :=
    Subst.find_none (fun p hp e => by have := h p hp; omega)
  simp [Ty.subst, this]

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

/-- Opening a scheme above its free variables, then substituting, is
instantiation. -/
theorem Scheme.open_block (s : Scheme) {m : Nat} {τs : List Ty}
    (hm : ∀ a ∈ s.ftv, a < m) (hlen : τs.length = s.arity) :
    (s.open m).subst (Subst.block m τs) = s.inst τs := by
  obtain ⟨k, p⟩ := s
  simp only [Scheme.open, Scheme.inst, Scheme.ftv] at *
  subst hlen
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
    simp only [PTy.inst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.block_find]
    · simp [hi, Ty.subst]
  | _ => rfl

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
