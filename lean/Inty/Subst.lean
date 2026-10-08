import Inty.Types

/-!
# Substitution algebra

What inference needs beyond `Inty.Types`: composing substitutions, applying a
substitution to a context, substitutions that agree on the free variables of
a type, and generalisation, which turns the variables of a type that the
context doesn't mention into a scheme's quantified variables.
-/

namespace Inty

/-! ## Substitution on each type former -/

/-! ## Composition -/

/-- `compose σ₂ σ₁` applies `σ₁`, then `σ₂`. -/
def Subst.compose (σ₂ σ₁ : Subst) : Subst :=
  σ₁.map (fun p => (p.1, p.2.subst σ₂)) ++ σ₂

theorem Subst.find_append (σ σ' : Subst) (a : Nat) :
    (σ ++ σ').find a = match σ.find a with
      | some t => some t
      | none => σ'.find a := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨b, τ⟩ := p
    by_cases h : a = b <;> simp [Subst.find, h, ih]

theorem Subst.find_compose (σ₂ σ₁ : Subst) (a : Nat) :
    (Subst.compose σ₂ σ₁).find a = match σ₁.find a with
      | some t => some (t.subst σ₂)
      | none => σ₂.find a := by
  simp only [Subst.compose, Subst.find_append]
  induction σ₁ with
  | nil => rfl
  | cons p σ₁ ih =>
    obtain ⟨b, τ⟩ := p
    by_cases h : a = b <;> simp [Subst.find, h, ih]

@[simp] theorem Ty.subst_compose (σ₂ σ₁ : Subst) (τ : Ty) :
    τ.subst (Subst.compose σ₂ σ₁) = (τ.subst σ₁).subst σ₂ := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.subst_fn, List.map_map, iht, ihr]
    congr 1
    exact List.map_congr_left ihps
  | var a =>
    simp only [Ty.subst, Subst.find_compose]
    cases σ₁.find a <;> rfl
  | _ => rfl

@[simp] theorem PTy.subst_compose (σ₂ σ₁ : Subst) (p : PTy) :
    p.subst (Subst.compose σ₂ σ₁) = (p.subst σ₁).subst σ₂ := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.subst, PTy.substs_eq, List.map_map, iht, ihr]
    congr 1
    exact List.map_congr_left ihps
  | free a =>
    simp only [PTy.subst, Ty.toPTy_subst, Subst.find_compose]
    cases σ₁.find a <;> rfl
  | _ => rfl

@[simp] theorem Pred.subst_compose (σ₂ σ₁ : Subst) (p : Pred) :
    p.subst (Subst.compose σ₂ σ₁) = (p.subst σ₁).subst σ₂ := by
  simp [Pred.subst]

@[simp] theorem PPred.subst_compose (σ₂ σ₁ : Subst) (p : PPred) :
    p.subst (Subst.compose σ₂ σ₁) = (p.subst σ₁).subst σ₂ := by
  simp [PPred.subst]

@[simp] theorem Scheme.subst_compose (σ₂ σ₁ : Subst) (s : Scheme) :
    s.subst (Subst.compose σ₂ σ₁) = (s.subst σ₁).subst σ₂ := by
  simp [Scheme.subst]

@[simp] theorem Ty.subst_nil (τ : Ty) : τ.subst [] = τ :=
  Ty.subst_id (σ := []) (fun _ _ => rfl)

@[simp] theorem PTy.subst_nil (p : PTy) : p.subst [] = p :=
  PTy.subst_id (σ := []) (fun _ _ => rfl)

@[simp] theorem Pred.subst_nil (p : Pred) : p.subst [] = p := by
  cases p; simp [Pred.subst]

@[simp] theorem PPred.subst_nil (p : PPred) : p.subst [] = p := by
  cases p; simp [PPred.subst]

@[simp] theorem Scheme.subst_nil (s : Scheme) : s.subst [] = s := by
  cases s; simp [Scheme.subst]

@[simp] theorem Scheme.subst_arity (σ : Subst) (s : Scheme) :
    (s.subst σ).arity = s.arity := rfl

/-! ## Contexts -/

/-- Apply a substitution to every scheme of a context. -/
def Ctx.subst (σ : Subst) (Γ : List Scheme) : List Scheme := Γ.map (Scheme.subst σ)

@[simp] theorem Ctx.subst_nil (Γ : List Scheme) : Ctx.subst [] Γ = Γ := by
  induction Γ <;> simp_all [Ctx.subst]

@[simp] theorem Ctx.subst_empty (σ : Subst) : Ctx.subst σ [] = [] := rfl

@[simp] theorem Ctx.subst_cons (σ : Subst) (s : Scheme) (Γ : List Scheme) :
    Ctx.subst σ (s :: Γ) = s.subst σ :: Ctx.subst σ Γ := rfl

@[simp] theorem Ctx.subst_compose (σ₂ σ₁ : Subst) (Γ : List Scheme) :
    Ctx.subst (Subst.compose σ₂ σ₁) Γ = Ctx.subst σ₂ (Ctx.subst σ₁ Γ) := by
  simp [Ctx.subst]

theorem Ctx.getElem?_subst (σ : Subst) (Γ : List Scheme) (i : Nat) :
    (Ctx.subst σ Γ)[i]? = Γ[i]?.map (Scheme.subst σ) := by
  simp [Ctx.subst]

/-! ## Substitutions that agree on the free variables -/

theorem Ty.subst_congr {σ σ' : Subst} {τ : Ty}
    (h : ∀ a ∈ τ.ftv, σ.find a = σ'.find a) : τ.subst σ = τ.subst σ' := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap] at h
    simp only [Ty.subst_fn, iht (fun a ha => h a (.inl (.inl ha))),
      ihr (fun a ha => h a (.inr ha)), Ty.fn.injEq, true_and, and_true]
    exact List.map_congr_left (fun p hp => ihps p hp (fun a ha => h a (.inl (.inr ⟨p, hp, ha⟩))))
  | var a => simp [Ty.subst, h a (by simp [Ty.ftv])]
  | _ => rfl

theorem PTy.subst_congr {σ σ' : Subst} {p : PTy}
    (h : ∀ a ∈ p.ftv, σ.find a = σ'.find a) : p.subst σ = p.subst σ' := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap] at h
    simp only [PTy.subst, PTy.substs_eq, iht (fun a ha => h a (.inl (.inl ha))),
      ihr (fun a ha => h a (.inr ha)), PTy.fn.injEq, true_and, and_true]
    exact List.map_congr_left (fun p hp => ihps p hp (fun a ha => h a (.inl (.inr ⟨p, hp, ha⟩))))
  | free a => simp [PTy.subst, h a (by simp [PTy.ftv])]
  | _ => rfl

theorem Pred.subst_congr {σ σ' : Subst} {p : Pred}
    (h : ∀ a ∈ p.ftv, σ.find a = σ'.find a) : p.subst σ = p.subst σ' := by
  obtain ⟨c, args⟩ := p
  simp only [Pred.subst, Pred.mk.injEq, true_and]
  exact List.map_congr_left (fun τ hτ =>
    Ty.subst_congr (fun a ha => h a (List.mem_flatMap.mpr ⟨τ, hτ, ha⟩)))

theorem PPred.subst_congr {σ σ' : Subst} {p : PPred}
    (h : ∀ a ∈ p.ftv, σ.find a = σ'.find a) : p.subst σ = p.subst σ' := by
  obtain ⟨c, args⟩ := p
  simp only [PPred.subst, PPred.mk.injEq, true_and]
  exact List.map_congr_left (fun q hq =>
    PTy.subst_congr (fun a ha => h a (List.mem_flatMap.mpr ⟨q, hq, ha⟩)))

theorem Ctx.subst_congr {σ σ' : Subst} {Γ : List Scheme}
    (h : ∀ a ∈ ctxFtv Γ, σ.find a = σ'.find a) : Ctx.subst σ Γ = Ctx.subst σ' Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    simp only [ctxFtv, List.flatMap_cons, List.mem_append] at h
    have hs : s.subst σ = s.subst σ' := by
      obtain ⟨k, p, ps⟩ := s
      simp only [Scheme.ftv, List.mem_append, List.mem_flatMap] at h
      simp only [Scheme.subst, Scheme.mk.injEq, true_and]
      exact ⟨PTy.subst_congr (fun a ha => h a (.inl (.inl ha))),
        List.map_congr_left (fun q hq =>
          PPred.subst_congr (fun a ha => h a (.inl (.inr ⟨q, hq, ha⟩))))⟩
    simp [hs, ih (fun a ha => h a (.inr (by simpa [ctxFtv] using ha)))]

/-! ## Generalisation -/

/-- The position of `a` in `l`, if it occurs. -/
def findIdx : List Nat → Nat → Option Nat
  | [], _ => none
  | b :: l, a => if a = b then some 0 else (findIdx l a).map (· + 1)

theorem findIdx_lt : ∀ {l : List Nat} {a i : Nat}, findIdx l a = some i → i < l.length
  | [], _, _, h => by simp [findIdx] at h
  | b :: l, a, i, h => by
    simp only [findIdx] at h
    split at h
    · cases h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := findIdx_lt hj; simp; omega

theorem findIdx_none : ∀ {l : List Nat} {a : Nat}, a ∉ l → findIdx l a = none
  | [], _, _ => rfl
  | b :: l, a, h => by
    simp only [List.mem_cons, not_or] at h
    simp [findIdx, h.1, findIdx_none h.2]

mutual
/-- `PTy` with the variables `ᾱ` quantified: `ᾱ[i]` becomes `bound i`. -/
def Ty.gen (ᾱ : List Nat) : Ty → PTy
  | .number => .number
  | .string => .string
  | .boolean => .boolean
  | .undefined => .undefined
  | .null => .null
  | .unknown => .unknown
  | .fn t ps r => .fn (t.gen ᾱ) (Ty.gens ᾱ ps) (r.gen ᾱ)
  | .var a =>
    match findIdx ᾱ a with
    | some i => .bound i
    | none => .free a
def Ty.gens (ᾱ : List Nat) : List Ty → List PTy
  | [] => []
  | τ :: τs => τ.gen ᾱ :: Ty.gens ᾱ τs
end

@[simp] theorem Ty.gens_eq (ᾱ : List Nat) (τs : List Ty) : Ty.gens ᾱ τs = τs.map (Ty.gen ᾱ) := by
  induction τs <;> simp_all [Ty.gens]

/-- A constraint with the variables `ᾱ` quantified. -/
def Pred.gen (ᾱ : List Nat) (p : Pred) : PPred := ⟨p.cls, p.args.map (Ty.gen ᾱ)⟩

/-- The scheme quantifying `ᾱ` in `τ`, with constraints `G`. -/
def generalize (ᾱ : List Nat) (τ : Ty) (G : List Pred) : Scheme :=
  ⟨ᾱ.length, τ.gen ᾱ, G.map (Pred.gen ᾱ)⟩

/-- The substitution renaming `ᾱ[i]` to `m + i`. -/
def renameBlock : List Nat → Nat → Subst
  | [], _ => []
  | a :: l, m => (a, .var m) :: renameBlock l (m + 1)

theorem renameBlock_find : ∀ (ᾱ : List Nat) (m a : Nat),
    (renameBlock ᾱ m).find a = (findIdx ᾱ a).map (fun i => .var (m + i))
  | [], _, _ => rfl
  | b :: l, m, a => by
    simp only [renameBlock, Subst.find, findIdx]
    split
    · rfl
    · rw [renameBlock_find l (m + 1) a]
      cases findIdx l a <;> simp [Nat.add_assoc, Nat.add_comm 1]

/-- Renaming the generalised variables to the block at `m` and substituting
`φ` for the rest is generalising, substituting `φ`, then opening at `m`. -/
theorem Ty.gen_inst (ᾱ : List Nat) (m : Nat) (φ : Subst) (τ : Ty) :
    τ.subst (renameBlock ᾱ m ++ φ) = ((τ.gen ᾱ).subst φ).inst (varBlock m ᾱ.length) := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.subst_fn, Ty.gen, PTy.subst, PTy.inst, Ty.gens_eq, PTy.substs_eq,
      PTy.insts_eq, List.map_map, iht, ihr, Ty.fn.injEq, true_and, and_true]
    exact List.map_congr_left ihps
  | var a =>
    simp only [Ty.subst, Ty.gen, Subst.find_append, renameBlock_find]
    cases h : findIdx ᾱ a with
    | some i =>
      have := findIdx_lt h
      simp [PTy.subst, PTy.inst, varBlock, List.getD_eq_getElem?_getD, this]
    | none => simp [PTy.subst]
  | _ => rfl

theorem generalize_open (ᾱ : List Nat) (m : Nat) (φ : Subst) (τ : Ty) (G : List Pred) :
    τ.subst (renameBlock ᾱ m ++ φ) = ((generalize ᾱ τ G).subst φ).open m :=
  Ty.gen_inst ᾱ m φ τ

theorem generalize_openPreds (ᾱ : List Nat) (m : Nat) (φ : Subst) (τ : Ty) (G : List Pred) :
    G.map (·.subst (renameBlock ᾱ m ++ φ)) = ((generalize ᾱ τ G).subst φ).openPreds m := by
  simp [generalize, Scheme.subst, Scheme.openPreds, Scheme.instPreds, Pred.gen, Pred.subst,
    PPred.subst, PPred.inst, Ty.gen_inst]

/-- A substitution that renames only variables outside `τ` leaves `τ` to the
rest of it. -/
theorem renameBlock_append_find {ᾱ : List Nat} {a : Nat} (m : Nat) (φ : Subst)
    (h : a ∉ ᾱ) : (renameBlock ᾱ m ++ φ).find a = φ.find a := by
  simp [Subst.find_append, renameBlock_find, findIdx_none h]

@[simp] theorem Scheme.mono_open (τ : Ty) (m : Nat) : (Scheme.mono τ).open m = τ := by
  simp [Scheme.open]

@[simp] theorem Scheme.mono_openPreds (τ : Ty) (m : Nat) : (Scheme.mono τ).openPreds m = [] := by
  simp [Scheme.openPreds, Scheme.instPreds, Scheme.mono]

end Inty
