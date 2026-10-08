import Inty.InferSound

/-!
# Completeness of inference

Whatever `HasType` accepts, `infer` finds, with a type of which the
accepted one is an instance (Damas and Milner; Naraschewski and Nipkow's
Isabelle proof of algorithm W is the model for its freshness invariants).

Inference allocates type variables from a counter `n`: everything it is
given mentions only variables below `n` (`Below`), and its substitutions
leave the variables at or above the counter alone and map the ones below
it to types below it (`Within`).
-/

namespace Inty

/-! ## Variables below a bound -/

def Ty.Below (n : Nat) (τ : Ty) : Prop := ∀ a ∈ τ.ftv, a < n
def Pred.Below (n : Nat) (p : Pred) : Prop := ∀ a ∈ p.ftv, a < n
def Ctx.Below (n : Nat) (Γ : Ctx) : Prop := ∀ a ∈ ctxFtv Γ, a < n
def Ret.Below (n : Nat) (R : Option Ty) : Prop := ∀ a ∈ Ret.ftv R, a < n

/-- `σ` maps the variables below `n` to types below `n`, and leaves the rest
alone. -/
def Subst.Within (n : Nat) (σ : Subst) : Prop :=
  ∀ a, (a < n → ((Ty.var a).subst σ).Below n) ∧ (n ≤ a → (Ty.var a).subst σ = .var a)

theorem Ty.Below.mono {n n' : Nat} {τ : Ty} (h : τ.Below n) (hn : n ≤ n') : τ.Below n' :=
  fun a ha => Nat.lt_of_lt_of_le (h a ha) hn

/-- Substitutions that agree on a type's variables, as types. -/
theorem Ty.subst_congr' {σ σ' : Subst} {τ : Ty}
    (h : ∀ a ∈ τ.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : τ.subst σ = τ.subst σ' := by
  induction τ using Ty.ind with
  | var a => exact h a (by simp)
  | app c args ih =>
    simp only [Ty.ftv_app, List.mem_flatMap] at h
    simp only [Ty.subst_app, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))

/-- The variables of a substituted type come from the images of its
variables. -/
theorem Ty.ftv_subst {σ : Subst} {τ : Ty} {a : Nat} (h : a ∈ (τ.subst σ).ftv) :
    ∃ b ∈ τ.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction τ using Ty.ind with
  | var b => exact ⟨b, by simp, h⟩
  | app c args ih =>
    simp only [Ty.subst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih p hp h
    exact ⟨b, by simp only [Ty.ftv_app, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩

theorem Subst.Within.subst_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {τ : Ty}
    (h : τ.Below n) : (τ.subst σ).Below n := fun a ha => by
  obtain ⟨b, hb, ha⟩ := Ty.ftv_subst ha
  exact (hσ b).1 (h b hb) a ha

theorem Subst.Within.mono {n n' : Nat} {σ : Subst} (hσ : σ.Within n) (hn : n ≤ n') :
    σ.Within n' := fun a => by
  refine ⟨fun ha => ?_, fun ha => (hσ a).2 (Nat.le_trans hn ha)⟩
  by_cases han : a < n
  · exact ((hσ a).1 han).mono hn
  · rw [(hσ a).2 (Nat.le_of_not_lt han)]; intro b hb; simp at hb; omega

theorem Subst.Within.nil (n : Nat) : Subst.Within n [] := fun a =>
  ⟨fun ha b hb => by simp at hb; omega, fun _ => by simp⟩

theorem Subst.Within.compose {n : Nat} {σ₁ σ₂ : Subst} (h₁ : σ₁.Within n) (h₂ : σ₂.Within n) :
    (Subst.compose σ₂ σ₁).Within n := fun a => by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [Ty.subst_compose]; exact h₂.subst_below ((h₁ a).1 ha)
  · rw [Ty.subst_compose, (h₁ a).2 ha, (h₂ a).2 ha]

theorem Subst.Within.single {n x : Nat} {τ : Ty} (hx : x < n) (hτ : τ.Below n) :
    Subst.Within n [(x, τ)] := fun a => by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · by_cases hax : a = x
    · subst hax; simpa [Ty.subst, Subst.find] using hτ
    · simp only [Ty.subst, Subst.find, hax, ite_false]; intro b hb; simp at hb; omega
  · have : a ≠ x := by omega
    simp [Ty.subst, Subst.find, this]

theorem Ty.Below.app {n : Nat} {c : Con} {args : List Ty} :
    (Ty.app c args).Below n ↔ ∀ p ∈ args, p.Below n := by
  simp only [Ty.Below, Ty.ftv_app, List.mem_flatMap]
  exact ⟨fun h p hp a ha => h a ⟨p, hp, ha⟩, fun h a ⟨p, hp, ha⟩ => h p hp a ha⟩

theorem Ty.Below.fn {n : Nat} {t r : Ty} {ps : List Ty} :
    (Ty.fn t ps r).Below n ↔ t.Below n ∧ (∀ p ∈ ps, p.Below n) ∧ r.Below n := by
  rw [Ty.Below.app]
  simp only [List.mem_cons, forall_eq_or_imp]
  exact ⟨fun ⟨ht, hr, hps⟩ => ⟨ht, hps, hr⟩, fun ⟨ht, hps, hr⟩ => ⟨ht, hr, hps⟩⟩

/-- A unifier of equations between types below `n` stays within `n`. -/
theorem unifyEqs_within {n : Nat} :
    ∀ (vs : List Nat) (eqs : List (Ty × Ty)), (∀ e ∈ eqs, e.1.Below n ∧ e.2.Below n) →
      ∀ {σ : Subst}, unifyEqs vs eqs = some σ → σ.Within n := by
  intro vs eqs
  induction vs, eqs using unifyEqs.induct with
  | case1 => intro _ σ h; unfold unifyEqs at h; cases h; exact .nil n
  | case2 vs b eqs ih =>
    intro hb σ h
    unfold unifyEqs at h; simp only [ite_true] at h
    exact ih (fun e he => hb e (by simp [he])) h
  | case3 vs a b eqs hab x τ ho hocc => intro _ σ h; unfold unifyEqs at h; simp [hab, ho, hocc] at h
  | case4 vs a b eqs hab x τ ho hocc hx ih =>
    intro hb σ h
    unfold unifyEqs at h; simp only [hab, ho, hocc, hx, ite_false, dite_true] at h
    obtain ⟨σ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    have h₀ := hb (a, b) (by simp)
    have hxτ : x < n ∧ τ.Below n := by
      rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨h₀.1 x (by simp [Ty.ftv]), h₀.2⟩
      · exact ⟨h₀.2 x (by simp [Ty.ftv]), h₀.1⟩
    have hs := Subst.Within.single hxτ.1 hxτ.2
    refine Subst.Within.compose hs (ih (fun e he => ?_) h')
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    have := hb e₀ (by simp [he₀])
    exact ⟨hs.subst_below this.1, hs.subst_below this.2⟩
  | case5 vs a b eqs hab x τ ho hocc hx =>
    intro _ σ h; unfold unifyEqs at h; simp [hab, ho, hocc, hx] at h
  | case6 vs eqs c₁ as₁ c₂ as₂ hc hne ho ih =>
    intro hb σ h
    unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_true hc, ite_true] at h
    have h₀ := hb _ List.mem_cons_self
    have h₁ := Ty.Below.app.mp h₀.1
    have h₂ := Ty.Below.app.mp h₀.2
    refine ih (fun e he => ?_) h
    rcases List.mem_append.mp he with he | he
    · exact ⟨h₁ _ (List.of_mem_zip he).1, h₂ _ (List.of_mem_zip he).2⟩
    · exact hb e (by simp [he])
  | case7 vs eqs c₁ as₁ c₂ as₂ hc hne ho =>
    intro _ σ h; unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_false hc] at h; cases h
  | case8 vs a b eqs hab ho happ =>
    intro _ σ h; unfold unifyEqs at h; simp only [hab, ho, ite_false] at h
    cases a <;> cases b <;> simp_all

theorem unify_within {n : Nat} {τ₁ τ₂ : Ty} {σ : Subst} (h₁ : τ₁.Below n) (h₂ : τ₂.Below n)
    (h : unify τ₁ τ₂ = some σ) : σ.Within n :=
  unifyEqs_within _ _ (fun e he => by simp only [List.mem_singleton] at he; subst he; exact ⟨h₁, h₂⟩) h

/-! ## Free variables through instantiation, substitution, generalisation -/

theorem Ty.toPTy_ftv (τ : Ty) : τ.toPTy.ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.ftv_app, Ty.ftv_app, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih

theorem PTy.ftv_inst {τs : List Ty} {p : PTy} {a : Nat} (h : a ∈ (p.inst τs).ftv) :
    a ∈ p.ftv ∨ ∃ τ ∈ τs, a ∈ τ.ftv := by
  induction p using PTy.ind with
  | free b => simp [PTy.inst] at h; simp [PTy.ftv, h]
  | bound i =>
    simp only [PTy.inst, List.getD_eq_getElem?_getD] at h
    cases hi : τs[i]? with
    | none => simp [hi] at h
    | some τ => simp only [hi, Option.getD_some] at h; exact .inr ⟨τ, List.mem_of_getElem? hi, h⟩
  | app c args ih =>
    simp only [PTy.inst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map] at h
    simp only [PTy.ftv_app, List.mem_flatMap]
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases ih q hq h with h | h
    · exact .inl ⟨q, hq, h⟩
    · exact .inr h

theorem PTy.ftv_subst {σ : Subst} {p : PTy} {a : Nat} (h : a ∈ (p.subst σ).ftv) :
    ∃ b ∈ p.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction p using PTy.ind with
  | free b =>
    simp only [PTy.subst, Ty.toPTy_ftv] at h
    exact ⟨b, by simp [PTy.ftv], by simpa [Ty.subst] using h⟩
  | bound i => simp [PTy.subst, PTy.ftv] at h
  | app c args ih =>
    simp only [PTy.subst_app, PTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih q hq h
    exact ⟨b, by simp only [PTy.ftv_app, List.mem_flatMap]; exact ⟨q, hq, hb⟩, h⟩

theorem Ty.gen_ftv {ᾱ : List Nat} {τ : Ty} {a : Nat} (h : a ∈ (τ.gen ᾱ).ftv) : a ∈ τ.ftv := by
  induction τ using Ty.ind with
  | var b =>
    simp only [Ty.gen] at h
    split at h <;> simp_all [PTy.ftv]
  | app c args ih =>
    simp only [Ty.gen_app, PTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    simp only [Ty.ftv_app, List.mem_flatMap]
    exact ⟨q, hq, ih q hq h⟩

/-! ## `Below` through the operations of inference -/

theorem Subst.Within.pred_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {p : Pred}
    (h : p.Below n) : (p.subst σ).Below n := fun a ha => by
  simp only [Pred.ftv, Pred.subst, List.flatMap_map, List.mem_flatMap] at ha
  obtain ⟨τ, hτ, ha⟩ := ha
  exact hσ.subst_below (fun b hb => h b (List.mem_flatMap.mpr ⟨τ, hτ, hb⟩)) a ha

theorem Subst.Within.ctx_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {Γ : Ctx}
    (h : Ctx.Below n Γ) : Ctx.Below n (Ctx.subst σ Γ) := fun a ha => by
  simp only [ctxFtv, Ctx.subst, List.flatMap_map, List.mem_flatMap] at ha
  obtain ⟨s, hs, ha⟩ := ha
  have hsb : ∀ b ∈ s.ftv, b < n := fun b hb => h b (List.mem_flatMap.mpr ⟨s, hs, hb⟩)
  simp only [Scheme.ftv, Scheme.subst, List.mem_append, List.mem_flatMap, List.mem_map] at ha hsb
  rcases ha with ha | ⟨_, ⟨q, hq, rfl⟩, ha⟩
  · obtain ⟨b, hb, ha⟩ := PTy.ftv_subst ha
    exact (hσ b).1 (hsb b (.inl hb)) a ha
  · simp only [PPred.ftv, PPred.subst, List.flatMap_map, List.mem_flatMap] at ha
    obtain ⟨r, hr, ha⟩ := ha
    obtain ⟨b, hb, ha⟩ := PTy.ftv_subst ha
    exact (hσ b).1 (hsb b (.inr ⟨q, hq, List.mem_flatMap.mpr ⟨r, hr, hb⟩⟩)) a ha

theorem Subst.Within.ret_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {R : Option Ty}
    (h : Ret.Below n R) : Ret.Below n (Ret.subst σ R) := by
  cases R with
  | none => intro a ha; simp [Ret.ftv] at ha
  | some τ =>
    have : τ.Below n := fun a ha => h a (by simpa [Ret.ftv] using ha)
    intro a ha
    simp only [Ret.subst_some, Ret.ftv, Option.map_some, Option.getD_some] at ha
    exact hσ.subst_below this a ha

theorem Ctx.Below.mono {n n' : Nat} {Γ : Ctx} (h : Ctx.Below n Γ) (hn : n ≤ n') : Ctx.Below n' Γ :=
  fun a ha => Nat.lt_of_lt_of_le (h a ha) hn

theorem Ret.Below.mono {n n' : Nat} {R : Option Ty} (h : Ret.Below n R) (hn : n ≤ n') :
    Ret.Below n' R := fun a ha => Nat.lt_of_lt_of_le (h a ha) hn

theorem Pred.Below.mono {n n' : Nat} {p : Pred} (h : p.Below n) (hn : n ≤ n') : p.Below n' :=
  fun a ha => Nat.lt_of_lt_of_le (h a ha) hn

theorem Ctx.Below.lookup {n : Nat} {Γ : Ctx} {i : Nat} {s : Scheme} (h : Ctx.Below n Γ)
    (hi : Γ[i]? = some s) : ∀ a ∈ s.ftv, a < n := fun a ha =>
  h a (List.mem_flatMap.mpr ⟨s, List.mem_of_getElem? hi, ha⟩)

/-- The block at `k`, sent by the substitution for it. -/
theorem varBlock_subst_block (k : Nat) (xs : List Ty) (φ : Subst) :
    (varBlock k xs.length).map (·.subst (Subst.block k xs ++ φ)) = xs := by
  apply List.ext_getElem (by simp [varBlock])
  intro i h₁ h₂
  have := Subst.block_find k xs i
  simp only [varBlock, List.getElem_map, List.getElem_range', Nat.one_mul, Ty.subst,
    Subst.find_append, this, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- The middle of a block of fresh variables, sent to the middle of a list. -/
theorem varBlock_subst_block_mid (m : Nat) (xs ys zs : List Ty) (φ : Subst) :
    (varBlock (m + xs.length) ys.length).map (·.subst (Subst.block m (xs ++ ys ++ zs) ++ φ)) =
      ys := by
  apply List.ext_getElem (by simp [varBlock])
  intro i h₁ h₂
  have := Subst.block_find m (xs ++ ys ++ zs) (xs.length + i)
  have hi : xs.length + i < (xs ++ ys ++ zs).length := by simp; omega
  simp only [varBlock, List.getElem_map, List.getElem_range', Nat.one_mul, Ty.subst,
    Subst.find_append, Nat.add_assoc, this, List.getElem?_eq_getElem hi, Option.getD_some]
  simp [List.getElem_append_left, List.getElem_append_right, h₂]

theorem varBlock_below {m k : Nat} : ∀ τ ∈ varBlock m k, τ.Below (m + k) := by
  intro τ hτ
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hτ
  intro a ha
  simp [Ty.ftv] at ha; subst ha
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hj; omega

theorem Scheme.open_below {n : Nat} {s : Scheme} (hs : ∀ a ∈ s.ftv, a < n) :
    (s.open n).Below (n + s.arity) := fun a ha => by
  rcases PTy.ftv_inst ha with ha | ⟨τ, hτ, ha⟩
  · have := hs a (List.mem_append_left _ ha); omega
  · exact varBlock_below τ hτ a ha

theorem Scheme.openPreds_below {n : Nat} {s : Scheme} (hs : ∀ a ∈ s.ftv, a < n) :
    ∀ p ∈ s.openPreds n, p.Below (n + s.arity) := by
  intro p hp a ha
  simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [Pred.ftv, PPred.inst, List.flatMap_map, List.mem_flatMap] at ha
  obtain ⟨r, hr, ha⟩ := ha
  rcases PTy.ftv_inst ha with ha | ⟨τ, hτ, ha⟩
  · have := hs a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq,
      List.mem_flatMap.mpr ⟨r, hr, ha⟩⟩)); omega
  · exact varBlock_below τ hτ a ha

theorem Scheme.inst_nil_below {n : Nat} {s : Scheme} (hs : ∀ a ∈ s.ftv, a < n) :
    (s.inst []).Below n := fun a ha => by
  rcases PTy.ftv_inst ha with ha | ⟨τ, hτ, _⟩
  · exact hs a (List.mem_append_left _ ha)
  · cases hτ

theorem Scheme.mono_ftv (τ : Ty) : (Scheme.mono τ).ftv = τ.ftv := by
  simp [Scheme.mono, Scheme.ftv, Ty.toPTy_ftv]

theorem letScheme_below {n : Nat} {gen : Bool} {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty}
    {preds : List Pred} (hτ : τ₁.Below n) (hp : ∀ p ∈ preds, p.Below n) :
    (∀ a ∈ (letScheme gen Γ₁ R₁ τ₁ preds).1.ftv, a < n) ∧
      ∀ p ∈ (letScheme gen Γ₁ R₁ τ₁ preds).2, p.Below n := by
  simp only [letScheme]
  split
  · refine ⟨fun a ha => ?_, fun p hp' => hp p (List.mem_filter.mp hp').1⟩
    simp only [generalize, Scheme.ftv, List.mem_append, List.mem_flatMap, List.mem_map] at ha
    rcases ha with ha | ⟨_, ⟨q, hq, rfl⟩, ha⟩
    · exact hτ a (Ty.gen_ftv ha)
    · simp only [PPred.ftv, Pred.gen, List.flatMap_map, List.mem_flatMap] at ha
      obtain ⟨r, hr, ha⟩ := ha
      exact hp q (List.mem_filter.mp hq).1 a (List.mem_flatMap.mpr ⟨r, hr, Ty.gen_ftv ha⟩)
  · exact ⟨fun a ha => hτ a (by simpa [Scheme.mono_ftv] using ha), hp⟩

theorem Ctx.Below.cons {n : Nat} {s : Scheme} {Γ : Ctx} (hs : ∀ a ∈ s.ftv, a < n)
    (h : Ctx.Below n Γ) : Ctx.Below n (s :: Γ) := fun a ha => by
  simp only [ctxFtv, List.flatMap_cons, List.mem_append] at ha
  rcases ha with ha | ha
  · exact hs a ha
  · exact h a ha

theorem Ctx.Below.mono_cons {n : Nat} {τ : Ty} {Γ : Ctx} (hτ : τ.Below n) (h : Ctx.Below n Γ) :
    Ctx.Below n (.mono τ :: Γ) :=
  Ctx.Below.cons (fun a ha => hτ a (by simpa [Scheme.mono_ftv] using ha)) h

theorem Ctx.Below.append_mono {n : Nat} {τs : List Ty} {Γ : Ctx} (hτs : ∀ τ ∈ τs, τ.Below n)
    (h : Ctx.Below n Γ) : Ctx.Below n (τs.map .mono ++ Γ) := by
  induction τs with
  | nil => simpa using h
  | cons τ τs ih =>
    exact Ctx.Below.mono_cons (hτs τ (by simp)) (ih (fun τ' h' => hτs τ' (by simp [h'])))

theorem Lit.ty_below (l : Lit) (n : Nat) : l.ty.Below n := by
  cases l <;> intro a ha <;> simp [Lit.ty] at ha

theorem Ty.Below.var {n a : Nat} (h : a < n) : (Ty.var a).Below n := by
  intro b hb; simp at hb; omega

/-! ## Improvement stays below the bound -/

theorem Pred.improve_below {n : Nat} {top : Bool} {p : Pred} {a b : Ty} (hp : p.Below n)
    (h : p.improve top = .eq a b) : a.Below n ∧ b.Below n := by
  unfold Pred.improve at h
  split at h
  · cases h
  · split at h
    · rename_i hs
      cases h
      have hmem := (List.of_mem_zip (Ty.field_mem hs)).2
      refine ⟨fun x hx => hp x ?_, fun x hx => hp x ?_⟩
      · simp only [Pred.ftv, List.flatMap_cons, List.mem_append, Ty.ftv_app, List.mem_flatMap]
        exact .inl ⟨_, hmem, hx⟩
      · simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
          List.append_nil] at hx
        simp only [Pred.ftv, List.flatMap_cons, List.mem_append, List.flatMap_nil, List.append_nil]
        rcases hx with hx | hx
        · simp at hx
        · exact .inr hx
    · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
    refine ⟨fun x hx => hp x (by simp [Pred.ftv, hx]), fun x hx => hp x ?_⟩
    simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.append_nil] at hx
    rcases hx with hx | hx
    · simp at hx
    · simp [Pred.ftv, hx]
  · cases h
    exact ⟨fun x hx => hp x (by simp [Pred.ftv, hx]), fun x hx => hp x (by simp [Pred.ftv, hx])⟩
  · cases h

theorem improveOne_sub {top : Bool} : ∀ {ps : List Pred} {a b : Ty} {rest : List Pred},
    improveOne top ps = some (some ((a, b), rest)) →
      (∃ p ∈ ps, p.improve top = .eq a b) ∧ ∀ q ∈ rest, q ∈ ps
  | [], _, _, _, h => by simp [improveOne] at h
  | p :: ps, a, b, rest, h => by
    simp only [improveOne] at h
    split at h
    · cases h
    · rename_i τ₁ τ₂ hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨⟨p, List.mem_cons_self, hp⟩, fun q hq => List.mem_cons_of_mem _ hq⟩
    · split at h
      · cases h
      · cases h
      · rename_i e r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨⟨p', hp'm, hp'⟩, hsub⟩ := improveOne_sub hr
        refine ⟨⟨p', List.mem_cons_of_mem _ hp'm, hp'⟩, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub q hq)

theorem improveAll_inv {n : Nat} {top : Bool} :
    ∀ (k : Nat) {ps : List Pred} {σ : Subst} {ps' : List Pred},
    (∀ p ∈ ps, p.Below n) → improveAll top k ps = some (σ, ps') →
      σ.Within n ∧ ∀ p ∈ ps', p.Below n
  | 0, ps, σ, ps', hps, h => by
    simp only [improveAll, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil n, hps⟩
  | k + 1, ps, σ, ps', hps, h => by
    simp only [improveAll] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.nil n, hps⟩
    · rename_i a b rest hone
      split at h
      · cases h
      rename_i σu hu
      split at h
      · cases h
      rename_i σ' ps'' hrec
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨p, hpm, hp⟩, hsub⟩ := improveOne_sub hone
      obtain ⟨ha, hb⟩ := Pred.improve_below (hps p hpm) hp
      have hσu := unify_within ha hb hu
      obtain ⟨hσ', hps''⟩ := improveAll_inv k
        (fun q hq => by
          obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
          exact hσu.pred_below (hps q₀ (hsub q₀ hq₀))) hrec
      exact ⟨hσu.compose hσ', hps''⟩

theorem objSlots_below {n : Nat} {L ls : List String} {τs absent : List Ty}
    (hτs : ∀ τ ∈ τs, τ.Below n) (habs : ∀ τ ∈ absent, τ.Below n) :
    ∀ s ∈ objSlots L ls τs absent, s.Below n := by
  intro s hs
  simp only [objSlots, List.mem_map] at hs
  obtain ⟨⟨l, a⟩, hla, rfl⟩ := hs
  simp only
  generalize hf : Ty.field l ls.reverse τs.reverse = o
  cases o with
  | some τ =>
    have hτ : τ ∈ τs := List.mem_reverse.mp (List.of_mem_zip (Ty.field_mem hf)).2
    intro x hx
    simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.append_nil] at hx
    rcases hx with hx | hx
    · simp at hx
    · exact hτs τ hτ x hx
  | none =>
    intro x hx
    simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.append_nil] at hx
    rcases hx with hx | hx
    · simp at hx
    · exact habs a (List.of_mem_zip hla).2 x hx

theorem zipWith_slot_below {n : Nat} : ∀ {ps τs : List Ty}, (∀ τ ∈ ps, τ.Below n) →
    (∀ τ ∈ τs, τ.Below n) → ∀ s ∈ List.zipWith Ty.slot ps τs, s.Below n
  | p :: ps, τ :: τs, hps, hτs, s, hs => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Ty.Below.app.mpr (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hps _ (by simp)
        · exact hτs _ (by simp))
    · exact zipWith_slot_below (fun x hx => hps x (by simp [hx]))
        (fun x hx => hτs x (by simp [hx])) s hs
  | [], _, _, _, _, hs | _ :: _, [], _, _, _, hs => by simp at hs

theorem mergePreds_below {n : Nat} : ∀ {ps τs ss rs : List Ty}, (∀ τ ∈ ps, τ.Below n) →
    (∀ τ ∈ τs, τ.Below n) → (∀ τ ∈ ss, τ.Below n) → (∀ τ ∈ rs, τ.Below n) →
    ∀ p ∈ mergePreds ps τs ss rs, p.Below n
  | p :: ps, τ :: τs, s :: ss, r :: rs, hps, hτs, hss, hrs, q, hq => by
    simp only [mergePreds, List.mem_cons] at hq
    rcases hq with rfl | hq
    · intro a ha
      simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at ha
      rcases ha with ha | ha | ha | ha
      · exact hps _ (by simp) a ha
      · exact hτs _ (by simp) a ha
      · exact hss _ (by simp) a ha
      · exact hrs _ (by simp) a ha
    · exact mergePreds_below (fun x hx => hps x (by simp [hx])) (fun x hx => hτs x (by simp [hx]))
        (fun x hx => hss x (by simp [hx])) (fun x hx => hrs x (by simp [hx])) q hq
  | [], _, _, _, _, _, _, _, _, hq | _ :: _, [], _, _, _, _, _, _, _, hq
  | _ :: _, _ :: _, [], _, _, _, _, _, _, hq | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, hq => by
    simp [mergePreds] at hq

/-! ## Invariants of inference -/

/-- What inference returns, from inputs below `n`, is below its next
unused variable. -/
def InferInv (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out}, Ctx.Below n Γ → Ret.Below n R →
    infer L Γ R e n = some o →
    n ≤ o.next ∧ o.σ.Within o.next ∧ o.τ.Below o.next ∧ ∀ p ∈ o.preds, p.Below o.next

theorem inferArgs_inv : ∀ (args : List Expr), (∀ a ∈ args, InferInv L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : OutArgs}, Ctx.Below n Γ → Ret.Below n R →
      inferArgs L Γ R args n = some o →
      n ≤ o.next ∧ o.σ.Within o.next ∧ (∀ τ ∈ o.τs, τ.Below o.next) ∧
        ∀ p ∈ o.preds, p.Below o.next
  | [], _, Γ, R, n, o, _, _, h => by
    simp only [inferArgs, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_refl _, .nil _, by simp, by simp⟩
  | a :: as, ih, Γ, R, n, o, hΓ, hR, h => by
    simp only [inferArgs] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih a (by simp) hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv as (fun a' ha' => ih a' (by simp [ha']))
      (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, ?_, ?_⟩
    · intro τ hτ
      simp only [List.mem_cons] at hτ
      rcases hτ with rfl | hτ
      · exact hσ₂.subst_below (hτ₁.mono hn₂)
      · exact hτs₂ τ hτ
    · intro p hp
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp

theorem infer_inv (L : List String) : ∀ e, InferInv L e := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro Γ R n o _ _ h
    simp only [infer, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_refl _, .nil _, Lit.ty_below l _, by simp⟩
  | var i =>
    intro Γ R n o hΓ _ h
    simp only [infer] at h
    split at h
    · rename_i s hs
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_add_right _ _, .nil _, Scheme.open_below (hΓ.lookup hs),
        Scheme.openPreds_below (hΓ.lookup hs)⟩
    · cases h
  | func k body ih =>
    intro Γ R n o hΓ _ h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    have hθ : (Ty.var n).Below (n + 2 + k) := .var (by omega)
    have hτs : ∀ τ ∈ varBlock (n + 1) k, τ.Below (n + 2 + k) := fun τ hτ =>
      (varBlock_below τ hτ).mono (by omega)
    have hρ : (Ty.var (n + 1 + k)).Below (n + 2 + k) := .var (by omega)
    have hfn : (Ty.fn (.var n) (varBlock (n + 1) k) (.var (n + 1 + k))).Below (n + 2 + k) :=
      Ty.Below.fn.mpr ⟨hθ, hτs, hρ⟩
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih
      (Ctx.Below.append_mono hτs (Ctx.Below.mono_cons hfn (Ctx.Below.mono_cons hθ
        (hΓ.mono (by omega)))))
      (fun a ha => hρ a (by simpa [Ret.ftv] using ha)) h₁
    have hσ' := unify_within (hσ₁.subst_below (hρ.mono hn₁)) hτ₁ hu
    refine ⟨by dsimp only; omega, hσ₁.compose hσ', ?_, ?_⟩
    · rw [Ty.subst_compose]; exact hσ'.subst_below (hσ₁.subst_below (hfn.mono hn₁))
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below (hp₁ q hq)
  | app f args ihf iha =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i σ₃ hu
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihf hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv args iha
      (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hσ₃ := unify_within ((hσ₂.subst_below (hτ₁.mono hn₂)).mono (Nat.le_succ _))
      (Ty.Below.fn.mpr ⟨fun a ha => by simp [Ty.ftv] at ha,
        fun τ hτ => (hτs₂ τ hτ).mono (Nat.le_succ _), .var (by omega)⟩) hu
    refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).mono (Nat.le_succ _)).compose hσ₃,
      hσ₃.subst_below (.var (by omega)), ?_⟩
    intro p hp
    simp only [List.mem_map, List.mem_append] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine hσ₃.pred_below (Pred.Below.mono ?_ (Nat.le_succ _))
    rcases hq with ⟨q', hq', rfl⟩ | hq
    · exact hσ₂.pred_below ((hp₁ q' hq').mono hn₂)
    · exact hp₂ q hq
  | let_ _ e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ hΓ hR h₁
    split at h
    · cases h
    rename_i σi preds₁ himp
    obtain ⟨hσi, hpi⟩ := improveAll_inv _ hp₁ himp
    have hσ₁' := hσ₁.compose hσi
    have hls := letScheme_below (gen := Expr.generalises e₁ e₂)
      (Γ₁ := Ctx.subst (Subst.compose σi o₁.σ) Γ) (R₁ := Ret.subst (Subst.compose σi o₁.σ) R)
      (hσi.subst_below hτ₁) hpi
    generalize letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
      (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁ = ls at h hls
    obtain ⟨s, rest⟩ := ls
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (Ctx.Below.cons hls.1 (hσ₁'.ctx_below (hΓ.mono hn₁)))
      (hσ₁'.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁'.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hls.2 q hq).mono hn₂)
    · exact hp₂ p hp
  | assign i e ih =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i s hs
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih hΓ hR h₁
    have hsb : (s.inst []).Below n := Scheme.inst_nil_below (hΓ.lookup hs)
    have hσ' := unify_within (hσ₁.subst_below (hsb.mono hn₁)) hτ₁ hu
    refine ⟨hn₁, hσ₁.compose hσ', ?_, ?_⟩
    · rw [Ty.subst_compose]; exact hσ'.subst_below (hσ₁.subst_below (hsb.mono hn₁))
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below (hp₁ q hq)
  | cond c t e ihc iht ihe =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i o₃ h₃
    split at h
    · cases h
    rename_i σ₄ hu
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihc hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := iht (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    obtain ⟨hn₃, hσ₃, hτ₃, hp₃⟩ := ihe (hσ₂.ctx_below (hσ₁.ctx_below (hΓ.mono hn₁) |>.mono hn₂))
      (hσ₂.ret_below (hσ₁.ret_below (hR.mono hn₁) |>.mono hn₂)) h₃
    have hσ₄ := unify_within (hσ₃.subst_below (hτ₂.mono hn₃)) hτ₃ hu
    refine ⟨by dsimp only; omega, ((((hσ₁.mono hn₂).compose hσ₂).mono hn₃).compose hσ₃).compose hσ₄,
      hσ₄.subst_below hτ₃, ?_⟩
    intro p hp
    simp only [List.mem_map, List.mem_append] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine hσ₄.pred_below ?_
    rcases hq with ⟨q', hq', rfl⟩ | hq
    · rcases hq' with ⟨q'', hq'', rfl⟩ | hq'
      · exact hσ₃.pred_below ((hσ₂.pred_below ((hp₁ q'' hq'').mono hn₂)).mono hn₃)
      · exact hσ₃.pred_below ((hp₂ q' hq').mono hn₃)
    · exact hp₃ q hq
  | unop op e ih =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih hΓ hR h₁
    cases op with
    | not =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨hn₁, hσ₁, fun a ha => by simp [Ty.ftv] at ha, hp₁⟩
    | typeof =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨hn₁, hσ₁, fun a ha => by simp [Ty.ftv] at ha, hp₁⟩
    | neg =>
      simp only at h
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      have hσ' := unify_within hτ₁ (fun a ha => by simp [Ty.ftv] at ha) hu
      refine ⟨hn₁, hσ₁.compose hσ', fun a ha => by simp [Ty.ftv] at ha, ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below (hp₁ q hq)
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hpre : ∀ p ∈ o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, p.Below o₂.next := by
      intro p hp
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp
    have hnum : Ty.number.Below o₂.next := fun a ha => by simp [Ty.ftv] at ha
    cases op with
    | plus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu
      simp only [Option.some.injEq] at h; subst h
      have hσ₃ := unify_within (hσ₂.subst_below (hτ₁.mono hn₂)) hτ₂ hu
      refine ⟨by dsimp only; omega, ((hσ₁.mono hn₂).compose hσ₂).compose hσ₃, hσ₃.subst_below hτ₂, ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      refine hσ₃.pred_below ?_
      rcases List.mem_append.mp hq with hq | hq
      · exact hpre q hq
      · simp only [List.mem_singleton] at hq; subst hq
        intro a ha; simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at ha; exact hτ₂ a ha
    | minus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu₃
      split at h
      · cases h
      rename_i σ₄ hu₄
      simp only [Option.some.injEq] at h; subst h
      have hσ₃ := unify_within (hσ₂.subst_below (hτ₁.mono hn₂)) hnum hu₃
      have hσ₄ := unify_within (hσ₃.subst_below hτ₂) hnum hu₄
      refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).compose hσ₃).compose hσ₄, hnum, ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact hσ₄.pred_below (hσ₃.pred_below (hpre q' hq'))
  | ret e ih =>
    intro Γ R n o hΓ hR h
    cases R with
    | none => simp [infer] at h
    | some τr =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih hΓ hR h₁
      have hτr : τr.Below n := fun a ha => hR a (by simpa [Ret.ftv] using ha)
      have hσ' := unify_within (hσ₁.subst_below (hτr.mono hn₁)) hτ₁ hu
      refine ⟨by dsimp only; omega, (hσ₁.compose hσ').mono (Nat.le_succ _), .var (by dsimp only; omega), ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hσ'.pred_below (hp₁ q hq)).mono (Nat.le_succ _)
  | throw_ e ih =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih hΓ hR h₁
    exact ⟨by dsimp only; omega, hσ₁.mono (Nat.le_succ _), .var (by dsimp only; omega),
      fun p hp => (hp₁ p hp).mono (Nat.le_succ _)⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp

  | while_ c body ihc ihb =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, _, hp₁⟩ := ihc hΓ hR h₁
    obtain ⟨hn₂, hσ₂, _, hp₂⟩ := ihb (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, fun a ha => by simp [Ty.ftv] at ha,
      ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp
  | break_ | continue_ =>
    intro Γ R n o _ _ h
    simp only [infer, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_succ _, .nil _, .var (Nat.lt_succ_self _), by simp⟩
  | tryCatch body handler ihb ihh =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i σ₃ hu
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihb hΓ hR h₁
    have hunk : Ty.unknown.Below o₁.next := fun a ha => by simp [Ty.ftv] at ha
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ihh (Ctx.Below.mono_cons hunk (hσ₁.ctx_below (hΓ.mono hn₁)))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hσ₃ := unify_within (hσ₂.subst_below (hτ₁.mono hn₂)) hτ₂ hu
    refine ⟨Nat.le_trans hn₁ hn₂, ((hσ₁.mono hn₂).compose hσ₂).compose hσ₃,
      hσ₃.subst_below hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_map, List.mem_append] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine hσ₃.pred_below ?_
    rcases hq with ⟨q', hq', rfl⟩ | hq
    · exact hσ₂.pred_below ((hp₁ q' hq').mono hn₂)
    · exact hp₂ q hq
  | tryFinally body fin ihb ihf =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihb hΓ hR h₁
    obtain ⟨hn₂, hσ₂, _, hp₂⟩ := ihf (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hσ₂.subst_below (hτ₁.mono hn₂), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp

  | obj ls es ih =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτs₁, hp₁⟩ := inferArgs_inv es ih hΓ hR h₁
    have hle : o₁.next ≤ o₁.next + L.length := Nat.le_add_right _ _
    refine ⟨Nat.le_trans hn₁ hle, hσ₁.mono hle, ?_, fun p hp => (hp₁ p hp).mono hle⟩
    exact Ty.Below.app.mpr (objSlots_below (fun τ hτ => (hτs₁ τ hτ).mono hle)
      (fun τ hτ => varBlock_below τ hτ))
  | get e l ih =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih hΓ hR h₁
    have hle : o₁.next ≤ o₁.next + 1 := Nat.le_succ _
    refine ⟨Nat.le_trans hn₁ hle, hσ₁.mono hle, Ty.Below.var (Nat.lt_succ_self _), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact (hp₁ p hp).mono hle
    · intro a ha
      simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, Ty.ftv_var, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Nat.lt_succ_of_lt (hτ₁ a ha)
      · exact Nat.lt_succ_self _
  | set e l v ihe ihv =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihe hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ihv (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with (⟨q, hq, rfl⟩ | hp) | rfl
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp
    · intro a ha
      simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at ha
      rcases ha with ha | ha
      · exact hσ₂.subst_below (hτ₁.mono hn₂) a ha
      · exact hτ₂ a ha
  | spread e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i σ₃ hu₃
    split at h
    · cases h
    rename_i σ₄ hu₄
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hle : o₂.next ≤ o₂.next + 4 * L.length := by omega
    have hb₀ : ∀ τ ∈ varBlock o₂.next L.length, τ.Below (o₂.next + 4 * L.length) :=
      fun τ hτ => (varBlock_below τ hτ).mono (by omega)
    have hb₁ : ∀ τ ∈ varBlock (o₂.next + L.length) L.length,
        τ.Below (o₂.next + 4 * L.length) :=
      fun τ hτ => (varBlock_below τ hτ).mono (by omega)
    have hb₂ : ∀ τ ∈ varBlock (o₂.next + 2 * L.length) L.length,
        τ.Below (o₂.next + 4 * L.length) :=
      fun τ hτ => (varBlock_below τ hτ).mono (by omega)
    have hb₃ : ∀ τ ∈ varBlock (o₂.next + 3 * L.length) L.length,
        τ.Below (o₂.next + 4 * L.length) :=
      fun τ hτ => (varBlock_below τ hτ).mono (by omega)
    have hσ₃ := unify_within ((hσ₂.mono hle).subst_below ((hτ₁.mono hn₂).mono hle))
      (Ty.Below.app.mpr hb₀) hu₃
    have hσ₄ := unify_within (hσ₃.subst_below (hτ₂.mono hle))
      (hσ₃.subst_below (Ty.Below.app.mpr (zipWith_slot_below hb₁ hb₂))) hu₄
    have hσ₄₃ := hσ₃.compose hσ₄
    refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).mono hle).compose hσ₄₃,
      hσ₄₃.subst_below (Ty.Below.app.mpr hb₃), ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    refine hσ₄₃.pred_below ?_
    simp only [List.mem_append, List.mem_map] at hq
    rcases hq with (⟨q', hq', rfl⟩ | hq') | hq'
    · exact (hσ₂.pred_below ((hp₁ q' hq').mono hn₂)).mono hle
    · exact (hp₂ q hq').mono hle
    · exact mergePreds_below hb₁ hb₂ hb₀ hb₃ q hq'

/-! ## Agreement of substitutions -/

theorem PTy.subst_congr' {σ σ' : Subst} {p : PTy}
    (h : ∀ a ∈ p.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : p.subst σ = p.subst σ' := by
  induction p using PTy.ind with
  | free a =>
    have := h a (by simp [PTy.ftv])
    simp only [Ty.subst] at this
    simp [PTy.subst, this]
  | bound i => rfl
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at h
    simp only [PTy.subst_app, PTy.app.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))

theorem Pred.subst_congr' {σ σ' : Subst} {p : Pred}
    (h : ∀ a ∈ p.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : p.subst σ = p.subst σ' := by
  obtain ⟨c, args⟩ := p
  simp only [Pred.subst, Pred.mk.injEq, true_and]
  exact List.map_congr_left (fun τ hτ =>
    Ty.subst_congr' (fun a ha => h a (List.mem_flatMap.mpr ⟨τ, hτ, ha⟩)))

theorem Scheme.subst_congr' {σ σ' : Subst} {s : Scheme}
    (h : ∀ a ∈ s.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : s.subst σ = s.subst σ' := by
  obtain ⟨k, p, ps⟩ := s
  simp only [Scheme.ftv, List.mem_append, List.mem_flatMap] at h
  simp only [Scheme.subst, Scheme.mk.injEq, true_and]
  refine ⟨PTy.subst_congr' (fun a ha => h a (.inl ha)), List.map_congr_left (fun q hq => ?_)⟩
  obtain ⟨c, args⟩ := q
  simp only [PPred.subst, PPred.mk.injEq, true_and]
  exact List.map_congr_left (fun r hr => PTy.subst_congr' (fun a ha =>
    h a (.inr ⟨_, hq, List.mem_flatMap.mpr ⟨r, hr, ha⟩⟩)))

theorem Ctx.subst_congr' {σ σ' : Subst} {Γ : Ctx}
    (h : ∀ a ∈ ctxFtv Γ, (Ty.var a).subst σ = (Ty.var a).subst σ') :
    Ctx.subst σ Γ = Ctx.subst σ' Γ := by
  simp only [Ctx.subst]
  exact List.map_congr_left (fun s hs => Scheme.subst_congr' (fun a ha =>
    h a (List.mem_flatMap.mpr ⟨s, hs, ha⟩)))

/-- `φ` after `σ` agrees with `ψ` below `n`. -/
def Agree (n : Nat) (σ φ ψ : Subst) : Prop :=
  ∀ a < n, ((Ty.var a).subst σ).subst φ = (Ty.var a).subst ψ

theorem Agree.ty {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {τ : Ty} (hτ : τ.Below n) :
    (τ.subst σ).subst φ = τ.subst ψ := by
  rw [← Ty.subst_compose]
  exact Ty.subst_congr' (fun a ha => by rw [Ty.subst_compose]; exact h a (hτ a ha))

theorem Agree.pred {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {p : Pred} (hp : p.Below n) :
    (p.subst σ).subst φ = p.subst ψ := by
  rw [← Pred.subst_compose]
  exact Pred.subst_congr' (fun a ha => by rw [Ty.subst_compose]; exact h a (hp a ha))

theorem Agree.ctx {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {Γ : Ctx} (hΓ : Ctx.Below n Γ) :
    Ctx.subst φ (Ctx.subst σ Γ) = Ctx.subst ψ Γ := by
  rw [← Ctx.subst_compose]
  exact Ctx.subst_congr' (fun a ha => by rw [Ty.subst_compose]; exact h a (hΓ a ha))

theorem Agree.ret {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {R : Option Ty}
    (hR : Ret.Below n R) : Ret.subst φ (Ret.subst σ R) = Ret.subst ψ R := by
  cases R with
  | none => rfl
  | some τ =>
    simp only [Ret.subst_some, Option.some.injEq]
    exact h.ty (fun a ha => hR a (by simpa [Ret.ftv] using ha))

theorem Agree.mono {n n' : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) (hn : n' ≤ n) :
    Agree n' σ φ ψ := fun a ha => h a (by omega)

/-- `φ` absorbs `σ`: `φ` after `σ` is `φ`. -/
def Absorbs (φ σ : Subst) : Prop := ∀ τ : Ty, (τ.subst σ).subst φ = τ.subst φ

theorem Absorbs.pred {φ σ : Subst} (h : Absorbs φ σ) (p : Pred) : (p.subst σ).subst φ = p.subst φ := by
  obtain ⟨c, args⟩ := p
  simp only [Pred.subst, List.map_map, Pred.mk.injEq, true_and]
  exact List.map_congr_left (fun τ _ => h τ)

/-- A binding of a variable `τ` doesn't mention changes nothing on `τ`. -/
theorem Ty.subst_cons_fresh {k : Nat} {ρ : Ty} {φ : Subst} {τ : Ty} (hτ : τ.Below k) :
    τ.subst ((k, ρ) :: φ) = τ.subst φ :=
  Ty.subst_congr (fun a ha => by
    have : a ≠ k := by have := hτ a ha; omega
    simp [Subst.find, this])

theorem Pred.subst_cons_fresh {k : Nat} {ρ : Ty} {φ : Subst} {p : Pred} (hp : p.Below k) :
    p.subst ((k, ρ) :: φ) = p.subst φ :=
  Pred.subst_congr (fun a ha => by
    have : a ≠ k := by have := hp a ha; omega
    simp [Subst.find, this])

/-- What `Sat` needs of a substitution is only what it does to the
constraints. -/
theorem Sat.congr {C P : List Pred} {φ φ' : Subst} (h : ∀ p ∈ P, p.subst φ = p.subst φ')
    (hs : Sat C P φ') : Sat C P φ := fun p hp => by rw [h p hp]; exact hs p hp

/-! ## Fresh variables -/

theorem Subst.block_find_none {m : Nat} {τs : List Ty} {a : Nat} (h : a < m) :
    (Subst.block m τs).find a = none :=
  Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)

theorem Subst.block_find_ge {m : Nat} {τs : List Ty} {a : Nat} (h : m + τs.length ≤ a) :
    (Subst.block m τs).find a = none :=
  Subst.find_none (fun p hp e => by
    have := (List.of_mem_zip hp).1
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp this; omega)

/-- Opening a scheme at fresh variables, then sending them to `τs` and the
rest by `ψ`, is instantiating the `ψ`-substituted scheme at `τs`. -/
theorem PTy.open_block_append {n : Nat} {τs : List Ty} {ψ : Subst} (p : PTy)
    (hp : ∀ a ∈ p.ftv, a < n) :
    (p.inst (varBlock n τs.length)).subst (Subst.block n τs ++ ψ) = (p.subst ψ).inst τs := by
  induction p using PTy.ind with
  | free a =>
    have ha := hp a (by simp [PTy.ftv])
    simp [PTy.inst, PTy.subst, Ty.subst, Subst.find_append, Subst.block_find_none ha]
  | bound i =>
    simp only [varBlock, PTy.inst, PTy.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.find_append, Subst.block_find]
    · simp [hi]
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at hp
    simp only [PTy.inst_app, PTy.subst_app, Ty.subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun q hq => ih q hq (fun a ha => hp a ⟨q, hq, ha⟩))

theorem Scheme.open_block_append {n : Nat} {τs : List Ty} {ψ : Subst} {s : Scheme}
    (hs : ∀ a ∈ s.ftv, a < n) (hlen : τs.length = s.arity) :
    (s.open n).subst (Subst.block n τs ++ ψ) = (s.subst ψ).inst τs := by
  simp only [Scheme.open, Scheme.inst, Scheme.subst, ← hlen]
  exact PTy.open_block_append _ (fun a ha => hs a (List.mem_append_left _ ha))

theorem Scheme.openPreds_block_append {n : Nat} {τs : List Ty} {ψ : Subst} {s : Scheme}
    (hs : ∀ a ∈ s.ftv, a < n) (hlen : τs.length = s.arity) :
    (s.openPreds n).map (·.subst (Subst.block n τs ++ ψ)) = (s.subst ψ).instPreds τs := by
  simp only [Scheme.openPreds, Scheme.instPreds, Scheme.subst, List.map_map, ← hlen]
  refine List.map_congr_left (fun q hq => ?_)
  obtain ⟨c, args⟩ := q
  simp only [Function.comp, PPred.inst, Pred.subst, PPred.subst, List.map_map, Pred.mk.injEq,
    true_and]
  exact List.map_congr_left (fun r hr => PTy.open_block_append r (fun a ha =>
    hs a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq,
      List.mem_flatMap.mpr ⟨r, hr, ha⟩⟩))))

/-- For a function's body: `this` at `n`, the parameters from `n + 1`, the
result after them, and `ψ` below. -/
def funSubst (n : Nat) (θ : Ty) (τs : List Ty) (ρ : Ty) (ψ : Subst) : Subst :=
  (n, θ) :: (Subst.block (n + 1) τs ++ ((n + 1 + τs.length, ρ) :: ψ))

theorem funSubst_below {n : Nat} {θ ρ : Ty} {τs : List Ty} {ψ : Subst} {a : Nat} (h : a < n) :
    (funSubst n θ τs ρ ψ).find a = ψ.find a := by
  have h₁ : a ≠ n := by omega
  have h₂ : a ≠ n + 1 + τs.length := by omega
  simp [funSubst, Subst.find, h₁, h₂, Subst.find_append, Subst.block_find_none (show a < n + 1 by omega)]

theorem funSubst_this {n : Nat} {θ ρ : Ty} {τs : List Ty} {ψ : Subst} :
    (Ty.var n).subst (funSubst n θ τs ρ ψ) = θ := by
  simp [funSubst, Ty.subst, Subst.find]

theorem funSubst_params {n : Nat} {θ ρ : Ty} {τs : List Ty} {ψ : Subst} :
    (varBlock (n + 1) τs.length).map (·.subst (funSubst n θ τs ρ ψ)) = τs := by
  apply List.ext_getElem (by simp [varBlock])
  intro i h₁ h₂
  simp only [varBlock, List.map_map, List.getElem_map, List.getElem_range', Function.comp,
    Ty.subst, funSubst, Subst.find]
  have : n + 1 + i ≠ n := by omega
  simp [this, Subst.find_append, Subst.block_find, h₂]

theorem funSubst_ret {n : Nat} {θ ρ : Ty} {τs : List Ty} {ψ : Subst} :
    (Ty.var (n + 1 + τs.length)).subst (funSubst n θ τs ρ ψ) = ρ := by
  have : n + 1 + τs.length ≠ n := by omega
  simp [funSubst, Ty.subst, Subst.find, this, Subst.find_append,
    Subst.block_find_ge (show n + 1 + τs.length ≤ n + 1 + τs.length from Nat.le_refl _)]

/-! ## A more general scheme -/

/-- `s'` is at least as general as `s` under the assumptions `C`: each
instance of `s` is an instance of `s'`, whose constraints follow from
`s`'s and `C`. -/
def Generalizes (C : List Pred) (s' s : Scheme) : Prop :=
  ∀ τs, τs.length = s.arity → ∃ τs', τs'.length = s'.arity ∧ s'.inst τs' = s.inst τs ∧
    ∀ c ∈ s'.instPreds τs', Entails (C ++ s.instPreds τs) c

theorem getElem?_middle {α : Type} (Δ Γ : List α) (x y : α) (i : Nat) (hi : i ≠ Δ.length) :
    (Δ ++ x :: Γ)[i]? = (Δ ++ y :: Γ)[i]? := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · simp [List.getElem?_append_left h]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [show Δ.length + j + 1 - Δ.length = j + 1 by omega]

theorem Expr.writesList_false : ∀ {i : Nat} {args : List Expr}, Expr.writesList i args = false →
    ∀ a ∈ args, a.writes i = false
  | _, [], _, _, ha => by cases ha
  | _, b :: bs, h, a, ha => by
    simp only [Expr.writesList, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact Expr.writesList_false h.2 a ha

/-- Typing survives replacing a scheme in the context by a more general one,
if the variable is never assigned or the new scheme is a monotype: an
assignment needs its variable's scheme to be one. -/
theorem HasType.generalize_ctx {C' : List Pred} {Γ₀ : Ctx} {R : Option Ty} {e : Expr} {τ : Ty}
    (h : HasType L C' Γ₀ R e τ) :
    ∀ {C : List Pred} {Δ Γ : Ctx} {s s' : Scheme}, Γ₀ = Δ ++ s :: Γ → (∀ c ∈ C, c ∈ C') →
      Generalizes C s' s → (s'.arity = 0 ∧ s'.preds = []) ∨ e.writes Δ.length = false →
      HasType L C' (Δ ++ s' :: Γ) R e τ := by
  induction h with
  | lit hl => intros; exact .lit hl
  | @var Γ₀ i s₀ C' R τs hi hlen hc =>
    intro C Δ Γ s s' hΓ hC hgen _
    subst hΓ
    by_cases hiΔ : i = Δ.length
    · subst hiΔ
      simp at hi; subst hi
      obtain ⟨τs', hlen', heq, hent⟩ := hgen τs hlen
      rw [← heq]
      refine .var (by simp) hlen' (fun c hc' => ?_)
      rcases hent c hc' with h | h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inr (hC c h)
        · exact hc c h
    · exact .var (by rw [← getElem?_middle Δ Γ s s' i hiΔ]; exact hi) hlen hc
  | @func n C' Γ₀ ρ body R θ τs hlen _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    subst hΓ
    refine .func hlen ?_
    have := ih (Δ := τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Δ) (Γ := Γ) (s := s)
      (by simp only [List.append_assoc, List.cons_append]) hC hgen (hw.imp id fun h => by
        simp only [Expr.writes] at h
        simpa [hlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h)
    simpa only [List.append_assoc, List.cons_append] using this
  | app _ hlen _ ihf iha =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .app (ihf hΓ hC hgen (hw'.imp id (·.1))) hlen (fun p hp => iha p hp hΓ hC hgen
      (hw'.imp id fun h => Expr.writesList_false h.2 _ (List.of_mem_zip hp).1))
  | let_ s₀ L _ hv hsimp _ ih₁ ih₂ =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    refine .let_ s₀ L (fun m hm => ih₁ m hm hΓ (fun c h => List.mem_append_left _ (hC c h)) hgen
      (hw'.imp id (·.1))) hv hsimp ?_
    have := ih₂ (Δ := s₀ :: Δ) (by rw [hΓ]; rfl) hC hgen (hw'.imp id (·.2))
    simpa using this
  | @assign Γ₀ i s₀ C' R e₀ hi ha hp _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    subst hΓ
    by_cases hiΔ : i = Δ.length
    · subst hiΔ
      rcases hw with ⟨ha', hp'⟩ | hw
      · simp at hi; subst hi
        obtain ⟨τs', hlen', heq, _⟩ := hgen [] (by simp [ha])
        rw [ha'] at hlen'
        obtain rfl := List.eq_nil_of_length_eq_zero hlen'
        rw [← heq]
        exact .assign (by simp) ha' hp' (heq ▸ ih rfl hC hgen (.inl ⟨ha', hp'⟩))
      · simp [Expr.writes] at hw
    · exact .assign (by rw [← getElem?_middle Δ Γ s s' i hiΔ]; exact hi) ha hp
        (ih rfl hC hgen (hw.imp id fun h => by simp [Expr.writes] at h; exact h.2))
  | cond _ _ _ ihc iht ihe =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .cond (ihc hΓ hC hgen (hw'.imp id (·.1.1))) (iht hΓ hC hgen (hw'.imp id (·.1.2)))
      (ihe hΓ hC hgen (hw'.imp id (·.2)))
  | unop hop _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    exact .unop hop (ih hΓ hC hgen (hw.imp id fun h => by simpa [Expr.writes] using h))
  | binop hop _ _ ih₁ ih₂ =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .binop hop (ih₁ hΓ hC hgen (hw'.imp id (·.1))) (ih₂ hΓ hC hgen (hw'.imp id (·.2)))
  | ret _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    exact .ret (ih hΓ hC hgen (hw.imp id fun h => by simpa [Expr.writes] using h))
  | throw_ _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    exact .throw_ (ih hΓ hC hgen (hw.imp id fun h => by simpa [Expr.writes] using h))
  | seq _ _ ih₁ ih₂ =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .seq (ih₁ hΓ hC hgen (hw'.imp id (·.1))) (ih₂ hΓ hC hgen (hw'.imp id (·.2)))
  | while_ _ _ ihc ihb =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .while_ (ihc hΓ hC hgen (hw'.imp id (·.1))) (ihb hΓ hC hgen (hw'.imp id (·.2)))
  | break_ => intros; exact .break_
  | continue_ => intros; exact .continue_
  | tryCatch _ _ ihb ihh =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    refine .tryCatch (ihb hΓ hC hgen (hw'.imp id (·.1))) ?_
    have := ihh (Δ := .mono .unknown :: Δ) (by rw [hΓ]; rfl) hC hgen (hw'.imp id (·.2))
    simpa using this
  | tryFinally _ _ ihb ihf =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .tryFinally (ihb hΓ hC hgen (hw'.imp id (·.1))) (ihf hΓ hC hgen (hw'.imp id (·.2)))
  | obj hτs habs hL hes _ ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .obj hτs habs hL hes (fun p hp => ih p hp hΓ hC hgen
      (hw'.imp id fun h => Expr.writesList_false h _ (List.of_mem_zip hp).1))
  | get _ hp ih =>
    intro C Δ Γ s s' hΓ hC hgen hw
    exact .get (ih hΓ hC hgen (hw.imp id fun h => by simpa [Expr.writes] using h)) hp
  | set _ hp _ ihe ihv =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .set (ihe hΓ hC hgen (hw'.imp id (·.1))) hp (ihv hΓ hC hgen (hw'.imp id (·.2)))
  | spread hps hτs hss hrs _ _ hm ih₁ ih₂ =>
    intro C Δ Γ s s' hΓ hC hgen hw
    have hw' := hw.imp id fun h => by simpa [Expr.writes] using h
    exact .spread hps hτs hss hrs (ih₁ hΓ hC hgen (hw'.imp id (·.1))) (ih₂ hΓ hC hgen
      (hw'.imp id (·.2))) hm

/-! ## Instantiating a generalised scheme -/

theorem zip_find : ∀ (ᾱ : List Nat) (τs : List Ty) (v : Nat), ᾱ.length = τs.length →
    Subst.find (ᾱ.zip τs) v = (findIdx ᾱ v).map (fun i => τs.getD i .undefined)
  | [], [], _, _ => rfl
  | a :: ᾱ, τ :: τs, v, h => by
    simp only [List.zip_cons_cons, Subst.find, findIdx]
    split
    · rfl
    · rw [zip_find ᾱ τs v (by simpa using h)]
      cases findIdx ᾱ v <;> simp
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp at h

/-- Instantiating a generalised type at `τs'` is substituting `τs'` for the
generalised variables. -/
theorem Ty.gen_subst_inst {ᾱ : List Nat} {τs' : List Ty} (φ : Subst) (h : ᾱ.length = τs'.length)
    (τ : Ty) : ((τ.gen ᾱ).subst φ).inst τs' = τ.subst (ᾱ.zip τs' ++ φ) := by
  induction τ using Ty.ind with
  | var v =>
    simp only [Ty.gen, Ty.subst, Subst.find_append, zip_find ᾱ τs' v h]
    cases findIdx ᾱ v with
    | some i => simp [PTy.subst, PTy.inst]
    | none => simp [PTy.subst]
  | app c args ih =>
    simp only [Ty.gen_app, PTy.subst_app, PTy.inst_app, Ty.subst_app, List.map_map,
      Ty.app.injEq, true_and]
    exact List.map_congr_left ih

theorem generalize_subst_inst {ᾱ : List Nat} {τs' : List Ty} (φ : Subst) (h : ᾱ.length = τs'.length)
    (τ : Ty) (G : List Pred) :
    ((generalize ᾱ τ G).subst φ).inst τs' = τ.subst (ᾱ.zip τs' ++ φ) :=
  Ty.gen_subst_inst φ h τ

theorem generalize_subst_instPreds {ᾱ : List Nat} {τs' : List Ty} (φ : Subst)
    (h : ᾱ.length = τs'.length) (τ : Ty) (G : List Pred) :
    ((generalize ᾱ τ G).subst φ).instPreds τs' = G.map (·.subst (ᾱ.zip τs' ++ φ)) := by
  simp only [generalize, Scheme.subst, Scheme.instPreds, List.map_map]
  refine List.map_congr_left (fun g _ => ?_)
  obtain ⟨c, args⟩ := g
  simp only [Function.comp, Pred.gen, PPred.subst, PPred.inst, Pred.subst, List.map_map,
    Pred.mk.injEq, true_and]
  exact List.map_congr_left (fun τ _ => Ty.gen_subst_inst φ h τ)

/-! ## Variables of substituted contexts -/

theorem Ty.ftv_subst_mem {σ : Subst} {v a : Nat} {τ : Ty} (hv : v ∈ τ.ftv)
    (ha : a ∈ ((Ty.var v).subst σ).ftv) : a ∈ (τ.subst σ).ftv := by
  induction τ using Ty.ind with
  | var b => simp at hv; subst hv; exact ha
  | app c args ih =>
    simp only [Ty.ftv_app, List.mem_flatMap] at hv
    simp only [Ty.subst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map]
    obtain ⟨p, hp, hv⟩ := hv
    exact ⟨_, ⟨p, hp, rfl⟩, ih p hp hv⟩

theorem PTy.ftv_subst_mem {σ : Subst} {v a : Nat} {p : PTy} (hv : v ∈ p.ftv)
    (ha : a ∈ ((Ty.var v).subst σ).ftv) : a ∈ (p.subst σ).ftv := by
  induction p using PTy.ind with
  | free b =>
    simp [PTy.ftv] at hv; subst hv
    simpa [PTy.subst, Ty.toPTy_ftv, Ty.subst] using ha
  | bound i => simp [PTy.ftv] at hv
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at hv
    simp only [PTy.subst_app, PTy.ftv_app, List.mem_flatMap, List.mem_map]
    obtain ⟨q, hq, hv⟩ := hv
    exact ⟨_, ⟨q, hq, rfl⟩, ih q hq hv⟩

theorem Ctx.ftv_subst_mem {σ : Subst} {v a : Nat} {Γ : Ctx} (hv : v ∈ ctxFtv Γ)
    (ha : a ∈ ((Ty.var v).subst σ).ftv) : a ∈ ctxFtv (Ctx.subst σ Γ) := by
  simp only [ctxFtv, List.mem_flatMap] at hv ⊢
  obtain ⟨s, hs, hv⟩ := hv
  refine ⟨s.subst σ, List.mem_map_of_mem hs, ?_⟩
  simp only [Scheme.ftv, Scheme.subst, List.mem_append, List.mem_flatMap, List.mem_map] at hv ⊢
  rcases hv with hv | ⟨q, hq, hv⟩
  · exact .inl (PTy.ftv_subst_mem hv ha)
  · simp only [PPred.ftv, List.mem_flatMap] at hv
    obtain ⟨r, hr, hv⟩ := hv
    refine .inr ⟨_, ⟨q, hq, rfl⟩, ?_⟩
    simp only [PPred.ftv, PPred.subst, List.flatMap_map, List.mem_flatMap]
    exact ⟨r, hr, PTy.ftv_subst_mem hv ha⟩

theorem Ret.ftv_subst_mem {σ : Subst} {v a : Nat} {R : Option Ty} (hv : v ∈ Ret.ftv R)
    (ha : a ∈ ((Ty.var v).subst σ).ftv) : a ∈ Ret.ftv (Ret.subst σ R) := by
  cases R with
  | none => simp [Ret.ftv] at hv
  | some τ => simpa [Ret.ftv] using Ty.ftv_subst_mem (by simpa [Ret.ftv] using hv) ha

/-- A block substitution leaves alone a type below it. -/
theorem Ty.subst_block_below {m : Nat} {τs : List Ty} {τ : Ty} (h : ∀ a ∈ τ.ftv, a < m) :
    τ.subst (Subst.block m τs) = τ :=
  Ty.subst_id (fun a ha => Subst.block_find_none (h a ha))

theorem Pred.subst_block_below {m : Nat} {τs : List Ty} {p : Pred} (h : ∀ a ∈ p.ftv, a < m) :
    p.subst (Subst.block m τs) = p :=
  Pred.subst_id (fun a ha => Subst.block_find_none (h a ha))

theorem Expr.isValue_complete {e : Expr} (h : e.IsValue) : e.isValue = true := by
  cases h <;> rfl

/-- A constraint on a type variable: `Plus a`, `HasProp l a σ`, or
`Merge a τ s r`. -/
def Pred.OnVarShaped (p : Pred) : Prop :=
  (∃ a, p = ⟨.plus, [.var a]⟩) ∨ (∃ l a σ, p = ⟨.hasProp l, [.var a, σ]⟩) ∨
    ∃ a τ s r, p = ⟨.merge, [.var a, τ, s, r]⟩

/-- What an assumption may be where improvement decides constraints, at the
top level (`top`) or where a binding generalises: on a type variable, as
a simple scheme's constraints are once opened, or, where a binding
generalises, any `Merge`, since a scheme's `Merge` may have a known
presence (`Scheme.Simple`) and improvement there leaves every `Merge` as
it is. -/
def Pred.AssumableAt (top : Bool) (p : Pred) : Prop :=
  (∃ a, p = ⟨.plus, [.var a]⟩) ∨ (∃ l a σ, p = ⟨.hasProp l, [.var a, σ]⟩) ∨
    ∃ q τ s r, p = ⟨.merge, [q, τ, s, r]⟩ ∧ (top = true → ∃ a, q = .var a)

theorem Pred.OnVarShaped.assumable {p : Pred} (h : p.OnVarShaped) (top : Bool) :
    p.AssumableAt top := by
  rcases h with h | h | ⟨a, τ, s, r, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨_, τ, s, r, rfl, fun _ => ⟨a, rfl⟩⟩)

/-! ### Improvement loses nothing -/

/-- A constraint improvement keeps is a `Plus`, a `HasProp` on a type
variable, or a `Merge`, on a type variable at the top level. -/
theorem Pred.improve_keep {top : Bool} {p : Pred} (h : p.improve top = .keep) :
    (∃ args, p = ⟨.plus, args⟩) ∨ (∃ l a σ, p = ⟨.hasProp l, [.var a, σ]⟩) ∨
      ∃ args, p = ⟨.merge, args⟩ ∧ (top = true → ∃ a τ s r, args = [.var a, τ, s, r]) := by
  unfold Pred.improve at h
  split at h
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · split at h <;> cases h
  · cases h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inr ⟨_, rfl, fun ht => by cases ht⟩)
  · exact .inr (.inr ⟨_, rfl, fun _ => ⟨_, _, _, _, rfl⟩⟩)
  · cases h
  · cases h
  · cases h

/-- A constraint whose decision is an equation is entailed, by assumptions
on type variables, only where the equation holds. -/
theorem Pred.improve_eq {top : Bool} {p : Pred} {a b : Ty} (h : p.improve top = .eq a b)
    {φ : Subst} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) (he : Entails C (p.subst φ)) :
    a.subst φ = b.subst φ := by
  unfold Pred.improve at h
  split at h
  · cases h
  · split at h
    · rename_i hf
      cases h
      rcases he with hi | hm
      · cases hi with
        | hasProp hf' =>
          simp only [Ty.substs_eq] at hf'
          rw [Ty.field_subst, hf] at hf'
          simpa using hf'
      · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, -⟩ <;>
          simp [Pred.subst] at hx
    · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
    rcases he with hi | hm
    · generalize hq : Pred.subst φ _ = q at hi
      cases hi <;> simp_all [Pred.subst]
    · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, hv⟩
      · simp [Pred.subst] at hx
      · simp [Pred.subst] at hx
      · obtain ⟨y, rfl⟩ := hv rfl
        simp [Pred.subst] at hx
  · cases h
    rcases he with hi | hm
    · generalize hq : Pred.subst φ _ = q at hi
      cases hi <;> simp_all [Pred.subst]
    · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, hv⟩
      · simp [Pred.subst] at hx
      · simp [Pred.subst] at hx
      · obtain ⟨y, rfl⟩ := hv rfl
        simp [Pred.subst] at hx
  · cases h

/-- A constraint improvement rejects is entailed by no assumptions on type
variables. -/
theorem Pred.improve_fail {top : Bool} {p : Pred} (h : p.improve top = .fail) {φ : Subst}
    {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) : ¬ Entails C (p.subst φ) := by
  unfold Pred.improve at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hf
      rintro (hi | hm)
      · cases hi with
        | hasProp hf' =>
          simp only [Ty.substs_eq] at hf'
          rw [Ty.field_subst, hf] at hf'; cases hf'
      · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, -⟩ <;>
          simp [Pred.subst] at hx
  · rename_i l args hvar hrec
    have hshape : ∀ t₁ t₂, args.map (·.subst φ) = [t₁, t₂] →
        (∀ a, t₁ ≠ .var a) ∧ (∀ ls slots, t₁ ≠ .record ls slots) := by
      intro t₁ t₂ h
      obtain ⟨a₁, a₂, rfl⟩ : ∃ a₁ a₂, args = [a₁, a₂] := by
        rcases args with _ | ⟨a₁, _ | ⟨a₂, _ | _⟩⟩ <;> simp at h
        exact ⟨a₁, a₂, rfl⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      cases a₁ with
      | var x => exact absurd rfl (hvar x a₂)
      | app c xs =>
        refine ⟨fun a e => by simp at e, fun ls slots e => ?_⟩
        simp only [Ty.subst_app, Ty.app.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact absurd rfl (hrec ls xs a₂)
    rintro (hi | hm)
    · generalize hq : Pred.subst φ ⟨.hasProp l, args⟩ = q at hi
      cases hi with
      | plusNumber | plusString | mergePre | mergeAbs => simp [Pred.subst] at hq
      | hasProp _ =>
        simp only [Pred.subst, Pred.mk.injEq] at hq
        exact (hshape _ _ hq.2).2 _ _ rfl
    · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, -⟩
      · simp [Pred.subst] at hx
      · simp only [Pred.subst, Pred.mk.injEq] at hx
        exact (hshape _ _ hx.2).1 x rfl
      · simp [Pred.subst] at hx
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · rename_i args hvar hpre habs
    -- The presence, once substituted, is neither `pre`, `abs` nor a variable.
    have hshape : ∀ t ts, args.map (·.subst φ) = t :: ts → ts.length = 3 →
        t ≠ .pre ∧ t ≠ .abs ∧ ∀ a, t ≠ .var a := by
      intro t ts h hl
      obtain ⟨a₁, a₂, a₃, a₄, rfl⟩ : ∃ a₁ a₂ a₃ a₄, args = [a₁, a₂, a₃, a₄] := by
        have hlen : args.length = 4 := by
          have := congrArg List.length h; simp at this; omega
        rcases args with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | _⟩⟩⟩⟩ <;> simp at hlen
        exact ⟨a₁, a₂, a₃, a₄, rfl⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases a₁ with
      | var x => exact absurd rfl (hvar x a₂ a₃ a₄)
      | app c xs =>
        refine ⟨fun e => ?_, fun e => ?_, fun a e => by simp at e⟩
        · simp only [Ty.subst_app, Ty.app.injEq, List.map_eq_nil_iff] at e
          obtain ⟨rfl, rfl⟩ := e
          exact hpre a₂ a₃ a₄ rfl
        · simp only [Ty.subst_app, Ty.app.injEq, List.map_eq_nil_iff] at e
          obtain ⟨rfl, rfl⟩ := e
          exact habs a₂ a₃ a₄ rfl
    rintro (hi | hm)
    · generalize hq : Pred.subst φ ⟨.merge, args⟩ = q at hi
      cases hi with
      | plusNumber | plusString | hasProp _ => simp [Pred.subst] at hq
      | mergePre =>
        simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
        exact (hshape _ _ hq rfl).1 rfl
      | mergeAbs =>
        simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
        exact (hshape _ _ hq rfl).2.1 rfl
    · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, hv⟩
      · simp [Pred.subst] at hx
      · simp [Pred.subst] at hx
      · obtain ⟨y, rfl⟩ := hv rfl
        simp only [Pred.subst, Pred.mk.injEq, true_and] at hx
        exact (hshape _ _ hx rfl).2.2 y rfl

theorem improveOne_none {top : Bool} : ∀ {ps : List Pred}, improveOne top ps = none →
    ∃ p ∈ ps, p.improve top = .fail
  | [], h => by simp [improveOne] at h
  | p :: ps, h => by
    simp only [improveOne] at h
    split at h
    · exact ⟨p, List.mem_cons_self, ‹_›⟩
    · cases h
    · split at h
      · obtain ⟨q, hq, hf⟩ := improveOne_none ‹_›
        exact ⟨q, List.mem_cons_of_mem _ hq, hf⟩
      · cases h
      · cases h

theorem improveOne_keep {top : Bool} : ∀ {ps : List Pred}, improveOne top ps = some none →
    ∀ p ∈ ps, p.improve top = .keep
  | [], _, p, hp => by cases hp
  | q :: ps, h, p, hp => by
    simp only [improveOne] at h
    split at h
    · cases h
    · cases h
    · rename_i hq
      split at h
      · cases h
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact hq
        · exact improveOne_keep ‹_› p hp
      · cases h

theorem improveOne_length {top : Bool} : ∀ {ps : List Pred} {e : Ty × Ty} {rest : List Pred},
    improveOne top ps = some (some (e, rest)) → rest.length + 1 = ps.length
  | [], _, _, h => by simp [improveOne] at h
  | p :: ps, e, rest, h => by
    simp only [improveOne] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; rfl
    · split at h
      · cases h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [improveOne_length ‹_›]

/-- Improvement succeeds wherever its constraints are entailed, by
assumptions on type variables, with a substitution any satisfying one
absorbs; what it leaves is still satisfied, and can't be improved further. -/
theorem improveAll_complete {top : Bool} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) :
    ∀ (k : Nat) {ps : List Pred} {φ : Subst}, ps.length ≤ k → Sat C ps φ →
      ∃ σ ps', improveAll top k ps = some (σ, ps') ∧ Absorbs φ σ ∧ Sat C ps' φ ∧
        (∀ p ∈ ps', p.improve top = .keep) ∧ (∀ p ∈ ps', ∃ q ∈ ps, p = q.subst σ)
  | 0, ps, φ, hk, hs => by
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], [], by simp [improveAll], fun τ => by simp, by simp, by simp, by simp⟩
  | k + 1, ps, φ, hk, hs => by
    cases hone : improveOne top ps with
    | none =>
      obtain ⟨p, hp, hf⟩ := improveOne_none hone
      exact absurd (hs p hp) (Pred.improve_fail hf hC)
    | some r =>
      cases r with
      | none =>
        exact ⟨[], ps, by simp [improveAll, hone], fun τ => by simp, hs, improveOne_keep hone,
          fun p hp => ⟨p, hp, by simp⟩⟩
      | some er =>
        obtain ⟨⟨a, b⟩, rest⟩ := er
        obtain ⟨p, hp, hq⟩ := improveOne_some hone
        obtain ⟨⟨p', hp'm, hp'⟩, hsub⟩ := improveOne_sub hone
        have hab : a.subst φ = b.subst φ := Pred.improve_eq hp' hC (hs p' hp'm)
        obtain ⟨σu, hu, habs⟩ := unify_mgu hab
        have hlen := improveOne_length hone
        obtain ⟨σ', ps', h', habs', hs', hkeep, hfrom⟩ := improveAll_complete hC k
          (ps := rest.map (·.subst σu)) (φ := φ) (by simp; omega)
          (fun q hq => by
            obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
            rw [Absorbs.pred habs]; exact hs q₀ (hsub q₀ hq₀))
        refine ⟨Subst.compose σ' σu, ps', ?_, fun τ => ?_, hs', hkeep, fun p hp => ?_⟩
        · simp [improveAll, hone, hu, h']
        · rw [Ty.subst_compose, habs', habs]
        · obtain ⟨q, hq, rfl⟩ := hfrom p hp
          obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
          exact ⟨q₀, hsub q₀ hq₀, by simp [Pred.subst_compose]⟩

/-! ### The variables the environment fixes -/

theorem length_filter_not_lt {α : Type} {f : α → Bool} :
    ∀ {l : List α}, (l.filter f).isEmpty = false → (l.filter (fun x => !f x)).length < l.length
  | [], h => by simp at h
  | x :: l, h => by
    by_cases hx : f x = true
    · simp only [List.filter_cons, hx, Bool.not_true, Bool.false_eq_true, ite_false,
        List.length_cons]
      have := List.length_filter_le (fun x => !f x) l
      omega
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ite_false, Bool.not_false,
        ite_true, List.length_cons] at h ⊢
      have := length_filter_not_lt h
      omega

/-- The fixed variables are closed: a constraint whose determining
arguments are fixed has the rest fixed. -/
theorem fixLoop_closed : ∀ (k : Nat) (ps : List Pred) (fixed : List Nat), ps.length ≤ k →
    ∀ p ∈ ps, p.fires (fixLoop k ps fixed) = true → ∀ v ∈ p.fixes, v ∈ fixLoop k ps fixed
  | 0, ps, fixed, hk, p, hp, _, _, _ => by
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero (by omega)
    cases hp
  | k + 1, ps, fixed, hk, p, hp, hfire, v, hv => by
    simp only [fixLoop] at hfire ⊢
    by_cases hempty : (ps.filter (Pred.fires fixed)).isEmpty = true
    · simp only [hempty, ↓reduceIte] at hfire ⊢
      have : p ∈ ps.filter (Pred.fires fixed) := List.mem_filter.mpr ⟨hp, hfire⟩
      simp [List.isEmpty_iff.mp hempty] at this
    · have hne := hempty
      simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hfire ⊢
      by_cases hpf : p.fires fixed = true
      · exact fixLoop_sup _ _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨p, List.mem_filter.mpr ⟨hp, hpf⟩, hv⟩))
      · have hlt := length_filter_not_lt (Bool.eq_false_iff.mpr hne)
        exact fixLoop_closed k _ _ (by omega) p (List.mem_filter.mpr ⟨hp, by simpa using hpf⟩)
          hfire v hv

/-- A property of variables that the dependencies preserve holds of every
fixed variable. -/
theorem fixLoop_all {Q : Nat → Prop} {ps₀ : List Pred}
    (hstep : ∀ p ∈ ps₀, (∀ v ∈ (p.fundep.map fun d => d.1.flatMap Ty.ftv).getD [], Q v) →
      ∀ v ∈ p.fixes, Q v) :
    ∀ (k : Nat) (ps : List Pred) (fixed : List Nat), (∀ p ∈ ps, p ∈ ps₀) →
      (∀ v ∈ fixed, Q v) → ∀ v ∈ fixLoop k ps fixed, Q v
  | 0, _, _, _, hf => hf
  | k + 1, ps, fixed, hps, hf => by
    simp only [fixLoop]
    split
    · exact hf
    · refine fixLoop_all hstep k _ _ (fun p hp => hps p (List.mem_filter.mp hp).1) ?_
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hf v hv
      · obtain ⟨p, hp, hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨hp, hfire⟩ := List.mem_filter.mp hp
        refine hstep p (hps p hp) (fun w hw => ?_) v hv
        unfold Pred.fires at hfire
        cases hd : p.fundep with
        | none => simp [hd] at hw
        | some d =>
          simp only [hd, Option.map_some, Option.getD_some] at hw hfire
          exact hf w (by simpa using List.all_eq_true.mp hfire w hw)

theorem findIdx_getElem : ∀ {l : List Nat} {a i : Nat}, findIdx l a = some i →
    l.getD i 0 = a
  | [], _, _, h => by simp [findIdx] at h
  | b :: l, a, i, h => by
    simp only [findIdx] at h
    split at h
    · cases h; simp_all
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using findIdx_getElem hj

theorem findIdx_some : ∀ {l : List Nat} {a : Nat}, a ∈ l → ∃ i, findIdx l a = some i
  | [], _, h => by cases h
  | b :: l, a, h => by
    simp only [findIdx]
    split
    · exact ⟨0, rfl⟩
    · rename_i hne
      obtain ⟨i, hi⟩ := findIdx_some ((List.mem_cons.mp h).resolve_left hne)
      exact ⟨i + 1, by simp [hi]⟩

theorem letScheme_rest {gen : Bool} {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty} {preds : List Pred} :
    ∀ c ∈ (letScheme gen Γ₁ R₁ τ₁ preds).2, c ∈ preds := by
  intro c hc
  simp only [letScheme] at hc
  split at hc
  · exact (List.mem_filter.mp hc).1
  · exact hc

/-- Substituting `f a` for each `a` in `ᾱ`, ahead of `σ`. -/
theorem Ty.subst_zip_map_mem {ᾱ : List Nat} {f : Nat → Ty} {σ : Subst} {v : Nat} (hv : v ∈ ᾱ) :
    (Ty.var v).subst (ᾱ.zip (ᾱ.map f) ++ σ) = f v := by
  induction ᾱ with
  | nil => cases hv
  | cons a ᾱ ih =>
    by_cases h : v = a
    · subst h; simp [Ty.subst, Subst.find]
    · have := ih ((List.mem_cons.mp hv).resolve_left h)
      simpa [Ty.subst, Subst.find, h] using this

theorem Ty.subst_zip_map_not_mem {ᾱ : List Nat} {f : Nat → Ty} {σ : Subst} {v : Nat}
    (hv : v ∉ ᾱ) : (Ty.var v).subst (ᾱ.zip (ᾱ.map f) ++ σ) = (Ty.var v).subst σ := by
  induction ᾱ with
  | nil => rfl
  | cons a ᾱ ih =>
    have h : v ≠ a := fun h => hv (h ▸ List.mem_cons_self)
    have := ih (fun h' => hv (List.mem_cons_of_mem _ h'))
    simpa [Ty.subst, Subst.find, h] using this

theorem exists_four_of_map {f : Ty → Ty} {args : List Ty} {a b c d : Ty}
    (h : args.map f = [a, b, c, d]) : ∃ q τ t r, args = [q, τ, t, r] := by
  rcases args with _ | ⟨q, _ | ⟨τ, _ | ⟨t, _ | ⟨r, _ | _⟩⟩⟩⟩ <;> simp at h
  exact ⟨q, τ, t, r, rfl⟩

/-- A generalised variable of a type is a quantified variable of its
generalisation. -/
theorem Ty.gen_bvs {ᾱ : List Nat} {a i : Nat} (hi : findIdx ᾱ a = some i) :
    ∀ {τ : Ty}, a ∈ τ.ftv → i ∈ (τ.gen ᾱ).bvs := by
  intro τ
  induction τ using Ty.ind with
  | var b =>
    intro h
    simp only [Ty.ftv_var, List.mem_singleton] at h
    subst h
    simp [Ty.gen, hi, PTy.bvs]
  | app c args ih =>
    intro h
    simp only [Ty.ftv_app, List.mem_flatMap] at h
    obtain ⟨x, hx, hax⟩ := h
    simp only [Ty.gen_app, PTy.bvs_app, List.flatMap_map, List.mem_flatMap]
    exact ⟨x, hx, ih x hx hax⟩

/-! ### Variables a substitution keeps below a bound -/

/-- If each variable of `τ` is sent below `m`, so is `τ`. -/
theorem Ty.subst_ftv_lt {τ : Ty} {φ : Subst} {m : Nat}
    (h : ∀ c ∈ τ.ftv, ∀ b ∈ ((Ty.var c).subst φ).ftv, b < m) : ∀ b ∈ (τ.subst φ).ftv, b < m :=
  fun b hb => by obtain ⟨c, hc, hb⟩ := Ty.ftv_subst hb; exact h c hc b hb

theorem Pred.subst_ftv_lt {p : Pred} {φ : Subst} {m : Nat}
    (h : ∀ c ∈ p.ftv, ∀ b ∈ ((Ty.var c).subst φ).ftv, b < m) : ∀ b ∈ (p.subst φ).ftv, b < m := by
  intro b hb
  simp only [Pred.ftv, Pred.subst, List.flatMap_map, List.mem_flatMap] at hb
  obtain ⟨τ, hτ, hb⟩ := hb
  exact Ty.subst_ftv_lt (fun c hc => h c (List.mem_flatMap.mpr ⟨τ, hτ, hc⟩)) b hb

theorem Pred.fundep_some {p : Pred} {ds rs : List Ty} (h : p.fundep = some (ds, rs)) :
    (∃ l r σ, p = ⟨.hasProp l, [r, σ]⟩ ∧ ds = [r] ∧ rs = [σ]) ∨
      ∃ q τ t r, p = ⟨.merge, [q, τ, t, r]⟩ ∧ ds = [q, τ, t] ∧ rs = [r] := by
  unfold Pred.fundep at h
  split at h
  · cases h; exact .inl ⟨_, _, _, rfl, rfl, rfl⟩
  · cases h; exact .inr ⟨_, _, _, _, rfl, rfl, rfl⟩
  · cases h

/-- A quantified variable of a scheme body, opened at `m`, is the variable
`m + i`. -/
theorem PTy.bvs_open {m k i : Nat} {q : PTy} (hi : i ∈ q.bvs) (hk : i < k) :
    m + i ∈ (q.inst (varBlock m k)).ftv := by
  induction q using PTy.ind with
  | free a => simp [PTy.bvs] at hi
  | bound j =>
    simp only [PTy.bvs, List.mem_singleton] at hi
    subst hi
    simp [PTy.inst, varBlock, List.getD_eq_getElem?_getD, hk]
  | app c args ih =>
    simp only [PTy.bvs_app, List.mem_flatMap] at hi
    obtain ⟨a, ha, hia⟩ := hi
    simp only [PTy.inst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map]
    exact ⟨_, ⟨a, ha, rfl⟩, ih a ha hia⟩

/-- A simple scheme's constraints, opened at `m`, are on a variable of the
block, or are `Merge`s whose determining arguments mention one. -/
theorem Scheme.Simple.openPreds_block {s : Scheme} (hs : s.Simple) {m : Nat} {p : Pred}
    (hp : p ∈ s.openPreds m) :
    (∃ v, m ≤ v ∧ ∃ rest, p.args = .var v :: rest ∧ p.cls ≠ .merge) ∨
      ∃ q τ t r, p = ⟨.merge, [q, τ, t, r]⟩ ∧ ∃ v, m ≤ v ∧ v ∈ q.ftv ++ τ.ftv ++ t.ftv := by
  simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rcases hs q hq with ⟨i, hi, hq' | ⟨l, σ, hq'⟩⟩ | ⟨q₀, τ₀, t₀, r₀, hq', i, hib, hi⟩ <;> subst hq'
  · exact .inl ⟨m + i, by omega, [], by simp [PPred.inst, PTy.inst, varBlock, hi],
      by simp [PPred.inst]⟩
  · exact .inl ⟨m + i, by omega, _, by simp [PPred.inst, PTy.inst, varBlock, hi]; rfl,
      by simp [PPred.inst]⟩
  · refine .inr ⟨q₀.inst (varBlock m s.arity), τ₀.inst (varBlock m s.arity),
      t₀.inst (varBlock m s.arity), r₀.inst (varBlock m s.arity),
      by simp only [PPred.inst, List.map_cons, List.map_nil], m + i, by omega, ?_⟩
    simp only [List.mem_append] at hib ⊢
    rcases hib with (h | h) | h
    · exact .inl (.inl (PTy.bvs_open h hi))
    · exact .inl (.inr (PTy.bvs_open h hi))
    · exact .inr (PTy.bvs_open h hi)

/-- A simple scheme's constraints, opened at `m`, mention a variable of the
block. -/
theorem Scheme.Simple.openPreds_mentions {s : Scheme} (hs : s.Simple) {m : Nat} {p : Pred}
    (hp : p ∈ s.openPreds m) : ∃ v, m ≤ v ∧ v ∈ p.ftv := by
  rcases hs.openPreds_block hp with ⟨v, hv, rest, he, -⟩ | ⟨q, τ, t, r, rfl, v, hv, hm⟩
  · exact ⟨v, hv, by simp [Pred.ftv, he]⟩
  · refine ⟨v, hv, ?_⟩
    simp only [List.mem_append] at hm
    simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    rcases hm with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))

/-- A constraint whose variables are all sent below `m` is entailed by the
assumptions `C` alone, not by the scheme's opened at `m`. -/
theorem Entails.drop_block {C : List Pred} {s : Scheme} (hs : s.Simple) {m : Nat} {p : Pred}
    (h : Entails (C ++ s.openPreds m) p) (hp : ∀ b ∈ p.ftv, b < m) : Entails C p := by
  rcases h with h | h
  · exact .inl h
  · rcases List.mem_append.mp h with h | h
    · exact .inr h
    · obtain ⟨v, hv, hm⟩ := hs.openPreds_mentions h
      have := hp v hm
      omega

/-! ## Completeness -/

theorem LitTy.eq_ty {l : Lit} {τ : Ty} (h : LitTy l τ) : τ = l.ty := by cases h <;> rfl

/-! ### Chaining -/

/-- Agreement through two inference steps. -/
theorem Agree.trans {n m : Nat} {σ₁ σ₂ φ₁ φ₂ ψ : Subst} (h₁ : Agree n σ₁ φ₁ ψ)
    (hσ₁ : σ₁.Within m) (hnm : n ≤ m) (h₂ : Agree m σ₂ φ₂ φ₁) :
    Agree n (Subst.compose σ₂ σ₁) φ₂ ψ := fun a ha => by
  rw [Ty.subst_compose, h₂.ty ((hσ₁ a).1 (by omega)), h₁ a ha]

/-- Agreement after a unifier the substitution absorbs. -/
theorem Agree.absorb {n : Nat} {σ σ' φ ψ : Subst} (h : Agree n σ φ ψ) (habs : Absorbs φ σ') :
    Agree n (Subst.compose σ' σ) φ ψ := fun a ha => by
  rw [Ty.subst_compose, habs, h a ha]

/-- Agreement survives binding a variable at or above the bound. -/
theorem Agree.fresh {n k : Nat} {σ φ ψ : Subst} {ρ : Ty} (h : Agree n σ φ ψ) (hσ : σ.Within k)
    (hnk : n ≤ k) : Agree n σ ((k, ρ) :: φ) ψ := fun a ha => by
  rw [Ty.subst_cons_fresh ((hσ a).1 (by omega)), h a ha]

theorem Sat.absorb {C P : List Pred} {φ σ : Subst} (habs : Absorbs φ σ) (h : Sat C P φ) :
    Sat C (P.map (·.subst σ)) φ := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [Absorbs.pred habs]; exact h q hq

theorem Sat.fresh {C P : List Pred} {φ : Subst} {k : Nat} {ρ : Ty} (hP : ∀ p ∈ P, p.Below k)
    (h : Sat C P φ) : Sat C P ((k, ρ) :: φ) := fun p hp => by
  rw [Pred.subst_cons_fresh (hP p hp)]; exact h p hp

theorem Sat.agree {C P : List Pred} {σ φ ψ : Subst} {n : Nat} (hag : Agree n σ φ ψ)
    (hP : ∀ p ∈ P, p.Below n) (h : Sat C P ψ) : Sat C (P.map (·.subst σ)) φ := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [hag.pred (hP q hq)]; exact h q hq

theorem Sat.app {C P Q : List Pred} {φ : Subst} (hP : Sat C P φ) (hQ : Sat C Q φ) :
    Sat C (P ++ Q) φ := fun p hp => (List.mem_append.mp hp).elim (hP p) (hQ p)

/-- What `infer_complete` says of one expression: if the expression has a
type in an instance of the context, inference finds one of which it is an
instance, with the constraints satisfied. (The instance is named `Γ'` and
`R'`, so that the typing derivation can be inverted.) -/
def InferComplete (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred} {τ' : Ty} {Γ' : Ctx}
    {R' : Option Ty},
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
    Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → HasType L C Γ' R' e τ' →
    ∃ o, infer L Γ R e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ o.τ.subst φ = τ' ∧ Sat C o.preds φ

theorem inferArgs_complete : ∀ (args : List Expr) (τs' : List Ty), (∀ a ∈ args, InferComplete L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
      Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → args.length = τs'.length →
      (∀ p ∈ args.zip τs', HasType L C Γ' R' p.1 p.2) →
      ∃ o, inferArgs L Γ R args n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
        o.τs.map (·.subst φ) = τs' ∧ Sat C o.preds φ
  | [], [], _, Γ, R, n, ψ, C, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferArgs], ψ, fun a _ => by simp, rfl, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, τ' :: τs', ih, Γ, R, n, ψ, C, Γ', R', hΓ, hR, hC, hΓ', hR', hlen, hargs => by
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ :=
      ih a (by simp) hΓ hR hC hΓ' hR' (hargs (a, τ') (by simp))
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L a hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete as τs'
      (fun a' ha' => ih a' (by simp [ha'])) (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR])
      (by simpa using hlen) (fun p hp => hargs p (by simp [hp]))
    refine ⟨_, by simp only [inferArgs, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
    · simp only [List.map_cons, hag₂.ty hτb₁, hτ₁, hτs₂]
    · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂

theorem infer_complete (L : List String) : ∀ e, InferComplete L e := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR _ _ _ ht
    cases ht with
    | lit hl =>
      exact ⟨⟨[], l.ty, [], n⟩, by simp [infer], ψ, fun a _ => by simp,
        by rw [LitTy.eq_ty hl, Lit.ty_subst], by simp⟩
  | var i =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR _ hΓ' _ ht
    cases ht with
    | @var _ _ s' _ _ τs hi hlen hc =>
      subst hΓ'
      rw [Ctx.getElem?_subst] at hi
      cases hs : Γ[i]? with
      | none => simp [hs] at hi
      | some s =>
        simp only [hs, Option.map_some, Option.some.injEq] at hi; subst hi
        have hlen' : τs.length = s.arity := by simpa using hlen
        refine ⟨⟨[], s.open n, s.openPreds n, n + s.arity⟩, by simp [infer, hs],
          Subst.block n τs ++ ψ, fun a ha => ?_, Scheme.open_block_append (hΓ.lookup hs) hlen',
          fun c hc' => hc _ ?_⟩
        · show ((Ty.var a).subst []).subst _ = _
          rw [Ty.subst_nil]
          simp only [Ty.subst, Subst.find_append, Subst.block_find_none ha]
        · rw [← Scheme.openPreds_block_append (hΓ.lookup hs) hlen']
          exact List.mem_map_of_mem hc'
  | func k body ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' _ ht
    cases ht with
    | @func _ _ _ ρ' _ _ θ' τs' hlen hb =>
      subst hlen hΓ'
      have hψΓ : Ctx.subst (funSubst n θ' τs' ρ' ψ) Γ = Ctx.subst ψ Γ :=
        Ctx.subst_congr (fun a ha => funSubst_below (hΓ a ha))
      have hparams := funSubst_params (n := n) (θ := θ') (ρ := ρ') (τs := τs') (ψ := ψ)
      have hθ : (Ty.var n).Below (n + 2 + τs'.length) := .var (by omega)
      have hτs : ∀ τ ∈ varBlock (n + 1) τs'.length, τ.Below (n + 2 + τs'.length) := fun τ hτ =>
        (varBlock_below τ hτ).mono (by omega)
      have hρ : (Ty.var (n + 1 + τs'.length)).Below (n + 2 + τs'.length) := .var (by omega)
      have hfn : (Ty.fn (.var n) (varBlock (n + 1) τs'.length) (.var (n + 1 + τs'.length))).Below
          (n + 2 + τs'.length) := Ty.Below.fn.mpr ⟨hθ, hτs, hρ⟩
      have hctx : τs'.map .mono ++ .mono (.fn θ' τs' ρ') :: .mono θ' :: Ctx.subst ψ Γ =
          Ctx.subst (funSubst n θ' τs' ρ' ψ)
            ((varBlock (n + 1) τs'.length).map .mono ++
              .mono (.fn (.var n) (varBlock (n + 1) τs'.length) (.var (n + 1 + τs'.length))) ::
              .mono (.var n) :: Γ) := by
        rw [← hψΓ]
        simp only [Ctx.subst, List.map_append, List.map_map, List.map_cons, Function.comp_def,
          Scheme.mono_subst, Ty.subst_fn, funSubst_this, funSubst_ret]
        have e₁ : List.map (fun x => Scheme.mono (Ty.subst (funSubst n θ' τs' ρ' ψ) x))
            (varBlock (n + 1) τs'.length) = τs'.map Scheme.mono := by
          conv => rhs; rw [← hparams]
          rw [List.map_map]; rfl
        rw [e₁, hparams]
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (R := some (.var (n + 1 + τs'.length)))
        (ψ := funSubst n θ' τs' ρ' ψ)
        (Ctx.Below.append_mono hτs (Ctx.Below.mono_cons hfn (Ctx.Below.mono_cons hθ
          (hΓ.mono (by omega)))))
        (fun a ha => hρ a (by simpa [Ret.ftv] using ha)) hC hctx
        (by simp only [Ret.subst_some, funSubst_ret]) hb
      have hu : ((Ty.var (n + 1 + τs'.length)).subst o₁.σ).subst φ₁ = o₁.τ.subst φ₁ := by
        rw [hag₁ _ (by omega), funSubst_ret, hτ₁]
      obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, h₁, hσ']; rfl, φ₁, fun a ha => ?_, ?_, fun p hp => ?_⟩
      · rw [Ty.subst_compose, habs, hag₁ a (by omega)]
        simp only [Ty.subst, funSubst_below ha]
      · rw [Ty.subst_compose, habs, hag₁.ty hfn]
        simp only [Ty.subst_fn, funSubst_this, funSubst_ret, hparams]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [Absorbs.pred habs]; exact hsat₁ q hq
  | app f args ihf iha =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | app hf hlen hargs =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihf hΓ hR hC hΓ' hR' hf
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L f hΓ hR h₁
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (ψ := φ₁)
        (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) hlen hargs
      obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a)
        (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
      have hu : (o₁.τ.subst o₂.σ).subst ((o₂.next, τ') :: φ₂) =
          (Ty.fn .undefined o₂.τs (.var o₂.next)).subst ((o₂.next, τ') :: φ₂) := by
        rw [Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono hn₂)), hag₂.ty hτb₁, hτ₁]
        simp only [Ty.subst_app, List.map_cons, List.map_nil, Ty.app.injEq, List.cons.injEq,
          true_and]
        refine ⟨by simp [Ty.subst, Subst.find], ?_⟩
        rw [← hτs₂]
        exact List.map_congr_left (fun τ hτ => (Ty.subst_cons_fresh (hτsb₂ τ hτ)).symm)
      obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, (o₂.next, τ') :: φ₂, ?_, ?_, ?_⟩
      · exact Agree.absorb ((hag₁.trans hσ₁ hn₁ hag₂).fresh ((hσ₁.mono hn₂).compose hσ₂)
          (by omega)) habs
      · show ((Ty.var o₂.next).subst σ₃).subst _ = τ'
        rw [habs]; simp [Ty.subst, Subst.find]
      · refine Sat.absorb habs (Sat.app ?_ ?_)
        · refine Sat.fresh (fun p hp => ?_) (Sat.agree hag₂ hp₁ hsat₁)
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
        · exact Sat.fresh hp₂ hsat₂
  | let_ mb e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | let_ s F hgen hval hsimp h₂ =>
      subst hΓ' hR'
      -- Open `s` at a block of variables fresh for everything in sight.
      obtain ⟨m, hmF, hmΓ, hmR, hms, hmC, hmψ⟩ : ∃ m, (∀ a ∈ F, a < m) ∧
          (∀ a ∈ ctxFtv (Ctx.subst ψ Γ), a < m) ∧ (∀ a ∈ Ret.ftv (Ret.subst ψ R), a < m) ∧
          (∀ a ∈ s.ftv, a < m) ∧ (∀ p ∈ C, ∀ a ∈ p.ftv, a < m) ∧
          (∀ a < n, ∀ b ∈ ((Ty.var a).subst ψ).ftv, b < m) := by
        have h := lt_maxPlusOne (l := F ++ ctxFtv (Ctx.subst ψ Γ) ++ Ret.ftv (Ret.subst ψ R) ++
          s.ftv ++ C.flatMap Pred.ftv ++ (List.range n).flatMap (fun a => ((Ty.var a).subst ψ).ftv))
        refine ⟨_, fun a ha => h a (by simp [ha]), fun a ha => h a (by simp [ha]),
          fun a ha => h a (by simp [ha]), fun a ha => h a (by simp [ha]), fun p hp a ha => h a ?_,
          fun a ha b hb => h b ?_⟩
        · simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨p, hp, ha⟩)
        · simp only [List.mem_append, List.mem_flatMap, List.mem_range]; exact .inr ⟨a, ha, hb⟩
      have hC₁ : ∀ p ∈ C ++ s.openPreds m, p.AssumableAt false := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hC p hp
        · simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          rcases hsimp q hq with ⟨i, hi, hq' | ⟨l, σ, hq'⟩⟩ | ⟨q₀, τ₀, t₀, r₀, hq', -⟩ <;>
            subst hq'
          · exact .inl ⟨m + i, by simp [PPred.inst, PTy.inst, varBlock, hi]⟩
          · exact .inr (.inl ⟨l, m + i, _, by simp [PPred.inst, PTy.inst, varBlock, hi]; rfl⟩)
          · exact .inr (.inr ⟨_, _, _, _, rfl, fun h => by cases h⟩)
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC₁ rfl rfl (hgen m hmF)
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      -- Improvement succeeds, and `φ₁` absorbs it.
      obtain ⟨σi, preds₁, himp, habsi, hsat₁', hkeep, _⟩ :=
        improveAll_complete hC₁ o₁.preds.length (Nat.le_refl _) hsat₁
      obtain ⟨hσi, hpi⟩ := improveAll_inv _ hp₁ himp
      have hσ₁' := hσ₁.compose hσi
      have hagS : Agree n (Subst.compose σi o₁.σ) φ₁ ψ := hag₁.absorb habsi
      have hτ₁' : (o₁.τ.subst σi).subst φ₁ = s.open m := by rw [habsi, hτ₁]
      have hτb₁' := hσi.subst_below hτb₁
      have hΓ₁ : Ctx.Below o₁.next (Ctx.subst (Subst.compose σi o₁.σ) Γ) :=
        hσ₁'.ctx_below (hΓ.mono hn₁)
      have hR₁ : Ret.Below o₁.next (Ret.subst (Subst.compose σi o₁.σ) R) :=
        hσ₁'.ret_below (hR.mono hn₁)
      -- Sending the block to `τs` turns the assumptions into `C` and `s`'s
      -- constraints at `τs`.
      have hCb : ∀ τs : List Ty, C.map (·.subst (Subst.block m τs)) = C := fun τs => by
        conv => rhs; rw [← List.map_id C]
        exact List.map_congr_left (fun q hq => Pred.subst_block_below (hmC q hq))
      have hblock : ∀ τs : List Ty, τs.length = s.arity → ∀ p ∈ preds₁,
          Entails (C ++ s.instPreds τs) ((p.subst φ₁).subst (Subst.block m τs)) := by
        intro τs hlen p hp
        have := Entails.subst (Subst.block m τs) (hsat₁' p hp)
        rwa [List.map_append, hCb, Scheme.openPreds_block s hms hlen] at this
      -- The variables the environment fixes are sent below the block.
      let env := ctxFtv (Ctx.subst (Subst.compose σi o₁.σ) Γ) ++
        Ret.ftv (Ret.subst (Subst.compose σi o₁.σ) R)
      have hQ : ∀ v ∈ fixedVars preds₁ env, ∀ b ∈ ((Ty.var v).subst φ₁).ftv, b < m := by
        refine fixLoop_all (ps₀ := preds₁) (fun p hp hds v hv => ?_) _ _ _ (fun p hp => hp)
          (fun v hv b hb => ?_)
        · unfold Pred.fixes at hv
          cases hd : p.fundep with
          | none => simp [hd] at hv
          | some d =>
            obtain ⟨ds, rs⟩ := d
            rcases Pred.fundep_some hd with ⟨l, r, σ, rfl, rfl, rfl⟩ | ⟨q, τ, t, r, rfl, rfl, rfl⟩
            · simp only [hd, Option.map_some, Option.getD_some, List.flatMap_cons,
                List.flatMap_nil, List.append_nil] at hds hv
              -- The receiver is sent below `m`, so the field is.
              have hr : ∀ b ∈ (r.subst φ₁).ftv, b < m := Ty.subst_ftv_lt hds
              intro b hb
              have hbσ : b ∈ (σ.subst φ₁).ftv := Ty.ftv_subst_mem hv hb
              rcases hsat₁' _ hp with hi | hm'
              · generalize hq : Pred.subst φ₁ ⟨.hasProp l, [r, σ]⟩ = q at hi
                cases hi with
                | plusNumber | plusString | mergePre | mergeAbs => simp [Pred.subst] at hq
                | hasProp hf =>
                  simp only [Pred.subst, Pred.mk.injEq, List.map_cons, List.map_nil,
                    List.cons.injEq, and_true] at hq
                  obtain ⟨-, hr', hσ'⟩ := hq
                  refine hr b ?_
                  rw [hr']
                  simp only [Ty.ftv_app, List.mem_flatMap]
                  refine ⟨_, (List.of_mem_zip (Ty.field_mem hf)).2, ?_⟩
                  simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
                    List.append_nil]
                  exact .inr (by rw [← hσ']; exact hbσ)
              · rcases List.mem_append.mp hm' with hm' | hm'
                · have : b ∈ (Pred.subst φ₁ ⟨.hasProp l, [r, σ]⟩).ftv := by
                    simp [Pred.ftv, Pred.subst, hbσ]
                  exact hmC _ hm' b this
                · rcases hsimp.openPreds_block hm' with ⟨v', hv', rest, he, -⟩ |
                    ⟨q', τ', t', r', he, -⟩
                  · simp only [Pred.subst, List.map_cons, List.cons.injEq] at he
                    have := hr v' (by rw [he.1]; simp)
                    omega
                  · simp [Pred.subst] at he
            · simp only [hd, Option.map_some, Option.getD_some, List.flatMap_cons,
                List.flatMap_nil, List.append_nil] at hds hv
              -- The operand's slot and the slot written over are sent below
              -- `m`, so the result is.
              have hd' : ∀ b ∈ (q.subst φ₁).ftv ++ (τ.subst φ₁).ftv ++ (t.subst φ₁).ftv, b < m := by
                intro b hb
                simp only [List.mem_append] at hb
                rcases hb with (hb | hb) | hb
                · exact Ty.subst_ftv_lt (fun c hc => hds c (by simp [hc])) b hb
                · exact Ty.subst_ftv_lt (fun c hc => hds c (by simp [hc])) b hb
                · exact Ty.subst_ftv_lt (fun c hc => hds c (by simp [hc])) b hb
              intro b hb
              have hbr : b ∈ (r.subst φ₁).ftv := Ty.ftv_subst_mem hv hb
              rcases hsat₁' _ hp with hi | hm'
              · generalize hq' : Pred.subst φ₁ ⟨.merge, [q, τ, t, r]⟩ = q'' at hi
                cases hi with
                | plusNumber | plusString | hasProp _ => simp [Pred.subst] at hq'
                | mergePre =>
                  simp only [Pred.subst, Pred.mk.injEq, List.map_cons, List.map_nil,
                    List.cons.injEq, and_true, true_and] at hq'
                  obtain ⟨-, hτ', -, hr'⟩ := hq'
                  rw [hr', ← hτ'] at hbr
                  simp only [Ty.ftv_app, List.flatMap_cons, List.flatMap_nil, List.mem_append,
                    List.append_nil] at hbr
                  rcases hbr with hbr | hbr
                  · simp at hbr
                  · exact hd' b (by simp [hbr])
                | mergeAbs =>
                  simp only [Pred.subst, Pred.mk.injEq, List.map_cons, List.map_nil,
                    List.cons.injEq, and_true, true_and] at hq'
                  obtain ⟨-, -, ht', hr'⟩ := hq'
                  rw [hr', ← ht'] at hbr
                  exact hd' b (by simp [hbr])
              · rcases List.mem_append.mp hm' with hm' | hm'
                · have : b ∈ (Pred.subst φ₁ ⟨.merge, [q, τ, t, r]⟩).ftv := by
                    simp [Pred.ftv, Pred.subst, hbr]
                  exact hmC _ hm' b this
                · rcases hsimp.openPreds_block hm' with ⟨v', hv', rest, he, hcls⟩ |
                    ⟨q', τ', t', r', he, v', hv', hmv⟩
                  · exact absurd (by simp [Pred.subst]) hcls
                  · simp only [Pred.subst, List.map_cons, List.map_nil, Pred.mk.injEq,
                      List.cons.injEq, and_true, true_and] at he
                    obtain ⟨rfl, rfl, rfl, -⟩ := he
                    have := hd' v' hmv
                    omega
        · rcases List.mem_append.mp hv with hv | hv
          · exact hmΓ b (by rw [← hagS.ctx hΓ]; exact Ctx.ftv_subst_mem hv hb)
          · exact hmR b (by rw [← hagS.ret hR]; exact Ret.ftv_subst_mem hv hb)
      have hls := letScheme_below (gen := Expr.generalises e₁ e₂)
        (Γ₁ := Ctx.subst (Subst.compose σi o₁.σ) Γ) (R₁ := Ret.subst (Subst.compose σi o₁.σ) R)
        hτb₁' hpi
      -- The scheme inference finds passes its check, is more general than
      -- `s`, and leaves constraints `C` entails.
      have key : (letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
            (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁).1.preds.all
            (PPred.isSimple (letScheme (Expr.generalises e₁ e₂)
              (Ctx.subst (Subst.compose σi o₁.σ) Γ) (Ret.subst (Subst.compose σi o₁.σ) R)
              (o₁.τ.subst σi) preds₁).1.arity) = true ∧
          Generalizes C ((letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
            (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁).1.subst φ₁) s ∧
          ((((letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
            (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁).1.subst φ₁).arity = 0 ∧
            ((letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
              (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁).1.subst φ₁).preds = [])
            ∨ e₂.writes 0 = false) ∧
          Sat C (letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
            (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁).2 φ₁ := by
        by_cases hv : Expr.generalises e₁ e₂ = true
        · have hw : e₂.writes 0 = false := by
            simp only [Expr.generalises, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
              Bool.not_true] at hv
            exact hv.2
          simp only [letScheme, hv, ↓reduceIte]
          generalize hα : genVars (Ctx.subst (Subst.compose σi o₁.σ) Γ)
            (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁ = ᾱ
          have hfixed : ∀ v ∈ ᾱ, v ∉ fixedVars preds₁ env := by
            intro v hv'; rw [← hα] at hv'
            simp only [genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at hv'
            exact hv'.2
          have hcover : ∀ v ∈ (o₁.τ.subst σi).ftv ++ preds₁.flatMap Pred.ftv,
              v ∈ ᾱ ∨ v ∈ fixedVars preds₁ env := by
            intro v hv'
            by_cases hf : v ∈ fixedVars preds₁ env
            · exact .inr hf
            · refine .inl ?_
              rw [← hα]
              simp only [genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
              exact ⟨hv', hf⟩
          -- Each variable is sent by the instance to where `φ₁` and the
          -- block send it.
          have hvar : ∀ (τs : List Ty) (v : Nat), (v ∈ ᾱ ∨ v ∈ fixedVars preds₁ env) →
              (Ty.var v).subst (ᾱ.zip (ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst
                (Subst.block m τs))) ++ φ₁) = ((Ty.var v).subst φ₁).subst (Subst.block m τs) := by
            intro τs v hv'
            by_cases hvα : v ∈ ᾱ
            · exact Ty.subst_zip_map_mem hvα
            · rw [Ty.subst_zip_map_not_mem hvα,
                Ty.subst_block_below (hQ v (hv'.resolve_left hvα))]
          refine ⟨?_, fun τs hlen => ?_, .inr hw, ?_⟩
          · -- Each generalised constraint is on a generalised variable.
            simp only [generalize, List.all_map, List.all_eq_true, Function.comp_apply]
            intro g hg
            obtain ⟨hgp, hgα⟩ := List.mem_filter.mp hg
            obtain ⟨a, ha, haα⟩ := List.any_eq_true.mp hgα
            simp only [decide_eq_true_eq] at haα
            rcases Pred.improve_keep (hkeep g hgp) with ⟨args, rfl⟩ | ⟨l, r, σ, rfl⟩ |
              ⟨args, rfl, -⟩
            · -- `Plus τ`: the type is a variable.
              obtain ⟨b, rfl⟩ : ∃ b, args = [.var b] := by
                rcases hsat₁' _ hgp with hi | hm'
                · generalize hq : Pred.subst φ₁ ⟨.plus, args⟩ = q at hi
                  cases hi <;> simp only [Pred.subst, Pred.mk.injEq, true_and] at hq <;>
                    match args, hq, ha with
                    | [.var b], _, _ => exact ⟨b, rfl⟩
                    | [.app _ []], _, ha => simp [Pred.ftv] at ha
                    | [.app _ (_ :: _)], hq, _ => simp at hq
                    | [], hq, _ => simp at hq
                    | _ :: _ :: _, hq, _ => simp at hq
                · rcases hC₁ _ hm' with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, -⟩
                  · simp only [Pred.subst, Pred.mk.injEq, true_and] at hx
                    match args, hx with
                    | [.var b], _ => exact ⟨b, rfl⟩
                    | [.app _ _], hx => simp at hx
                    | [], hx => simp at hx
                    | _ :: _ :: _, hx => simp at hx
                  · simp [Pred.subst] at hx
                  · simp [Pred.subst] at hx
              simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                Ty.ftv_var, List.mem_singleton] at ha
              subst ha
              obtain ⟨i, hi⟩ := findIdx_some haα
              simp [Pred.gen, Ty.gen, hi, PPred.isSimple, findIdx_lt hi]
            · -- `HasProp l r σ`: the receiver is generalised, since a fixed one
              -- would fix the field too.
              have hrα : r ∈ ᾱ := by
                rcases hcover r (List.mem_append_right _
                    (List.mem_flatMap.mpr ⟨_, hgp, by simp [Pred.ftv]⟩)) with h | hr
                · exact h
                · exfalso
                  have hfire : Pred.fires (fixedVars preds₁ env) ⟨.hasProp l, [.var r, σ]⟩ = true := by
                    simp [Pred.fires, Pred.fundep, hr]
                  have hσfix := fixLoop_closed _ _ _ (Nat.le_refl _) _ hgp hfire
                  simp only [Pred.fixes, Pred.fundep, List.flatMap_cons, List.flatMap_nil,
                    List.append_nil] at hσfix
                  simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                    Ty.ftv_var, List.mem_append, List.mem_singleton] at ha
                  rcases ha with rfl | ha
                  · exact hfixed _ haα hr
                  · exact hfixed _ haα (hσfix a ha)
              obtain ⟨i, hi⟩ := findIdx_some hrα
              simp [Pred.gen, Ty.gen, hi, PPred.isSimple, findIdx_lt hi]
            · -- `Merge q τ t r`: a variable of the operand's slot or of the
              -- slot written over is generalised, since fixed ones would fix
              -- the result too.
              obtain ⟨q, τ, t, r, rfl⟩ : ∃ q τ t r, args = [q, τ, t, r] := by
                rcases hsat₁' _ hgp with hi | hm'
                · generalize hq : Pred.subst φ₁ ⟨.merge, args⟩ = q at hi
                  cases hi with
                  | plusNumber | plusString | hasProp _ => simp [Pred.subst] at hq
                  | mergePre | mergeAbs =>
                    simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
                    exact exists_four_of_map hq
                · rcases hC₁ _ hm' with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨q', τ', s', r', hx, -⟩
                  · simp [Pred.subst] at hx
                  · simp [Pred.subst] at hx
                  · simp only [Pred.subst, Pred.mk.injEq, true_and] at hx
                    exact exists_four_of_map hx
              by_cases hdet : ∃ v ∈ q.ftv ++ τ.ftv ++ t.ftv, v ∈ ᾱ
              · obtain ⟨v, hv, hvα⟩ := hdet
                obtain ⟨i, hi⟩ := findIdx_some hvα
                simp only [Pred.gen, List.map_cons, List.map_nil, PPred.isSimple, List.any_eq_true,
                  decide_eq_true_eq]
                refine ⟨i, ?_, findIdx_lt hi⟩
                simp only [List.mem_append] at hv ⊢
                rcases hv with (hv | hv) | hv
                · exact .inl (.inl (Ty.gen_bvs hi hv))
                · exact .inl (.inr (Ty.gen_bvs hi hv))
                · exact .inr (Ty.gen_bvs hi hv)
              · exfalso
                have hdfix : ∀ v ∈ q.ftv ++ τ.ftv ++ t.ftv, v ∈ fixedVars preds₁ env := by
                  intro v hv
                  refine (hcover v (List.mem_append_right _
                    (List.mem_flatMap.mpr ⟨_, hgp, ?_⟩))).resolve_left
                    (fun hvα => hdet ⟨v, hv, hvα⟩)
                  simp only [List.mem_append] at hv
                  simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                    List.mem_append]
                  rcases hv with (hv | hv) | hv
                  · exact .inl hv
                  · exact .inr (.inl hv)
                  · exact .inr (.inr (.inl hv))
                have hfire : Pred.fires (fixedVars preds₁ env) ⟨.merge, [q, τ, t, r]⟩ = true := by
                  simp only [Pred.fires, Pred.fundep, List.all_eq_true, decide_eq_true_eq]
                  intro v hv
                  exact hdfix v (by simpa using hv)
                have hrfix := fixLoop_closed _ _ _ (Nat.le_refl _) _ hgp hfire
                simp only [Pred.fixes, Pred.fundep, List.flatMap_cons, List.flatMap_nil,
                  List.append_nil] at hrfix
                simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  List.mem_append] at ha
                rcases ha with ha | ha | ha | ha
                · exact hdet ⟨a, by simp [ha], haα⟩
                · exact hdet ⟨a, by simp [ha], haα⟩
                · exact hdet ⟨a, by simp [ha], haα⟩
                · exact hfixed _ haα (hrfix a ha)
          · -- More general than `s`.
            have hlen' : ᾱ.length =
                (ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst (Subst.block m τs))).length := by simp
            refine ⟨ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst (Subst.block m τs)),
              by simp [generalize, Scheme.subst], ?_, ?_⟩
            · rw [generalize_subst_inst φ₁ hlen', ← Scheme.open_block s hms hlen, ← hτ₁',
                ← Ty.subst_compose (Subst.block m τs) φ₁ (o₁.τ.subst σi)]
              refine Ty.subst_congr' (fun v hv' => ?_)
              rw [Ty.subst_compose]
              exact hvar τs v (hcover v (List.mem_append_left _ hv'))
            · intro c hc
              rw [generalize_subst_instPreds φ₁ hlen'] at hc
              obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hc
              have hgp := (List.mem_filter.mp hg).1
              have heq : g.subst (ᾱ.zip (ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst
                  (Subst.block m τs))) ++ φ₁) = (g.subst φ₁).subst (Subst.block m τs) := by
                rw [← Pred.subst_compose]
                exact Pred.subst_congr' (fun v hv' => by
                  rw [Ty.subst_compose]
                  exact hvar τs v (hcover v (List.mem_append_right _
                    (List.mem_flatMap.mpr ⟨g, hgp, hv'⟩))))
              rw [heq]
              exact hblock τs hlen _ hgp
          · -- What stays pending has only fixed variables, so `C` entails it.
            intro c hc
            obtain ⟨hcp, hcα⟩ := List.mem_filter.mp hc
            have hcfix : ∀ v ∈ c.ftv, v ∈ fixedVars preds₁ env := fun v hv' =>
              (hcover v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hcp, hv'⟩))).resolve_left
                (fun hvα => by
                  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
                    decide_eq_true_eq] at hcα
                  exact hcα v hv' hvα)
            exact (hsat₁' c hcp).drop_block hsimp
              (Pred.subst_ftv_lt (fun v hv' => hQ v (hcfix v hv')))
        · -- Not generalised: `s` quantifies nothing.
          have harity : s.arity = 0 ∧ s.preds = [] :=
            hval.resolve_right (fun ⟨hv', hw'⟩ => hv (by
              simp [Expr.generalises, Expr.isValue_complete hv', hw']))
          simp only [letScheme, hv, Bool.false_eq_true, ↓reduceIte]
          refine ⟨by simp [Scheme.mono], fun τs hlen =>
            ⟨[], by simp [Scheme.mono, Scheme.subst], ?_, by
              simp [Scheme.instPreds, Scheme.mono, Scheme.subst]⟩,
            .inl ⟨by simp [Scheme.mono, Scheme.subst], by simp [Scheme.mono, Scheme.subst]⟩, ?_⟩
          · have hτs : τs = [] := List.eq_nil_of_length_eq_zero (hlen.trans harity.1)
            subst hτs
            rw [Scheme.mono_subst, Scheme.mono_inst, hτ₁']
            simp [Scheme.open, varBlock, harity.1]
          · intro c hc
            have := hsat₁' c hc
            simpa [Scheme.openPreds, Scheme.instPreds, harity.2] using this
      rcases hlsq : letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
        (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁ with ⟨s₁, rest⟩
      rw [hlsq] at hls key
      obtain ⟨hall, hgz, hw, hsatr⟩ := key
      have h₂' := h₂.generalize_ctx (Δ := []) (Γ := Ctx.subst ψ Γ) (s := s) (s' := s₁.subst φ₁)
        rfl (fun c h => h) hgz hw
      obtain ⟨o₂, h₂o, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (Γ := s₁ :: Ctx.subst (Subst.compose σi o₁.σ) Γ)
        (R := Ret.subst (Subst.compose σi o₁.σ) R) (ψ := φ₁) (Ctx.Below.cons hls.1 hΓ₁) hR₁ hC
        (by simp only [List.nil_append, Ctx.subst_cons, hagS.ctx hΓ]) (hagS.ret hR).symm h₂'
      refine ⟨⟨Subst.compose o₂.σ (Subst.compose σi o₁.σ), o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.preds,
        o₂.next⟩, ?_, φ₂, hagS.trans hσ₁' hn₁ hag₂, hτ₂,
        Sat.app (Sat.agree hag₂ hls.2 hsatr) hsat₂⟩
      simp only [infer, h₁, himp, hlsq, hall, ↓reduceIte, h₂o]
  | assign i e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | @assign _ _ s' _ _ _ hi ha hp he =>
      subst hΓ'
      rw [Ctx.getElem?_subst] at hi
      cases hs : Γ[i]? with
      | none => simp [hs] at hi
      | some s =>
        simp only [hs, Option.map_some, Option.some.injEq] at hi; subst hi
        have ha' : s.arity = 0 := by simpa [Scheme.subst] using ha
        have hp' : s.preds = [] := by simpa [Scheme.subst] using hp
        rw [← Scheme.inst_nil_subst] at he ⊢
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC rfl hR' he
        have hsb : (s.inst []).Below n := Scheme.inst_nil_below (hΓ.lookup hs)
        have hu : ((s.inst []).subst o₁.σ).subst φ₁ = o₁.τ.subst φ₁ := by
          rw [hag₁.ty hsb, hτ₁]
        obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
        refine ⟨_, by simp only [infer, hs, ha', hp', and_self, ↓reduceIte, h₁, hσ']; rfl, φ₁,
          hag₁.absorb habs, ?_, Sat.absorb habs hsat₁⟩
        show ((s.inst []).subst (Subst.compose σ' o₁.σ)).subst φ₁ = _
        rw [Ty.subst_compose, habs, hag₁.ty hsb]
  | cond c t e ihc iht ihe =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | cond hc htt hte =>
      obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc hΓ hR hC hΓ' hR' hc
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L c hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := iht (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) htt
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L t hΓ₁ hR₁ h₂
      have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
      have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
      obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := ihe (ψ := φ₂) hΓ₂ hR₂ hC
        (by rw [hΓ', hag₂.ctx hΓ₁, hag₁.ctx hΓ]) (by rw [hR', hag₂.ret hR₁, hag₁.ret hR]) hte
      obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := infer_inv L e hΓ₂ hR₂ h₃
      have hu : (o₂.τ.subst o₃.σ).subst φ₃ = o₃.τ.subst φ₃ := by rw [hag₃.ty hτb₂, hτ₂, hτ₃]
      obtain ⟨σ₄, hσ₄, habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, h₁, h₂, h₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
      · exact ((hag₁.trans hσ₁ hn₁ hag₂).trans ((hσ₁.mono hn₂).compose hσ₂) (by omega)
          hag₃).absorb habs
      · show (o₃.τ.subst σ₄).subst φ₃ = τ'
        rw [habs, hτ₃]
      · refine Sat.absorb habs (Sat.app (Sat.agree hag₃ (fun p hp => ?_)
          (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂)) hsat₃)
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
        · exact hp₂ p hp
  | unop op e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | unop hop he =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      cases hop with
      | not =>
        exact ⟨⟨o₁.σ, .boolean, o₁.preds, o₁.next⟩, by simp only [infer, h₁], φ₁, hag₁, rfl,
          hsat₁⟩
      | typeof =>
        exact ⟨⟨o₁.σ, .string, o₁.preds, o₁.next⟩, by simp only [infer, h₁], φ₁, hag₁, rfl,
          hsat₁⟩
      | neg =>
        obtain ⟨σ', hσ', habs⟩ := unify_mgu (τ₁ := o₁.τ) (τ₂ := .number) (ψ := φ₁)
          (by rw [hτ₁]; rfl)
        exact ⟨_, by simp only [infer, h₁, hσ']; rfl, φ₁, hag₁.absorb habs, rfl,
          Sat.absorb habs hsat₁⟩
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | binop hop ht₁ ht₂ =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' ht₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) ht₂
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L e₂ hΓ₁ hR₁ h₂
      have hag₁₂ := hag₁.trans hσ₁ hn₁ hag₂
      have hsat₁₂ : Sat C (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds) φ₂ :=
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂
      have h₁₂ : (o₁.τ.subst o₂.σ).subst φ₂ = o₁.τ.subst φ₁ := hag₂.ty hτb₁
      cases hop with
      | plus hent =>
        obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu (τ₁ := o₁.τ.subst o₂.σ) (τ₂ := o₂.τ) (ψ := φ₂)
          (by rw [h₁₂, hτ₁, hτ₂])
        refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, φ₂, hag₁₂.absorb habs, ?_, ?_⟩
        · show (o₂.τ.subst σ₃).subst φ₂ = _
          rw [habs, hτ₂]
        · refine Sat.absorb habs (Sat.app hsat₁₂ (fun p hp => ?_))
          simp only [List.mem_singleton] at hp; subst hp
          simpa [Pred.subst, hτ₂] using hent
      | minus =>
        obtain ⟨σ₃, hσ₃, habs₃⟩ := unify_mgu (τ₁ := o₁.τ.subst o₂.σ) (τ₂ := .number) (ψ := φ₂)
          (by rw [h₁₂, hτ₁]; rfl)
        obtain ⟨σ₄, hσ₄, habs₄⟩ := unify_mgu (τ₁ := o₂.τ.subst σ₃) (τ₂ := .number) (ψ := φ₂)
          (by rw [habs₃, hτ₂]; rfl)
        exact ⟨_, by simp only [infer, h₁, h₂, hσ₃, hσ₄]; rfl, φ₂,
          (hag₁₂.absorb habs₃).absorb habs₄, rfl, Sat.absorb habs₄ (Sat.absorb habs₃ hsat₁₂)⟩
  | ret e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | @ret _ _ τr' _ _ he =>
      cases R with
      | none => simp at hR'
      | some τr =>
        simp only [Ret.subst_some, Option.some.injEq] at hR'
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' (by rw [hR']; rfl) he
        obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
        have hτr : τr.Below n := fun a ha => hR a (by simpa [Ret.ftv] using ha)
        obtain ⟨σ', hσ', habs⟩ := unify_mgu (τ₁ := τr.subst o₁.σ) (τ₂ := o₁.τ) (ψ := φ₁)
          (by rw [hag₁.ty hτr, hτ₁, hR'])
        have hσ'w := unify_within (hσ₁.subst_below (hτr.mono hn₁)) hτb₁ hσ'
        refine ⟨_, by simp only [infer, h₁, hσ']; rfl, (o₁.next, τ') :: φ₁,
          (hag₁.absorb habs).fresh (hσ₁.compose hσ'w) hn₁, by simp [Ty.subst, Subst.find],
          Sat.fresh (fun p hp => ?_) (Sat.absorb habs hsat₁)⟩
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ'w.pred_below (hp₁ q hq)
  | throw_ e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | throw_ he =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      exact ⟨⟨o₁.σ, .var o₁.next, o₁.preds, o₁.next + 1⟩, by simp only [infer, h₁],
        (o₁.next, τ') :: φ₁, hag₁.fresh hσ₁ hn₁, by simp [Ty.subst, Subst.find],
        Sat.fresh hp₁ hsat₁⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | seq ht₁ ht₂ =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' ht₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) ht₂
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
        by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂,
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

  | while_ c body ihc ihb =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | while_ hc hb =>
      obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc hΓ hR hC hΓ' hR' hc
      obtain ⟨hn₁, hσ₁, _, hp₁⟩ := infer_inv L c hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := ihb (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) hb
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, .undefined, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
        o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, rfl,
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩
  | break_ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | break_ =>
      exact ⟨⟨[], .var n, [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
        fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha],
        by simp [Ty.subst, Subst.find], by simp [Sat]⟩
  | continue_ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | continue_ =>
      exact ⟨⟨[], .var n, [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
        fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha],
        by simp [Ty.subst, Subst.find], by simp [Sat]⟩
  | tryCatch body handler ihb ihh =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | tryCatch hb hh =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihb hΓ hR hC hΓ' hR' hb
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L body hΓ hR h₁
      have hunk : Ty.unknown.Below o₁.next := fun a ha => by simp [Ty.ftv] at ha
      have hΓ₁ := Ctx.Below.mono_cons hunk (hσ₁.ctx_below (hΓ.mono hn₁))
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihh (ψ := φ₁) hΓ₁ hR₁ hC
        (by simp only [Ctx.subst_cons, Scheme.mono_subst, Ty.subst_app, List.map_nil]; rw [hΓ', hag₁.ctx hΓ])
        (by rw [hR', hag₁.ret hR]) hh
      have hu : (o₁.τ.subst o₂.σ).subst φ₂ = o₂.τ.subst φ₂ := by rw [hag₂.ty hτb₁, hτ₁, hτ₂]
      obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, φ₂, (hag₁.trans hσ₁ hn₁ hag₂).absorb habs,
        ?_, Sat.absorb habs (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂)⟩
      show (o₂.τ.subst σ₃).subst φ₂ = τ'
      rw [habs, hτ₂]
  | tryFinally body fin ihb ihf =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | tryFinally hb hf =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihb hΓ hR hC hΓ' hR' hb
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L body hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := ihf (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) hf
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
        o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂,
        by rw [hag₂.ty hτb₁, hτ₁], Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

  | obj ls es ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | obj hτs habs hL hes hargs =>
      obtain ⟨o, h, φ, hag, hτs', hsat⟩ :=
        inferArgs_complete es _ ih hΓ hR hC hΓ' hR' (by omega) hargs
      obtain ⟨hn, hσ, hτsb, hpb⟩ := inferArgs_inv es (fun a _ => infer_inv L a) hΓ hR h
      rename_i absent
      have hfresh : ∀ τ : Ty, τ.Below o.next →
          τ.subst (Subst.block o.next absent ++ φ) = τ.subst φ := fun τ hτ =>
        Ty.subst_congr (fun a ha => by
          simp [Subst.find_append, Subst.block_find_none (hτ a ha)])
      have hc : ls.all (· ∈ L) = true ∧ es.length = ls.length :=
        ⟨List.all_eq_true.mpr (fun l hl => by simpa using hL l hl), hes⟩
      refine ⟨_, by simp only [infer, hc, and_self, ↓reduceIte, h]; rfl,
        Subst.block o.next absent ++ φ, fun a ha => ?_, ?_,
        fun p hp => ?_⟩
      · rw [hfresh _ ((hσ a).1 (by omega))]; exact hag a ha
      · simp only [Ty.subst_app, objSlots_subst]
        have h₁ : o.τs.map (·.subst (Subst.block o.next absent ++ φ)) = o.τs.map (·.subst φ) :=
          List.map_congr_left (fun τ hτ => hfresh τ (hτsb τ hτ))
        rw [h₁, hτs', ← habs, varBlock_subst_block]
      · rw [Pred.subst_congr (σ' := φ) (fun a ha => by
          simp [Subst.find_append, Subst.block_find_none (hpb p hp a ha)])]
        exact hsat p hp
  | get e l ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | get he hpr =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      refine ⟨⟨o₁.σ, .var o₁.next, o₁.preds ++ [⟨.hasProp l, [o₁.τ, .var o₁.next]⟩], o₁.next + 1⟩,
        by simp only [infer, h₁], (o₁.next, τ') :: φ₁, hag₁.fresh hσ₁ hn₁,
        by simp [Ty.subst, Subst.find], ?_⟩
      refine Sat.app (Sat.fresh hp₁ hsat₁) ?_
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_cons_fresh hτb₁, hτ₁]
      simpa [Ty.subst, Subst.find] using hpr
  | set e l v ihe ihv =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | set he hpr hv =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihv (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
        (hσ₁.ret_below (hR.mono hn₁)) hC (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) hv
      refine ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
          [⟨.hasProp l, [o₁.τ.subst o₂.σ, o₂.τ]⟩], o₂.next⟩,
        by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂, ?_⟩
      refine Sat.app (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂) ?_
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Pred.subst, List.map_cons, List.map_nil, hag₂.ty hτb₁, hτ₁, hτ₂]
      exact hpr
  | spread e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | spread hps hτs hss hrs he₁ he₂ hm =>
      rename_i ss ps τs rs
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' he₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) he₂
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L e₂ hΓ₁ hR₁ h₂
      -- The fresh variables, sent to the slots of the derivation.
      let φ₃ := Subst.block o₂.next (ss ++ ps ++ τs ++ rs) ++ φ₂
      have hfresh : ∀ τ : Ty, τ.Below o₂.next → τ.subst φ₃ = τ.subst φ₂ := fun τ hτ =>
        Ty.subst_congr (fun a ha => by
          simp [φ₃, Subst.find_append, Subst.block_find_none (hτ a ha)])
      have hpfresh : ∀ p : Pred, p.Below o₂.next → p.subst φ₃ = p.subst φ₂ := fun p hp =>
        Pred.subst_congr (fun a ha => by
          simp [φ₃, Subst.find_append, Subst.block_find_none (hp a ha)])
      have hbss : (varBlock o₂.next L.length).map (·.subst φ₃) = ss := by
        have := varBlock_subst_block_mid o₂.next [] ss (ps ++ τs ++ rs) φ₂
        simp only [List.length_nil, Nat.add_zero, List.nil_append, ← List.append_assoc,
          hss] at this
        exact this
      have hbps : (varBlock (o₂.next + L.length) L.length).map (·.subst φ₃) = ps := by
        have := varBlock_subst_block_mid o₂.next ss ps (τs ++ rs) φ₂
        simp only [← List.append_assoc, hss, hps] at this
        exact this
      have hbτs : (varBlock (o₂.next + 2 * L.length) L.length).map (·.subst φ₃) = τs := by
        have := varBlock_subst_block_mid o₂.next (ss ++ ps) τs rs φ₂
        simp only [List.length_append, hss, hps, hτs] at this
        rw [show L.length + L.length = 2 * L.length by omega] at this
        exact this
      have hbrs : (varBlock (o₂.next + 3 * L.length) L.length).map (·.subst φ₃) = rs := by
        have := varBlock_subst_block_mid o₂.next (ss ++ ps ++ τs) rs [] φ₂
        simp only [List.length_append, hss, hps, hτs, hrs, List.append_nil] at this
        rw [show L.length + L.length + L.length = 3 * L.length by omega] at this
        exact this
      -- `e₁`'s type is a record over the slots written over.
      have hu₃ : (o₁.τ.subst o₂.σ).subst φ₃ =
          (Ty.record L (varBlock o₂.next L.length)).subst φ₃ := by
        rw [hfresh _ (hσ₂.subst_below (hτb₁.mono hn₂)), hag₂.ty hτb₁, hτ₁]
        simp only [Ty.subst_app, hbss]
      obtain ⟨σ₃, hσ₃, habs₃⟩ := unify_mgu hu₃
      -- `e₂`'s, over the operand's presences and types.
      have hu₄ : (o₂.τ.subst σ₃).subst φ₃ = ((Ty.record L (List.zipWith Ty.slot
          (varBlock (o₂.next + L.length) L.length)
          (varBlock (o₂.next + 2 * L.length) L.length))).subst σ₃).subst φ₃ := by
        rw [habs₃, habs₃, hfresh _ hτb₂, hτ₂]
        simp only [Ty.subst_app, zipWith_slot_subst, hbps, hbτs]
      obtain ⟨σ₄, hσ₄, habs₄⟩ := unify_mgu hu₄
      have habs : Absorbs φ₃ (Subst.compose σ₄ σ₃) := fun τ => by
        rw [Ty.subst_compose, habs₄, habs₃]
      refine ⟨_, by simp only [infer, h₁, h₂, hσ₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
      · refine Agree.absorb (fun a ha => ?_) habs
        rw [hfresh _ ((((hσ₁.mono hn₂).compose hσ₂) a).1 (by omega))]
        exact (hag₁.trans hσ₁ hn₁ hag₂) a ha
      · show ((Ty.record L _).subst (Subst.compose σ₄ σ₃)).subst φ₃ = _
        rw [habs]
        simp only [Ty.subst_app, hbrs]
      · refine Sat.absorb habs (Sat.app (Sat.app ?_ ?_) ?_)
        · intro p hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          rw [hpfresh _ (hσ₂.pred_below ((hp₁ q hq).mono hn₂))]
          exact Sat.agree hag₂ hp₁ hsat₁ _ (List.mem_map_of_mem hq)
        · intro p hp
          rw [hpfresh _ (hp₂ p hp)]
          exact hsat₂ p hp
        · intro p hp
          have hmem : p.subst φ₃ ∈ mergePreds ps τs ss rs := by
            rw [← hbps, ← hbτs, ← hbss, ← hbrs, ← mergePreds_subst]
            exact List.mem_map_of_mem hp
          exact hm _ hmem

/-- What improvement leaves of entailed constraints is settled: an instance,
or on a type variable. -/
theorem Pred.settled_of_keep {C : List Pred} (hC : ∀ c ∈ C, c.OnVarShaped) {p : Pred}
    {φ : Subst} (hk : p.improve true = .keep) (he : Entails C (p.subst φ)) :
    p.settled = true := by
  simp only [Pred.settled, Bool.or_eq_true]
  rcases Pred.improve_keep hk with ⟨args, rfl⟩ | ⟨l, a, σ, rfl⟩ | ⟨args, rfl, hv⟩
  · rcases he with hi | hm
    · generalize hq : Pred.subst φ ⟨.plus, args⟩ = q at hi
      obtain ⟨τ, rfl, hτ⟩ : ∃ τ, args = [τ] ∧ (τ.subst φ = .number ∨ τ.subst φ = .string) := by
        cases hi with
        | plusNumber =>
          simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
          match args, hq with
          | [τ], hq => exact ⟨τ, rfl, .inl (by simpa using hq)⟩
          | [], hq => simp at hq
          | _ :: _ :: _, hq => simp at hq
        | plusString =>
          simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
          match args, hq with
          | [τ], hq => exact ⟨τ, rfl, .inr (by simpa using hq)⟩
          | [], hq => simp at hq
          | _ :: _ :: _, hq => simp at hq
        | hasProp _ | mergePre | mergeAbs => simp [Pred.subst] at hq
      cases τ with
      | var b => exact .inr (by simp [Pred.onVar])
      | app c xs =>
        rcases hτ with hτ | hτ <;> simp only [Ty.subst_app, Ty.app.injEq] at hτ <;>
          obtain ⟨rfl, hxs⟩ := hτ <;> obtain rfl : xs = [] := List.eq_nil_of_map_eq_nil hxs <;>
          exact .inl rfl
    · rcases hC _ hm with ⟨x, hx⟩ | ⟨l', x, σ', hx⟩ | ⟨x, τ', s', r', hx⟩
      · simp only [Pred.subst, Pred.mk.injEq, true_and] at hx
        match args, hx with
        | [.var b], _ => exact .inr (by simp [Pred.onVar])
        | [.app _ _], hx => simp at hx
        | [], hx => simp at hx
        | _ :: _ :: _, hx => simp at hx
      · simp [Pred.subst] at hx
      · simp [Pred.subst] at hx
  · exact .inr (by simp [Pred.onVar])
  · obtain ⟨b, τ, s', r, rfl⟩ := hv rfl
    exact .inr (by simp [Pred.onVar])

/-- Completeness, for a program in a closed context (such as the builtins'):
if it has a type, under assumptions on type variables, and passes the scope
checks (`Expr.scoped`), inference accepts it, finding a type of which that
one is an instance. -/
theorem inferIn_complete {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}
    (hΓ : ctxFtv Γ = []) (hC : ∀ p ∈ C, p.OnVarShaped)
    (hm : e.scoped (Γ.map fun _ => false) = true) (ht : HasType L C Γ none e τ') :
    ∃ o, infer L Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ ∃ τ, inferIn L Γ e = some τ := by
  have hclosed : Ctx.subst [] Γ = Γ := by simp
  obtain ⟨o, h, φ, _, hτ, hsat⟩ := infer_complete L e (n := 0) (ψ := []) (R := none)
    (fun a ha => by simp [hΓ] at ha) (fun a ha => by simp [Ret.ftv] at ha)
    (fun p hp => (hC p hp).assumable false) hclosed.symm rfl ht
  obtain ⟨σi, preds, himp, _, hsat', hkeep, _⟩ :=
    improveAll_complete (fun p hp => (hC p hp).assumable true) o.preds.length (Nat.le_refl _)
      hsat
  refine ⟨o, h, ⟨φ, hτ⟩, o.τ.subst σi, ?_⟩
  have hall : preds.all Pred.settled = true := List.all_eq_true.mpr (fun p hp =>
    Pred.settled_of_keep hC (hkeep p hp) (hsat' p hp))
  simp [inferIn, hm, h, himp, hall]

/-- Completeness for closed programs: one that has a type, with records over
its labels, and passes the scope checks is accepted. -/
theorem inferProgram_complete {e : Expr} {τ' : Ty} (hm : e.scoped [] = true)
    (ht : HasType e.labels.eraseDups [] [] none e τ') : ∃ τ, inferProgram e = some τ := by
  obtain ⟨_, _, _, h⟩ := inferIn_complete (Γ := []) rfl (fun _ h => by cases h) hm ht
  exact h

end Inty
