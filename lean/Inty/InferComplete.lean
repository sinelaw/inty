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
  | fn t ps r iht ihps ihr =>
    simp only [Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap] at h
    simp only [Ty.subst_fn, iht (fun a ha => h a (.inl (.inl ha))),
      ihr (fun a ha => h a (.inr ha)), Ty.fn.injEq, true_and, and_true]
    exact List.map_congr_left (fun p hp => ihps p hp (fun a ha => h a (.inl (.inr ⟨p, hp, ha⟩))))
  | var a => exact h a (by simp [Ty.ftv])
  | _ => rfl

/-- The variables of a substituted type come from the images of its
variables. -/
theorem Ty.ftv_subst {σ : Subst} {τ : Ty} {a : Nat} (h : a ∈ (τ.subst σ).ftv) :
    ∃ b ∈ τ.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.subst_fn, Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap,
      List.mem_map] at h
    rcases h with (h | ⟨_, ⟨p, hp, rfl⟩, h⟩) | h
    · obtain ⟨b, hb, h⟩ := iht h; exact ⟨b, by simp [Ty.ftv, hb], h⟩
    · obtain ⟨b, hb, h⟩ := ihps p hp h
      have hb' : b ∈ (Ty.fn t ps r).ftv := by
        simp only [Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap]
        exact .inl (.inr ⟨p, hp, hb⟩)
      exact ⟨b, hb', h⟩
    · obtain ⟨b, hb, h⟩ := ihr h; exact ⟨b, by simp [Ty.ftv, hb], h⟩
  | var b => exact ⟨b, by simp [Ty.ftv], h⟩
  | _ => simp [Ty.subst, Ty.ftv] at h

theorem Subst.Within.subst_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {τ : Ty}
    (h : τ.Below n) : (τ.subst σ).Below n := fun a ha => by
  obtain ⟨b, hb, ha⟩ := Ty.ftv_subst ha
  exact (hσ b).1 (h b hb) a ha

theorem Subst.Within.mono {n n' : Nat} {σ : Subst} (hσ : σ.Within n) (hn : n ≤ n') :
    σ.Within n' := fun a => by
  refine ⟨fun ha => ?_, fun ha => (hσ a).2 (Nat.le_trans hn ha)⟩
  by_cases han : a < n
  · exact ((hσ a).1 han).mono hn
  · rw [(hσ a).2 (Nat.le_of_not_lt han)]; intro b hb; simp [Ty.ftv] at hb; omega

theorem Subst.Within.nil (n : Nat) : Subst.Within n [] := fun a =>
  ⟨fun ha b hb => by simp [Ty.ftv] at hb; omega, fun _ => by simp⟩

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
    · simp only [Ty.subst, Subst.find, hax, ite_false]; intro b hb; simp [Ty.ftv] at hb; omega
  · have : a ≠ x := by omega
    simp [Ty.subst, Subst.find, this]

theorem Ty.Below.fn {n : Nat} {t r : Ty} {ps : List Ty} :
    (Ty.fn t ps r).Below n ↔ t.Below n ∧ (∀ p ∈ ps, p.Below n) ∧ r.Below n := by
  simp only [Ty.Below, Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap]
  exact ⟨fun h => ⟨fun a ha => h a (.inl (.inl ha)), fun p hp a ha => h a (.inl (.inr ⟨p, hp, ha⟩)),
      fun a ha => h a (.inr ha)⟩,
    fun ⟨ht, hps, hr⟩ a ha => by
      rcases ha with (ha | ⟨p, hp, ha⟩) | ha
      · exact ht a ha
      · exact hps p hp a ha
      · exact hr a ha⟩

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
  | case6 vs eqs t₁ ps₁ r₁ t₂ ps₂ r₂ hlen hne ho ih =>
    intro hb σ h
    unfold unifyEqs at h; simp only [hne, ho, hlen, ite_false, ite_true] at h
    have h₀ := hb _ List.mem_cons_self
    obtain ⟨ht₁, hps₁, hr₁⟩ := Ty.Below.fn.mp h₀.1
    obtain ⟨ht₂, hps₂, hr₂⟩ := Ty.Below.fn.mp h₀.2
    refine ih (fun e he => ?_) h
    simp only [List.mem_cons, List.mem_append] at he
    rcases he with (rfl | rfl | he) | he
    · exact ⟨ht₁, ht₂⟩
    · exact ⟨hr₁, hr₂⟩
    · exact ⟨hps₁ _ (List.of_mem_zip he).1, hps₂ _ (List.of_mem_zip he).2⟩
    · exact hb e (by simp [he])
  | case7 vs eqs t₁ ps₁ r₁ t₂ ps₂ r₂ hlen hne ho =>
    intro _ σ h; unfold unifyEqs at h; simp [hne, ho, hlen] at h
  | case8 vs a b eqs hab ho hfn =>
    intro _ σ h; unfold unifyEqs at h; simp only [hab, ho, ite_false] at h; cases h

theorem unify_within {n : Nat} {τ₁ τ₂ : Ty} {σ : Subst} (h₁ : τ₁.Below n) (h₂ : τ₂.Below n)
    (h : unify τ₁ τ₂ = some σ) : σ.Within n :=
  unifyEqs_within _ _ (fun e he => by simp only [List.mem_singleton] at he; subst he; exact ⟨h₁, h₂⟩) h

/-! ## Free variables through instantiation, substitution, generalisation -/

theorem Ty.toPTy_ftv (τ : Ty) : τ.toPTy.ftv = τ.ftv := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.toPTy, PTy.ftv, Ty.ftv, Ty.toPTys_eq, PTy.ftvs_eq, Ty.ftvs_eq, iht, ihr,
      List.flatMap_map]
    congr 2
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ihps
  | _ => rfl

theorem PTy.ftv_inst {τs : List Ty} {p : PTy} {a : Nat} (h : a ∈ (p.inst τs).ftv) :
    a ∈ p.ftv ∨ ∃ τ ∈ τs, a ∈ τ.ftv := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.inst, PTy.insts_eq, Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap,
      List.mem_map] at h
    simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap]
    rcases h with (h | ⟨_, ⟨q, hq, rfl⟩, h⟩) | h
    · rcases iht h with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr h
    · rcases ihps q hq h with h | h
      · exact .inl (.inl (.inr ⟨q, hq, h⟩))
      · exact .inr h
    · rcases ihr h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | free b => simp [PTy.inst, Ty.ftv] at h; simp [PTy.ftv, h]
  | bound i =>
    simp only [PTy.inst, List.getD_eq_getElem?_getD] at h
    cases hi : τs[i]? with
    | none => simp [hi, Ty.ftv] at h
    | some τ => simp only [hi, Option.getD_some] at h; exact .inr ⟨τ, List.mem_of_getElem? hi, h⟩
  | _ => simp [PTy.inst, Ty.ftv] at h

theorem PTy.ftv_subst {σ : Subst} {p : PTy} {a : Nat} (h : a ∈ (p.subst σ).ftv) :
    ∃ b ∈ p.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.subst, PTy.substs_eq, PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap,
      List.mem_map] at h
    rcases h with (h | ⟨_, ⟨q, hq, rfl⟩, h⟩) | h
    · obtain ⟨b, hb, h⟩ := iht h; exact ⟨b, by simp [PTy.ftv, hb], h⟩
    · obtain ⟨b, hb, h⟩ := ihps q hq h
      have hb' : b ∈ (PTy.fn t ps r).ftv := by
        simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap]
        exact .inl (.inr ⟨q, hq, hb⟩)
      exact ⟨b, hb', h⟩
    · obtain ⟨b, hb, h⟩ := ihr h; exact ⟨b, by simp [PTy.ftv, hb], h⟩
  | free b =>
    simp only [PTy.subst, Ty.toPTy_ftv] at h
    exact ⟨b, by simp [PTy.ftv], by simpa [Ty.subst] using h⟩
  | _ => simp [PTy.subst, PTy.ftv] at h

theorem Ty.gen_ftv {ᾱ : List Nat} {τ : Ty} {a : Nat} (h : a ∈ (τ.gen ᾱ).ftv) : a ∈ τ.ftv := by
  induction τ using Ty.ind with
  | fn t ps r iht ihps ihr =>
    simp only [Ty.gen, Ty.gens_eq, PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap,
      List.mem_map] at h
    simp only [Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap]
    rcases h with (h | ⟨_, ⟨q, hq, rfl⟩, h⟩) | h
    · exact .inl (.inl (iht h))
    · exact .inl (.inr ⟨q, hq, ihps q hq h⟩)
    · exact .inr (ihr h)
  | var b =>
    simp only [Ty.gen] at h
    split at h <;> simp_all [PTy.ftv, Ty.ftv]
  | _ => simp [Ty.gen, PTy.ftv] at h

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
  cases l <;> intro a ha <;> simp [Lit.ty, Ty.ftv] at ha

theorem Ty.Below.var {n a : Nat} (h : a < n) : (Ty.var a).Below n := by
  intro b hb; simp [Ty.ftv] at hb; omega

/-! ## Invariants of inference -/

/-- What inference returns, from inputs below `n`, is below its next
unused variable. -/
def InferInv (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out}, Ctx.Below n Γ → Ret.Below n R →
    infer Γ R e n = some o →
    n ≤ o.next ∧ o.σ.Within o.next ∧ o.τ.Below o.next ∧ ∀ p ∈ o.preds, p.Below o.next

theorem inferArgs_inv : ∀ (args : List Expr), (∀ a ∈ args, InferInv a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : OutArgs}, Ctx.Below n Γ → Ret.Below n R →
      inferArgs Γ R args n = some o →
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

theorem infer_inv : ∀ e, InferInv e := by
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
    have hls := letScheme_below (gen := Expr.generalises e₁ e₂) (Γ₁ := Ctx.subst o₁.σ Γ)
      (R₁ := Ret.subst o₁.σ R) hτ₁ hp₁
    generalize letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ
      o₁.preds = ls at h hls
    obtain ⟨s, rest⟩ := ls
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (Ctx.Below.cons hls.1 (hσ₁.ctx_below (hΓ.mono hn₁)))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
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

/-! ## Agreement of substitutions -/

theorem PTy.subst_congr' {σ σ' : Subst} {p : PTy}
    (h : ∀ a ∈ p.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : p.subst σ = p.subst σ' := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap] at h
    simp only [PTy.subst, PTy.substs_eq, iht (fun a ha => h a (.inl (.inl ha))),
      ihr (fun a ha => h a (.inr ha)), PTy.fn.injEq, true_and, and_true]
    exact List.map_congr_left (fun p hp => ihps p hp (fun a ha => h a (.inl (.inr ⟨p, hp, ha⟩))))
  | free a =>
    have := h a (by simp [PTy.ftv])
    simp only [Ty.subst] at this
    simp [PTy.subst, this]
  | _ => rfl

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
  | fn t ps r iht ihps ihr =>
    simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap] at hp
    simp only [PTy.inst, PTy.subst, PTy.insts_eq, PTy.substs_eq, Ty.subst_fn, List.map_map,
      iht (fun a ha => hp a (.inl (.inl ha))), ihr (fun a ha => hp a (.inr ha)),
      Ty.fn.injEq, true_and, and_true]
    exact List.map_congr_left (fun q hq => ihps q hq (fun a ha => hp a (.inl (.inr ⟨q, hq, ha⟩))))
  | free a =>
    have ha := hp a (by simp [PTy.ftv])
    simp [PTy.inst, PTy.subst, Ty.subst, Subst.find_append, Subst.block_find_none ha]
  | bound i =>
    simp only [varBlock, PTy.inst, PTy.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.find_append, Subst.block_find]
    · simp [hi]
  | _ => rfl

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
    (h : HasType C' Γ₀ R e τ) :
    ∀ {C : List Pred} {Δ Γ : Ctx} {s s' : Scheme}, Γ₀ = Δ ++ s :: Γ → (∀ c ∈ C, c ∈ C') →
      Generalizes C s' s → (s'.arity = 0 ∧ s'.preds = []) ∨ e.writes Δ.length = false →
      HasType C' (Δ ++ s' :: Γ) R e τ := by
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
  | fn t ps r iht ihps ihr =>
    simp only [Ty.gen, Ty.gens_eq, PTy.subst, PTy.substs_eq, PTy.inst, PTy.insts_eq, List.map_map,
      Ty.subst_fn, iht, ihr, Ty.fn.injEq, true_and, and_true]
    exact List.map_congr_left ihps
  | var v =>
    simp only [Ty.gen, Ty.subst, Subst.find_append, zip_find ᾱ τs' v h]
    cases findIdx ᾱ v with
    | some i => simp [PTy.subst, PTy.inst]
    | none => simp [PTy.subst]
  | _ => rfl

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
  | fn t ps r iht ihps ihr =>
    simp only [Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap] at hv
    simp only [Ty.subst_fn, Ty.ftv, Ty.ftvs_eq, List.mem_append, List.mem_flatMap, List.mem_map]
    rcases hv with (hv | ⟨p, hp, hv⟩) | hv
    · exact .inl (.inl (iht hv))
    · exact .inl (.inr ⟨_, ⟨p, hp, rfl⟩, ihps p hp hv⟩)
    · exact .inr (ihr hv)
  | var b => simp [Ty.ftv] at hv; subst hv; exact ha
  | _ => simp [Ty.ftv] at hv

theorem PTy.ftv_subst_mem {σ : Subst} {v a : Nat} {p : PTy} (hv : v ∈ p.ftv)
    (ha : a ∈ ((Ty.var v).subst σ).ftv) : a ∈ (p.subst σ).ftv := by
  induction p using PTy.ind with
  | fn t ps r iht ihps ihr =>
    simp only [PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap] at hv
    simp only [PTy.subst, PTy.substs_eq, PTy.ftv, PTy.ftvs_eq, List.mem_append, List.mem_flatMap,
      List.mem_map]
    rcases hv with (hv | ⟨q, hq, hv⟩) | hv
    · exact .inl (.inl (iht hv))
    · exact .inl (.inr ⟨_, ⟨q, hq, rfl⟩, ihps q hq hv⟩)
    · exact .inr (ihr hv)
  | free b =>
    simp [PTy.ftv] at hv; subst hv
    simpa [PTy.subst, Ty.toPTy_ftv, Ty.subst] using ha
  | _ => simp [PTy.ftv] at hv

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

/-- Under assumptions that are all `Plus` on variables, a constraint with a
variable that is entailed once substituted is `Plus` on a variable. -/
theorem Pred.plus_var_of_entails {C₁ : List Pred} {φ : Subst} {g : Pred}
    (hC₁ : ∀ p ∈ C₁, ∃ a, p = ⟨.plus, [.var a]⟩) (h : Entails C₁ (g.subst φ))
    (hv : g.ftv ≠ []) : ∃ b, g = ⟨.plus, [.var b]⟩ := by
  obtain ⟨c, args⟩ := g
  cases c
  have key : ∀ τ : Ty, (τ.subst φ = .number ∨ τ.subst φ = .string ∨ ∃ a, τ.subst φ = .var a) →
      τ.ftv ≠ [] → ∃ b, τ = .var b := by
    intro τ hτ hne
    cases τ with
    | var b => exact ⟨b, rfl⟩
    | fn t ps r => simp [Ty.subst_fn] at hτ
    | _ => simp [Ty.ftv] at hne
  generalize hq : Pred.subst φ ⟨.plus, args⟩ = q at h
  have hargs : ∃ τ, args = [τ] ∧
      (τ.subst φ = .number ∨ τ.subst φ = .string ∨ ∃ a, τ.subst φ = .var a) := by
    rcases h with h | h
    · cases h <;> simp only [Pred.subst, Pred.mk.injEq, true_and] at hq <;>
        match args, hq with
        | [τ], hq => simp at hq; exact ⟨τ, rfl, by simp [hq]⟩
        | [], hq => simp at hq
        | _ :: _ :: _, hq => simp at hq
    · obtain ⟨a, rfl⟩ := hC₁ q h
      simp only [Pred.subst, Pred.mk.injEq, true_and] at hq
      match args, hq with
      | [τ], hq => simp at hq; exact ⟨τ, rfl, .inr (.inr ⟨a, hq⟩)⟩
      | [], hq => simp at hq
      | _ :: _ :: _, hq => simp at hq
  obtain ⟨τ, rfl, hτ⟩ := hargs
  obtain ⟨b, rfl⟩ := key τ hτ (by simpa [Pred.ftv] using hv)
  exact ⟨b, rfl⟩

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

/-- What a value's scheme is: its type with the variables `ᾱ` generalised,
each of the others in the context or the return type, and with constraints
from those inferred that mention one of `ᾱ`. -/
theorem letScheme_value {gen : Bool} {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty} {preds : List Pred}
    (hv : gen = true) : ∃ ᾱ G, (letScheme gen Γ₁ R₁ τ₁ preds).1 = generalize ᾱ τ₁ G ∧
      (∀ a ∈ τ₁.ftv, a ∉ ᾱ → a ∈ ctxFtv Γ₁ ∨ a ∈ Ret.ftv R₁) ∧
      ∀ g ∈ G, g ∈ preds ∧ ∃ a ∈ g.ftv, a ∈ ᾱ := by
  refine ⟨(τ₁.ftv.filter (fun a => a ∉ ctxFtv Γ₁ ++ Ret.ftv R₁)).eraseDups,
    preds.filter (fun c => c.ftv.any
      (· ∈ (τ₁.ftv.filter (fun a => a ∉ ctxFtv Γ₁ ++ Ret.ftv R₁)).eraseDups)),
    by simp [letScheme, hv], fun a ha hna => ?_, fun g hg => ?_⟩
  · by_cases h : a ∈ ctxFtv Γ₁ ∨ a ∈ Ret.ftv R₁
    · exact h
    · exact absurd (List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨ha, by simpa [not_or] using h⟩))
        hna
  · obtain ⟨h₁, h₂⟩ := List.mem_filter.mp hg
    exact ⟨h₁, by simpa using h₂⟩

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
def InferComplete (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred} {τ' : Ty} {Γ' : Ctx}
    {R' : Option Ty},
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, ∃ a, p = ⟨.plus, [.var a]⟩) →
    Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → HasType C Γ' R' e τ' →
    ∃ o, infer Γ R e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ o.τ.subst φ = τ' ∧ Sat C o.preds φ

theorem inferArgs_complete : ∀ (args : List Expr) (τs' : List Ty), (∀ a ∈ args, InferComplete a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, ∃ a, p = ⟨.plus, [.var a]⟩) →
      Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → args.length = τs'.length →
      (∀ p ∈ args.zip τs', HasType C Γ' R' p.1 p.2) →
      ∃ o, inferArgs Γ R args n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
        o.τs.map (·.subst φ) = τs' ∧ Sat C o.preds φ
  | [], [], _, Γ, R, n, ψ, C, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferArgs], ψ, fun a _ => by simp, rfl, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, τ' :: τs', ih, Γ, R, n, ψ, C, Γ', R', hΓ, hR, hC, hΓ', hR', hlen, hargs => by
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ :=
      ih a (by simp) hΓ hR hC hΓ' hR' (hargs (a, τ') (by simp))
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv a hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete as τs'
      (fun a' ha' => ih a' (by simp [ha'])) (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR])
      (by simpa using hlen) (fun p hp => hargs p (by simp [hp]))
    refine ⟨_, by simp only [inferArgs, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
    · simp only [List.map_cons, hag₂.ty hτb₁, hτ₁, hτs₂]
    · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂

theorem infer_complete : ∀ e, InferComplete e := by
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
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv f hΓ hR h₁
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (ψ := φ₁)
        (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) hlen hargs
      obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv a)
        (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
      have hu : (o₁.τ.subst o₂.σ).subst ((o₂.next, τ') :: φ₂) =
          (Ty.fn .undefined o₂.τs (.var o₂.next)).subst ((o₂.next, τ') :: φ₂) := by
        rw [Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono hn₂)), hag₂.ty hτb₁, hτ₁]
        simp only [Ty.subst_fn, Ty.subst_undefined, Ty.fn.injEq, true_and]
        refine ⟨?_, by simp [Ty.subst, Subst.find]⟩
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
    | let_ s L hgen hval hsimp h₂ =>
      subst hΓ' hR'
      -- Open `s` at a block of variables fresh for everything in sight.
      obtain ⟨m, hmL, hmΓ, hmR, hms, hmC, hmψ⟩ : ∃ m, (∀ a ∈ L, a < m) ∧
          (∀ a ∈ ctxFtv (Ctx.subst ψ Γ), a < m) ∧ (∀ a ∈ Ret.ftv (Ret.subst ψ R), a < m) ∧
          (∀ a ∈ s.ftv, a < m) ∧ (∀ p ∈ C, ∀ a ∈ p.ftv, a < m) ∧
          (∀ a < n, ∀ b ∈ ((Ty.var a).subst ψ).ftv, b < m) := by
        have h := lt_maxPlusOne (l := L ++ ctxFtv (Ctx.subst ψ Γ) ++ Ret.ftv (Ret.subst ψ R) ++
          s.ftv ++ C.flatMap Pred.ftv ++ (List.range n).flatMap (fun a => ((Ty.var a).subst ψ).ftv))
        refine ⟨_, fun a ha => h a (by simp [ha]), fun a ha => h a (by simp [ha]),
          fun a ha => h a (by simp [ha]), fun a ha => h a (by simp [ha]), fun p hp a ha => h a ?_,
          fun a ha b hb => h b ?_⟩
        · simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨p, hp, ha⟩)
        · simp only [List.mem_append, List.mem_flatMap, List.mem_range]; exact .inr ⟨a, ha, hb⟩
      have hC₁ : ∀ p ∈ C ++ s.openPreds m, ∃ a, p = ⟨.plus, [.var a]⟩ := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hC p hp
        · simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          obtain ⟨i, hi, rfl⟩ := hsimp q hq
          exact ⟨m + i, by simp [PPred.inst, PTy.inst, varBlock, hi]⟩
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC₁ rfl rfl (hgen m hmL)
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      -- Sending the block to `τs` turns the assumptions into `C` and `s`'s
      -- constraints at `τs`.
      have hCb : ∀ τs : List Ty, C.map (·.subst (Subst.block m τs)) = C := fun τs => by
        conv => rhs; rw [← List.map_id C]
        exact List.map_congr_left (fun q hq => Pred.subst_block_below (hmC q hq))
      have hblock : ∀ τs : List Ty, τs.length = s.arity → ∀ p ∈ o₁.preds,
          Entails (C ++ s.instPreds τs) ((p.subst φ₁).subst (Subst.block m τs)) := by
        intro τs hlen p hp
        have := Entails.subst (Subst.block m τs) (hsat₁ p hp)
        rwa [List.map_append, hCb, Scheme.openPreds_block s hms hlen] at this
      -- An instance of `s` whose constraints hold: at `Number`.
      obtain ⟨τs₀, hlen₀, hinst₀⟩ : ∃ τs₀ : List Ty, τs₀.length = s.arity ∧
          ∀ c ∈ s.instPreds τs₀, Inst c := by
        refine ⟨List.replicate s.arity .number, by simp, fun c hc => ?_⟩
        simp only [Scheme.instPreds, List.mem_map] at hc
        obtain ⟨q, hq, rfl⟩ := hc
        obtain ⟨i, hi, rfl⟩ := hsimp q hq
        simpa [PPred.inst, PTy.inst, hi] using Inst.plusNumber
      -- `φ₁`, with the block sent to that instance: what the rest of the
      -- program sees.
      obtain ⟨φs, hφs⟩ : ∃ φs, φs = Subst.compose (Subst.block m τs₀) φ₁ := ⟨_, rfl⟩
      have hagS : Agree n o₁.σ φs ψ := fun a ha => by
        rw [hφs, Ty.subst_compose, hag₁ a ha]
        exact Ty.subst_block_below (hmψ a ha)
      have hsatS : Sat C o₁.preds φs := fun p hp => by
        rw [hφs, Pred.subst_compose]
        rcases hblock τs₀ hlen₀ p hp with h | h
        · exact .inl h
        · rcases List.mem_append.mp h with h | h
          · exact .inr h
          · exact .inl (hinst₀ _ h)
      have hls := letScheme_below (gen := Expr.generalises e₁ e₂) (Γ₁ := Ctx.subst o₁.σ Γ)
        (R₁ := Ret.subst o₁.σ R) hτb₁ hp₁
      have hrest := letScheme_rest (gen := Expr.generalises e₁ e₂) (Γ₁ := Ctx.subst o₁.σ Γ)
        (R₁ := Ret.subst o₁.σ R) (τ₁ := o₁.τ) (preds := o₁.preds)
      -- The scheme inference finds passes its check, and is more general
      -- than `s`.
      have key : (letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ
            o₁.preds).1.preds.all PPred.isPlusBound = true ∧
          Generalizes C ((letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R)
            o₁.τ o₁.preds).1.subst φs) s ∧
          (((letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ
            o₁.preds).1.subst φs).arity = 0 ∧
            ((letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ
              o₁.preds).1.subst φs).preds = [] ∨ e₂.writes 0 = false) := by
        by_cases hv : Expr.generalises e₁ e₂ = true
        · obtain ⟨ᾱ, G, hs₁, hfree, hG⟩ := letScheme_value (Γ₁ := Ctx.subst o₁.σ Γ)
            (R₁ := Ret.subst o₁.σ R) (τ₁ := o₁.τ) (preds := o₁.preds) hv
          rw [hs₁]
          have hw : e₂.writes 0 = false := by
            simp only [Expr.generalises, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
              Bool.not_true] at hv
            exact hv.2
          refine and_assoc.mp ⟨?_, .inr hw⟩
          -- Each generalised constraint is `Plus` on a generalised variable.
          have hGv : ∀ g ∈ G, ∃ b ∈ ᾱ, g = ⟨.plus, [.var b]⟩ := by
            intro g hg
            obtain ⟨hgp, a, ha, haᾱ⟩ := hG g hg
            obtain ⟨b, rfl⟩ := Pred.plus_var_of_entails hC₁ (hsat₁ g hgp) (List.ne_nil_of_mem ha)
            simp [Pred.ftv, Ty.ftv] at ha
            subst ha
            exact ⟨_, haᾱ, rfl⟩
          refine ⟨?_, fun τs hlen => ?_⟩
          · simp only [generalize, List.all_map, List.all_eq_true]
            intro g hg
            obtain ⟨b, hb, rfl⟩ := hGv g hg
            obtain ⟨i, hi⟩ := findIdx_some hb
            simp [Pred.gen, Ty.gen, hi, PPred.isPlusBound]
          · have hlen' : ᾱ.length =
                (ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst (Subst.block m τs))).length := by simp
            have hin : ∀ v ∈ ᾱ, (Ty.var v).subst (ᾱ.zip (ᾱ.map
                (fun a => ((Ty.var a).subst φ₁).subst (Subst.block m τs))) ++ φs) =
                ((Ty.var v).subst φ₁).subst (Subst.block m τs) := fun v hv =>
              Ty.subst_zip_map_mem hv
            refine ⟨ᾱ.map (fun a => ((Ty.var a).subst φ₁).subst (Subst.block m τs)),
              by simp [generalize, Scheme.subst], ?_, ?_⟩
            · rw [generalize_subst_inst φs hlen' o₁.τ G, ← Scheme.open_block s hms hlen, ← hτ₁,
                ← Ty.subst_compose]
              refine Ty.subst_congr' (fun v hv' => ?_)
              rw [Ty.subst_compose]
              by_cases hvα : v ∈ ᾱ
              · exact hin v hvα
              · -- A variable not generalised is in the context, which has
                -- nothing in the block.
                rw [Ty.subst_zip_map_not_mem hvα, hφs, Ty.subst_compose]
                have hb : ∀ b ∈ ((Ty.var v).subst φ₁).ftv, b < m := by
                  intro b hb
                  rcases hfree v hv' hvα with h | h
                  · exact hmΓ b (by rw [← hag₁.ctx hΓ]; exact Ctx.ftv_subst_mem h hb)
                  · exact hmR b (by rw [← hag₁.ret hR]; exact Ret.ftv_subst_mem h hb)
                rw [Ty.subst_block_below hb, Ty.subst_block_below hb]
            · intro c hc
              rw [generalize_subst_instPreds φs hlen' o₁.τ G] at hc
              obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hc
              have hgp := (hG g hg).1
              obtain ⟨b, hb, rfl⟩ := hGv g hg
              have := hblock τs hlen _ hgp
              simpa only [Pred.subst, List.map_cons, List.map_nil, hin b hb] using this
        · -- Not generalised: `s` quantifies nothing.
          have harity : s.arity = 0 ∧ s.preds = [] :=
            hval.resolve_right (fun ⟨hv', hw'⟩ => hv (by
              simp [Expr.generalises, Expr.isValue_complete hv', hw']))
          simp only [letScheme, hv, Bool.false_eq_true, ↓reduceIte]
          refine ⟨by simp [Scheme.mono], fun τs hlen =>
            ⟨[], by simp [Scheme.mono, Scheme.subst], ?_, by
              simp [Scheme.instPreds, Scheme.mono, Scheme.subst]⟩,
            .inl ⟨by simp [Scheme.mono, Scheme.subst], by simp [Scheme.mono, Scheme.subst]⟩⟩
          have hτs : τs = [] := List.eq_nil_of_length_eq_zero (hlen.trans harity.1)
          have hτs₀ : τs₀ = [] := List.eq_nil_of_length_eq_zero (hlen₀.trans harity.1)
          subst hτs hτs₀
          rw [Scheme.mono_subst, Scheme.mono_inst, hφs, Ty.subst_compose, hτ₁]
          exact Scheme.open_block s hms hlen₀
      rcases hlsq : letScheme (Expr.generalises e₁ e₂) (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ
        o₁.preds with ⟨s₁, rest⟩
      rw [hlsq] at hls hrest key
      obtain ⟨hall, hgz, hw⟩ := key
      have h₂' := h₂.generalize_ctx (Δ := []) (Γ := Ctx.subst ψ Γ) (s := s) (s' := s₁.subst φs)
        rfl (fun c h => h) hgz hw
      obtain ⟨o₂, h₂o, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (Γ := s₁ :: Ctx.subst o₁.σ Γ)
        (R := Ret.subst o₁.σ R) (ψ := φs) (Ctx.Below.cons hls.1 hΓ₁) hR₁ hC
        (by simp only [List.nil_append, Ctx.subst_cons, hagS.ctx hΓ]) (hagS.ret hR).symm h₂'
      refine ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, rest.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
        ?_, φ₂, hagS.trans hσ₁ hn₁ hag₂, hτ₂,
        Sat.app (Sat.agree hag₂ hls.2 (fun p hp => hsatS p (hrest p hp))) hsat₂⟩
      simp only [infer, h₁, hlsq, hall, ↓reduceIte, h₂o]
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
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv c hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := iht (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) htt
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv t hΓ₁ hR₁ h₂
      have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
      have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
      obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := ihe (ψ := φ₂) hΓ₂ hR₂ hC
        (by rw [hΓ', hag₂.ctx hΓ₁, hag₁.ctx hΓ]) (by rw [hR', hag₂.ret hR₁, hag₁.ret hR]) hte
      obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := infer_inv e hΓ₂ hR₂ h₃
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
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e hΓ hR h₁
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
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) ht₂
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv e₂ hΓ₁ hR₁ h₂
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
        obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e hΓ hR h₁
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
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e hΓ hR h₁
      exact ⟨⟨o₁.σ, .var o₁.next, o₁.preds, o₁.next + 1⟩, by simp only [infer, h₁],
        (o₁.next, τ') :: φ₁, hag₁.fresh hσ₁ hn₁, by simp [Ty.subst, Subst.find],
        Sat.fresh hp₁ hsat₁⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    cases ht with
    | seq ht₁ ht₂ =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' ht₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (by rw [hΓ', hag₁.ctx hΓ]) (by rw [hR', hag₁.ret hR]) ht₂
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
        by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂,
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

/-- A constraint some substitution makes an instance is satisfiable. -/
theorem Pred.satisfiable_of_inst {p : Pred} {φ : Subst} (h : Inst (p.subst φ)) :
    p.satisfiable = true := by
  obtain ⟨c, args⟩ := p
  cases c
  generalize hq : Pred.subst φ ⟨.plus, args⟩ = q at h
  cases h <;> simp only [Pred.subst, Pred.mk.injEq, true_and] at hq <;>
    match args, hq with
    | [τ], hq =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hq
      cases τ <;> simp_all [Pred.satisfiable, Pred.isInst, Ty.subst]
    | _ :: _ :: _, hq => simp at hq

/-- Completeness, for a program in a closed context (such as the builtins'):
if it has a type, and assigns only to its own `let`s and parameters,
inference accepts it, finding a type of which that one is an instance. -/
theorem inferIn_complete {Γ : Ctx} {e : Expr} {τ' : Ty} (hΓ : ctxFtv Γ = [])
    (hm : e.assignsMutable (Γ.map fun _ => false) = true) (ht : HasType [] Γ none e τ') :
    ∃ o, infer Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ ∃ τ, inferIn Γ e = some τ := by
  have hclosed : Ctx.subst [] Γ = Γ := by simp
  obtain ⟨o, h, φ, _, hτ, hsat⟩ := infer_complete e (n := 0) (ψ := []) (R := none)
    (fun a ha => by simp [hΓ] at ha) (fun a ha => by simp [Ret.ftv] at ha) (fun _ h => by cases h)
    hclosed.symm rfl ht
  refine ⟨o, h, ⟨φ, hτ⟩, o.τ.subst (defaultSubst o.preds), ?_⟩
  have hall : o.preds.all Pred.satisfiable = true := List.all_eq_true.mpr (fun p hp =>
    Pred.satisfiable_of_inst ((hsat p hp).elim id (fun h => by cases h)))
  simp [inferIn, hm, h, hall]

/-- Completeness for closed programs: one that has a type, and assigns only
to its own `let`s and parameters, is accepted. -/
theorem inferProgram_complete {e : Expr} {τ' : Ty} (hm : e.assignsMutable [] = true)
    (ht : HasType [] [] none e τ') : ∃ τ, inferProgram e = some τ := by
  obtain ⟨_, _, _, h⟩ := inferIn_complete (Γ := []) rfl hm ht
  exact h

end Inty
