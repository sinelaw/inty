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

theorem Scheme.mono_ftv (τ : Ty) : (Scheme.mono τ).ftv = τ.ftv := by
  simp [Scheme.mono, Scheme.ftv, Ty.toPTy_ftv]

theorem letScheme_below {n : Nat} {e₁ : Expr} {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty}
    {preds : List Pred} (hτ : τ₁.Below n) (hp : ∀ p ∈ preds, p.Below n) :
    (∀ a ∈ (letScheme e₁ Γ₁ R₁ τ₁ preds).1.ftv, a < n) ∧
      ∀ p ∈ (letScheme e₁ Γ₁ R₁ τ₁ preds).2, p.Below n := by
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
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ hΓ hR h₁
    have hls := letScheme_below (e₁ := e₁) (Γ₁ := Ctx.subst o₁.σ Γ) (R₁ := Ret.subst o₁.σ R)
      hτ₁ hp₁
    generalize letScheme e₁ (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ o₁.preds = ls at h hls
    obtain ⟨s, rest⟩ := ls
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

end Inty
