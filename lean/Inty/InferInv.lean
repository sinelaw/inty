import Inty.InferSound
import Inty.Weaken

/-!
# Invariants of inference

Inference allocates type variables from a counter `n`: everything it is
given mentions only variables below `n` (`Below`), and its substitutions
leave the variables at or above the counter alone and map the ones below
it to types below it (`Within`). Naraschewski and Nipkow's Isabelle proof
of algorithm W is the model. Completeness rests on these
(`Inty.InferComplete`).
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

theorem RTy.subst_congr' {σ σ' : Subst} {r : RTy}
    (h : ∀ a ∈ r.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : r.subst σ = r.subst σ' := by
  induction r using RTy.ind with
  | free a =>
    have := h a (by simp [RTy.ftv])
    simp only [Ty.subst] at this
    simp [RTy.subst, this]
  | self j => rfl
  | app c args ih =>
    simp only [RTy.ftv_app, List.mem_flatMap] at h
    simp only [RTy.subst_app, RTy.app.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))
  | mu i sys ih =>
    simp only [RTy.ftv_mu, List.mem_flatMap] at h
    simp only [RTy.subst_mu, RTy.mu.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))

/-- Substitutions that agree on a type's variables, as types. -/
theorem Ty.subst_congr' {σ σ' : Subst} {τ : Ty}
    (h : ∀ a ∈ τ.ftv, (Ty.var a).subst σ = (Ty.var a).subst σ') : τ.subst σ = τ.subst σ' := by
  induction τ using Ty.ind with
  | var a => exact h a (by simp)
  | app c args ih =>
    simp only [Ty.ftv_app, List.mem_flatMap] at h
    simp only [Ty.subst_app, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun p hp => ih p hp (fun a ha => h a ⟨p, hp, ha⟩))
  | mu i sys =>
    simp only [Ty.ftv_mu, List.mem_flatMap] at h
    simp only [Ty.subst_mu, Ty.mu.injEq, true_and]
    exact List.map_congr_left (fun p hp => RTy.subst_congr' (fun a ha => h a ⟨p, hp, ha⟩))

theorem RTy.ftv_subst {σ : Subst} {r : RTy} {a : Nat} (h : a ∈ (r.subst σ).ftv) :
    ∃ b ∈ r.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction r using RTy.ind with
  | free b =>
    simp only [RTy.subst, Ty.toRTy_ftv] at h
    exact ⟨b, by simp [RTy.ftv], by simpa [Ty.subst] using h⟩
  | self j => simp [RTy.subst, RTy.ftv] at h
  | app c args ih =>
    simp only [RTy.subst_app, RTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih p hp h
    exact ⟨b, by simp only [RTy.ftv_app, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩
  | mu i sys ih =>
    simp only [RTy.subst_mu, RTy.ftv_mu, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih p hp h
    exact ⟨b, by simp only [RTy.ftv_mu, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩

/-- The variables of a substituted type come from the images of its
variables. -/
theorem Ty.ftv_subst {σ : Subst} {τ : Ty} {a : Nat} (h : a ∈ (τ.subst σ).ftv) :
    ∃ b ∈ τ.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  have h' : a ∈ (τ.toRTy.subst σ).ftv := by simpa using h
  obtain ⟨b, hb, h⟩ := RTy.ftv_subst h'
  exact ⟨b, by simpa using hb, h⟩

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

/-- A right-hand side's variables are below `n`. -/
def RTy.Below (n : Nat) (r : RTy) : Prop := ∀ a ∈ r.ftv, a < n

theorem Subst.Within.rsubst_below {n : Nat} {σ : Subst} (hσ : σ.Within n) {r : RTy}
    (h : r.Below n) : (r.subst σ).Below n := fun a ha => by
  obtain ⟨b, hb, ha⟩ := RTy.ftv_subst ha
  exact (hσ b).1 (h b hb) a ha

theorem Ty.Below.view {n : Nat} {τ t : Ty} (h : τ.Below n) (hv : τ.view = some t) : t.Below n :=
  fun a ha => h a (Ty.view_ftv hv a ha)

/-- The unifier of types below `n` stays within `n`. -/
theorem unify_within {n : Nat} {τ₁ τ₂ : Ty} {σ : Subst} (h₁ : τ₁.Below n) (h₂ : τ₂.Below n)
    (h : unify τ₁ τ₂ = some σ) : σ.Within n := fun a => by
  constructor
  · intro ha
    cases hf : σ.find a with
    | none => simp only [Ty.subst, hf, Option.getD_none]; intro b hb; simp at hb; omega
    | some t =>
      simp only [Ty.subst, hf, Option.getD_some]
      intro b hb
      rcases (unify_ftv h hf).2 b hb with hb | hb
      · exact h₁ b hb
      · exact h₂ b hb
  · intro ha
    cases hf : σ.find a with
    | none => simp [Ty.subst, hf]
    | some t =>
      exfalso
      rcases (unify_ftv h hf).1 with hb | hb
      · have := h₁ a hb; omega
      · have := h₂ a hb; omega

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

theorem Pred.below_of_args {n : Nat} {p : Pred} (h : ∀ τ ∈ p.args, τ.Below n) : p.Below n :=
  fun a ha => by
    simp only [Pred.ftv, List.mem_flatMap] at ha
    obtain ⟨τ, hτ, ha⟩ := ha
    exact h τ hτ a ha

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

theorem Pred.normHead_ftv {p : Pred} {a : Nat} (h : a ∈ p.normHead.ftv) : a ∈ p.ftv := by
  obtain ⟨c, args⟩ := p
  unfold Pred.normHead at h
  match args with
  | [] => exact h
  | t :: rest =>
    simp only at h
    split at h
    · simp only [Pred.ftv, List.flatMap_cons, List.mem_append] at h ⊢
      exact h.imp_left Ty.whnf_ftv
    · exact h

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
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      exact hp q₀ (List.mem_filter.mp hq₀).1 a
        (Pred.normHead_ftv (List.mem_flatMap.mpr ⟨r, hr, Ty.gen_ftv ha⟩))
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

theorem Ty.Below.con {n : Nat} {c : Con} : (Ty.app c []).Below n :=
  Ty.Below.app.mpr (fun _ h => by cases h)

theorem Ty.Below.slot_iff {n : Nat} {p k τ : Ty} :
    (Ty.slot p k τ).Below n ↔ p.Below n ∧ k.Below n ∧ τ.Below n := by
  rw [Ty.Below.app]
  simp

theorem Pred.decideCopy_below {n : Nat} {s r a b : Ty} (hs : s.Below n) (hr : r.Below n)
    (h : Pred.decideCopy s r = .eq a b) : a.Below n ∧ b.Below n := by
  unfold Pred.decideCopy at h
  split at h
  · rename_i p k τ hw
    have hsw : (Ty.slot p k τ).Below n := fun x hx => hs x (Ty.whnf_ftv (by rw [hw]; exact hx))
    split at h <;> (try cases h)
    · exact ⟨hr, hs⟩
    · exact ⟨hr, Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con,
        (Ty.Below.slot_iff.mp hsw).2.2⟩⟩
    · exact ⟨hr, Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, Ty.Below.con⟩⟩
    · exact ⟨hr, hs⟩
  · cases h
  · cases h

/-- A decision's equation mentions only the constraint's variables. -/
theorem Pred.decide₀_below {n : Nat} {c : Cls} {t : Ty} {rest : List Ty} {a b : Ty}
    (hp : Pred.Below n ⟨c, t :: rest⟩) (h : Pred.decide₀ c t rest = .eq a b) :
    a.Below n ∧ b.Below n := by
  have ht : t.Below n := fun x hx => hp x (by simp [Pred.ftv, hx])
  have hr : ∀ τ ∈ rest, τ.Below n := fun τ hτ x hx =>
    hp x (by simp only [Pred.ftv, List.flatMap_cons, List.mem_append, List.mem_flatMap]; exact .inr ⟨τ, hτ, hx⟩)
  have hnum : Ty.number.Below n := Ty.Below.con
  unfold Pred.decide₀ at h
  split at h
  all_goals first | (cases h; done) | skip
  · split at h
    · rename_i hs
      cases h
      refine ⟨fun x hx => ht x ?_, Ty.Below.slot_iff.mpr ⟨Ty.Below.con, hr _ (by simp),
        hr _ (by simp)⟩⟩
      simp only [Ty.ftv_app, List.mem_flatMap]
      exact ⟨_, (List.of_mem_zip (Ty.field_mem hs)).2, hx⟩
    · cases h
  · split at h
    · cases h
      exact ⟨Ty.Below.app.mpr (fun τ hτ => hr τ (by simpa using hτ)),
        Ty.Below.app.mpr (fun τ hτ => by simp at hτ; rcases hτ with rfl | rfl <;> exact Ty.Below.con)⟩
    · cases h
  · split at h
    · cases h
      exact ⟨Ty.Below.app.mpr (fun τ hτ => hr τ (by simpa using hτ)),
        Ty.Below.app.mpr (fun τ hτ => by simp at hτ; rcases hτ with rfl | rfl <;> exact Ty.Below.con)⟩
    · cases h
  · cases h
    refine ⟨Ty.Below.app.mpr (fun τ hτ => hr τ (by simpa using hτ)), Ty.Below.app.mpr (fun τ hτ => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact hnum
    · exact fun x hx => ht x (by simp [hx])
  · cases h
    refine ⟨Ty.Below.app.mpr (fun τ hτ => hr τ (by simpa using hτ)), Ty.Below.app.mpr (fun τ hτ => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl <;> exact Ty.Below.con
  · cases h; exact ⟨hnum, hnum⟩
  · split at h
    · cases h
    · cases h; exact ⟨hnum, hnum⟩
  · rename_i k τ s r
    unfold Pred.decidePre at h
    split at h
    · cases h
      exact ⟨hr _ (by simp), Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, hr _ (by simp)⟩⟩
    · cases h
      exact ⟨hr _ (by simp), Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, hr _ (by simp)⟩⟩
    · exact Pred.decideCopy_below (hr s (by simp)) (hr r (by simp)) h
    · cases h
    · cases h
  · rename_i k τ s r
    exact Pred.decideCopy_below (hr s (by simp)) (hr r (by simp)) h
  · rename_i T
    unfold Pred.decideInject at h
    split at h
    rotate_left
    · cases h
    rename_i hT
    have hTb : T.Below n := fun x hx => by rw [hT] at hx; cases hx
    split at h
    · rename_i z σ hw
      have hσ : σ.Below n := fun x hx => hTb x (Ty.whnf_ftv (by rw [hw]; simp [hx]))
      split at h
      · split at h
        · cases h; exact ⟨ht, hTb⟩
        · split at h
          · cases h; exact ⟨hnum, hnum⟩
          · cases h; exact ⟨ht, hσ⟩
      · cases h; exact ⟨ht, hTb⟩
    · cases h; exact ⟨ht, hTb⟩
  · rename_i σ
    have hσ : σ.Below n := hr σ (by simp)
    unfold Pred.decideStrip at h
    split at h
    · rename_i z σ'
      cases h
      exact ⟨hσ, fun x hx => ht x (by simp [Ty.ftv, hx])⟩
    · split at h
      · cases h
      · cases h
      · cases h
      · cases h; exact ⟨hσ, ht⟩
    · cases h

theorem Pred.decide_below {n : Nat} {c : Cls} {t : Ty} {rest : List Ty} {a b : Ty}
    (hp : Pred.Below n ⟨c, t :: rest⟩) (h : Pred.decide c t rest = .eq a b) :
    a.Below n ∧ b.Below n := by
  refine Pred.decide₀_below (t := t.whnf) (fun x hx => ?_) h
  simp only [Pred.ftv, List.flatMap_cons, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hp x (by simp [Pred.ftv, Ty.whnf_ftv hx])
  · exact hp x (by simp only [Pred.ftv, List.flatMap_cons, List.mem_append]; exact .inr hx)

theorem Pred.improveArgs_below {n : Nat} {c : Cls} {args : List Ty} {a b : Ty}
    (hp : Pred.Below n ⟨c, args⟩) (h : Pred.improveArgs c args = .eq a b) :
    a.Below n ∧ b.Below n := by
  unfold Pred.improveArgs at h
  split at h
  · split at h
    · split at h <;> cases h
    · exact Pred.decide_below hp h
  · cases h

theorem Pred.improve_below {n : Nat} {top : Bool} {p : Pred} {a b : Ty} (hp : p.Below n)
    (h : p.improve top = .eq a b) : a.Below n ∧ b.Below n := by
  obtain ⟨cls, args⟩ := p
  cases cls <;> simp only [Pred.improve] at h
  case plus => cases h
  case merge =>
    split at h
    · exact Pred.improveArgs_below hp h
    · cases h
  all_goals exact Pred.improveArgs_below hp h

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

theorem objSlots_below {n : Nat} {L ls : List String} {ss : List Ty}
    (hss : ∀ s ∈ ss, s.Below n) : ∀ s ∈ objSlots L ls ss, s.Below n := by
  intro s hs
  simp only [objSlots, List.mem_map] at hs
  obtain ⟨l, -, rfl⟩ := hs
  generalize hf : Ty.field l ls.reverse ss.reverse = o
  cases o with
  | some τ => exact hss τ (List.mem_reverse.mp (List.of_mem_zip (Ty.field_mem hf)).2)
  | none => exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, Ty.Below.con⟩

theorem slots3_below {n : Nat} : ∀ {ps ks τs : List Ty}, (∀ τ ∈ ps, τ.Below n) →
    (∀ τ ∈ ks, τ.Below n) → (∀ τ ∈ τs, τ.Below n) → ∀ s ∈ slots3 ps ks τs, s.Below n
  | p :: ps, k :: ks, τ :: τs, hps, hks, hτs, s, hs => by
    simp only [slots3, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Ty.Below.slot_iff.mpr ⟨hps _ (by simp), hks _ (by simp), hτs _ (by simp)⟩
    · exact slots3_below (fun x hx => hps x (by simp [hx])) (fun x hx => hks x (by simp [hx]))
        (fun x hx => hτs x (by simp [hx])) s hs
  | [], _, _, _, _, _, _, hs | _ :: _, [], _, _, _, _, _, hs
  | _ :: _, _ :: _, [], _, _, _, _, hs => by simp [slots3] at hs

theorem mergePreds_below {n : Nat} : ∀ {ps ks τs ss rs : List Ty}, (∀ τ ∈ ps, τ.Below n) →
    (∀ τ ∈ ks, τ.Below n) → (∀ τ ∈ τs, τ.Below n) → (∀ τ ∈ ss, τ.Below n) →
    (∀ τ ∈ rs, τ.Below n) → ∀ p ∈ mergePreds ps ks τs ss rs, p.Below n
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs, hps, hks, hτs, hss, hrs, q, hq => by
    simp only [mergePreds, List.mem_cons] at hq
    rcases hq with rfl | hq
    · intro a ha
      simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at ha
      rcases ha with ha | ha | ha | ha | ha
      · exact hps _ (by simp) a ha
      · exact hks _ (by simp) a ha
      · exact hτs _ (by simp) a ha
      · exact hss _ (by simp) a ha
      · exact hrs _ (by simp) a ha
    · exact mergePreds_below (fun x hx => hps x (by simp [hx])) (fun x hx => hks x (by simp [hx]))
        (fun x hx => hτs x (by simp [hx])) (fun x hx => hss x (by simp [hx]))
        (fun x hx => hrs x (by simp [hx])) q hq
  | [], _, _, _, _, _, _, _, _, _, _, hq | _ :: _, [], _, _, _, _, _, _, _, _, _, hq
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, hq
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, hq
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, hq => by simp [mergePreds] at hq

/-! ## Invariants of inference -/

/-- What inference returns, from inputs below `n`, is below its next
unused variable. -/
def InferInv (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {o : Out}, RetOk rm R →
    Ex.Closed ex → Ctx.Below n Γ → Ret.Below n R → infer L Γ R rm ex e n = some o →
    n ≤ o.next ∧ o.σ.Within o.next ∧ o.τ.Below o.next ∧ ∀ p ∈ o.preds, p.Below o.next

theorem Ty.Below.closed {n : Nat} {T : Ty} (h : T.ftv = []) : T.Below n := fun a ha => by
  rw [h] at ha; cases ha

theorem Ex.Closed.getD_below {ex : Option Ty} {m k : Nat} (hex : Ex.Closed ex) (h : m < k) :
    (ex.getD (.var m)).Below k := by
  cases ex with
  | none => exact Ty.Below.var h
  | some T => exact Ty.Below.closed (hex T rfl)

/-- Inferring `e` against `ex`, as its caller sees it (`checkEx`). -/
theorem InferInv.check {e : Expr} (ih : InferInv L e) {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {ex : Option Ty} {n : Nat} {o : Out} (hRo : RetOk rm R) (hex : Ex.Closed ex)
    (hΓ : Ctx.Below n Γ) (hR : Ret.Below n R)
    (h : (infer L Γ R rm ex e n).map (checkEx ex e) = some o) :
    n ≤ o.next ∧ o.σ.Within o.next ∧ o.τ.Below o.next ∧ ∀ p ∈ o.preds, p.Below o.next := by
  obtain ⟨o', h', rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hn, hσ, hτ, hp⟩ := ih hRo hex hΓ hR h'
  match ex, hex with
  | none, _ => exact ⟨hn, hσ, hτ, hp⟩
  | some T, hex =>
    have hT : T.Below o'.next := Ty.Below.closed (hex T rfl)
    simp only [checkEx]
    split
    · exact ⟨hn, hσ, hτ, hp⟩
    · refine ⟨hn, hσ, hT, fun p hp' => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hp'
      rcases hp' with hp' | rfl
      · exact hp p hp'
      · exact Pred.below_of_args (by simp [hτ])

theorem inferArgs_inv : ∀ (args : List Expr), (∀ a ∈ args, InferInv L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {o : OutArgs}, RetOk rm R →
      Ex.Closed ex → Ctx.Below n Γ → Ret.Below n R → inferArgs L Γ R rm ex args n = some o →
      n ≤ o.next ∧ o.σ.Within o.next ∧ (∀ τ ∈ o.τs, τ.Below o.next) ∧
        ∀ p ∈ o.preds, p.Below o.next
  | [], _, Γ, R, rm, ex, n, o, _, _, _, _, h => by
    simp only [inferArgs, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_refl _, .nil _, by simp, by simp⟩
  | a :: as, ih, Γ, R, rm, ex, n, o, hRo, hex, hΓ, hR, h => by
    simp only [inferArgs] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := InferInv.check (ih a (by simp)) hRo hex hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv as (fun a' ha' => ih a' (by simp [ha'])) (by ret_ok) hex
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

theorem fieldSlots_below {m : Nat} {ks : List FieldKind} {es : List Expr} {τs θs ss : List Ty}
    (h : fieldSlots ks es τs = some (θs, ss)) (hτs : ∀ τ ∈ τs, τ.Below m) :
    (∀ θ ∈ θs, θ.Below m) ∧ ∀ s ∈ ss, s.Below m := by
  induction ks, es, τs using fieldSlots.induct generalizing θs ss with
  | case1 =>
    simp only [fieldSlots, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | case2 ks e es τ τs ih =>
    simp only [fieldSlots] at h
    cases hr : fieldSlots ks es τs with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss'⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      refine ⟨h₁, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, hτs τ List.mem_cons_self⟩
      · exact h₂ s hs
  | case3 ks m' b es θ ρ τs' τs ih =>
    simp only [fieldSlots] at h
    cases hr : fieldSlots ks es τs with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss'⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      have hf := hτs _ List.mem_cons_self
      refine ⟨fun θ' hθ' => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hθ' with rfl | hθ'
        · exact Ty.Below.app.mp hf _ List.mem_cons_self
        · exact h₁ θ' hθ'
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, hf⟩
        · exact h₂ s hs
  | case4 ks b es θ σ τs ih =>
    simp only [fieldSlots] at h
    cases hr : fieldSlots ks es τs with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss'⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      have hf := hτs _ List.mem_cons_self
      refine ⟨fun θ' hθ' => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hθ' with rfl | hθ'
        · exact Ty.Below.app.mp hf _ List.mem_cons_self
        · exact h₁ θ' hθ'
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con,
            Ty.Below.app.mp hf _ (by simp)⟩
        · exact h₂ s hs
  | case5 x y z h1 h2 h3 h4 =>
    exfalso
    rw [fieldSlots.eq_def] at h
    split at h
    · exact h1 rfl rfl rfl
    · exact h2 _ _ _ _ _ rfl rfl rfl
    · exact h3 _ _ _ _ _ _ _ _ rfl rfl rfl
    · exact h4 _ _ _ _ _ _ rfl rfl rfl
    · cases h

theorem memberSlots_below {ks : List ClassKind} {es : List Expr} {τs : List Ty} {n : Nat}
    {θs ss : List Ty} {n' : Nat} (h : memberSlots ks es τs n = some (θs, ss, n'))
    (hτs : ∀ τ ∈ τs, τ.Below n) :
    n ≤ n' ∧ (∀ θ ∈ θs, θ.Below n') ∧ ∀ s ∈ ss, s.Below n' := by
  induction ks, es, τs, n using memberSlots.induct generalizing θs ss n' with
  | case1 n =>
    simp only [memberSlots, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | case2 ks e es τ τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs n with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₀, h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      refine ⟨h₀, h₁, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con,
          (hτs τ List.mem_cons_self).mono h₀⟩
      · exact h₂ s hs
  | case3 ks m b es θ ρ τs' τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs (n + 1) with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₀, h₁, h₂⟩ := ih hr (fun t ht => (hτs t (List.mem_cons_of_mem _ ht)).mono (by omega))
      have hf := (hτs _ List.mem_cons_self).mono (show n ≤ n'' by omega)
      refine ⟨by omega, fun θ' hθ' => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hθ' with rfl | hθ'
        · exact Ty.Below.app.mp hf _ List.mem_cons_self
        · exact h₁ θ' hθ'
      · rcases List.mem_cons.mp hs with rfl | hs
        · refine Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, Ty.Below.app.mpr ?_⟩
          intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | rfl | ht
          · exact Ty.Below.var (by omega)
          · exact Ty.Below.app.mp hf _ (by simp)
          · exact Ty.Below.app.mp hf _ (by simp [ht])
        · exact h₂ s hs
  | case4 ks m b es θ ρ τs' τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs n with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₀, h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      have hf := (hτs _ List.mem_cons_self).mono h₀
      refine ⟨h₀, fun θ' hθ' => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hθ' with rfl | hθ'
        · exact Ty.Below.app.mp hf _ List.mem_cons_self
        · exact h₁ θ' hθ'
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con, hf⟩
        · exact h₂ s hs
  | case5 ks b es θ σ τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs n with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₀, h₁, h₂⟩ := ih hr (fun t ht => hτs t (List.mem_cons_of_mem _ ht))
      have hf := (hτs _ List.mem_cons_self).mono h₀
      refine ⟨h₀, fun θ' hθ' => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hθ' with rfl | hθ'
        · exact Ty.Below.app.mp hf _ List.mem_cons_self
        · exact h₁ θ' hθ'
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Ty.Below.slot_iff.mpr ⟨Ty.Below.con, Ty.Below.con,
            Ty.Below.app.mp hf _ (by simp)⟩
        · exact h₂ s hs
  | case6 t x y m h1 h2 h3 h4 h5 =>
    exfalso
    rw [memberSlots.eq_def] at h
    split at h
    · exact h1 rfl rfl rfl
    · exact h2 _ _ _ _ _ rfl rfl rfl
    · exact h3 _ _ _ _ _ _ _ _ rfl rfl rfl
    · exact h4 _ _ _ _ _ _ _ _ rfl rfl rfl
    · exact h5 _ _ _ _ _ _ rfl rfl rfl
    · cases h

theorem unifyThis_within {m : Nat} {θs : List Ty} {T : Ty} {σ : Subst}
    (h : unifyThis θs T = some σ) (hθs : ∀ θ ∈ θs, θ.Below m) (hT : T.Below m) : σ.Within m := by
  unfold unifyThis at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact .nil m
  · rename_i θ θs'
    split at h
    · cases h
    rename_i σ₁ hu₁
    split at h
    · cases h
    rename_i σ₂ hu₂
    simp only [Option.some.injEq] at h; subst h
    have hw₁ := unify_within (Ty.Below.app.mpr hθs) (Ty.Below.app.mpr (fun τ hτ => by
      rw [List.eq_of_mem_replicate hτ]; exact hθs θ List.mem_cons_self)) hu₁
    have hw₂ := unify_within (hw₁.subst_below (hθs θ List.mem_cons_self)) (hw₁.subst_below hT) hu₂
    exact hw₁.compose hw₂

theorem inferMembers_inv : ∀ (es : List Expr) (ks : List ClassKind), (∀ a ∈ es, InferInv L a) →
    ∀ {Γ : Ctx} {Δ : List Ty} {R : Option Ty} {n : Nat} {o : OutArgs}, Ctx.Below n Γ →
      (∀ τ ∈ Δ, τ.Below n) → Ret.Below n R → inferMembers L Γ Δ R es ks n = some o →
      n ≤ o.next ∧ o.σ.Within o.next ∧ (∀ τ ∈ o.τs, τ.Below o.next) ∧
        ∀ p ∈ o.preds, p.Below o.next
  | [], [], _, Γ, Δ, R, n, o, _, _, _, h => by
    simp only [inferMembers, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_refl _, .nil _, by simp, by simp⟩
  | [], _ :: _, _, Γ, Δ, R, n, o, _, _, _, h | _ :: _, [], _, Γ, Δ, R, n, o, _, _, _, h => by
    simp [inferMembers] at h
  | a :: as, k :: ks, ih, Γ, Δ, R, n, o, hΓ, hΔ, hR, h => by
    have ih' : ∀ a ∈ as, InferInv L a := fun a' ha' => ih a' (List.mem_cons_of_mem _ ha')
    cases k
    case data =>
      simp only [inferMembers] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih a List.mem_cons_self RetOk.synth .none (Ctx.Below.append_mono hΔ hΓ) hR h₁
      obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferMembers_inv as ks ih'
        (hσ₁.ctx_below (hΓ.mono hn₁))
        (fun τ hτ => by
          rcases List.mem_cons.mp hτ with rfl | hτ
          · exact hτ₁
          · obtain ⟨τ₀, hτ₀, rfl⟩ := List.mem_map.mp hτ
            exact hσ₁.subst_below ((hΔ τ₀ hτ₀).mono hn₁))
        (hσ₁.ret_below (hR.mono hn₁)) h₂
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
    all_goals
      simp only [inferMembers] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih a List.mem_cons_self RetOk.synth .none hΓ hR h₁
      obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferMembers_inv as ks ih'
        (hσ₁.ctx_below (hΓ.mono hn₁))
        (fun τ hτ => by
          obtain ⟨τ₀, hτ₀, rfl⟩ := List.mem_map.mp hτ
          exact hσ₁.subst_below ((hΔ τ₀ hτ₀).mono hn₁))
        (hσ₁.ret_below (hR.mono hn₁)) h₂
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
    intro Γ R rm ex n o hRo hex _ _ h
    simp only [infer, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_refl _, .nil _, Lit.ty_below l _, by simp⟩
  | var i =>
    intro Γ R rm ex n o hRo hex hΓ _ h
    simp only [infer] at h
    split at h
    · rename_i s hs
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_add_right _ _, .nil _, Scheme.open_below (hΓ.lookup hs),
        Scheme.openPreds_below (hΓ.lookup hs)⟩
    · cases h
  | func k body ih =>
    intro Γ R rm ex n o hRo hex hΓ _ h
    simp only [infer] at h
    split at h
    · rename_i T θ τs ρ hft
      obtain rfl := funcTarget_some hft
      obtain ⟨-, hw, -⟩ := funcTarget_fst hft rfl
      have hT := hex T rfl
      have hfn := Ty.ftv_nil_of_whnf hw hT
      have hf := hfn
      simp only [Ty.ftv, Ty.ftvs_eq, List.flatMap_cons, List.append_eq_nil_iff,
        List.flatMap_eq_nil_iff] at hf
      obtain ⟨hθ, hρ, hτs⟩ := hf
      split at h
      · cases h
      rename_i o₁ h₁
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check ih (RetOk.check hρ) (Ex.Closed.some hρ)
        (Ctx.Below.append_mono (fun τ hτ => Ty.Below.closed (hτs τ hτ))
          (Ctx.Below.mono_cons (Ty.Below.closed hfn) (Ctx.Below.mono_cons (Ty.Below.closed hθ) hΓ)))
        (fun a ha => by simp [Ret.ftv, hρ] at ha) h₁
      exact ⟨hn₁, hσ₁, Ty.Below.closed hT, hp₁⟩
    · split at h
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
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih RetOk.synth .none
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
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihf (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv args iha (by ret_ok) .none
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
  | let_ _ ann e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    cases ann with
    | some a =>
      simp only [infer] at h
      split at h
      rotate_left
      · cases h
      rename_i ha
      have hT := Scheme.inst_nil_closed ha.2.2
      split at h
      · cases h
      rename_i o₁ h₁
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := InferInv.check ih₁ hRo (Ex.Closed.some hT) hΓ hR h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check ih₂ (by ret_ok) hex
        (Ctx.Below.cons (fun b hb => by simp [ha.2.2] at hb) (hσ₁.ctx_below (hΓ.mono hn₁)))
        (hσ₁.ret_below (hR.mono hn₁)) h₂
      refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
      intro p hp
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp
    | none =>
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ (by ret_ok) .none hΓ hR h₁
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
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check ih₂ (by ret_ok) hex (Ctx.Below.cons hls.1 (hσ₁'.ctx_below (hΓ.mono hn₁)))
      (hσ₁'.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁'.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hls.2 q hq).mono hn₂)
    · exact hp₂ p hp
  | assign i e ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih (by ret_ok) .none hΓ hR h₁
    have hsb : (s.inst []).Below n := Scheme.inst_nil_below (hΓ.lookup hs)
    have hσ' := unify_within (hσ₁.subst_below (hsb.mono hn₁)) hτ₁ hu
    refine ⟨hn₁, hσ₁.compose hσ', ?_, ?_⟩
    · rw [Ty.subst_compose]; exact hσ'.subst_below (hσ₁.subst_below (hsb.mono hn₁))
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below (hp₁ q hq)
  | cond c t e ihc iht ihe =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihc (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check iht (by ret_ok) hex (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    obtain ⟨hn₃, hσ₃, hτ₃, hp₃⟩ := InferInv.check ihe (by ret_ok) hex (hσ₂.ctx_below (hσ₁.ctx_below (hΓ.mono hn₁) |>.mono hn₂))
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
  | unwrap e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check ih₂ (by ret_ok) hex hΓ₁ hR₁ h₂
    have hβ : (Ty.var o₂.next).Below (o₂.next + 1) := .var (by omega)
    obtain ⟨hn₃, hσ₃, hτ₃, hp₃⟩ := InferInv.check ih₃ (by ret_ok) hex
      (Ctx.Below.mono_cons hβ ((hσ₂.ctx_below (hΓ₁.mono hn₂)).mono (by omega)))
      ((hσ₂.ret_below (hR₁.mono hn₂)).mono (by omega)) h₃
    have hσ₄ := unify_within (hσ₃.subst_below (hτ₂.mono (by omega))) hτ₃ hu
    refine ⟨by dsimp only; omega,
      ((((hσ₁.mono hn₂).compose hσ₂).mono (by omega)).compose hσ₃).compose hσ₄,
      hσ₄.subst_below hτ₃, ?_⟩
    intro p hp
    simp only [List.mem_map, List.mem_append] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine hσ₄.pred_below ?_
    rcases hq with ⟨q', hq', rfl⟩ | hq
    · refine hσ₃.pred_below ?_
      rcases hq' with (⟨q'', hq'', rfl⟩ | hq') | hq'
      · exact (hσ₂.pred_below ((hp₁ q'' hq'').mono hn₂)).mono (by omega)
      · exact (hp₂ q' hq').mono (by omega)
      · simp only [List.mem_singleton] at hq'; subst hq'
        refine Pred.below_of_args (fun τ hτ => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
        rcases hτ with rfl | rfl
        · exact (hσ₂.subst_below (hτ₁.mono hn₂)).mono (by omega)
        · exact hβ.mono (by omega)
    · exact hp₃ q hq
  | unop op e ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih (by ret_ok) .none hΓ hR h₁
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
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
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
    intro Γ R rm ex n o hRo hex hΓ hR h
    match R, rm with
    | none, _ => simp [infer] at h
    | some τr, .synth =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih (by ret_ok) .none hΓ hR h₁
      have hτr : τr.Below n := fun a ha => hR a (by simpa [Ret.ftv] using ha)
      have hσ' := unify_within (hσ₁.subst_below (hτr.mono hn₁)) hτ₁ hu
      refine ⟨by dsimp only; omega, (hσ₁.compose hσ').mono (Nat.le_succ _),
        hex.getD_below (by dsimp only; omega), ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hσ'.pred_below (hp₁ q hq)).mono (Nat.le_succ _)
    | some τr, .check =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check ih hRo (Ex.Closed.some (hRo rfl τr rfl)) hΓ hR h₁
      refine ⟨by dsimp only; omega, hσ₁.mono (Nat.le_succ _), hex.getD_below (by dsimp only; omega),
        fun p hp => (hp₁ p hp).mono (Nat.le_succ _)⟩
  | throw_ e ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih (by ret_ok) .none hΓ hR h₁
    exact ⟨by dsimp only; omega, hσ₁.mono (Nat.le_succ _), .var (by dsimp only; omega),
      fun p hp => (hp₁ p hp).mono (Nat.le_succ _)⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check ih₂ (by ret_ok) hex (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp

  | while_ c body ihc ihb =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, _, hp₁⟩ := ihc (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, _, hp₂⟩ := ihb (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, fun a ha => by simp [Ty.ftv] at ha,
      ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp
  | break_ | continue_ =>
    intro Γ R rm ex n o hRo hex _ _ h
    simp only [infer, Option.some.injEq] at h; subst h
    exact ⟨Nat.le_succ _, .nil _, hex.getD_below (Nat.lt_succ_self _), by simp⟩
  | tryCatch body handler ihb ihh =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := InferInv.check ihb (by ret_ok) hex hΓ hR h₁
    have hunk : Ty.unknown.Below o₁.next := fun a ha => by simp [Ty.ftv] at ha
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := InferInv.check ihh (by ret_ok) hex (Ctx.Below.mono_cons hunk (hσ₁.ctx_below (hΓ.mono hn₁)))
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
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := InferInv.check ihb (by ret_ok) hex hΓ hR h₁
    obtain ⟨hn₂, hσ₂, _, hp₂⟩ := ihf (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hσ₂.subst_below (hτ₁.mono hn₂), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp

  | obj ls es ks ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτs₁, hp₁⟩ := inferArgs_inv es ih (by ret_ok) .none hΓ hR h₁
    split at h
    · cases h
    rename_i θs ss hfs
    obtain ⟨hθs, hss⟩ := fieldSlots_below hfs hτs₁
    have hT : (Ty.record L (objSlots L ls ss)).Below o₁.next := Ty.Below.app.mpr (objSlots_below hss)
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    have hw := unifyThis_within hu hθs hT
    refine ⟨hn₁, hσ₁.compose hw, hw.subst_below hT, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hw.pred_below (hp₁ q hq)
  | cls ls es ks ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    split at h
    · cases h
    rename_i o₁ h₁
    obtain ⟨hn₁, hσ₁, hτs₁, hp₁⟩ := inferMembers_inv es ks ih hΓ (by simp) (R := none) (fun a ha => by simp [Ret.ftv] at ha) h₁
    split at h
    · cases h
    rename_i θs ss n' hms
    obtain ⟨hn', hθs, hss⟩ := memberSlots_below hms hτs₁
    have hT : (Ty.record L (objSlots L ls ss)).Below n' := Ty.Below.app.mpr (objSlots_below hss)
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    have hw := unifyThis_within hu hθs hT
    refine ⟨Nat.le_trans hn₁ hn', (hσ₁.mono hn').compose hw, hw.subst_below hT, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp hq with hq | hq
    · exact hw.pred_below ((hp₁ q hq).mono hn')
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at ha
      exact hw.pred_below (fun x hx => by simp [Pred.ftv, Ty.ftv] at hx; omega)
  | ctor k body ih =>
    intro Γ R rm ex n o hRo hex hΓ _ h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    have hθ : Ty.newTarget.Below (n + 1 + k) := Ty.Below.con
    have hτs : ∀ τ ∈ varBlock n k, τ.Below (n + 1 + k) := fun τ hτ =>
      (varBlock_below τ hτ).mono (by omega)
    have hρ : (Ty.var (n + k)).Below (n + 1 + k) := .var (by omega)
    have hfn : (Ty.fn .newTarget (varBlock n k) (.var (n + k))).Below (n + 1 + k) :=
      Ty.Below.fn.mpr ⟨hθ, hτs, hρ⟩
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih RetOk.synth .none
      (Ctx.Below.append_mono hτs (Ctx.Below.mono_cons hfn (Ctx.Below.mono_cons hθ
        (hΓ.mono (by omega)))))
      (fun a ha => hρ a (by simpa [Ret.ftv] using ha)) h₁
    have hσ' := unify_within (hσ₁.subst_below (hρ.mono hn₁)) hτ₁ hu
    refine ⟨by dsimp only; omega, hσ₁.compose hσ', ?_, ?_⟩
    · exact (hσ₁.compose hσ').subst_below (hfn.mono (by omega))
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below (hp₁ q hq)
  | new_ f args ihf iha =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihf (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv args iha (by ret_ok) .none
      (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hle : o₂.next ≤ o₂.next + L.length := Nat.le_add_right _ _
    have hρ : (Ty.record L (varBlock o₂.next L.length)).Below (o₂.next + L.length) :=
      Ty.Below.app.mpr (fun τ hτ => varBlock_below τ hτ)
    have hσ₃ := unify_within ((hσ₂.subst_below (hτ₁.mono hn₂)).mono hle)
      (Ty.Below.fn.mpr ⟨Ty.Below.con, fun τ hτ => (hτs₂ τ hτ).mono hle, hρ⟩) hu
    refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).mono hle).compose hσ₃,
      hσ₃.subst_below hρ, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    refine hσ₃.pred_below ?_
    simp only [List.mem_append, List.mem_map] at hq
    rcases hq with ⟨q', hq', rfl⟩ | hq'
    · exact (hσ₂.pred_below ((hp₁ q' hq').mono hn₂)).mono hle
    · exact (hp₂ q hq').mono hle
  | get e l ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih (by ret_ok) .none hΓ hR h₁
    have hle : o₁.next ≤ o₁.next + 2 := by omega
    dsimp only
    refine ⟨Nat.le_trans hn₁ hle, hσ₁.mono hle, Ty.Below.var (by omega), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact (hp₁ p hp).mono hle
    · intro a ha
      simp only [Pred.ftv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, Ty.ftv_var, List.mem_singleton] at ha
      rcases ha with ha | rfl | rfl
      · exact Nat.lt_of_lt_of_le (hτ₁ a ha) hle
      · omega
      · omega
  | set e l v ihe ihv =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihe (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ihv (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    refine ⟨Nat.le_trans hn₁ hn₂, (hσ₁.mono hn₂).compose hσ₂, hτ₂, ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    have hr := hσ₂.subst_below (hτ₁.mono hn₂)
    rcases hp with (⟨q, hq, rfl⟩ | hp) | hp
    · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
    · exact hp₂ p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact Pred.below_of_args (by simp [hr, hτ₂, Ty.Below.con])
  | spread e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ih₁ (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ih₂ (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hle : o₂.next ≤ o₂.next + 5 * L.length := by omega
    have hb : ∀ j, j < 5 → ∀ τ ∈ varBlock (o₂.next + j * L.length) L.length,
        τ.Below (o₂.next + 5 * L.length) := fun j hj τ hτ =>
      (varBlock_below τ hτ).mono (by
        have : j * L.length + L.length ≤ 5 * L.length := by
          have := Nat.mul_le_mul_right L.length (show j + 1 ≤ 5 by omega)
          simpa [Nat.add_mul] using this
        omega)
    have hb₀ : ∀ τ ∈ varBlock o₂.next L.length, τ.Below (o₂.next + 5 * L.length) := by
      simpa using hb 0 (by omega)
    have hb₁ : ∀ τ ∈ varBlock (o₂.next + L.length) L.length, τ.Below (o₂.next + 5 * L.length) := by
      simpa using hb 1 (by omega)
    have hb₂ := hb 2 (by omega)
    have hb₃ := hb 3 (by omega)
    have hb₄ := hb 4 (by omega)
    have hσ₃ := unify_within ((hσ₂.mono hle).subst_below ((hτ₁.mono hn₂).mono hle))
      (Ty.Below.app.mpr hb₀) hu₃
    have hσ₄ := unify_within (hσ₃.subst_below (hτ₂.mono hle))
      (hσ₃.subst_below (Ty.Below.app.mpr (slots3_below hb₁ hb₂ hb₃))) hu₄
    have hσ₄₃ := hσ₃.compose hσ₄
    refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).mono hle).compose hσ₄₃,
      hσ₄₃.subst_below (Ty.Below.app.mpr hb₄), ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    refine hσ₄₃.pred_below ?_
    simp only [List.mem_append, List.mem_map] at hq
    rcases hq with (⟨q', hq', rfl⟩ | hq') | hq'
    · exact (hσ₂.pred_below ((hp₁ q' hq').mono hn₂)).mono hle
    · exact (hp₂ q hq').mono hle
    · exact mergePreds_below hb₁ hb₂ hb₃ hb₀ hb₄ q hq'
  | arr es ih =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · rename_i T σ hat
      obtain rfl := arrTarget_some hat
      obtain ⟨-, hw⟩ := arrTarget_fst hat rfl
      have hT := hex T rfl
      have hσ : σ.ftv = [] := by simpa [Ty.ftv] using Ty.ftv_nil_of_whnf hw hT
      split at h
      · cases h
      rename_i o₁ h₁
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, -, hp₁⟩ := inferArgs_inv es (fun a ha => ih a ha) hRo (Ex.Closed.some hσ) hΓ hR h₁
      exact ⟨hn₁, hσ₁, Ty.Below.closed hT, hp₁⟩
    · split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hn₁, hσ₁, hτs₁, hp₁⟩ := inferArgs_inv es (fun a ha => ih a ha) (by ret_ok) .none hΓ hR h₁
      have hle : o₁.next ≤ o₁.next + 1 := Nat.le_succ _
      have hα : (Ty.var o₁.next).Below (o₁.next + 1) := Ty.Below.var (Nat.lt_succ_self _)
      have hσ' := unify_within (Ty.Below.app.mpr (fun τ hτ => (hτs₁ τ hτ).mono hle))
        (Ty.Below.app.mpr (fun τ hτ => by rw [List.eq_of_mem_replicate hτ]; exact hα)) hu
      refine ⟨by dsimp only; omega, (hσ₁.mono hle).compose hσ',
        hσ'.subst_below (Ty.Below.app.mpr (fun τ hτ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ; subst hτ; exact hα)), ?_⟩
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hσ'.pred_below ((hp₁ q hq).mono hle)
  | index e i ihe ihi =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihe (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ihi (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hle : o₂.next ≤ o₂.next + 1 := Nat.le_succ _
    refine ⟨by dsimp only; omega, ((hσ₁.mono hn₂).compose hσ₂).mono hle,
      Ty.Below.var (Nat.lt_succ_self _), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with (⟨q, hq, rfl⟩ | hp) | rfl
    · exact (hσ₂.pred_below ((hp₁ q hq).mono hn₂)).mono hle
    · exact (hp₂ p hp).mono hle
    · refine Pred.below_of_args ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro τ (rfl | rfl | rfl)
      · exact (hσ₂.subst_below (hτ₁.mono hn₂)).mono hle
      · exact hτ₂.mono hle
      · exact Ty.Below.var (Nat.lt_succ_self _)
  | setIndex e i v ihe ihi ihv =>
    intro Γ R rm ex n o hRo hex hΓ hR h
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
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihe (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτ₂, hp₂⟩ := ihi (by ret_ok) .none (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) h₂
    obtain ⟨hn₃, hσ₃, hτ₃, hp₃⟩ := ihv (by ret_ok) .none (hσ₂.ctx_below ((hσ₁.ctx_below (hΓ.mono hn₁)).mono hn₂))
      (hσ₂.ret_below ((hσ₁.ret_below (hR.mono hn₁)).mono hn₂)) h₃
    refine ⟨by dsimp only; omega, (((hσ₁.mono hn₂).compose hσ₂).mono hn₃).compose hσ₃, hτ₃, ?_⟩
    have hc := hσ₃.subst_below ((hσ₂.subst_below (hτ₁.mono hn₂)).mono hn₃)
    have hi := hσ₃.subst_below (hτ₂.mono hn₃)
    intro p hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with (⟨q, (⟨q', hq', rfl⟩ | hq), rfl⟩ | hp) | hp
    · exact hσ₃.pred_below ((hσ₂.pred_below ((hp₁ q' hq').mono hn₂)).mono hn₃)
    · exact hσ₃.pred_below ((hp₂ q hq).mono hn₃)
    · exact hp₃ p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact Pred.below_of_args (by simp [hc, hi, hτ₃])
  | mcall e l args ihe iha =>
    intro Γ R rm ex n o hRo hex hΓ hR h
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hn₁, hσ₁, hτ₁, hp₁⟩ := ihe (by ret_ok) .none hΓ hR h₁
    obtain ⟨hn₂, hσ₂, hτs₂, hp₂⟩ := inferArgs_inv args iha (by ret_ok) .none
      (hσ₁.ctx_below (hΓ.mono hn₁)) (hσ₁.ret_below (hR.mono hn₁)) h₂
    have hle : o₂.next ≤ o₂.next + 2 := by omega
    have hτ : (o₁.τ.subst o₂.σ).Below (o₂.next + 2) := (hσ₂.subst_below (hτ₁.mono hn₂)).mono hle
    dsimp only
    refine ⟨by omega, ((hσ₁.mono hn₂).compose hσ₂).mono hle,
      Ty.Below.var (by omega), ?_⟩
    intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with (⟨q, hq, rfl⟩ | hp) | rfl
    · exact (hσ₂.pred_below ((hp₁ q hq).mono hn₂)).mono hle
    · exact (hp₂ p hp).mono hle
    · refine Pred.below_of_args ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro τ (rfl | rfl | rfl)
      · exact hτ
      · exact Ty.Below.var (by omega)
      · exact Ty.Below.fn.mpr ⟨hτ, fun t ht => (hτs₂ t ht).mono hle, Ty.Below.var (by omega)⟩

end Inty
