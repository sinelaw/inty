import Inty.RigidKeys

/-!
# Completeness of inference

Whatever `HasType` accepts, `infer` finds, with a type of which the accepted
one is an instance up to equal types (Damas and Milner; Naraschewski and
Nipkow's Isabelle proof of algorithm W is the model for its freshness
invariants, `Inty.InferInv`).

A typing's context need only have schemes equal to inference's under a
substitution (`CtxEq`), and its types need only be equal (`TyEq`): the
conversion rule may replace any type by an equal one, and the unifier is
most general up to equal types (`unify_mgu`). A `let`'s scheme found by
inference is more general than the typing's, and the typing of the rest
moves to it (`HasTypeS.weaken`).
-/

namespace Inty

/-! ## Agreement up to equal types -/

/-- `φ` after `σ` agrees with `ψ` below `n`, up to equal types. -/
def Agree (n : Nat) (σ φ ψ : Subst) : Prop :=
  ∀ a < n, TyEq (((Ty.var a).subst σ).subst φ) ((Ty.var a).subst ψ)

theorem Agree.ty {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {τ : Ty} (hτ : τ.Below n) :
    TyEq ((τ.subst σ).subst φ) (τ.subst ψ) := by
  rw [← Ty.subst_compose]
  exact Ty.subst_tyEq_congr (fun a ha => by rw [Ty.subst_compose]; exact h a (hτ a ha))

theorem Agree.pred {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {p : Pred} (hp : p.Below n) :
    PredEq ((p.subst σ).subst φ) (p.subst ψ) := by
  rw [← Pred.subst_compose]
  exact Pred.subst_predEq_congr_tv (fun a ha => by
    rw [Ty.subst_compose]; exact h a (hp a (Pred.tv_sub_ftv ha)))

theorem Agree.scheme {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {s : Scheme}
    (hs : ∀ a ∈ s.ftv, a < n) : SchemeEq ((s.subst σ).subst φ) (s.subst ψ) := by
  rw [← Scheme.subst_compose]
  exact Scheme.subst_congr_ftv (fun a ha => by rw [Ty.subst_compose]; exact h a (hs a ha))

theorem Agree.ctx {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {Γ : Ctx} (hΓ : Ctx.Below n Γ) :
    CtxEq (Ctx.subst φ (Ctx.subst σ Γ)) (Ctx.subst ψ Γ) := by
  rw [← Ctx.subst_compose]
  exact Ctx.subst_congr_tv (fun a ha => by
    rw [Ty.subst_compose]; exact h a (hΓ a (ctxTv_sub_ftv ha)))

theorem Ret.tv_sub_ftv {R : Option Ty} {a : Nat} (h : a ∈ Ret.tv R) : a ∈ Ret.ftv R := by
  cases R <;> simp_all [Ret.tv, Ret.ftv, Ty.tv_sub_ftv]

theorem Agree.ret {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {R : Option Ty}
    (hR : Ret.Below n R) : RetEq (Ret.subst φ (Ret.subst σ R)) (Ret.subst ψ R) := by
  rw [← Ret.subst_compose]
  exact Ret.subst_congr_tv (fun a ha => by
    rw [Ty.subst_compose]; exact h a (hR a (Ret.tv_sub_ftv ha)))

theorem Agree.mono {n n' : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) (hn : n' ≤ n) :
    Agree n' σ φ ψ := fun a ha => h a (by omega)

theorem Agree.nil (n : Nat) (ψ : Subst) : Agree n [] ψ ψ := fun a _ => by simp; exact TyEq.refl _

/-- `φ` absorbs `σ`: applying `σ` first changes nothing, up to equal types. -/
def Absorbs (φ σ : Subst) : Prop := ∀ τ : Ty, TyEq ((τ.subst σ).subst φ) (τ.subst φ)

theorem Absorbs.pred {φ σ : Subst} (h : Absorbs φ σ) (p : Pred) :
    PredEq ((p.subst σ).subst φ) (p.subst φ) := by
  refine ⟨rfl, by simp [Pred.subst], fun x hx => ?_⟩
  simp only [Pred.subst, List.map_map] at hx
  obtain ⟨y, hy, rfl⟩ := zip_map_map_mem hx
  exact h y

theorem Absorbs.compose {φ σ σ' : Subst} (h : Absorbs φ σ) (h' : Absorbs φ σ') :
    Absorbs φ (Subst.compose σ' σ) := fun τ => by
  rw [Ty.subst_compose]; exact (h' _).trans (h τ)

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

theorem Ty.subst_block_fresh {k : Nat} {τs : List Ty} {φ : Subst} {τ : Ty} (hτ : τ.Below k) :
    τ.subst (Subst.block k τs ++ φ) = τ.subst φ :=
  Ty.subst_congr (fun a ha => by simp [Subst.find_append, Subst.block_find_none (hτ a ha)])

theorem Pred.subst_block_fresh {k : Nat} {τs : List Ty} {φ : Subst} {p : Pred} (hp : p.Below k) :
    p.subst (Subst.block k τs ++ φ) = p.subst φ :=
  Pred.subst_congr (fun a ha => by simp [Subst.find_append, Subst.block_find_none (hp a ha)])

/-- Agreement through two inference steps. -/
theorem Agree.trans {n m : Nat} {σ₁ σ₂ φ₁ φ₂ ψ : Subst} (h₁ : Agree n σ₁ φ₁ ψ)
    (hσ₁ : σ₁.Within m) (hnm : n ≤ m) (h₂ : Agree m σ₂ φ₂ φ₁) :
    Agree n (Subst.compose σ₂ σ₁) φ₂ ψ := fun a ha => by
  rw [Ty.subst_compose]
  exact (h₂.ty ((hσ₁ a).1 (by omega))).trans (h₁ a ha)

/-- Agreement after a unifier the substitution absorbs. -/
theorem Agree.absorb {n : Nat} {σ σ' φ ψ : Subst} (h : Agree n σ φ ψ) (habs : Absorbs φ σ') :
    Agree n (Subst.compose σ' σ) φ ψ := fun a ha => by
  rw [Ty.subst_compose]; exact (habs _).trans (h a ha)

/-- Agreement survives binding a variable at or above the bound. -/
theorem Agree.cons_fresh (k : Nat) (ρ : Ty) (φ : Subst) : Agree k [] ((k, ρ) :: φ) φ :=
  fun a ha => by
    simp only [Ty.subst_nil]
    rw [Ty.subst_cons_fresh (Ty.Below.var ha)]; exact TyEq.refl _

theorem Agree.fresh {n k : Nat} {σ φ ψ : Subst} {ρ : Ty} (h : Agree n σ φ ψ) (hσ : σ.Within k)
    (hnk : n ≤ k) : Agree n σ ((k, ρ) :: φ) ψ := fun a ha => by
  rw [Ty.subst_cons_fresh ((hσ a).1 (by omega))]; exact h a ha

theorem Agree.block {n k : Nat} {σ φ ψ : Subst} {τs : List Ty} (h : Agree n σ φ ψ)
    (hσ : σ.Within k) (hnk : n ≤ k) : Agree n σ (Subst.block k τs ++ φ) ψ := fun a ha => by
  rw [Ty.subst_block_fresh ((hσ a).1 (by omega))]; exact h a ha

theorem RetEq.symm : ∀ {R R' : Option Ty}, RetEq R R' → RetEq R' R
  | none, none, _ => trivial
  | some _, some _, h => TyEq.symm h

theorem RetEq.trans : ∀ {R R' R'' : Option Ty}, RetEq R R' → RetEq R' R'' → RetEq R R''
  | none, none, none, _, _ => trivial
  | some _, some _, some _, h₁, h₂ => TyEq.trans h₁ h₂

/-! ## Satisfied constraints -/

theorem Sat.predEq {C P : List Pred} {φ φ' : Subst} (h : ∀ p ∈ P, PredEq (p.subst φ') (p.subst φ))
    (hs : Sat C P φ') : Sat C P φ := fun p hp => (hs p hp).of_predEq (h p hp)

theorem Sat.absorb {C P : List Pred} {φ σ : Subst} (habs : Absorbs φ σ) (h : Sat C P φ) :
    Sat C (P.map (·.subst σ)) φ := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).of_predEq (habs.pred q).symm

theorem Sat.fresh {C P : List Pred} {φ : Subst} {k : Nat} {ρ : Ty} (hP : ∀ p ∈ P, p.Below k)
    (h : Sat C P φ) : Sat C P ((k, ρ) :: φ) := fun p hp => by
  rw [Pred.subst_cons_fresh (hP p hp)]; exact h p hp

theorem Sat.block {C P : List Pred} {φ : Subst} {k : Nat} {τs : List Ty}
    (hP : ∀ p ∈ P, p.Below k) (h : Sat C P φ) : Sat C P (Subst.block k τs ++ φ) := fun p hp => by
  rw [Pred.subst_block_fresh (hP p hp)]; exact h p hp

theorem Sat.agree {C P : List Pred} {σ φ ψ : Subst} {n : Nat} (hag : Agree n σ φ ψ)
    (hP : ∀ p ∈ P, p.Below n) (h : Sat C P ψ) : Sat C (P.map (·.subst σ)) φ := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).of_predEq (hag.pred (hP q hq)).symm

theorem Sat.app {C P Q : List Pred} {φ : Subst} (hP : Sat C P φ) (hQ : Sat C Q φ) :
    Sat C (P ++ Q) φ := fun p hp => (List.mem_append.mp hp).elim (hP p) (hQ p)

/-! ## Fresh variables -/

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

theorem RTy.gen_subst_instR {ᾱ : List Nat} {τs' : List Ty} (φ : Subst)
    (h : ᾱ.length = τs'.length) (r : RTy) :
    ((r.gen ᾱ).subst φ).instR τs' = r.subst (ᾱ.zip τs' ++ φ) := by
  induction r using RTy.ind with
  | free v =>
    simp only [RTy.gen, RTy.subst, Subst.find_append, zip_find ᾱ τs' v h]
    cases findIdx ᾱ v with
    | some i => simp [PTy.subst, PTy.instR]
    | none => simp [PTy.subst]
  | self j => rfl
  | app c args ih =>
    simp only [RTy.gen_app, PTy.subst_app, PTy.instR_app, RTy.subst_app, List.map_map,
      RTy.app.injEq, true_and]
    exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.gen_mu, PTy.subst_mu, PTy.instR_mu, RTy.subst_mu, List.map_map,
      RTy.mu.injEq, true_and]
    exact List.map_congr_left ih

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
  | mu i sys =>
    simp only [Ty.gen_mu, PTy.subst_mu, PTy.inst_mu, Ty.subst_mu, List.map_map,
      Ty.mu.injEq, true_and]
    exact List.map_congr_left (fun r _ => RTy.gen_subst_instR φ h r)

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


theorem Expr.isValue_complete {e : Expr} (h : e.IsValue) : e.isValue = true := by
  cases h <;> rfl

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
    (hstep : ∀ p ∈ ps₀, (∀ v ∈ (p.fundep.map fun d => d.1.flatMap Ty.tv).getD [], Q v) →
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
theorem RTy.gen_bvs {ᾱ : List Nat} {a i : Nat} (hi : findIdx ᾱ a = some i) :
    ∀ {r : RTy}, a ∈ r.ftv → i ∈ (r.gen ᾱ).bvs := by
  intro r
  induction r using RTy.ind with
  | free b =>
    intro h
    simp only [RTy.ftv, List.mem_singleton] at h
    subst h
    simp [RTy.gen, hi, PTy.bvs]
  | self j => intro h; simp [RTy.ftv] at h
  | app c args ih =>
    intro h
    simp only [RTy.ftv_app, List.mem_flatMap] at h
    obtain ⟨x, hx, hax⟩ := h
    simp only [RTy.gen_app, PTy.bvs_app, List.flatMap_map, List.mem_flatMap]
    exact ⟨x, hx, ih x hx hax⟩
  | mu j sys ih =>
    intro h
    simp only [RTy.ftv_mu, List.mem_flatMap] at h
    obtain ⟨x, hx, hax⟩ := h
    simp only [RTy.gen_mu, PTy.bvs_mu, List.flatMap_map, List.mem_flatMap]
    exact ⟨x, hx, ih x hx hax⟩

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
  | mu j sys =>
    intro h
    simp only [Ty.ftv_mu, List.mem_flatMap] at h
    obtain ⟨x, hx, hax⟩ := h
    simp only [Ty.gen_mu, PTy.bvs_mu, List.flatMap_map, List.mem_flatMap]
    exact ⟨x, hx, RTy.gen_bvs hi hax⟩

theorem Pred.fundep_some {p : Pred} {ds rs : List Ty} (h : p.fundep = some (ds, rs)) :
    (p.cls ≠ .plus ∧ p.cls ≠ .merge ∧ ∃ d, p.args = d :: rs ∧ ds = [d]) ∨
      ∃ q k τ t r, p = ⟨.merge, [q, k, τ, t, r]⟩ ∧ ds = [q, k, τ, t] ∧ rs = [r] := by
  obtain ⟨cls, args⟩ := p
  cases cls
  case plus => simp [Pred.fundep] at h
  case merge =>
    match args, h with
    | [q, k, τ, t, r], h =>
      simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨_, _, _, _, _, rfl, rfl, rfl⟩
    | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
    | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
      simp [Pred.fundep] at h
  all_goals
    match args, h with
    | d :: rest, h =>
      simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨by simp, by simp, d, rfl, rfl⟩
    | [], h => simp [Pred.fundep] at h

theorem Pred.fundep_of_args {p : Pred} {d : Ty} {rest : List Ty} (hp : p.cls ≠ .plus)
    (hm : p.cls ≠ .merge) (h : p.args = d :: rest) : p.fundep = some ([d], rest) := by
  obtain ⟨cls, args⟩ := p
  simp only at hp hm h; subst h
  cases cls <;> simp_all [Pred.fundep]


/-! ## Deciding constraints -/

/-- A decision right under `φ`: waiting, or an equation `φ` makes hold. -/
def Improve.Holds (φ : Subst) : Improve → Prop
  | .keep => True
  | .fail => False
  | .eq a b => TyEq (a.subst φ) (b.subst φ)

theorem Pred.improveArgs_cons {c : Cls} {t : Ty} {rest : List Ty} :
    Pred.improveArgs c (t :: rest) =
      if t.whnf.isVar then (if rest.length + 1 = c.arity then .keep else .fail)
      else Pred.decide₀ c t.whnf rest := rfl

/-- What a spread copies of a slot whose image is equal to one it copies. -/
theorem Pred.decideCopy_complete {s r s₀ r₀ : Ty} {φ : Subst} (hc : SlotCopy s₀ r₀)
    (hs : TyEq (s.subst φ) s₀) (hr : TyEq (r.subst φ) r₀) : (Pred.decideCopy s r).Holds φ := by
  have hslot : ∃ p₀ k₀ τ₀, s₀ = .slot p₀ k₀ τ₀ := by cases hc <;> exact ⟨_, _, _, rfl⟩
  obtain ⟨p₀, k₀, τ₀, rfl⟩ := hslot
  rcases Ty.whnf_app_of_tyEq hs with ⟨a, ha⟩ | ⟨xs, hxs, hl, hz⟩
  · simp [Pred.decideCopy, ha, Improve.Holds]
  match xs, hl with
  | [p, k, τ], _ =>
    have hp : TyEq (p.subst φ) p₀ := hz (p, p₀) (by simp)
    have hk : TyEq (k.subst φ) k₀ := hz (k, k₀) (by simp)
    have hτ : TyEq (τ.subst φ) τ₀ := hz (τ, τ₀) (by simp)
    cases hc with
    | data =>
      rcases Ty.whnf_con_of_tyEq hp with ⟨a, ha⟩ | hpre
      · simp [Pred.decideCopy, hxs, ha, Improve.Holds]
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkd
      · simp [Pred.decideCopy, hxs, hpre, ha, Improve.Holds]
      simp only [Pred.decideCopy, hxs, hpre, hkd, Improve.Holds]
      exact hr.trans hs.symm
    | getter =>
      rcases Ty.whnf_con_of_tyEq hp with ⟨a, ha⟩ | hpre
      · simp [Pred.decideCopy, hxs, ha, Improve.Holds]
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkd
      · simp [Pred.decideCopy, hxs, hpre, ha, Improve.Holds]
      simp only [Pred.decideCopy, hxs, hpre, hkd, Improve.Holds]
      exact hr.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ.symm)
    | proto =>
      rcases Ty.whnf_con_of_tyEq hp with ⟨a, ha⟩ | hpre
      · simp [Pred.decideCopy, hxs, ha, Improve.Holds]
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkd
      · simp [Pred.decideCopy, hxs, hpre, ha, Improve.Holds]
      simp only [Pred.decideCopy, hxs, hpre, hkd, Improve.Holds]
      simpa using hr
    | abs =>
      rcases Ty.whnf_con_of_tyEq hp with ⟨a, ha⟩ | habs
      · simp [Pred.decideCopy, hxs, ha, Improve.Holds]
      simp only [Pred.decideCopy, hxs, habs, Improve.Holds]
      exact hr.trans hs.symm

/-- A slot whose image waits on a variable waits. -/
theorem Pred.decideCopy_keep_subst {s r : Ty} {φ : Subst} (h : (s.subst φ).SlotOnVar) :
    Pred.decideCopy s r = .keep := by
  unfold Ty.SlotOnVar at h
  generalize hw : (s.subst φ).whnf = w at h
  match w, h with
  | .var a, _ =>
    obtain ⟨b, hb⟩ := Ty.whnf_subst_var hw
    simp [Pred.decideCopy, hb]
  | .slot p k τ, h =>
    rcases Ty.whnf_subst_app hw with ⟨b, hb⟩ | ⟨xs, hxs, he⟩
    · simp [Pred.decideCopy, hb]
    match xs, he with
    | [p₁, k₁, τ₁], he =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      rcases h with ⟨a, ha⟩ | ⟨hpre, a, ha⟩
      · obtain ⟨b, hb⟩ := Ty.whnf_subst_var ha
        simp [Pred.decideCopy, hxs, hb]
      · obtain ⟨b, hb⟩ := Ty.whnf_subst_var ha
        rcases Ty.whnf_subst_app hpre with ⟨c, hc⟩ | ⟨ys, hys, hye⟩
        · simp [Pred.decideCopy, hxs, hc]
        · obtain rfl : ys = [] := by simpa using hye.symm
          simp [Pred.decideCopy, hxs, hys, hb]

/-- A `Merge` whose image waits on a variable waits. -/
theorem Pred.improveArgs_merge_keep {args : List Ty} {φ : Subst}
    (h : Pred.MergeOnVar ⟨.merge, args.map (·.subst φ)⟩) : Pred.improveArgs .merge args = .keep := by
  match args, h with
  | [q, k, τ, s, r], h =>
    simp only [List.map_cons, List.map_nil, Pred.MergeOnVar] at h
    rw [Pred.improveArgs_cons]
    split
    · simp [Cls.arity]
    rename_i hnv
    have hpre_or : ∀ {c : Con}, (q.subst φ).whnf = .app c [] → q.whnf = .app c [] := fun {c} hc => by
      rcases Ty.whnf_subst_app hc with ⟨a, ha⟩ | ⟨xs, hxs, hxe⟩
      · simp [ha, Ty.isVar] at hnv
      · obtain rfl : xs = [] := by simpa using hxe.symm
        exact hxs
    rcases h with ⟨hpre, a, ha⟩ | ⟨hqk, hsv⟩
    · obtain ⟨b, hb⟩ := Ty.whnf_subst_var ha
      simp [hpre_or hpre, Pred.decide₀, Pred.decidePre, hb]
    · rcases hqk with ⟨hpre, hpro⟩ | habs
      · rcases Ty.whnf_subst_app hpro with ⟨b, hb⟩ | ⟨xs, hxs, hxe⟩
        · simp [hpre_or hpre, Pred.decide₀, Pred.decidePre, hb]
        · obtain rfl : xs = [] := by simpa using hxe.symm
          simp [hpre_or hpre, Pred.decide₀, Pred.decidePre, hxs, Pred.decideCopy_keep_subst hsv]
      · simp [hpre_or habs, Pred.decide₀, Pred.decideCopy_keep_subst hsv]

theorem Ty.field_zip {l : String} {φ : Subst} : ∀ {ls : List String} {xs fs : List Ty} {f₀ : Ty},
    xs.length = fs.length → (∀ x ∈ xs.zip fs, TyEq (x.1.subst φ) x.2) →
    Ty.field l ls fs = some f₀ → ∃ x, Ty.field l ls xs = some x ∧ TyEq (x.subst φ) f₀
  | [], _, _, _, _, _, h => by simp [Ty.field] at h
  | _ :: _, [], [], _, _, _, h => by simp [Ty.field] at h
  | l' :: ls, x :: xs, f :: fs, f₀, hl, hz, h => by
    simp only [Ty.field] at h ⊢
    split at h
    · rename_i he
      cases h; exact ⟨x, by simp [he], hz (x, f) (by simp)⟩
    · rename_i he
      simp only [he, ↓reduceIte]
      exact Ty.field_zip (by simpa using hl) (fun y hy => hz y (List.mem_cons_of_mem _ hy)) h
  | _ :: _, [], _ :: _, _, hl, _, _ | _ :: _, _ :: _, [], _, hl, _, _ => by simp at hl

theorem TyEq.tuple₂ {a b a' b' : Ty} (ha : TyEq a a') (hb : TyEq b b') :
    TyEq (.tuple [a, b]) (.tuple [a', b']) :=
  TyEq.app (by simp) (fun p hp => by
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hb)

theorem TyEq.not_maybe {c : Con} {args : List Ty} {z : Nothing} {σ : Ty} (hc : c ≠ .maybe z) :
    ¬ TyEq (.app c args) (.maybe z σ) := fun h => hc (TyEq.app_iff.mp h).1

theorem Ty.whnf_of_tyEq_maybe {T σ₀ : Ty} {z : Nothing} (h : TyEq T (.maybe z σ₀)) :
    ∃ σ, T.whnf = .maybe z σ ∧ TyEq σ σ₀ := by
  obtain ⟨ys, hys, he⟩ := TyEq.whnf_app (c := .maybe z) (xs := [σ₀]) h.symm rfl
  obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp he
  match ys, hl, hz with
  | [σ], _, hz => exact ⟨σ, hys, (hz (σ₀, σ) (by simp)).symm⟩

theorem Pred.decide₀_inject (T t : Ty) : Pred.decide₀ (.inject T) t [] = Pred.decideInject t T := by
  unfold Pred.decide₀; split <;> simp_all

/-- An `Inject T τ` whose image is `Inject T T`: its decision holds. -/
theorem Pred.decideInject_self {t T : Ty} {φ : Subst} (hT : T.ftv = [])
    (ht : TyEq (t.subst φ) T) (hnv : t.whnf.isVar = false) :
    (Pred.decideInject t.whnf T).Holds φ := by
  have hW : TyEq (t.whnf.subst φ) T := ((TyEq.whnf t).subst φ).trans ht
  generalize t.whnf = w at hnv hW
  have hTφ := Ty.closed_subst hT φ
  unfold Pred.decideInject
  simp only [hT, ↓reduceIte]
  split
  · rename_i z σ hTw
    have hTm : TyEq T (.maybe z σ) := TyEq.of_whnf hTw
    split
    · rename_i c args
      split
      · simp only [Improve.Holds, hTφ]; exact hW
      · rename_i hc
        exact absurd (by simpa [Ty.subst_app] using hW.trans hTm) (TyEq.not_maybe hc)
    · simp only [Improve.Holds, hTφ]; exact hW
  · rename_i ts Rs hTw
    split
    · rename_i c args
      have hc : c = .variant .typeOf ts :=
        TyEq.con ((by simpa [Ty.subst_app] using hW : TyEq (.app c _) T).trans (TyEq.of_whnf hTw))
      subst hc
      simp only [Con.typeTag, Improve.Holds, hTφ]; exact hW
    · simp only [Improve.Holds, hTφ]; exact hW
  · simp only [Improve.Holds, hTφ]; exact hW

/-- An `Inject T τ` whose image is `Inject (Nullable σ) Null` (or alike):
its decision holds. -/
theorem Pred.decideInject_nothing {t T σ₀ : Ty} {z : Nothing} {φ : Subst} (hT : T.ftv = [])
    (hTm : TyEq T (.maybe z σ₀)) (ht : TyEq (t.subst φ) z.ty) (hnv : t.whnf.isVar = false) :
    (Pred.decideInject t.whnf T).Holds φ := by
  rcases Ty.whnf_con_of_tyEq (c := z.con) ht with ⟨a, ha⟩ | hw
  · simp [ha, Ty.isVar] at hnv
  rw [hw]
  obtain ⟨σ, hTw, -⟩ := Ty.whnf_of_tyEq_maybe hTm
  have hne : z.con ≠ .maybe z := by cases z <;> simp [Nothing.con]
  unfold Pred.decideInject
  simp only [hT, ↓reduceIte, hTw, hne, and_self, Improve.Holds]
  exact TyEq.refl _

/-- An `Inject T τ` whose image is `Inject (Nullable τ') τ'` (or alike):
its decision holds. -/
theorem Pred.decideInject_some {t T : Ty} {z : Nothing} {c₀ : Con} {a₀ : List Ty} {φ : Subst}
    (hT : T.ftv = []) (hTm : TyEq T (.maybe z (.app c₀ a₀))) (hc₀ : c₀ ≠ .maybe z)
    (hn₀ : ¬ (c₀ = z.con ∧ a₀ = [])) (ht : TyEq (t.subst φ) (.app c₀ a₀))
    (hnv : t.whnf.isVar = false) : (Pred.decideInject t.whnf T).Holds φ := by
  rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, -⟩
  · simp [ha, Ty.isVar] at hnv
  obtain ⟨σ, hTw, hσ⟩ := Ty.whnf_of_tyEq_maybe hTm
  have hσc : σ.ftv = [] := by
    have := Ty.ftv_nil_of_whnf hTw hT
    simpa [Ty.ftv] using this
  have hW : TyEq (t.whnf.subst φ) σ := ((TyEq.whnf t).subst φ).trans (ht.trans hσ.symm)
  rw [hxs] at hW ⊢
  have hn : ¬ (c₀ = z.con ∧ xs = []) := fun ⟨h1, h2⟩ =>
    hn₀ ⟨h1, List.eq_nil_of_length_eq_zero (by rw [← hxl, h2]; rfl)⟩
  unfold Pred.decideInject
  simp only [hT, ↓reduceIte, hTw, hc₀, hn, Improve.Holds, Ty.closed_subst hσc]
  exact hW

theorem Pred.decide₀_strip (t σ : Ty) : Pred.decide₀ .strip t [σ] = Pred.decideStrip t σ := by
  unfold Pred.decide₀; split <;> simp_all

theorem Pred.decideStrip_app {c : Con} {xs : List Ty} {σ : Ty} (hm : ∀ z, c ≠ .maybe z)
    (hn : c ≠ .null) (hu : c ≠ .undefined) :
    Pred.decideStrip (.app c xs) σ = .eq σ (.app c xs) := by
  cases c <;> simp_all [Pred.decideStrip]

theorem firstIdx_of_nodup {t : String} : ∀ {ts : List String} {i : Nat}, ts.Nodup →
    ts[i]? = some t → firstIdx t ts = some i
  | [], _, _, h => by simp at h
  | x :: xs, 0, _, h => by simp at h; subst h; simp [firstIdx]
  | x :: xs, i + 1, hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    have hx : x ≠ t := fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.mem_of_getElem? h)
    simp [firstIdx, hx, firstIdx_of_nodup (List.nodup_cons.mp hnd).2 h]

theorem zip_eraseIdx_mem {α β : Type} : ∀ (xs : List α) (ys : List β) (i : Nat),
    xs.length = ys.length → ∀ p ∈ (xs.eraseIdx i).zip (ys.eraseIdx i), p ∈ xs.zip ys
  | [], _, _, _, p, hp => by simp at hp
  | _ :: _, [], _, h, _, _ => by simp at h
  | x :: xs, y :: ys, 0, _, p, hp => by simp only [List.eraseIdx_cons_zero] at hp; simp [hp]
  | x :: xs, y :: ys, i + 1, h, p, hp => by
    simp only [List.eraseIdx_cons_succ, List.zip_cons_cons, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp
    · exact .inl rfl
    · exact .inr (zip_eraseIdx_mem xs ys i (by simpa using h) p hp)

theorem variantRest_tyEq {d : Disc} {ts : List String} : ∀ {xs ys : List Ty},
    xs.length = ys.length → (∀ p ∈ xs.zip ys, TyEq p.1 p.2) →
      TyEq (variantRest d ts xs) (variantRest d ts ys)
  | [], [], _, _ => TyEq.refl _
  | [x], [y], _, hz => hz (x, y) (by simp)
  | x :: x' :: xs, y :: y' :: ys, hl, hz => TyEq.app hl hz
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl
  | [_], _ :: _ :: _, hl, _ | _ :: _ :: _, [_], hl, _ => by simp at hl

/-- An `Inject T τ` whose image is into a variant told apart by `typeof`, at
its case of `τ`'s head's tag: its decision holds. -/
theorem Pred.decideInject_arm {t T R : Ty} {ts : List String} {Rs : List Ty} {c : Con}
    {args : List Ty} {t' : String} {i : Nat} {φ : Subst} (hT : T.ftv = [])
    (hw : T.whnf = .variant .typeOf ts Rs) (hn : ts.Nodup) (htag : c.typeTag = some t')
    (hi : ts[i]? = some t') (hR : Rs[i]? = some R) (he : TyEq (.app c args) R)
    (ht : TyEq (t.subst φ) (.app c args)) (hnv : t.whnf.isVar = false) :
    (Pred.decideInject t.whnf T).Holds φ := by
  rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, -, -⟩
  · simp [ha, Ty.isVar] at hnv
  have hRc : R.ftv = [] := by
    have := Ty.ftv_nil_of_whnf hw hT
    simp only [Ty.ftv_app, List.flatMap_eq_nil_iff] at this
    exact this R (List.mem_of_getElem? hR)
  have hW : TyEq ((Ty.app c xs).subst φ) R := by
    rw [← hxs]; exact (((TyEq.whnf t).subst φ).trans ht).trans he
  unfold Pred.decideInject
  simp only [hT, ↓reduceIte, hw, hxs, htag, hn, firstIdx_of_nodup hn hi, hR, Improve.Holds,
    Ty.closed_subst hRc]
  exact hW

/-- Deciding a constraint whose image is equal to an instance: it waits, or
its equation holds. -/
theorem Pred.improveArgs_inst {c : Cls} {args : List Ty} {φ : Subst} {q₀ : Pred} (hc : c ≠ .plus)
    (hq : PredEq ⟨c, args.map (·.subst φ)⟩ q₀) (hi : Inst q₀) :
    (Pred.improveArgs c args).Holds φ := by
  have hl := hq.2.1
  cases hi with
  | plusNumber => exact absurd hq.1 hc
  | plusString => exact absurd hq.1 hc
  | @hasProp l ls fs k₀ σ₀ hf =>
    match args, hl with
    | [t, κ, σ], _ =>
      obtain ⟨rfl, ht, hκ, hσ⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, hz⟩
      · simp [ha, Ty.isVar] at hnv
      obtain ⟨x, hx, hxe⟩ := Ty.field_zip hxl hz hf
      simp only [hxs, Pred.decide₀, hx, Improve.Holds, Ty.subst_app, List.map_cons, List.map_nil]
      exact hxe.trans (TyEq.slot_mk (TyEq.refl _) hκ.symm hσ.symm)
  | @mergeData τ₀ s₀ =>
    match args, hl with
    | [q, k, τ, s, r], _ =>
      obtain ⟨rfl, hq', hk, hτ, -, hr⟩ := PredEq.five hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq hq' with ⟨a, ha⟩ | hpre
      · simp [ha, Ty.isVar] at hnv
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkd
      · simp [hpre, Pred.decide₀, Pred.decidePre, ha, Improve.Holds]
      simp only [hpre, Pred.decide₀, Pred.decidePre, hkd, Improve.Holds, Ty.subst_app,
        List.map_cons, List.map_nil]
      exact hr.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ.symm)
  | @mergeGetter τ₀ s₀ =>
    match args, hl with
    | [q, k, τ, s, r], _ =>
      obtain ⟨rfl, hq', hk, hτ, -, hr⟩ := PredEq.five hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq hq' with ⟨a, ha⟩ | hpre
      · simp [ha, Ty.isVar] at hnv
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkd
      · simp [hpre, Pred.decide₀, Pred.decidePre, ha, Improve.Holds]
      simp only [hpre, Pred.decide₀, Pred.decidePre, hkd, Improve.Holds, Ty.subst_app,
        List.map_cons, List.map_nil]
      exact hr.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ.symm)
  | @mergeAbs s₀ r₀ k₀ τ₀ hcp =>
    match args, hl with
    | [q, k, τ, s, r], _ =>
      obtain ⟨rfl, hq', -, -, hs, hr⟩ := PredEq.five hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq hq' with ⟨a, ha⟩ | habs
      · simp [ha, Ty.isVar] at hnv
      simp only [habs, Pred.decide₀]
      exact Pred.decideCopy_complete hcp hs hr
  | @mergeProto s₀ r₀ τ₀ hcp =>
    match args, hl with
    | [q, k, τ, s, r], _ =>
      obtain ⟨rfl, hq', hk, -, hs, hr⟩ := PredEq.five hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq hq' with ⟨a, ha⟩ | hpre
      · simp [ha, Ty.isVar] at hnv
      rcases Ty.whnf_con_of_tyEq hk with ⟨a, ha⟩ | hkp
      · simp [hpre, Pred.decide₀, Pred.decidePre, ha, Improve.Holds]
      simp only [hpre, Pred.decide₀, Pred.decidePre, hkp]
      exact Pred.decideCopy_complete hcp hs hr
  | @lengthArray τ₀ =>
    match args, hl with
    | [t, κ, σ], _ =>
      obtain ⟨rfl, ht, hκ, hσ⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, -⟩
      · simp [ha, Ty.isVar] at hnv
      match xs, hxl with
      | [x], _ =>
        simp only [hxs, Pred.decide₀, ↓reduceIte, Improve.Holds, Ty.subst_app, List.map_cons,
          List.map_nil]
        exact TyEq.tuple₂ hκ hσ
  | lengthString =>
    match args, hl with
    | [t, κ, σ], _ =>
      obtain ⟨rfl, ht, hκ, hσ⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq ht with ⟨a, ha⟩ | hstr
      · simp [ha, Ty.isVar] at hnv
      simp only [hstr, Pred.decide₀, ↓reduceIte, Improve.Holds, Ty.subst_app, List.map_cons,
        List.map_nil]
      exact TyEq.tuple₂ hκ hσ
  | @indexArray τ₀ =>
    match args, hl with
    | [t, i, e], _ =>
      obtain ⟨rfl, ht, hi, he⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, hz⟩
      · simp [ha, Ty.isVar] at hnv
      match xs, hxl with
      | [x], _ =>
        have hx : TyEq (x.subst φ) τ₀ := hz (x, τ₀) (by simp)
        simp only [hxs, Pred.decide₀, Improve.Holds, Ty.subst_app, List.map_cons, List.map_nil]
        exact TyEq.tuple₂ hi (he.trans hx.symm)
  | indexString =>
    match args, hl with
    | [t, i, e], _ =>
      obtain ⟨rfl, ht, hi, he⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_con_of_tyEq ht with ⟨a, ha⟩ | hstr
      · simp [ha, Ty.isVar] at hnv
      simp only [hstr, Pred.decide₀, Improve.Holds, Ty.subst_app, List.map_cons, List.map_nil]
      exact TyEq.tuple₂ hi he
  | @writeArray τ₀ =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, -⟩
      · simp [ha, Ty.isVar] at hnv
      match xs, hxl with
      | [x], _ =>
        simp only [hxs, Pred.decide₀, Improve.Holds]
        exact TyEq.refl _
  | @notNew c₀ xs₀ hc₀ =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, -, -⟩
      · simp [ha, Ty.isVar] at hnv
      simp only [hxs, Pred.decide₀, hc₀, ↓reduceIte, Improve.Holds]
      exact TyEq.refl _
  | @injectSelf T hT =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_inject]
      exact Pred.decideInject_self hT ht (by simpa using hnv)
  | @injectNothing T z σ₀ hTm hT =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_inject]
      exact Pred.decideInject_nothing hT hTm ht (by simpa using hnv)
  | @injectSome T z c₀ a₀ hTm hT _ hc₀ hn₀ =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_inject]
      exact Pred.decideInject_some hT hTm hc₀ hn₀ ht (by simpa using hnv)
  | injectArm hT hw hn htag hi hR he _ =>
    match args, hl with
    | [t], _ =>
      obtain ⟨rfl, ht⟩ := PredEq.one hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_inject]
      exact Pred.decideInject_arm hT hw hn htag hi hR he ht (by simpa using hnv)
  | @stripSome z σ₀ =>
    match args, hl with
    | [t, s], _ =>
      obtain ⟨rfl, ht, hs⟩ := PredEq.two hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_strip]
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, hxl, hz⟩
      · simp [ha, Ty.isVar] at hnv
      match xs, hxl with
      | [x], _ =>
        rw [hxs]
        simp only [Pred.decideStrip, Improve.Holds]
        exact hs.trans (hz (x, σ₀) (by simp)).symm
  | @stripSelf c₀ a₀ hm hn hu =>
    match args, hl with
    | [t, s], _ =>
      obtain ⟨rfl, ht, hs⟩ := PredEq.two hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rw [Pred.decide₀_strip]
      rcases Ty.whnf_app_of_tyEq ht with ⟨a, ha⟩ | ⟨xs, hxs, -, -⟩
      · simp [ha, Ty.isVar] at hnv
      have hW : TyEq ((Ty.app c₀ xs).subst φ) (.app c₀ a₀) := by
        rw [← hxs]; exact ((TyEq.whnf t).subst φ).trans ht
      rw [hxs, Pred.decideStrip_app hm hn hu]
      exact hs.trans hW.symm
  | @caseHit ts i t₀ Rs R₀ l₀ hnd hi hR =>
    match args, hl with
    | [τ, σ, ρ], _ =>
      obtain ⟨rfl, hτ, hσ, hρ⟩ := PredEq.three hq
      rw [Pred.improveArgs_cons]
      split
      · simp [Cls.arity, Improve.Holds]
      rename_i hnv
      rcases Ty.whnf_app_of_tyEq hτ with ⟨a, ha⟩ | ⟨xs, hxs, hxl, hz⟩
      · simp [ha, Ty.isVar] at hnv
      have hil : i < xs.length := by rw [hxl]; exact (List.getElem?_eq_some_iff.mp hR).1
      have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hil
      have hxR : TyEq (xs[i].subst φ) R₀ :=
        hz (xs[i], R₀) (List.mem_iff_getElem?.mpr ⟨i, by simp [List.getElem?_zip_eq_some, hx, hR]⟩)
      have hrest : TyEq ((variantRest l₀ (ts.eraseIdx i) (xs.eraseIdx i)).subst φ)
          (variantRest l₀ (ts.eraseIdx i) (Rs.eraseIdx i)) := by
        rw [variantRest_subst, ← eraseIdx_map]
        refine variantRest_tyEq (by simp [List.length_eraseIdx, hxl]) (fun p hp => ?_)
        have := zip_eraseIdx_mem (xs.map (·.subst φ)) Rs i (by simp [hxl]) p hp
        rw [List.zip_map_left] at this
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
        exact hz q hq
      simp only [hxs, Pred.decide₀, Pred.decideCase, hnd, and_self, ↓reduceIte,
        firstIdx_of_nodup hnd hi, hx, Improve.Holds, Ty.subst_app, List.map_cons, List.map_nil]
      exact TyEq.tuple₂ (hσ.trans hxR.symm) (hρ.trans hrest.symm)

theorem Pred.improve_of_args {top : Bool} {c : Cls} {args : List Ty} {φ : Subst}
    (h : c ≠ .plus → (c = .merge → top = true) → (Pred.improveArgs c args).Holds φ) :
    (Pred.improve top ⟨c, args⟩).Holds φ := by
  cases c <;> simp only [Pred.improve]
  case plus => trivial
  case merge =>
    cases top
    · trivial
    · exact h (by simp) (fun _ => rfl)
  all_goals exact h (by simp) (by simp)

theorem Pred.improve_inst {top : Bool} {p : Pred} {φ : Subst} {q₀ : Pred}
    (hq : PredEq (p.subst φ) q₀) (hi : Inst q₀) : (p.improve top).Holds φ := by
  obtain ⟨c, args⟩ := p
  exact Pred.improve_of_args (fun hc _ => Pred.improveArgs_inst hc hq hi)

def Pred.OnVarShaped (p : Pred) : Prop :=
  (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
    ∃ q k τ s r, p = ⟨.merge, [q, k, τ, s, r]⟩ ∧ ((∃ a, q = .var a) ∨ p.MergeOnVar)

/-- What an assumption may be where improvement decides constraints, at the
top level (`top`) or where a binding generalises: on a type variable, as
a simple scheme's constraints are once opened, or, where a binding
generalises, any `Merge`, since a scheme's `Merge` may have a known
presence (`Scheme.Simple`) and improvement there leaves every `Merge` as
it is. -/
def Pred.AssumableAt (top : Bool) (p : Pred) : Prop :=
  (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
    ∃ q k τ s r, p = ⟨.merge, [q, k, τ, s, r]⟩ ∧
      (top = true → (∃ a, q = .var a) ∨ p.MergeOnVar)

theorem Pred.OnVarShaped.assumable {p : Pred} (h : p.OnVarShaped) (top : Bool) :
    p.AssumableAt top := by
  rcases h with h | ⟨q, k, τ, s, r, rfl, h⟩
  · exact .inl h
  · exact .inr ⟨_, _, _, _, _, rfl, fun _ => h⟩

/-- An assumption improvement can't decide: a constraint equal to one waits. -/
theorem Pred.improve_assumable {top : Bool} {p c : Pred} {φ : Subst} (hc : c.AssumableAt top)
    (hq : PredEq (p.subst φ) c) : (p.improve top).Holds φ := by
  obtain ⟨cls, args⟩ := p
  refine Pred.improve_of_args (fun hcp hm => ?_)
  rcases hc with ⟨hcm, hl, a, rest, he⟩ | ⟨q, k, τ, s, r, rfl, hv⟩
  · obtain ⟨c, cargs⟩ := c
    obtain ⟨hcls, hlen, hz⟩ := hq
    simp only [Pred.subst] at hcls hlen hz he hl hcm
    subst hcls he
    match args, hlen with
    | t :: rest', hlen =>
      obtain ⟨b, hb⟩ := Ty.whnf_var_of_tyEq (hz (t.subst φ, .var a) (by simp))
      simp only [List.length_map, List.length_cons] at hlen hl
      simp [Pred.improveArgs_cons, hb, Ty.isVar, Improve.Holds, ← hl, hlen]
  · obtain ⟨hcls, hlen, hz⟩ := hq
    simp only [Pred.subst] at hcls hlen hz
    subst hcls
    match args, hlen with
    | [q', k', τ', s', r'], _ =>
      rcases hv (hm rfl) with ⟨a, rfl⟩ | hmv
      · obtain ⟨b, hb⟩ := Ty.whnf_var_of_tyEq (hz (q'.subst φ, .var a) (by simp))
        simp [Pred.improveArgs_cons, hb, Ty.isVar, Improve.Holds, Cls.arity]
      · have hpe : PredEq (Pred.subst φ ⟨.merge, [q', k', τ', s', r']⟩)
            ⟨.merge, [q, k, τ, s, r]⟩ := ⟨rfl, by simp [Pred.subst], hz⟩
        rw [Pred.improveArgs_merge_keep (φ := φ) (hmv.predEq hpe.symm)]
        trivial

/-- Improvement is right for whatever entailed constraints, by assumptions
it can't decide. -/
theorem Pred.improve_complete {top : Bool} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top)
    {p : Pred} {φ : Subst} (h : Entails C (p.subst φ)) : (p.improve top).Holds φ := by
  rcases h with ⟨q₀, hq, hi⟩ | ⟨c, hc, hq⟩
  · exact Pred.improve_inst hq hi
  · exact Pred.improve_assumable (hC c hc) hq

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
assumptions it can't decide, with a substitution any satisfying one
absorbs; what it leaves is still satisfied, and can't be improved further. -/
theorem improveAll_complete {top : Bool} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) :
    ∀ (k : Nat) {ps : List Pred} {φ : Subst}, ps.length ≤ k → Sat C ps φ →
      ∃ σ ps', improveAll top k ps = some (σ, ps') ∧ Absorbs φ σ ∧ Sat C ps' φ ∧
        (∀ p ∈ ps', p.improve top = .keep) ∧ (∀ p ∈ ps', ∃ q ∈ ps, p = q.subst σ)
  | 0, ps, φ, hk, hs => by
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], [], by simp [improveAll], fun τ => by simp; exact TyEq.refl _, by simp, by simp,
      by simp⟩
  | k + 1, ps, φ, hk, hs => by
    cases hone : improveOne top ps with
    | none =>
      obtain ⟨p, hp, hf⟩ := improveOne_none hone
      have := Pred.improve_complete hC (hs p hp)
      rw [hf] at this; exact this.elim
    | some r =>
      cases r with
      | none =>
        exact ⟨[], ps, by simp [improveAll, hone], fun τ => by simp; exact TyEq.refl _, hs,
          improveOne_keep hone, fun p hp => ⟨p, hp, by simp⟩⟩
      | some er =>
        obtain ⟨⟨a, b⟩, rest⟩ := er
        obtain ⟨⟨p', hp'm, hp'⟩, hsub⟩ := improveOne_sub hone
        have hab : TyEq (a.subst φ) (b.subst φ) := by
          have := Pred.improve_complete hC (hs p' hp'm)
          rw [hp'] at this; exact this
        obtain ⟨σu, hu, habs⟩ := unify_mgu hab
        have hlen := improveOne_length hone
        obtain ⟨σ', ps', h', habs', hs', hkeep, hfrom⟩ := improveAll_complete hC k
          (ps := rest.map (·.subst σu)) (φ := φ) (by simp; omega)
          (Sat.absorb habs (fun q hq => hs q (hsub q hq)))
        refine ⟨Subst.compose σ' σu, ps', ?_, Absorbs.compose habs habs', hs', hkeep,
          fun p hp => ?_⟩
        · simp [improveAll, hone, hu, h']
        · obtain ⟨q, hq, rfl⟩ := hfrom p hp
          obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
          exact ⟨q₀, hsub q₀ hq₀, by simp [Pred.subst_compose]⟩

/-! ## Equal lists of types -/

/-- Two lists of pairwise equal types. -/
inductive TyEqs : List Ty → List Ty → Prop
  | nil : TyEqs [] []
  | cons {x y : Ty} {xs ys : List Ty} : TyEq x y → TyEqs xs ys → TyEqs (x :: xs) (y :: ys)

theorem TyEqs.zip_of : ∀ {xs ys : List Ty}, TyEqs xs ys →
    xs.length = ys.length ∧ ∀ x ∈ xs.zip ys, TyEq x.1 x.2
  | [], [], _ => ⟨rfl, by simp⟩
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨hl, hz⟩ := TyEqs.zip_of hs
    refine ⟨by simp [hl], fun x hx => ?_⟩
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h
    · exact hz x hx

theorem TyEqs.of_zip : ∀ {xs ys : List Ty}, xs.length = ys.length →
    (∀ x ∈ xs.zip ys, TyEq x.1 x.2) → TyEqs xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h =>
    .cons (h (x, y) (by simp)) (TyEqs.of_zip (by simpa using hl)
      (fun z hz => h z (List.mem_cons_of_mem _ hz)))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem TyEqs.refl : ∀ (xs : List Ty), TyEqs xs xs
  | [] => .nil
  | x :: xs => .cons (TyEq.refl x) (TyEqs.refl xs)

theorem TyEqs.trans : ∀ {xs ys zs : List Ty}, TyEqs xs ys → TyEqs ys zs → TyEqs xs zs
  | [], [], [], _, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')

theorem TyEqs.symm : ∀ {xs ys : List Ty}, TyEqs xs ys → TyEqs ys xs
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => .cons h.symm hs.symm

theorem TyEqs.length {xs ys : List Ty} (h : TyEqs xs ys) : xs.length = ys.length :=
  h.zip_of.1

theorem TyEq.app_eqs {c : Con} {xs ys : List Ty} (h : TyEqs xs ys) :
    TyEq (.app c xs) (.app c ys) :=
  TyEq.app h.zip_of.1 h.zip_of.2

theorem TyEq.fn_mk {θ θ' ρ ρ' : Ty} {τs τs' : List Ty} (hθ : TyEq θ θ') (hρ : TyEq ρ ρ')
    (h : TyEqs τs τs') : TyEq (.fn θ τs ρ) (.fn θ' τs' ρ') :=
  TyEq.app_eqs (.cons hθ (.cons hρ h))

theorem CtxEq.append_left : ∀ (Δ : Ctx) {Γ Γ' : Ctx}, CtxEq Γ Γ' → CtxEq (Δ ++ Γ) (Δ ++ Γ')
  | [], _, _, h => h
  | s :: Δ, _, _, h => CtxEq.cons (SchemeEq.refl s) (CtxEq.append_left Δ h)

theorem LitTy.eq_ty {l : Lit} {τ : Ty} (h : LitTy l τ) : τ = l.ty := by cases h <;> rfl

/-! ## Completeness -/

/-- A derivation's mode and type, as the expected type `ex` gives them: in
check mode at `ex` if `e` takes it in (`Expr.pushes`), synthesised
otherwise. -/
def ExMatch (ex : Option Ty) (e : Expr) (md : Mode) (τ : Ty) : Prop :=
  md = exMode ex e ∧ ∀ T ∈ ex, e.pushes T → τ = T

theorem ExMatch.none {e : Expr} {τ : Ty} : ExMatch none e .synth τ := ⟨rfl, fun _ h => nomatch h⟩

/-- `RetOk`'s return type, as a derivation of a subexpression sees it. -/
theorem RetOk.eq_subst {rm : Mode} {R R' : Option Ty} (hRo : RetOk rm R)
    (hRc : rm = .check → R' = R) (σ : Subst) : rm = .check → R' = Ret.subst σ R := fun hm => by
  rw [hRc hm]; subst hm; exact (hRo.subst_eq σ).symm

/-- Proves `rm = .check → R' = R₁` for `R₁` the return type `R` of
assumptions `RetOk rm R` and `rm = .check → R' = R`, substituted. -/
macro "ret_eq" : tactic =>
  `(tactic| first
    | assumption
    | exact RetOk.eq_subst ‹_› ‹_› _
    | exact RetOk.eq_subst (RetOk.subst ‹_› _) (RetOk.eq_subst ‹_› ‹_› _) _
    | exact RetOk.eq_subst (RetOk.subst (RetOk.subst ‹_› _) _)
        (RetOk.eq_subst (RetOk.subst ‹_› _) (RetOk.eq_subst ‹_› ‹_› _) _) _
    | (intro h; cases h))

mutual
/-- Whether every annotation in a program is monomorphic. Inference is
complete for such programs (`infer_complete`). With polymorphic ones it is
complete where no rigid type variable escapes (`Expr.PolyOK`,
`infer_complete_polyOK`), and not elsewhere (`polyGap`). -/
def Expr.monoAnn : Expr → Bool
  | .lit _ | .var _ | .break_ | .continue_ => true
  | .func _ body | .ctor _ body => body.monoAnn
  | .app f args | .mcall f _ args | .new_ f args => f.monoAnn && Expr.monoAnnList args
  | .let_ _ ann e₁ e₂ => (ann.all fun a => a.arity == 0) && e₁.monoAnn && e₂.monoAnn
  | .assign _ e | .unop _ e | .ret e | .throw_ e | .get e _ => e.monoAnn
  | .cond c t e | .setIndex c t e | .unwrap c t e | .caseTag c _ _ t e =>
    c.monoAnn && t.monoAnn && e.monoAnn
  | .binop _ e₁ e₂ | .seq e₁ e₂ | .while_ e₁ e₂ | .tryFinally e₁ e₂ | .spread e₁ e₂
  | .index e₁ e₂ | .tryCatch e₁ e₂ | .set e₁ _ e₂ => e₁.monoAnn && e₂.monoAnn
  | .obj _ es _ | .arr es | .cls _ es _ => Expr.monoAnnList es
/-- `monoAnn`, for a list of expressions. -/
def Expr.monoAnnList : List Expr → Bool
  | [] => true
  | e :: es => e.monoAnn && Expr.monoAnnList es
end

@[simp] theorem Expr.monoAnnList_eq (es : List Expr) : Expr.monoAnnList es = es.all Expr.monoAnn := by
  induction es <;> simp_all [Expr.monoAnnList]

/-- At a polymorphic annotation `a` on the initialiser `e₁`, inference's
escape check passes wherever the rules type `e₁`: in every context in which
`e₁` has the annotation's type at every rigid name outside a finite set,
checking `e₁` against `a` at inference's fresh rigid variables `k` and
deciding what improvement can leaves `k` in neither the context, the return
type, nor a constraint left. Inference rejects the program where it doesn't,
and can miss a typing there (`polyGap`): a constraint on `k` that waits on a
type variable would need an implication constraint to keep, as in
OutsideIn(X). In such a context `k` is never in the tree of a context
variable's instance (`infer_complete_letPoly`), so the check can fire there
only on a constraint left, or on a recursive type's unreached equation. -/
def RigidStays (L : List String) (a : Scheme) (e₁ : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {n : Nat} {ψ : Subst} {C : List Pred} {Γ' : Ctx}
    {R' : Option Ty} {K : List Nat} {o₁ : Out} {σi : Subst} {preds₁ : List Pred},
    RetOk rm R → (rm = .check → R' = R) → Ctx.Below n Γ → Ret.Below n R →
    (∀ p ∈ C, p.AssumableAt false) → CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) →
    (∀ k, k ∉ K → HasType L C Γ' R' rm .check e₁ (a.inst (rigids k a.arity))) →
    (infer L Γ R rm (some (a.inst (rigids (maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R)) a.arity))) e₁
      n).map (checkEx (some (a.inst (rigids (maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R)) a.arity))) e₁) =
      some o₁ →
    improveAll false o₁.preds.length o₁.preds = some (σi, preds₁) →
    maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ ctxRkeys (Ctx.subst (Subst.compose σi o₁.σ) Γ) ∧
      maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ Ret.rkeys (Ret.subst (Subst.compose σi o₁.σ) R) ∧
      maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ preds₁.flatMap Pred.rkeys

mutual
/-- Whether no rigid type variable escapes at any polymorphic annotation in a
program (`RigidStays`): inference is complete for such programs
(`infer_complete_polyOK`), which include those whose annotations are all
monomorphic (`Expr.polyOK_of_monoAnn`). -/
def Expr.PolyOK (L : List String) : Expr → Prop
  | .lit _ | .var _ | .break_ | .continue_ => True
  | .func _ body | .ctor _ body => body.PolyOK L
  | .app f args | .mcall f _ args | .new_ f args => f.PolyOK L ∧ Expr.PolyOKList L args
  | .let_ _ ann e₁ e₂ =>
    ((∀ a ∈ ann, 0 < a.arity → RigidStays L a e₁) ∧ e₁.PolyOK L) ∧ e₂.PolyOK L
  | .assign _ e | .unop _ e | .ret e | .throw_ e | .get e _ => e.PolyOK L
  | .cond c t e | .setIndex c t e | .unwrap c t e | .caseTag c _ _ t e =>
    (c.PolyOK L ∧ t.PolyOK L) ∧ e.PolyOK L
  | .binop _ e₁ e₂ | .seq e₁ e₂ | .while_ e₁ e₂ | .tryFinally e₁ e₂ | .spread e₁ e₂
  | .index e₁ e₂ | .tryCatch e₁ e₂ | .set e₁ _ e₂ => e₁.PolyOK L ∧ e₂.PolyOK L
  | .obj _ es _ | .arr es | .cls _ es _ => Expr.PolyOKList L es
/-- `PolyOK`, for a list of expressions. -/
def Expr.PolyOKList (L : List String) : List Expr → Prop
  | [] => True
  | e :: es => e.PolyOK L ∧ Expr.PolyOKList L es
end

@[simp] theorem Expr.PolyOKList_eq (L : List String) (es : List Expr) :
    Expr.PolyOKList L es ↔ ∀ e ∈ es, e.PolyOK L := by
  induction es <;> simp_all [Expr.PolyOKList]

/-- A program whose annotations are all monomorphic has no rigid type
variables to escape. -/
theorem Expr.polyOK_of_monoAnn (L : List String) : ∀ {e : Expr}, e.monoAnn = true → e.PolyOK L := by
  intro e
  induction e using Expr.ind with
  | let_ mb ann e₁ e₂ ih₁ ih₂ =>
    intro h
    simp only [Expr.monoAnn, Bool.and_eq_true] at h
    refine ⟨⟨fun a ha h0 => ?_, ih₁ h.1.2⟩, ih₂ h.2⟩
    subst ha
    simp only [Option.all, beq_iff_eq] at h
    omega
  | _ => intro h; simp_all [Expr.monoAnn, Expr.PolyOK]

/-- What `infer_complete` says of one expression: if the expression has a
type in a context equal to an instance of inference's, inference finds a
type of which it is an instance, with the constraints satisfied. -/
def InferComplete (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
    {md : Mode} {τ' : Ty} {Γ' : Ctx} {R' : Option Ty},
    RetOk rm R → (rm = .check → R' = R) → Ex.Closed ex → ExMatch ex e md τ' →
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
    CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → HasType L C Γ' R' rm md e τ' →
    ∃ o, infer L Γ R rm ex e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ TyEq (o.τ.subst φ) τ' ∧
      Sat C o.preds φ

/-- What an object literal is checked against (`ObjCase`) is what inference
checks it against. -/
theorem objTarget_complete {ls : List String} {es : List Expr} {T P : Ty} {L : List String}
    {ss : List Ty} (hc : ObjCase ls es T P) (he : TyEq P (.record L ss)) :
    objTarget T ls es = some P := by
  cases hc with
  | self =>
    obtain ⟨ys, hys, -⟩ := TyEq.whnf_app he.symm (Ty.whnf_app _ _)
    unfold objTarget; rw [hys]
  | variant hw hl hi hP ht => unfold objTarget; simp [hw, hl, hi, hP, ht]

/-- A variant's rest has the tree variables of its cases. -/
theorem variantRest_tv {d : Disc} {ts : List String} {Rs : List Ty} {b : Nat}
    (h : (variantRest d ts Rs).TV b) : ∃ R ∈ Rs, R.TV b := by
  match Rs, h with
  | [R], h => exact ⟨R, by simp, h⟩
  | [], h => exact Ty.tv_app.mp h
  | _ :: _ :: _, h => exact Ty.tv_app.mp h

/-- A check-mode derivation of an expression that doesn't take the expected
type in injects a synthesised type into it, or drops it (into `unknown`). -/
theorem HasTypeS.inj_inv {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {e : Expr} {T : Ty} (h : HasType L C Γ R rm .check e T) (hp : e.pushes T = false) :
    ∃ τ₀, HasType L C Γ R rm .synth e τ₀ ∧ (T = .unknown ∨ Entails C ⟨.inject T, [τ₀]⟩) := by
  cases h with
  | inj h _ hi => exact ⟨_, h, .inr hi⟩
  | drop h => exact ⟨_, h, .inl rfl⟩
  | funcCheck hw _ hlen _ => simp [Expr.pushes, funcTarget, hw, hlen] at hp
  | arrCheck hw _ _ => simp [Expr.pushes, arrTarget, hw] at hp
  | litStr hw => simp [Expr.pushes, hw] at hp
  | objCheck hc hnd hk _ _ _ he _ => simp [Expr.pushes, objTarget_complete hc he, hnd, hk] at hp
  | _ => simp [Expr.pushes] at hp

/-- Inferring `e` against `ex`, as its caller sees it (`checkEx`), is
complete: for a derivation in check mode at `ex`, if it is given. -/
theorem InferComplete.check {e : Expr} (ih : InferComplete L e) {Γ : Ctx} {R : Option Ty}
    {rm : Mode} {ex : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred} {τ' : Ty} {Γ' : Ctx}
    {R' : Option Ty} (hRo : RetOk rm R) (hRc : rm = .check → R' = R) (hex : Ex.Closed ex)
    (hτ : ∀ T ∈ ex, τ' = T) (hΓ : Ctx.Below n Γ) (hR : Ret.Below n R)
    (hC : ∀ p ∈ C, p.AssumableAt false) (hΓ' : CtxEq Γ' (Ctx.subst ψ Γ))
    (hR' : RetEq R' (Ret.subst ψ R)) (ht : HasType L C Γ' R' rm (Ex.mode ex) e τ') :
    ∃ o, (infer L Γ R rm ex e n).map (checkEx ex e) = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
      TyEq (o.τ.subst φ) τ' ∧ Sat C o.preds φ := by
  match ex, hex with
  | none, hex =>
    obtain ⟨o, h, φ, hag, hty, hsat⟩ := ih hRo hRc hex .none hΓ hR hC hΓ' hR' ht
    exact ⟨o, by simp [h], φ, hag, hty, hsat⟩
  | some T, hex =>
    have hT := hex T rfl
    obtain rfl := hτ T rfl
    by_cases hp : e.pushes τ'
    · obtain ⟨o, h, φ, hag, hty, hsat⟩ := ih hRo hRc hex
        ⟨by simp [exMode, hp], fun _ hT _ => by cases hT; rfl⟩ hΓ hR hC hΓ' hR' ht
      exact ⟨o, by simp [h, checkEx, hp], φ, hag, hty, hsat⟩
    · have hp' : e.pushes τ' = false := by simpa using hp
      obtain ⟨τ₀, ht₀, hi⟩ := HasTypeS.inj_inv ht hp'
      obtain ⟨o, h, φ, hag, hty, hsat⟩ := ih hRo hRc hex
        ⟨by simp [exMode, hp'], fun _ hT h => by cases hT; exact absurd h hp⟩ hΓ hR hC hΓ' hR' ht₀
      refine ⟨checkEx (some τ') e o, by simp [h], φ, by rw [checkEx_σ]; exact hag, ?_, ?_⟩
      · by_cases hu : τ' = .unknown
        · subst hu
          simp only [checkEx, hp', Bool.false_eq_true, ↓reduceIte]
          exact TyEq.refl _
        simp only [checkEx, hp', hu, Bool.false_eq_true, ↓reduceIte, Ty.closed_subst hT]
        exact TyEq.refl _
      · by_cases hu : τ' = .unknown
        · subst hu
          simp only [checkEx, hp', Bool.false_eq_true, ↓reduceIte]
          exact hsat
        replace hi := hi.resolve_left hu
        simp only [checkEx, hp', hu, Bool.false_eq_true, ↓reduceIte, Sat.append]
        refine ⟨hsat, fun c hc => ?_⟩
        simp only [List.mem_singleton] at hc; subst hc
        exact hi.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons hty.symm zip_tyEq_nil))

theorem inferArgs_complete : ∀ (args : List Expr) (τs' : List Ty), (∀ a ∈ args, InferComplete L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      RetOk rm R → (rm = .check → R' = R) → Ex.Closed ex → (∀ T ∈ ex, ∀ τ ∈ τs', τ = T) →
      Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
      CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → args.length = τs'.length →
      (∀ p ∈ args.zip τs', HasType L C Γ' R' rm (Ex.mode ex) p.1 p.2) →
      ∃ o, inferArgs L Γ R rm ex args n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
        TyEqs (o.τs.map (·.subst φ)) τs' ∧ Sat C o.preds φ
  | [], [], _, Γ, R, rm, ex, n, ψ, C, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferArgs], ψ, Agree.nil n ψ, .nil, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, τ' :: τs', ih, Γ, R, rm, ex, n, ψ, C, Γ', R', hRo, hRc, hex, hτs, hΓ, hR, hC, hΓ', hR',
      hlen, hargs => by
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check (ih a (by simp)) hRo hRc hex
      (fun T hT => hτs T hT τ' (by simp)) hΓ hR hC hΓ' hR' (hargs (a, τ') (by simp))
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := InferInv.check (infer_inv L a) hRo hex hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete as τs'
      (fun a' ha' => ih a' (by simp [ha'])) (ψ := φ₁) (hRo.subst _) (RetOk.eq_subst hRo hRc _) hex
      (fun T hT τ hτ => hτs T hT τ (by simp [hτ])) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (hΓ'.trans (hag₁.ctx hΓ).symm)
      (hR'.trans (hag₁.ret hR).symm) (by simpa using hlen) (fun p hp => hargs p (by simp [hp]))
    refine ⟨_, by simp only [inferArgs, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
    · simp only [List.map_cons]
      exact .cons ((hag₂.ty hτb₁).trans hτ₁) hτs₂
    · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂

/-- Inferring an object literal's fields, each against its type with no
type variables, is complete. -/
theorem inferFields_complete : ∀ (es : List Expr) (τs : List Ty), (∀ a ∈ es, InferComplete L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      RetOk rm R → (rm = .check → R' = R) → (∀ τ ∈ τs, τ.ftv = []) →
      Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
      CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → es.length = τs.length →
      (∀ p ∈ es.zip τs, HasType L C Γ' R' rm .check p.1 p.2) →
      ∃ o, inferFields L Γ R rm es τs n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ Sat C o.preds φ
  | [], [], _, Γ, R, rm, n, ψ, C, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferFields], ψ, Agree.nil n ψ, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, τ :: τs, ih, Γ, R, rm, n, ψ, C, Γ', R', hRo, hRc, hτs, hΓ, hR, hC, hΓ', hR',
      hlen, hargs => by
    have hτ := hτs τ (by simp)
    obtain ⟨o₁, h₁, φ₁, hag₁, -, hsat₁⟩ := InferComplete.check (ih a (by simp)) hRo hRc
      (Ex.Closed.some hτ) (fun T hT => by cases hT; rfl) hΓ hR hC hΓ' hR'
      (by simpa using hargs (a, τ) (by simp))
    obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check (infer_inv L a) hRo (Ex.Closed.some hτ) hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hsat₂⟩ := inferFields_complete as τs
      (fun a' ha' => ih a' (by simp [ha'])) (ψ := φ₁) (hRo.subst _) (RetOk.eq_subst hRo hRc _)
      (fun τ' h' => hτs τ' (by simp [h'])) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (hΓ'.trans (hag₁.ctx hΓ).symm)
      (hR'.trans (hag₁.ret hR).symm) (by simpa using hlen) (fun p hp => hargs p (by simp [hp]))
    exact ⟨_, by simp only [inferFields, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂,
      Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

theorem PredEq.of_eqs {c : Cls} {xs ys : List Ty} (h : TyEqs xs ys) : PredEq ⟨c, xs⟩ ⟨c, ys⟩ :=
  ⟨rfl, h.zip_of.1, h.zip_of.2⟩

theorem Agree.below {n : Nat} {σ φ ψ : Subst} (h : Agree n σ φ ψ) {k : Nat} (hk : k ≤ n)
    {τ : Ty} (hτ : τ.Below k) : TyEq ((τ.subst σ).subst φ) (τ.subst ψ) := h.ty (hτ.mono hk)

/-- For a constructor's body: the parameters from `n`, the result after them,
and `ψ` below. -/
def ctorSubst (n : Nat) (τs : List Ty) (ρ : Ty) (ψ : Subst) : Subst :=
  Subst.block n τs ++ ((n + τs.length, ρ) :: ψ)

theorem ctorSubst_below {n : Nat} {ρ : Ty} {τs : List Ty} {ψ : Subst} {a : Nat} (h : a < n) :
    (ctorSubst n τs ρ ψ).find a = ψ.find a := by
  have h₂ : a ≠ n + τs.length := by omega
  simp [ctorSubst, Subst.find, h₂, Subst.find_append, Subst.block_find_none h]

theorem ctorSubst_params {n : Nat} {ρ : Ty} {τs : List Ty} {ψ : Subst} :
    (varBlock n τs.length).map (·.subst (ctorSubst n τs ρ ψ)) = τs :=
  varBlock_subst_block n τs _

theorem ctorSubst_ret {n : Nat} {ρ : Ty} {τs : List Ty} {ψ : Subst} :
    (Ty.var (n + τs.length)).subst (ctorSubst n τs ρ ψ) = ρ := by
  simp [ctorSubst, Ty.subst, Subst.find, Subst.find_append,
    Subst.block_find_ge (show n + τs.length ≤ n + τs.length from Nat.le_refl _)]

/-! ### Object literals -/

/-- A function expression's type is a function type with its parameters. -/
def FnShaped (es : List Expr) (τs : List Ty) : Prop :=
  ∀ (i k : Nat) (b : Expr) (τ : Ty), es[i]? = some (Expr.func k b) → τs[i]? = some τ →
    ∃ (θ : Ty) (ps : List Ty) (ρ : Ty), τ = Ty.fn θ ps ρ ∧ ps.length = k

theorem FnShaped.cons {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty}
    (h : ∀ k b, e = .func k b → ∃ θ ps ρ, τ = .fn θ ps ρ ∧ ps.length = k)
    (hs : FnShaped es τs) : FnShaped (e :: es) (τ :: τs) := by
  intro i k b τ' he hτ
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hτ
    subst hτ; exact h k b he
  | succ i => exact hs i k b τ' (by simpa using he) (by simpa using hτ)

theorem FnShaped.tail {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty}
    (h : FnShaped (e :: es) (τ :: τs)) : FnShaped es τs :=
  fun i k b τ' he hτ => h (i + 1) k b τ' (by simpa using he) (by simpa using hτ)

theorem FnShaped.head {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty}
    (h : FnShaped (e :: es) (τ :: τs)) {k : Nat} {b : Expr} (he : e = .func k b) :
    ∃ θ ps ρ, τ = .fn θ ps ρ ∧ ps.length = k :=
  h 0 k b τ (by simp [he]) rfl

theorem FnShaped.subst {es : List Expr} {τs : List Ty} (h : FnShaped es τs) (σ : Subst) :
    FnShaped es (τs.map (·.subst σ)) := by
  intro i k b τ he hτ
  rw [List.getElem?_map] at hτ
  cases hτ' : τs[i]? with
  | none => rw [hτ'] at hτ; cases hτ
  | some τ₀ =>
    rw [hτ'] at hτ; simp only [Option.map_some, Option.some.injEq] at hτ; subst hτ
    obtain ⟨θ, ps, ρ, rfl, hl⟩ := h i k b τ₀ he hτ'
    exact ⟨_, _, _, Ty.subst_fn _ _ _ _, by simpa using hl⟩

theorem infer_func_shape {Γ : Ctx} {R : Option Ty} {rm : Mode} {k : Nat} {b : Expr} {n : Nat}
    {o : Out} (h : infer L Γ R rm none (.func k b) n = some o) :
    ∃ θ ps ρ, o.τ = .fn θ ps ρ ∧ ps.length = k := by
  simp only [infer, funcTarget] at h
  split at h
  · cases h
  split at h
  · cases h
  simp only [Option.some.injEq] at h; subst h
  exact ⟨_, _, _, Ty.subst_fn _ _ _ _, by simp [varBlock]⟩

theorem inferArgs_shape : ∀ {es : List Expr} {Γ : Ctx} {R : Option Ty} {rm : Mode} {n : Nat}
    {o : OutArgs}, inferArgs L Γ R rm none es n = some o → FnShaped es o.τs
  | [], _, _, _, _, o, h => by
    simp only [inferArgs, Option.some.injEq] at h; subst h
    intro i k b τ he; simp at he
  | e :: es, Γ, R, rm, n, o, h => by
    simp only [inferArgs, checkEx_none, Option.map_id] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    refine FnShaped.cons (fun k b he => ?_) (inferArgs_shape h₂)
    subst he
    obtain ⟨θ, ps, ρ, hτ, hl⟩ := infer_func_shape h₁
    exact ⟨_, _, _, by rw [hτ, Ty.subst_fn], by simpa using hl⟩

theorem TyEq.fn_inv {θ θ' ρ ρ' : Ty} {ps ps' : List Ty} (h : TyEq (.fn θ ps ρ) (.fn θ' ps' ρ')) :
    TyEq θ θ' ∧ TyEq ρ ρ' ∧ TyEqs ps ps' := by
  obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp h
  have := TyEqs.of_zip hl hz
  cases this with
  | cons h₁ hs =>
    cases hs with
    | cons h₂ hs => exact ⟨h₁, h₂, hs⟩

/-- An object literal's slots, from types equal under `φ` to a typing's. -/
theorem fieldSlots_complete {T' : Ty} {φ : Subst} : ∀ {ks : List FieldKind} {es : List Expr}
    {τs τs' ss' : List Ty}, FnShaped es τs → TyEqs (τs.map (·.subst φ)) τs' →
    ks.length = es.length → es.length = τs.length → ss'.length = τs'.length →
    (∀ x ∈ ks.zip (es.zip (τs'.zip ss')), FieldSlot T' x.1 x.2.1 x.2.2.1 x.2.2.2) →
    ∃ θs ss, fieldSlots ks es τs = some (θs, ss) ∧ TyEqs (ss.map (·.subst φ)) ss' ∧
      ∀ θ ∈ θs, TyEq (θ.subst φ) T'
  | [], [], [], [], [], _, _, _, _, _, _ => ⟨[], [], rfl, .nil, by simp⟩
  | k :: ks, e :: es, τ :: τs, τ' :: τs', s' :: ss', hsh, hτs, hk, he, hs, hf => by
    cases hτs with
    | cons hτ hτs =>
    obtain ⟨θs, ss, h, hss, hθs⟩ := fieldSlots_complete hsh.tail hτs (by simpa using hk)
      (by simpa using he) (by simpa using hs) (fun x hx => hf x (by simp [hx]))
    have hf₀ := hf (k, e, τ', s') (by simp)
    simp only at hf₀
    cases hf₀ with
    | data =>
      refine ⟨θs, .slot .pre .data τ :: ss, by simp [fieldSlots, h], .cons ?_ hss, hθs⟩
      exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ
    | @method θ' n b τs'' ρ' hθ =>
      obtain ⟨θ, ps, ρ, rfl, -⟩ := hsh.head rfl
      refine ⟨θ :: θs, .slot .pre .data (.fn θ ps ρ) :: ss, by simp [fieldSlots, h],
        .cons (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ) hss, ?_⟩
      intro θ₁ hθ₁
      rcases List.mem_cons.mp hθ₁ with rfl | hθ₁
      · simp only [Ty.subst_fn] at hτ; exact (TyEq.fn_inv hτ).1.trans hθ
      · exact hθs θ₁ hθ₁
    | @getter θ' b σ' hθ =>
      obtain ⟨θ, ps, ρ, rfl, hl⟩ := hsh.head rfl
      obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hl
      simp only [Ty.subst_fn] at hτ
      obtain ⟨h₁, h₂, -⟩ := TyEq.fn_inv hτ
      refine ⟨θ :: θs, .slot .pre .getter ρ :: ss, by simp [fieldSlots, h],
        .cons (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) h₂) hss, ?_⟩
      intro θ₁ hθ₁
      rcases List.mem_cons.mp hθ₁ with rfl | hθ₁
      · exact h₁.trans hθ
      · exact hθs θ₁ hθ₁
  | [], _ :: _, _, _, _, _, _, hk, _, _, _ | _ :: _, [], _, _, _, _, _, hk, _, _, _ => by
    simp at hk
  | _, [], _ :: _, _, _, _, _, _, he, _, _ | _, _ :: _, [], _, _, _, _, _, he, _, _ => by
    simp at he
  | _, _, [], _ :: _, _, _, hτs, _, _, _, _ | _, _, _ :: _, [], _, _, hτs, _, _, _, _ => by
    cases hτs
  | _, _, _, [], _ :: _, _, _, _, _, hs, _ | _, _, _, _ :: _, [], _, _, _, _, hs, _ => by
    simp at hs

/-- `this` types equal under `φ` to the literal's type: their unifier. -/
theorem unifyThis_complete {θs : List Ty} {T : Ty} {φ : Subst}
    (h : ∀ θ ∈ θs, TyEq (θ.subst φ) (T.subst φ)) :
    ∃ σ, unifyThis θs T = some σ ∧ Absorbs φ σ := by
  match θs, h with
  | [], _ => exact ⟨[], rfl, fun τ => by simp; exact TyEq.refl _⟩
  | θ :: θs, h =>
    have h₁ : TyEq ((Ty.tuple (θ :: θs)).subst φ)
        ((Ty.tuple (List.replicate (θs.length + 1) θ)).subst φ) := by
      simp only [Ty.subst_app, List.map_replicate]
      refine TyEq.app_eqs (TyEqs.of_zip (by simp) (fun x hx => ?_))
      obtain ⟨y, z⟩ := x
      have hz : z = θ.subst φ := List.eq_of_mem_replicate (List.of_mem_zip hx).2
      obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip hx).1
      subst hz
      exact (h y₀ hy₀).trans (h θ List.mem_cons_self).symm
    obtain ⟨σ₁, hu₁, habs₁⟩ := unify_mgu h₁
    have h₂ : TyEq ((θ.subst σ₁).subst φ) ((T.subst σ₁).subst φ) :=
      (habs₁ _).trans ((h θ List.mem_cons_self).trans (habs₁ _).symm)
    obtain ⟨σ₂, hu₂, habs₂⟩ := unify_mgu h₂
    exact ⟨Subst.compose σ₂ σ₁, by simp [unifyThis, hu₁, hu₂], Absorbs.compose habs₁ habs₂⟩

theorem TyEqs.append : ∀ {xs ys xs' ys' : List Ty}, TyEqs xs ys → TyEqs xs' ys' →
    TyEqs (xs ++ xs') (ys ++ ys')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, .cons h hs, h' => .cons h (hs.append h')

theorem TyEqs.reverse : ∀ {xs ys : List Ty}, TyEqs xs ys → TyEqs xs.reverse ys.reverse
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.reverse_cons]
    exact hs.reverse.append (.cons h .nil)

theorem Ty.field_tyEqs {l : String} : ∀ {ls : List String} {xs ys : List Ty}, TyEqs xs ys →
    (Ty.field l ls xs = none ∧ Ty.field l ls ys = none) ∨
      ∃ x y, Ty.field l ls xs = some x ∧ Ty.field l ls ys = some y ∧ TyEq x y
  | [], _, _, _ => .inl ⟨rfl, rfl⟩
  | _ :: _, [], [], _ => .inl ⟨rfl, rfl⟩
  | l' :: ls, x :: xs, y :: ys, .cons h hs => by
    simp only [Ty.field]
    split
    · exact .inr ⟨x, y, rfl, rfl, h⟩
    · exact Ty.field_tyEqs hs

theorem objSlots_tyEqs {L ls : List String} {xs ys : List Ty} (h : TyEqs xs ys) :
    TyEqs (objSlots L ls xs) (objSlots L ls ys) := by
  have hr := h.reverse
  refine TyEqs.of_zip (by simp [objSlots]) (fun x hx => ?_)
  simp only [objSlots] at hx
  obtain ⟨y, hy, rfl⟩ := zip_map_map_mem hx
  rcases Ty.field_tyEqs (l := y) (ls := ls.reverse) hr with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hab⟩
  · rw [h₁, h₂]; exact TyEq.refl _
  · rw [h₁, h₂]; exact hab

/-! ### Classes -/

/-- `memberCtx`, with the types `Δ` of fields before the members, the
latest first. -/
def memberCtxD (Δ : List Ty) (Γ : Ctx) (ks : List ClassKind) (τs : List Ty) (i : Nat) :
    ClassKind → Ctx
  | .data =>
    (((ks.zip τs).take i).filter (·.1 == .data)).reverse.map (fun p => .mono p.2) ++
      Δ.map .mono ++ Γ
  | _ => Γ

theorem memberCtx_eq (Γ : Ctx) (ks : List ClassKind) (τs : List Ty) (i : Nat) (k : ClassKind) :
    memberCtx Γ ks τs i k = memberCtxD [] Γ ks τs i k := by
  cases k <;> simp [memberCtx, memberCtxD]

theorem memberCtxD_zero (Δ : List Ty) (Γ : Ctx) (ks : List ClassKind) (τs : List Ty)
    (k : ClassKind) : memberCtxD Δ Γ ks τs 0 k = if k = .data then Δ.map .mono ++ Γ else Γ := by
  cases k <;> simp [memberCtxD]

theorem memberCtxD_succ (Δ : List Ty) (Γ : Ctx) (k₀ : ClassKind) (ks : List ClassKind) (τ₀ : Ty)
    (τs : List Ty) (i : Nat) (k : ClassKind) :
    memberCtxD Δ Γ (k₀ :: ks) (τ₀ :: τs) (i + 1) k =
      memberCtxD (if k₀ = .data then τ₀ :: Δ else Δ) Γ ks τs i k := by
  cases k <;> try rfl
  cases k₀ <;> simp [memberCtxD, List.take_succ_cons]

theorem SchemeEq.of_mono {τ τ' : Ty} (h : TyEq τ τ') : SchemeEq (.mono τ) (.mono τ') :=
  ⟨rfl, rfl, fun τs _ => ⟨by simpa [Scheme.mono, Scheme.inst] using h, by
    simp [Scheme.instPreds, Scheme.mono]⟩⟩

theorem CtxEq.monos : ∀ {xs ys : List Ty} {Γ Γ' : Ctx}, TyEqs xs ys → CtxEq Γ Γ' →
    CtxEq (xs.map .mono ++ Γ) (ys.map .mono ++ Γ')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, .cons hx hs, h => CtxEq.cons (SchemeEq.of_mono hx) (CtxEq.monos hs h)

theorem inferMembers_shape : ∀ {es : List Expr} {ks : List ClassKind} {Γ : Ctx} {Δ : List Ty}
    {R : Option Ty} {n : Nat} {o : OutArgs},
    inferMembers L Γ Δ R es ks n = some o → FnShaped es o.τs
  | [], [], _, _, _, _, o, h => by
    simp only [inferMembers, Option.some.injEq] at h; subst h
    intro i k b τ he; simp at he
  | [], _ :: _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, h => by simp [inferMembers] at h
  | e :: es, k :: ks, Γ, Δ, R, n, o, h => by
    cases k <;> (
      simp only [inferMembers] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      refine FnShaped.cons (fun k b he => ?_) (inferMembers_shape h₂)
      subst he
      obtain ⟨θ, ps, ρ, hτ, hl⟩ := infer_func_shape h₁
      exact ⟨_, _, _, by rw [hτ, Ty.subst_fn], by simpa using hl⟩)

theorem inferMembers_complete : ∀ (es : List Expr) (ks : List ClassKind) (τs' : List Ty),
    (∀ a ∈ es, InferComplete L a) →
    ∀ {Γ : Ctx} {Δ Δ' : List Ty} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      Ctx.Below n Γ → (∀ τ ∈ Δ, τ.Below n) → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
      CtxEq Γ' (Ctx.subst ψ Γ) → TyEqs Δ' (Δ.map (·.subst ψ)) → RetEq R' (Ret.subst ψ R) →
      ks.length = es.length → es.length = τs'.length →
      (∀ i e k τ, es[i]? = some e → ks[i]? = some k → τs'[i]? = some τ →
        HasType L C (memberCtxD Δ' Γ' ks τs' i k) R' .synth .synth e τ) →
      ∃ o, inferMembers L Γ Δ R es ks n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
        TyEqs (o.τs.map (·.subst φ)) τs' ∧ Sat C o.preds φ
  | [], [], [], _, Γ, Δ, Δ', R, n, ψ, C, Γ', R', _, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferMembers], ψ, Agree.nil n ψ, .nil, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _, _
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _, _ => by simp at hk
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _ => by
    simp at he
  | e :: es, k :: ks, τ' :: τs', ih, Γ, Δ, Δ', R, n, ψ, C, Γ', R', hΓ, hΔ, hR, hC, hΓ', hΔ',
      hR', hk, he, hms => by
    have ih' : ∀ a ∈ es, InferComplete L a := fun a ha => ih a (List.mem_cons_of_mem _ ha)
    have hrest : ∀ i e₁ k₁ τ₁, es[i]? = some e₁ → ks[i]? = some k₁ → τs'[i]? = some τ₁ →
        HasType L C (memberCtxD (if k = .data then τ' :: Δ' else Δ') Γ' ks τs' i k₁) R' .synth .synth
          e₁ τ₁ := by
      intro i e₁ k₁ τ₁ he₁ hk₁ hτ₁
      have := hms (i + 1) e₁ k₁ τ₁ (by simpa using he₁) (by simpa using hk₁) (by simpa using hτ₁)
      rwa [memberCtxD_succ] at this
    have h₀ := hms 0 e k τ' rfl rfl rfl
    rw [memberCtxD_zero] at h₀
    cases k with
    | data =>
      simp only [↓reduceIte] at h₀ hrest
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih e List.mem_cons_self RetOk.synth nofun .none .none
        (Γ := Δ.map .mono ++ Γ) (R := R) (n := n) (ψ := ψ)
        (Ctx.Below.append_mono hΔ hΓ) hR hC
        (by
          have := CtxEq.monos hΔ' hΓ'
          simpa [Ctx.subst, List.map_map, Function.comp_def, Scheme.mono_subst] using this)
        hR' h₀
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e RetOk.synth .none (Ctx.Below.append_mono hΔ hΓ) hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      have hagΓ : Agree n o₁.σ φ₁ ψ := fun a ha => hag₁ a ha
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferMembers_complete es ks τs' ih'
        (Δ := o₁.τ :: Δ.map (·.subst o₁.σ)) (Δ' := τ' :: Δ') (ψ := φ₁) hΓ₁
        (fun τ hτ => by
          rcases List.mem_cons.mp hτ with rfl | hτ
          · exact hτb₁
          · obtain ⟨τ₀, hτ₀, rfl⟩ := List.mem_map.mp hτ
            exact hσ₁.subst_below ((hΔ τ₀ hτ₀).mono hn₁))
        hR₁ hC (hΓ'.trans (hagΓ.ctx hΓ).symm)
        (by
          simp only [List.map_cons, List.map_map]
          refine .cons hτ₁.symm (hΔ'.trans (TyEqs.of_zip (by simp) (fun x hx => ?_)))
          obtain ⟨τ₀, hτ₀, rfl⟩ := zip_map_map_mem hx
          exact (hagΓ.ty (hΔ τ₀ hτ₀)).symm)
        (hR'.trans (hagΓ.ret hR).symm) (by simpa using hk) (by simpa using he) hrest
      refine ⟨_, by simp only [inferMembers, h₁, h₂]; rfl, φ₂, hagΓ.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
      · simp only [List.map_cons]
        exact .cons ((hag₂.ty hτb₁).trans hτ₁) hτs₂
      · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂
    | arrow | method | getter =>
      simp only [reduceCtorEq, ↓reduceIte] at h₀ hrest
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih e List.mem_cons_self RetOk.synth nofun .none .none hΓ hR hC hΓ' hR' h₀
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e RetOk.synth .none hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferMembers_complete es ks τs' ih'
        (Δ := Δ.map (·.subst o₁.σ)) (Δ' := Δ') (ψ := φ₁) hΓ₁
        (fun τ hτ => by
          obtain ⟨τ₀, hτ₀, rfl⟩ := List.mem_map.mp hτ
          exact hσ₁.subst_below ((hΔ τ₀ hτ₀).mono hn₁))
        hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm)
        (by
          simp only [List.map_map]
          refine hΔ'.trans (TyEqs.of_zip (by simp) (fun x hx => ?_))
          obtain ⟨τ₀, hτ₀, rfl⟩ := zip_map_map_mem hx
          exact (hag₁.ty (hΔ τ₀ hτ₀)).symm)
        (hR'.trans (hag₁.ret hR).symm) (by simpa using hk) (by simpa using he) hrest
      refine ⟨_, by simp only [inferMembers, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
      · simp only [List.map_cons]
        exact .cons ((hag₂.ty hτb₁).trans hτ₁) hτs₂
      · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂

/-- A class's member slots, from types equal under `φ` to a typing's: an
arrow field's `this` is a fresh variable, sent to the typing's. -/
theorem memberSlots_complete {C : List Pred} {T' : Ty} : ∀ {ks : List ClassKind} {es : List Expr}
    {τs τs' ss' : List Ty} {m : Nat} {φ : Subst}, FnShaped es τs → (∀ τ ∈ τs, τ.Below m) →
    TyEqs (τs.map (·.subst φ)) τs' →
    ks.length = es.length → es.length = τs.length → ss'.length = τs'.length →
    (∀ x ∈ ks.zip (es.zip (τs'.zip ss')), MemberSlot C T' x.1 x.2.1 x.2.2.1 x.2.2.2) →
    ∃ θs ss m' φ', memberSlots ks es τs m = some (θs, ss, m') ∧ m ≤ m' ∧
      (∀ τ : Ty, τ.Below m → τ.subst φ' = τ.subst φ) ∧
      TyEqs (ss.map (·.subst φ')) ss' ∧ (∀ θ ∈ θs, TyEq (θ.subst φ') T') ∧
      Sat C (notNewPreds m m') φ'
  | [], [], [], [], [], m, φ, _, _, _, _, _, _, _ =>
    ⟨[], [], m, φ, rfl, Nat.le_refl _, fun _ _ => rfl, .nil, by simp, by simp [notNewPreds]⟩
  | k :: ks, e :: es, τ :: τs, τ' :: τs', s' :: ss', m, φ, hsh, hb, hτs, hk, he, hs, hf => by
    cases hτs with
    | cons hτ hτs =>
    dsimp only at hτ
    have hb₀ := hb τ List.mem_cons_self
    have hbs : ∀ τ ∈ τs, τ.Below m := fun τ hτ => hb τ (List.mem_cons_of_mem _ hτ)
    have hf₀ := hf (k, e, τ', s') (by simp)
    have hf' : ∀ x ∈ ks.zip (es.zip (τs'.zip ss')), MemberSlot C T' x.1 x.2.1 x.2.2.1 x.2.2.2 :=
      fun x hx => hf x (by simp [hx])
    simp only at hf₀
    cases hf₀ with
    | data =>
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs, hnn⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      refine ⟨θs, .slot .pre .data τ :: ss, m', φ', by simp [memberSlots, h], hm, hφ',
        .cons ?_ hss, hθs, hnn⟩
      dsimp only
      rw [hφ' _ (Ty.Below.app.mpr (by simp [hb₀, Ty.Below.con]))]
      exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ
    | @arrow θ' θ'' n b τs'' ρ' hθ hn =>
      obtain ⟨θ, ps, ρ, rfl, -⟩ := hsh.head rfl
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs, hnn⟩ := memberSlots_complete (m := m + 1)
        (φ := (m, θ'') :: φ) hsh.tail (fun τ hτ => (hbs τ hτ).mono (Nat.le_succ _))
        (by rw [List.map_congr_left (fun τ hτ => Ty.subst_cons_fresh (hbs τ hτ))]; exact hτs)
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      obtain ⟨hθb, hpsb, hρb⟩ := Ty.Below.fn.mp hb₀
      have hφm : ∀ τ : Ty, τ.Below m → τ.subst φ' = τ.subst φ := fun τ hτ => by
        rw [hφ' τ (hτ.mono (Nat.le_succ _)), Ty.subst_cons_fresh hτ]
      simp only [Ty.subst_fn] at hτ
      obtain ⟨h₁, h₂, h₃⟩ := TyEq.fn_inv hτ
      have hvm : (Ty.var m).subst φ' = θ'' := by
        rw [hφ' _ (Ty.Below.var (Nat.lt_succ_self m))]; simp [Ty.subst, Subst.find]
      refine ⟨θ :: θs, .slot .pre .data (.fn (.var m) ps ρ) :: ss, m', φ',
        by simp [memberSlots, h], by omega, hφm, .cons ?_ hss, ?_, ?_⟩
      · simp only [Ty.subst_app, List.map_cons, List.map_nil]
        refine TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) (TyEq.fn_mk ?_ ?_ ?_)
        · rw [hφ' _ (Ty.Below.var (Nat.lt_succ_self m))]
          simp [Ty.subst, Subst.find]; exact TyEq.refl _
        · rw [hφm _ hρb]; exact h₂
        · rw [List.map_congr_left (fun τ hτ => hφm τ (hpsb τ hτ))]; exact h₃
      · intro θ₁ hθ₁
        rcases List.mem_cons.mp hθ₁ with rfl | hθ₁
        · rw [hφm _ hθb]; exact h₁.trans hθ
        · exact hθs θ₁ hθ₁
      · rw [notNewPreds_succ (by omega)]
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa [Pred.subst, hvm] using hn
        · exact hnn p hp
    | @method θ' n b τs'' ρ' hθ =>
      obtain ⟨θ, ps, ρ, rfl, -⟩ := hsh.head rfl
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs, hnn⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      refine ⟨θ :: θs, .slot .pre .proto (.fn θ ps ρ) :: ss, m', φ', by simp [memberSlots, h], hm,
        hφ', .cons ?_ hss, ?_, hnn⟩
      · dsimp only
        rw [hφ' _ (Ty.Below.app.mpr (by simp [hb₀, Ty.Below.con]))]
        exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ
      · intro θ₁ hθ₁
        rcases List.mem_cons.mp hθ₁ with rfl | hθ₁
        · rw [hφ' _ (Ty.Below.fn.mp hb₀).1]
          simp only [Ty.subst_fn] at hτ
          exact (TyEq.fn_inv hτ).1.trans hθ
        · exact hθs θ₁ hθ₁
    | @getter θ' b σ' hθ =>
      obtain ⟨θ, ps, ρ, rfl, hl⟩ := hsh.head rfl
      obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hl
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs, hnn⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      obtain ⟨hθb, -, hρb⟩ := Ty.Below.fn.mp hb₀
      simp only [Ty.subst_fn] at hτ
      obtain ⟨h₁, h₂, -⟩ := TyEq.fn_inv hτ
      refine ⟨θ :: θs, .slot .pre .proto ρ :: ss, m', φ', by simp [memberSlots, h], hm,
        hφ', .cons ?_ hss, ?_, hnn⟩
      · dsimp only
        rw [hφ' _ (Ty.Below.app.mpr (by simp [hρb, Ty.Below.con]))]
        exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) h₂
      · intro θ₁ hθ₁
        rcases List.mem_cons.mp hθ₁ with rfl | hθ₁
        · rw [hφ' _ hθb]; exact h₁.trans hθ
        · exact hθs θ₁ hθ₁
  | [], _ :: _, _, _, _, _, _, _, _, _, hk, _, _, _ | _ :: _, [], _, _, _, _, _, _, _, _, hk, _, _, _ => by
    simp at hk
  | _, [], _ :: _, _, _, _, _, _, _, _, _, he, _, _ | _, _ :: _, [], _, _, _, _, _, _, _, _, he, _, _ => by
    simp at he
  | _, _, [], _ :: _, _, _, _, _, _, hτs, _, _, _, _ | _, _, _ :: _, [], _, _, _, _, _, hτs, _, _, _, _ => by
    cases hτs
  | _, _, _, [], _ :: _, _, _, _, _, _, _, _, hs, _ | _, _, _, _ :: _, [], _, _, _, _, _, _, _, hs, _ => by
    simp at hs

/-! ### Generalisation -/

theorem TyEqs.mem_left : ∀ {xs ys : List Ty}, TyEqs xs ys → ∀ {x : Ty}, x ∈ xs →
    ∃ y ∈ ys, TyEq x y
  | _ :: _, y :: _, .cons h hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, h⟩
    · obtain ⟨y', hy', h'⟩ := hs.mem_left hx
      exact ⟨y', List.mem_cons_of_mem _ hy', h'⟩

theorem TyEqs.mem_right {xs ys : List Ty} (h : TyEqs xs ys) {y : Ty} (hy : y ∈ ys) :
    ∃ x ∈ xs, TyEq x y := by
  obtain ⟨x, hx, he⟩ := h.symm.mem_left hy
  exact ⟨x, hx, he.symm⟩

theorem PredEq.args_eqs {p q : Pred} (h : PredEq p q) : TyEqs p.args q.args :=
  TyEqs.of_zip h.2.1 h.2.2

theorem TyEqs.map_subst {xs : List Ty} {σ σ' : Subst}
    (h : ∀ x ∈ xs, TyEq (x.subst σ) (x.subst σ')) :
    TyEqs (xs.map (·.subst σ)) (xs.map (·.subst σ')) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem Pred.fundep_mem {p : Pred} {ds rs : List Ty} (h : p.fundep = some (ds, rs)) :
    (∀ d ∈ ds, d ∈ p.args) ∧ ∀ r ∈ rs, r ∈ p.args := by
  rcases Pred.fundep_some h with ⟨-, -, d, he, rfl⟩ | ⟨q, k, τ, t, r, rfl, rfl, rfl⟩
  · exact ⟨fun x hx => by simp at hx; simp [he, hx], fun x hx => by simp [he, hx]⟩
  · refine ⟨fun x hx => ?_, fun x hx => by simp at hx; simp [hx]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h <;> simp [h]

theorem Pred.subst_fundep {p : Pred} {ds rs : List Ty} (h : p.fundep = some (ds, rs))
    (φ : Subst) : (p.subst φ).fundep = some (ds.map (·.subst φ), rs.map (·.subst φ)) := by
  rcases Pred.fundep_some h with ⟨hp, hm, d, he, rfl⟩ | ⟨q, k, τ, t, r, rfl, rfl, rfl⟩
  · exact Pred.fundep_of_args (p := p.subst φ) hp hm (by simp [Pred.subst, he])
  · rfl

theorem Pred.fundep_predEq {p q : Pred} (h : PredEq p q) {ds rs : List Ty}
    (hf : p.fundep = some (ds, rs)) :
    ∃ ds' rs', q.fundep = some (ds', rs') ∧ TyEqs ds ds' ∧ TyEqs rs rs' := by
  have he := h.args_eqs
  obtain ⟨c, args⟩ := q
  have hc : p.cls = c := h.1
  rcases Pred.fundep_some hf with ⟨hp, hm, d, hpa, rfl⟩ | ⟨q₁, k, τ, t, r, rfl, rfl, rfl⟩
  · rw [hpa] at he
    cases he with
    | @cons _ d' _ rs' hd hrs =>
      refine ⟨[d'], rs', Pred.fundep_of_args (p := ⟨c, d' :: rs'⟩) (hc ▸ hp) (hc ▸ hm) rfl,
        .cons hd .nil, hrs⟩
  · simp only at hc; subst hc
    cases he with
    | cons h₁ he => cases he with
      | cons h₂ he => cases he with
        | cons h₃ he => cases he with
          | cons h₄ he => cases he with
            | cons h₅ he => cases he with
              | nil => exact ⟨_, _, rfl, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))),
                  .cons h₅ .nil⟩

theorem SlotCopy.tv {s r : Ty} (h : SlotCopy s r) {b : Nat} (hb : r.TV b) : s.TV b := by
  cases h with
  | data => exact hb
  | abs => exact hb
  | getter =>
    obtain ⟨x, hx, hxb⟩ := Ty.tv_app.mp hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact absurd hxb Ty.tv_con
    · exact absurd hxb Ty.tv_con
    · exact Ty.tv_app.mpr ⟨x, by simp, hxb⟩
  | proto =>
    obtain ⟨x, hx, hxb⟩ := Ty.tv_app.mp hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact absurd hxb Ty.tv_con

/-- An instance's determining arguments determine the rest: their tree
variables are theirs. -/
theorem Inst.fundep_tv {q : Pred} (h : Inst q) {ds rs : List Ty} (hf : q.fundep = some (ds, rs)) :
    ∀ r ∈ rs, ∀ b, r.TV b → ∃ d ∈ ds, d.TV b := by
  intro r hr b hb
  cases h with
  | plusNumber | plusString => simp [Pred.fundep] at hf
  | injectSelf _ | injectNothing _ _ | injectSome _ _ _ _ _ | injectArm _ _ _ _ _ _ _ _ =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨-, rfl⟩ := hf
    cases hr
  | stripSome =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Ty.tv_app.mpr ⟨r, by simp, hb⟩⟩
  | stripSelf _ _ _ =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, hb⟩
  | @hasProp l ls fs k σ hfl =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine ⟨_, List.mem_singleton_self _, Ty.tv_app.mpr ⟨_, (List.of_mem_zip (Ty.field_mem hfl)).2,
      Ty.tv_app.mpr ⟨r, ?_, hb⟩⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  | mergeData | mergeGetter =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨x, hx, hxb⟩ := Ty.tv_app.mp hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact absurd hxb Ty.tv_con
    · exact absurd hxb Ty.tv_con
    · exact ⟨x, by simp, hxb⟩
  | mergeAbs hc | mergeProto hc =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, hc.tv hb⟩
  | lengthArray | lengthString =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact absurd hb Ty.tv_con
  | @indexArray τ =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact absurd hb Ty.tv_con
    · exact ⟨_, List.mem_singleton_self _, Ty.tv_app.mpr ⟨r, by simp, hb⟩⟩
  | indexString =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact absurd hb Ty.tv_con
  | writeArray | notNew _ =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp at hr
  | caseHit _ _ hR =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact Ty.tv_app.mpr ⟨r, List.mem_of_getElem? hR, hb⟩
    · obtain ⟨x, hx, hxb⟩ := variantRest_tv hb
      exact Ty.tv_app.mpr ⟨x, List.mem_of_mem_eraseIdx hx, hxb⟩

/-- A constraint equal to one of a simple scheme's, opened at `m`, has a
determining argument whose tree has a variable of the block. -/
theorem Scheme.Simple.openPred_tv {s : Scheme} (hs : s.Simple) {m : Nat}
    (hms : ∀ a ∈ s.ftv, a < m) {p q : Pred} (hq : q ∈ s.openPreds m) (hpq : PredEq p q) :
    ∃ b, m ≤ b ∧ ((p.cls ≠ .merge ∧ ∃ t rest, p.args = t :: rest ∧ t.TV b) ∨
      (p.cls = .merge ∧ ∃ x ∈ p.args.take 4, x.TV b)) := by
  simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hq
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  have he := hpq.args_eqs
  have hc : p.cls = q₀.cls := hpq.1
  rcases hs q₀ hq₀ with ⟨hcls, -, i, hi, rest, hq'⟩ | ⟨q', k, τ, t, r, hq', i, hi, x, hx, hb⟩
  · simp only [PPred.inst, hq', List.map_cons] at he
    obtain ⟨c, args⟩ := p
    cases he with
    | @cons t _ _ _ ht _ =>
      refine ⟨m + i, by omega, .inl ⟨hc ▸ hcls, t, _, rfl, (ht.tv).mpr ?_⟩⟩
      simp only [PTy.inst, varBlock, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range', hi, Option.map_some, Option.getD_some, Nat.one_mul]
      exact Ty.tv_var_self _
  · subst hq'
    have hxs : ∀ a ∈ x.ftv, a < m := fun a ha => hms a (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hq₀, by
        simp only [PPred.ftv, List.flatMap_cons, List.flatMap_nil, List.mem_append]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [ha]⟩))
    have hb' := (PTy.treeBound_iff hi hxs).mp hb
    simp only [PPred.inst, List.map_cons, List.map_nil] at he
    obtain ⟨c, args⟩ := p
    simp only at hc; subst hc
    cases he with
    | cons h₁ he => cases he with
      | cons h₂ he => cases he with
        | cons h₃ he => cases he with
          | cons h₄ he => cases he with
            | cons h₅ he => cases he with
              | nil =>
                refine ⟨m + i, by omega, .inr ⟨rfl, ?_⟩⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact ⟨_, by simp, h₁.tv.mpr hb'⟩
                · exact ⟨_, by simp, h₂.tv.mpr hb'⟩
                · exact ⟨_, by simp, h₃.tv.mpr hb'⟩
                · exact ⟨_, by simp, h₄.tv.mpr hb'⟩

/-- A constraint whose trees have only variables below `m` is entailed by the
assumptions alone, not by a simple scheme's opened at `m`. -/
theorem EntailsS.drop_block {C : List Pred} {s : Scheme} (hs : s.Simple) {m : Nat}
    (hms : ∀ a ∈ s.ftv, a < m) {p : Pred} (h : Entails (C ++ s.openPreds m) p)
    (hp : ∀ x ∈ p.args, ∀ b, x.TV b → b < m) : Entails C p := by
  rcases h with hi | ⟨q, hq, hpq⟩
  · exact .inl hi
  · rcases List.mem_append.mp hq with hq | hq
    · exact .inr ⟨q, hq, hpq⟩
    · exfalso
      obtain ⟨b, hb, h⟩ := hs.openPred_tv hms hq hpq
      rcases h with ⟨-, t, rest, he, ht⟩ | ⟨-, x, hx, hxb⟩
      · have := hp t (by simp [he]) b ht; omega
      · have := hp x (List.mem_of_mem_take hx) b hxb; omega

/-- What determining arguments' trees bound, entailment bounds in the rest. -/
theorem tv_determined {C : List Pred} {s : Scheme} (hs : s.Simple) {m : Nat}
    (hmC : ∀ p ∈ C, ∀ a ∈ p.ftv, a < m) (hms : ∀ a ∈ s.ftv, a < m)
    {p : Pred} {φ : Subst} (he : Entails (C ++ s.openPreds m) (p.subst φ))
    {ds rs : List Ty} (hf : p.fundep = some (ds, rs))
    (hds : ∀ d ∈ ds, ∀ b, (d.subst φ).TV b → b < m) :
    ∀ r ∈ rs, ∀ b, (r.subst φ).TV b → b < m := by
  intro r hr b hb
  have hrm : r.subst φ ∈ (p.subst φ).args := by
    simp only [Pred.subst, List.mem_map]; exact ⟨r, (Pred.fundep_mem hf).2 r hr, rfl⟩
  rcases he with ⟨q₀, hpq, hi⟩ | ⟨c, hc, hpc⟩
  · obtain ⟨ds', rs', hf₀, hdd, hrr⟩ := Pred.fundep_predEq hpq (Pred.subst_fundep hf φ)
    obtain ⟨r', hr', hre⟩ := hrr.mem_left (List.mem_map_of_mem hr)
    obtain ⟨d', hd', hdb⟩ := Inst.fundep_tv hi hf₀ r' hr' b (hre.tv.mp hb)
    obtain ⟨d₁, hd₁, hde⟩ := hdd.mem_right hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd₁
    exact hds d hd b (hde.tv.mpr hdb)
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨y, hy, hye⟩ := hpc.args_eqs.mem_left hrm
      exact hmC c hc b (List.mem_flatMap.mpr ⟨y, hy, (hye.tv.mp hb).ftv⟩)
    · exfalso
      obtain ⟨b', hb', h⟩ := hs.openPred_tv hms hc hpc
      rcases Pred.fundep_some hf with ⟨-, hm, d, hpa, rfl⟩ | ⟨q, k, τ, t, r₀, rfl, rfl, rfl⟩
      · rcases h with ⟨-, t', rest, he', ht'⟩ | ⟨hm', -⟩
        · simp only [Pred.subst, hpa, List.map_cons, List.cons.injEq] at he'
          obtain ⟨rfl, -⟩ := he'
          have := hds d (by simp) b' ht'; omega
        · exact hm hm'
      · rcases h with ⟨hm', -⟩ | ⟨-, x, hx, hxb⟩
        · exact hm' rfl
        · simp only [Pred.subst, List.map_cons, List.map_nil, List.take_succ_cons,
            List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · have := hds q (by simp) b' hxb; omega
          · have := hds k (by simp) b' hxb; omega
          · have := hds τ (by simp) b' hxb; omega
          · have := hds t (by simp) b' hxb; omega

/-- The variables the environment fixes are sent by `φ` to trees below `m`. -/
theorem fixed_tv_lt {C : List Pred} {s : Scheme} (hs : s.Simple) {m : Nat}
    (hmC : ∀ p ∈ C, ∀ a ∈ p.ftv, a < m) (hms : ∀ a ∈ s.ftv, a < m)
    {preds : List Pred} {φ : Subst} (hsat : Sat (C ++ s.openPreds m) preds φ)
    {env : List Nat} (henv : ∀ v ∈ env, ∀ b, ((Ty.var v).subst φ).TV b → b < m) :
    ∀ v ∈ fixedVars preds env, ∀ b, ((Ty.var v).subst φ).TV b → b < m := by
  refine fixLoop_all (ps₀ := preds) (fun p hp hds v hv => ?_) _ _ _ (fun p hp => hp) henv
  unfold Pred.fixes at hv
  cases hd : p.fundep with
  | none => simp [hd] at hv
  | some d =>
    obtain ⟨ds, rs⟩ := d
    simp only [hd, Option.map_some, Option.getD_some] at hds hv
    obtain ⟨r, hr, hvr⟩ := List.mem_flatMap.mp hv
    intro b hb
    refine tv_determined hs hmC hms (hsat p hp) hd (fun d hd' b hb' => ?_) r hr b
      (Ty.TV.subst_of (Ty.mem_tv.mp hvr) hb)
    obtain ⟨a, ha, hab⟩ := Ty.TV.subst_inv hb'
    exact hds a (List.mem_flatMap.mpr ⟨d, hd', Ty.mem_tv.mpr ha⟩) b hab

/-- A block substitution doesn't change a type whose tree is below it. -/
theorem Ty.subst_block_tv_lt {t : Ty} {m : Nat} {τs : List Ty} (h : ∀ b, t.TV b → b < m) :
    TyEq (t.subst (Subst.block m τs)) t := by
  have := Ty.subst_tyEq_congr_tv (σ := Subst.block m τs) (σ' := []) (τ := t) (fun a ha => by
    simp only [Ty.subst, Subst.block_find_none (h a ha)]; exact TyEq.refl _)
  simpa using this

theorem genVars_mem {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty} {preds : List Pred} {v : Nat} :
    v ∈ genVars Γ₁ R₁ τ₁ preds ↔ v ∈ τ₁.tv ++ preds.flatMap Pred.tv ∧
      v ∉ fixedVars preds (ctxTv Γ₁ ++ Ret.tv R₁) := by
  simp [genVars, List.mem_eraseDups, List.mem_filter, or_and_right]

/-- An entailed constraint has its class's arity. -/
theorem EntailsS.arity {top : Bool} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) {p : Pred}
    (h : Entails C p) : p.args.length = p.cls.arity := by
  rcases h with ⟨q, hpq, hi⟩ | ⟨c, hc, hpc⟩
  · rw [hpq.2.1, hpq.1]; cases hi <;> rfl
  · rw [hpc.2.1, hpc.1]
    rcases hC c hc with ⟨-, hl, -⟩ | ⟨q, k, τ, s, r, rfl, -⟩
    · exact hl
    · rfl

/-- An `Inject` on a known type is decided. -/
theorem Pred.decideInject_ne_keep {t T : Ty} : Pred.decideInject t T ≠ .keep := by
  intro h
  unfold Pred.decideInject at h
  repeat' split at h
  all_goals cases h

/-- A `Case` on a known type is decided. -/
theorem Pred.decideCase_ne_keep {d d' : Disc} {t : String} {ts : List String} {Ps : List Ty}
    {σ ρ : Ty} : Pred.decideCase d t d' ts Ps σ ρ ≠ .keep := by
  intro h
  unfold Pred.decideCase at h
  split at h
  · split at h
    · split at h <;> cases h
    · cases h
  · cases h

/-- A `Strip` on a known type is decided. -/
theorem Pred.decideStrip_ne_keep {t σ : Ty} : Pred.decideStrip t σ ≠ .keep := by
  intro h
  unfold Pred.decideStrip at h
  split at h
  · cases h
  · split at h <;> cases h
  · cases h

theorem Pred.decide₀_keep_merge {c : Cls} {t : Ty} {rest : List Ty}
    (h : Pred.decide₀ c t rest = .keep) : c = .merge := by
  unfold Pred.decide₀ at h
  split at h <;> first | rfl | (split at h <;> cases h) | cases h |
    exact absurd h Pred.decideInject_ne_keep | exact absurd h Pred.decideStrip_ne_keep |
    exact absurd h Pred.decideCase_ne_keep

/-- What improvement keeps where a binding generalises. -/
theorem Pred.improve_keep_false {p : Pred} (h : p.improve false = .keep) :
    p.cls = .plus ∨ p.cls = .merge ∨
      (p.cls ≠ .plus ∧ p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧
        ∃ t rest, p.args = t :: rest ∧ ∃ a, t.whnf = .var a) := by
  obtain ⟨cls, args⟩ := p
  cases cls
  case plus => exact .inl rfl
  case merge => exact .inr (.inl rfl)
  all_goals
    simp only [Pred.improve] at h
    right; right
    refine ⟨by simp, by simp, ?_⟩
    match args, h with
    | t :: rest, h =>
      rw [Pred.improveArgs_cons] at h
      split at h
      · rename_i hv
        split at h
        · rename_i hl
          obtain ⟨a, ha⟩ := Ty.isVar_iff.mp hv
          exact ⟨by simpa using hl, t, rest, rfl, a, ha⟩
        · cases h
      · have := Pred.decide₀_keep_merge h; cases this
    | [], h => simp [Pred.improveArgs] at h

/-- An entailed constraint other than a `Merge`, by assumptions where a
binding generalises: its first argument unfolds to a variable, or it is an
instance. -/
theorem EntailsS.first_var_or_inst {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt false)
    {p : Pred} {φ : Subst} (h : Entails C (p.subst φ)) (hm : p.cls ≠ .merge) {t : Ty}
    {rest : List Ty} (ht : p.args = t :: rest) :
    (∃ a, t.whnf = .var a) ∨ ∃ q₀, PredEq (p.subst φ) q₀ ∧ Inst q₀ := by
  rcases h with ⟨q₀, hpq, hi⟩ | ⟨c, hc, hpc⟩
  · exact .inr ⟨q₀, hpq, hi⟩
  · left
    have he := hpc.args_eqs
    simp only [Pred.subst, ht, List.map_cons] at he
    rcases hC c hc with ⟨-, -, a, rest', hca⟩ | ⟨q, k, τ, s, r, rfl, -⟩
    · rw [hca] at he
      cases he with
      | cons h₁ _ => exact Ty.whnf_var_of_tyEq h₁
    · exact absurd hpc.1 hm

/-- A generalised variable in a tree is a quantified variable in the
generalisation's tree. -/
theorem Ty.gen_treeBound {ᾱ : List Nat} {x : Ty} {v i : Nat} (hv : x.TV v)
    (hi : findIdx ᾱ v = some i) : (x.gen ᾱ).TreeBound ᾱ.length i := by
  have hN := lt_maxPlusOne (l := (x.gen ᾱ).ftv)
  rw [PTy.treeBound_iff (findIdx_lt hi) hN]
  have := Ty.gen_inst ᾱ (maxPlusOne (x.gen ᾱ).ftv) [] x
  rw [PTy.subst_nil, List.append_nil] at this
  rw [← this]
  exact Ty.TV.subst_of hv (by simp [Ty.subst, renameBlock_find, hi, Ty.tv_var_self])

theorem Pred.normHead_cons (c : Cls) (t : Ty) (rest : List Ty) :
    ∃ t', Pred.normHead ⟨c, t :: rest⟩ = ⟨c, t' :: rest⟩ ∧ TyEq t' t ∧
      ∀ a, t.whnf = .var a → t' = .var a := by
  unfold Pred.normHead
  simp only
  split
  · exact ⟨t.whnf, rfl, TyEq.whnf t, fun a ha => ha⟩
  · rename_i hnv
    exact ⟨t, rfl, TyEq.refl t, fun a ha => by simp [ha, Ty.isVar] at hnv⟩

/-- A simple scheme's constraints, opened, are assumptions improvement can't
decide where a binding generalises. -/
theorem assumable_open {C : List Pred} (hC : ∀ p ∈ C, p.AssumableAt false) {s : Scheme}
    (hs : s.Simple) (m : Nat) : ∀ p ∈ C ++ s.openPreds m, p.AssumableAt false := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hC p hp
  · simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rcases hs q hq with ⟨hcls, hlen, i, hi, rest, hq'⟩ | ⟨q₀, k₀, τ₀, t₀, r₀, hq', -⟩
    · exact .inl ⟨hcls, by simpa [PPred.inst] using hlen, m + i,
        rest.map (·.inst (varBlock m s.arity)), by simp [PPred.inst, hq', PTy.inst, varBlock, hi]⟩
    · subst hq'
      exact .inr ⟨_, _, _, _, _, rfl, fun h => by cases h⟩

theorem Ret.tv_subst {σ : Subst} {R : Option Ty} {b : Nat} (h : b ∈ Ret.tv (Ret.subst σ R)) :
    ∃ a ∈ Ret.ftv R, ((Ty.var a).subst σ).TV b := by
  cases R with
  | none => simp [Ret.tv] at h
  | some τ =>
    simp only [Ret.subst_some, Ret.tv, Option.map_some, Option.getD_some] at h
    obtain ⟨a, ha, hb⟩ := Ty.TV.subst_inv (Ty.mem_tv.mp h)
    exact ⟨a, by simpa [Ret.ftv] using ha.ftv, hb⟩

/-- The scheme inference gives a binding passes its check, is more general
than a typing's, and leaves pending only constraints the assumptions
entail. -/
theorem letScheme_complete {C : List Pred} (hC : ∀ p ∈ C, p.AssumableAt false) {s : Scheme}
    (hs : s.Simple) {m : Nat} (hmC : ∀ p ∈ C, ∀ a ∈ p.ftv, a < m) (hms : ∀ a ∈ s.ftv, a < m)
    {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty} {preds : List Pred} {φ : Subst}
    (hτ : TyEq (τ₁.subst φ) (s.open m)) (hsat : Sat (C ++ s.openPreds m) preds φ)
    (hkeep : ∀ p ∈ preds, p.improve false = .keep)
    (henv : ∀ v ∈ ctxTv Γ₁ ++ Ret.tv R₁, ∀ b, ((Ty.var v).subst φ).TV b → b < m)
    {e₁ e₂ : Expr} (hval : (s.arity = 0 ∧ s.preds = []) ∨ (e₁.IsValue ∧ e₂.writes 0 = false)) :
    (letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).1.preds.all
        (PPred.isSimple (letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).1.arity) = true ∧
      Generalizes C ((letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).1.subst φ) s ∧
      ((s.arity = 0 ∧ s.preds = [] →
          ((letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).1.subst φ).arity = 0 ∧
          ((letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).1.subst φ).preds = []) ∨
        e₂.writes 0 = false) ∧
      Sat C (letScheme (Expr.generalises e₁ e₂) Γ₁ R₁ τ₁ preds).2 φ := by
  have hC₁ := assumable_open hC hs m
  have hCb : ∀ τs : List Ty, C.map (·.subst (Subst.block m τs)) = C := fun τs => by
    conv => rhs; rw [← List.map_id C]
    exact List.map_congr_left (fun q hq =>
      Pred.subst_id (fun a ha => Subst.block_find_none (hmC q hq a ha)))
  by_cases hv : Expr.generalises e₁ e₂ = true
  · have hw : e₂.writes 0 = false := by
      simp only [Expr.generalises, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      exact hv.2
    simp only [letScheme, hv, ↓reduceIte]
    generalize hα : genVars Γ₁ R₁ τ₁ preds = ᾱ
    have hQ := fixed_tv_lt hs hmC hms hsat henv
    generalize hfx : fixedVars preds (ctxTv Γ₁ ++ Ret.tv R₁) = fixed at hQ
    have hfixed : ∀ v ∈ ᾱ, v ∉ fixed := fun v hv' => by
      rw [← hα, genVars_mem, hfx] at hv'; exact hv'.2
    have hcover : ∀ v ∈ τ₁.tv ++ preds.flatMap Pred.tv, v ∈ ᾱ ∨ v ∈ fixed := by
      intro v hv'
      by_cases hf : v ∈ fixed
      · exact .inr hf
      · exact .inl (by rw [← hα, genVars_mem, hfx]; exact ⟨hv', hf⟩)
    have hcov' : ∀ g ∈ preds, ∀ v ∈ g.tv, v ∈ ᾱ ∨ v ∈ fixed := fun g hg v hv' =>
      hcover v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg, hv'⟩))
    have hclosed : ∀ g ∈ preds, g.fires fixed = true → ∀ v ∈ g.fixes, v ∈ fixed := by
      intro g hg hfire v hv'
      rw [← hfx] at hfire ⊢
      exact fixLoop_closed _ _ _ (Nat.le_refl _) g hg hfire v hv'
    -- Each variable goes where `φ` and the block send it.
    let f : List Ty → Nat → Ty := fun τs a => ((Ty.var a).subst φ).subst (Subst.block m τs)
    have hblock : ∀ (τs : List Ty) (v : Nat), (v ∈ ᾱ ∨ v ∈ fixed) →
        TyEq ((Ty.var v).subst (ᾱ.zip (ᾱ.map (f τs)) ++ φ)) (f τs v) := by
      intro τs v hv'
      by_cases hvα : v ∈ ᾱ
      · rw [Ty.subst_zip_map_mem hvα]; exact TyEq.refl _
      · rw [Ty.subst_zip_map_not_mem hvα]
        exact (Ty.subst_block_tv_lt (hQ v (hv'.resolve_left hvα))).symm
    refine ⟨?_, fun τs hlen => ?_, .inr hw, ?_⟩
    · -- Each generalised constraint is simple.
      simp only [generalize, List.all_map, List.all_eq_true, Function.comp_apply]
      intro g hgf
      obtain ⟨hg, hgα⟩ := List.mem_filter.mp hgf
      obtain ⟨a, ha, haα⟩ := List.any_eq_true.mp hgα
      simp only [decide_eq_true_eq] at haα
      have he := hsat g hg
      have hl := he.arity hC₁
      simp only [Pred.subst, List.length_map] at hl
      obtain ⟨c, args⟩ := g
      simp only at hl
      rcases Pred.improve_keep_false (hkeep _ hg) with hcls | hcls |
        ⟨hcp, hcm, -, t, rest, hargs, r, hr⟩
      · -- `Plus t`: `t` unfolds to a variable, which is generalised.
        simp only at hcls; subst hcls
        match args, hl with
        | [t], _ =>
          have htr : ∃ r, t.whnf = .var r := by
            rcases he.first_var_or_inst hC₁ (by simp) rfl with h | ⟨q₀, hpq, hi⟩
            · exact h
            · have hq₀ : q₀ = ⟨.plus, [.number]⟩ ∨ q₀ = ⟨.plus, [.string]⟩ := by
                have hc := hpq.1
                cases hi <;> simp_all [Pred.subst]
              rcases hq₀ with rfl | rfl
              all_goals
                obtain ⟨-, hq⟩ := PredEq.one hpq
                rcases Ty.whnf_con_of_tyEq hq with h | hc
                · exact h
                · exfalso
                  have hta : t.TV a := Ty.mem_tv.mp (by simpa [Pred.tv] using ha)
                  rw [← (TyEq.whnf t).tv, hc] at hta
                  exact Ty.tv_con hta
          obtain ⟨r, hr⟩ := htr
          have hta : t.TV a := Ty.mem_tv.mp (by simpa [Pred.tv] using ha)
          rw [← (TyEq.whnf t).tv, hr, Ty.tv_var] at hta
          subst hta
          obtain ⟨i, hi⟩ := findIdx_some haα
          obtain ⟨t', hn, -, ht'⟩ := Pred.normHead_cons .plus t []
          rw [hn, ht' _ hr]
          simp [Pred.gen, Ty.gen, hi, PPred.isSimple, findIdx_lt hi, Cls.arity]
      · -- `Merge`: a determining argument has a generalised variable in its tree.
        simp only at hcls; subst hcls
        match args, hl with
        | [q, k, τ, t, r], _ =>
          have hdet : ∃ x ∈ [q, k, τ, t], ∃ w, x.TV w ∧ w ∈ ᾱ := by
            refine Classical.byContradiction fun hno' => ?_
            have hno : ∀ x ∈ [q, k, τ, t], ∀ w, x.TV w → w ∉ ᾱ :=
              fun x hx w hw hwα => hno' ⟨x, hx, w, hw, hwα⟩
            have hdfix : ∀ x ∈ [q, k, τ, t], ∀ w ∈ x.tv, w ∈ fixed := fun x hx w hw =>
              (hcov' _ hg w (by
                simp only [Pred.tv, List.mem_flatMap]
                refine ⟨x, ?_, hw⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                rcases hx with h | h | h | h <;> simp [h])).resolve_left
                (hno x hx w (Ty.mem_tv.mp hw))
            have hfire : Pred.fires fixed ⟨.merge, [q, k, τ, t, r]⟩ = true := by
              simp only [Pred.fires, Pred.fundep, List.all_eq_true, decide_eq_true_eq,
                List.mem_flatMap]
              exact fun w ⟨x, hx, hw⟩ => hdfix x hx w hw
            have hrfix := hclosed _ hg hfire
            simp only [Pred.fixes, Pred.fundep, List.flatMap_cons, List.flatMap_nil,
              List.append_nil] at hrfix
            simp only [Pred.tv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
              List.mem_append] at ha
            rcases ha with ha | ha | ha | ha | ha
            · exact hno q (by simp) a (Ty.mem_tv.mp ha) haα
            · exact hno k (by simp) a (Ty.mem_tv.mp ha) haα
            · exact hno τ (by simp) a (Ty.mem_tv.mp ha) haα
            · exact hno t (by simp) a (Ty.mem_tv.mp ha) haα
            · exact hfixed a haα (hrfix a ha)
          obtain ⟨x, hx, w, hxw, hwα⟩ := hdet
          obtain ⟨i, hi⟩ := findIdx_some hwα
          obtain ⟨q', hn, hq', -⟩ := Pred.normHead_cons .merge q [k, τ, t, r]
          rw [hn]
          simp only [Pred.gen, List.map_cons, List.map_nil, PPred.isSimple, List.any_eq_true,
            List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
          refine ⟨i, findIdx_lt hi, ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨_, .inl rfl, PTy.treeBound_spec.mpr
              (Ty.gen_treeBound (hq'.tv.mpr hxw) hi)⟩
          · exact ⟨_, .inr (.inl rfl), PTy.treeBound_spec.mpr (Ty.gen_treeBound hxw hi)⟩
          · exact ⟨_, .inr (.inr (.inl rfl)), PTy.treeBound_spec.mpr (Ty.gen_treeBound hxw hi)⟩
          · exact ⟨_, .inr (.inr (.inr rfl)), PTy.treeBound_spec.mpr (Ty.gen_treeBound hxw hi)⟩
      · -- On a variable: the variable is generalised, since a fixed one would
        -- fix the rest too.
        simp only at hcp hcm hargs; subst hargs
        have htr : ∀ w, t.TV w ↔ w = r := fun w => by
          rw [← (TyEq.whnf t).tv, hr, Ty.tv_var]
        have hrα : r ∈ ᾱ := by
          rcases hcov' _ hg r (by
              simp only [Pred.tv, List.flatMap_cons, List.mem_append]
              exact .inl (Ty.mem_tv.mpr ((htr r).mpr rfl))) with h | hrf
          · exact h
          · exfalso
            have hfd : Pred.fundep ⟨c, t :: rest⟩ = some ([t], rest) :=
              Pred.fundep_of_args hcp hcm rfl
            have hfire : Pred.fires fixed ⟨c, t :: rest⟩ = true := by
              simp only [Pred.fires, hfd, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                List.all_eq_true, decide_eq_true_eq]
              intro w hw
              rw [(htr w).mp (Ty.mem_tv.mp hw)]; exact hrf
            have hrest := hclosed _ hg hfire
            simp only [Pred.fixes, hfd] at hrest
            simp only [Pred.tv, List.flatMap_cons, List.mem_append] at ha
            rcases ha with ha | ha
            · rw [(htr a).mp (Ty.mem_tv.mp ha)] at haα; exact hfixed r haα hrf
            · exact hfixed a haα (hrest a ha)
        obtain ⟨i, hi⟩ := findIdx_some hrα
        obtain ⟨t', hn, -, ht'⟩ := Pred.normHead_cons c t rest
        rw [hn, ht' _ hr]
        cases c <;> simp_all [Pred.gen, Ty.gen, PPred.isSimple, findIdx_lt hi, Cls.arity]
    · -- More general than `s`.
      have hlen' : ᾱ.length = (ᾱ.map (f τs)).length := by simp
      refine ⟨ᾱ.map (f τs), by simp [generalize, Scheme.subst], ?_, ?_⟩
      · rw [generalize_subst_inst φ hlen', ← Scheme.open_block s hms hlen]
        refine TyEq.trans ?_ (hτ.subst (Subst.block m τs))
        rw [← Ty.subst_compose]
        exact Ty.subst_tyEq_congr_tv (fun v hv' => by
          rw [Ty.subst_compose]
          exact hblock τs v (hcover v (List.mem_append_left _ (Ty.mem_tv.mpr hv'))))
      · intro c hc
        rw [generalize_subst_instPreds φ hlen'] at hc
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hc
        obtain ⟨g, hgf, rfl⟩ := List.mem_map.mp hg'
        obtain ⟨hg, -⟩ := List.mem_filter.mp hgf
        have hb : Entails (C ++ s.instPreds τs) ((g.subst φ).subst (Subst.block m τs)) := by
          have := EntailsS.subst (Subst.block m τs) (hsat g hg)
          rwa [List.map_append, hCb, Scheme.openPreds_block s hms hlen] at this
        refine hb.of_predEq (PredEq.trans ?_ ((Pred.normHead_predEq g).subst _))
        rw [← Pred.subst_compose]
        exact Pred.subst_predEq_congr_tv (fun v hv' => by
          rw [Ty.subst_compose]; exact (hblock τs v (hcov' g hg v hv')).symm)
    · -- What stays pending has only fixed variables, so `C` entails it.
      intro c hc
      obtain ⟨hcp, hcα⟩ := List.mem_filter.mp hc
      have hcfix : ∀ v ∈ c.tv, v ∈ fixed := fun v hv' =>
        (hcov' c hcp v hv').resolve_left (fun hvα => by
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
            decide_eq_true_eq] at hcα
          exact hcα v hv' hvα)
      refine (hsat c hcp).drop_block hs hms (fun x hx b hb => ?_)
      simp only [Pred.subst, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨v, hv', hvb⟩ := Ty.TV.subst_inv hb
      exact hQ v (hcfix v (List.mem_flatMap.mpr ⟨y, hy, Ty.mem_tv.mpr hv'⟩)) b hvb
  · -- Not generalised: `s` quantifies nothing.
    have harity : s.arity = 0 ∧ s.preds = [] :=
      hval.resolve_right (fun ⟨hv', hw'⟩ => hv (by
        simp [Expr.generalises, Expr.isValue_complete hv', hw']))
    simp only [letScheme, hv, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp [Scheme.mono], fun τs hlen => ⟨[], by simp [Scheme.mono, Scheme.subst], ?_,
      by simp [Scheme.instPreds, Scheme.mono, Scheme.subst]⟩,
      .inl (fun _ => ⟨by simp [Scheme.mono, Scheme.subst], by simp [Scheme.mono, Scheme.subst]⟩),
      ?_⟩
    · have hτs : τs = [] := List.eq_nil_of_length_eq_zero (hlen.trans harity.1)
      subst hτs
      rw [Scheme.mono_subst, Scheme.mono_inst]
      refine hτ.trans ?_
      simp [Scheme.open, varBlock, harity.1]
      exact TyEq.refl _
    · intro c hc
      have := hsat c hc
      simpa [Scheme.openPreds, Scheme.instPreds, harity.2] using this

@[simp] theorem Ty.newTarget_subst (σ : Subst) : Ty.newTarget.subst σ = .newTarget := rfl

/-- An entailed `Inject T τ`, with `τ` a known type and `T` not a sum, under
assumptions each on a type variable: `τ` is `T`. -/
theorem EntailsS.inject_app {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt false) {T : Ty} {c : Con}
    {xs : List Ty} (h : Entails C ⟨.inject T, [.app c xs]⟩) (hT : ∀ z σ, ¬ TyEq T (.maybe z σ))
    (hV : ∀ ts Rs, T.whnf ≠ .variant .typeOf ts Rs) : TyEq (.app c xs) T := by
  rcases h with ⟨q₀, hpq, hi⟩ | ⟨q, hq, hpq⟩
  · obtain ⟨cq, args⟩ := q₀
    match args, hpq.2.1 with
    | [a], _ =>
      obtain ⟨hcq, hτ⟩ := PredEq.one hpq
      subst hcq
      cases hi with
      | injectSelf _ => exact hτ
      | injectNothing he _ => exact absurd he (hT _ _)
      | injectSome he _ _ _ _ => exact absurd he (hT _ _)
      | injectArm _ hw _ _ _ _ _ _ => exact absurd hw (hV _ _)
  · rcases hC q hq with ⟨-, -, a, rest, hqa⟩ | ⟨q', k, τ, s, r, rfl, -⟩
    · obtain ⟨cq, args⟩ := q
      simp only at hqa; subst hqa
      have := hpq.2.2 (.app c xs, .var a) (by simp)
      obtain ⟨b, hb⟩ := Ty.whnf_var_of_tyEq (φ := []) (by simpa using this)
      simp at hb
    · exact absurd hpq.1 (by simp)

theorem Ty.not_maybe_of_whnf {T : Ty} {c : Con} {xs : List Ty} (hw : T.whnf = .app c xs)
    (hc : ∀ z, c ≠ .maybe z) : ∀ z σ, ¬ TyEq T (.maybe z σ) := fun z _ he =>
  TyEq.not_maybe (hc z) ((TyEq.of_whnf hw).symm.trans he)

/-! ### An object literal synthesised and injected, checked instead -/

theorem Ty.field_map_some {l : String} {f : String → Ty} :
    ∀ {L : List String}, l ∈ L → Ty.field l L (L.map f) = some (f l)
  | [], h => by simp at h
  | l' :: L, h => by
    simp only [List.mem_cons] at h
    simp only [List.map_cons, Ty.field]
    split
    · simp_all
    · rename_i hne; exact Ty.field_map_some (h.resolve_left fun e => hne e.symm)

theorem Ty.field_map_fn {l : String} (f : Ty → Ty) :
    ∀ (ls : List String) (fs : List Ty), Ty.field l ls (fs.map f) = (Ty.field l ls fs).map f
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, x :: fs => by
    simp only [List.map_cons, Ty.field]
    split
    · rfl
    · exact Ty.field_map_fn f ls fs

/-- An object's record type has, for a field it has once, its slot. -/
theorem objSlots_field_some {L ls : List String} {ss : List Ty} {l : String} {s : Ty}
    (hnd : ls.Nodup) (hL : l ∈ L) (hm : (l, s) ∈ ls.zip ss) (hlen : ls.length = ss.length) :
    Ty.field l L (objSlots L ls ss) = some s := by
  have hnd' : ((ls.zip ss).map (·.1)).Nodup := by rw [List.map_fst_zip (by omega)]; exact hnd
  unfold objSlots
  rw [Ty.field_map_some hL, Ty.field_eq_lookup, ← zip_reverse hlen, lookup_reverse hnd',
    lookup_of_mem hnd' hm]
  rfl

/-- A type equal to a record has, for its field that holds a value, an
equal field that does. -/
theorem Ty.dataField_of_tyEq {T : Ty} {L : List String} {slots : List Ty} {l : String} {s τ : Ty}
    (he : TyEq T (.record L slots)) (hf : Ty.field l L slots = some s)
    (hs : TyEq s (.slot .pre .data τ)) : ∃ τ', T.dataField l = some τ' ∧ TyEq τ τ' := by
  obtain ⟨ys, hys, hrec⟩ := TyEq.whnf_app he.symm (Ty.whnf_app _ _)
  obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp hrec
  obtain ⟨s', hf', hss⟩ := Ty.field_tyEq hl hz hf
  obtain ⟨zs, hzs, hslot⟩ := TyEq.whnf_app (hs.symm.trans hss) (Ty.whnf_app _ _)
  obtain ⟨-, hl', hz'⟩ := TyEq.app_iff.mp hslot
  match zs, hl', hz', hzs with
  | [p', k', τ'], _, hz', hzs =>
    have hp' := TyEq.whnf_con (hz' (.pre, p') (by simp)) (Ty.whnf_app _ _)
    have hk' := TyEq.whnf_con (hz' (.data, k') (by simp)) (Ty.whnf_app _ _)
    refine ⟨τ', ?_, hz' (τ, τ') (by simp)⟩
    simp only [Ty.dataField, hys, hf', hzs, hp', hk', and_self, ↓reduceIte]

theorem Ty.dataFields_build {T : Ty} : ∀ (ls : List String) (τs : List Ty), ls.length = τs.length →
    (∀ l τ, (l, τ) ∈ ls.zip τs → ∃ τ', T.dataField l = some τ' ∧ TyEq τ τ') →
    ∃ τs', T.dataFields ls = some τs' ∧ TyEqs τs τs'
  | [], [], _, _ => ⟨[], rfl, .nil⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl
  | l :: ls, τ :: τs, hl, h => by
    obtain ⟨τ', h₁, he⟩ := h l τ (by simp)
    obtain ⟨τs', h₂, hes⟩ := Ty.dataFields_build ls τs (by simpa using hl)
      (fun l' τ'' hm => h l' τ'' (by simp [hm]))
    exact ⟨τ' :: τs', by simp [Ty.dataFields, h₁, h₂], .cons he hes⟩

/-- The slots of fields that all hold values. -/
theorem slots_of_data {T : Ty} : ∀ (ks : List FieldKind) (es : List Expr) (τs ss : List Ty),
    (∀ k ∈ ks, k = .data) → ks.length = es.length → es.length = τs.length →
    τs.length = ss.length →
    (∀ x ∈ ks.zip (es.zip (τs.zip ss)), FieldSlot T x.1 x.2.1 x.2.2.1 x.2.2.2) →
    ss = τs.map fun τ => .slot .pre .data τ
  | [], [], [], [], _, _, _, _, _ => rfl
  | [], [], [], _ :: _, _, _, _, h, _ => by simp at h
  | [], [], _ :: _, _, _, _, h, _, _ => by simp at h
  | [], _ :: _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h, _ => by simp at h
  | k :: ks, e :: es, τ :: τs, s :: ss, hk, h₁, h₂, h₃, hf => by
    have hs : FieldSlot T k e τ s := hf (k, e, τ, s) (by simp)
    rw [hk k (by simp)] at hs
    cases hs
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact slots_of_data ks es τs ss (fun k' h' => hk k' (by simp [h'])) (by simpa using h₁)
      (by simpa using h₂) (by simpa using h₃) (fun x hx => hf x (by simp [hx]))

theorem zip_trans_mem₃ {α : Type} : ∀ (es : List α) (τs τs' : List Ty), es.length = τs.length →
    τs.length = τs'.length → ∀ p ∈ es.zip τs', ∃ τ, (p.1, τ) ∈ es.zip τs ∧ (τ, p.2) ∈ τs.zip τs'
  | [], _, _, _, _, p, hp => by simp at hp
  | _ :: _, [], _, h, _, _, _ | _ :: _, _ :: _, [], _, h, _, _ => by simp at h
  | e :: es, τ :: τs, τ' :: τs', h₁, h₂, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨τ, by simp, by simp⟩
    · obtain ⟨τ'', h₃, h₄⟩ := zip_trans_mem₃ es τs τs' (by simpa using h₁) (by simpa using h₂) p hp
      exact ⟨τ'', by simp [h₃], by simp [h₄]⟩

theorem objTarget_whnf {T P : Ty} {ls : List String} {es : List Expr}
    (h : objTarget T ls es = some P) :
    (∃ L' ys, T.whnf = .app (.record L') ys ∧ P = T) ∨
      ∃ l ts Ps, T.whnf = .variant (.field l) ts Ps := by
  unfold objTarget at h
  split at h
  · rename_i L' ys hw; cases h; exact .inl ⟨L', ys, hw, rfl⟩
  · rename_i l ts Ps hw; exact .inr ⟨l, ts, Ps, hw⟩
  · cases h

/-- A check-mode derivation of an expression that takes the expected type in
ends, but for conversions, with that expression's rule in check mode: an
injection of its synthesised type is pushed into its parts. -/
theorem HasTypeS.check_top {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {e : Expr} {T : Ty} (hC : ∀ p ∈ C, p.AssumableAt false) (h : HasType L C Γ R rm .check e T)
    (hT : T.ftv = []) (hp : e.pushes T) : HasTypeTop L C Γ R rm .check e T := by
  cases h with
  | cond hc ht he => exact .cond hc ht he
  | let_ s F h₁ hv hs ha h₂ => exact .let_ s F h₁ hv hs ha h₂
  | letPoly a K h0 hp' hf hr h₁ hv hw h₂ => exact .letPoly a K h0 hp' hf hr h₁ hv hw h₂
  | ret h => exact .ret h
  | seq h₁ h₂ => exact .seq h₁ h₂
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch hb hh => exact .tryCatch hb hh
  | tryFinally hb hf => exact .tryFinally hb hf
  | unwrap h₁ hs h₂ h₃ => exact .unwrap h₁ hs h₂ h₃
  | funcCheck hw hT' hl hb => exact .funcCheck hw hT' hl hb
  | arrCheck hw hT' hes => exact .arrCheck hw hT' hes
  | litStr hw => exact .litStr hw
  | objCheck hc hnd hk hl hL hd he hf => exact .objCheck hc hnd hk hl hL hd he hf
  | caseTag h₁ hs h₂ h₃ => exact .caseTag h₁ hs h₂ h₃
  | inj h' _ hi =>
    obtain ⟨τ₀, he, ht⟩ := h'.top_synth
    have hi' : Entails C ⟨.inject T, [τ₀]⟩ :=
      hi.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons he.symm zip_tyEq_nil))
    cases ht with
    | cond hc ht he' => exact .cond hc (.inj ht hT hi') (.inj he' hT hi')
    | let_ s F h₁ hv hs ha h₂ => exact .let_ s F h₁ hv hs ha (.inj h₂ hT hi')
    | letPoly a K h0 hp' hf hr h₁ hv hw h₂ => exact .letPoly a K h0 hp' hf hr h₁ hv hw (.inj h₂ hT hi')
    | ret h => exact .ret h
    | seq h₁ h₂ => exact .seq h₁ (.inj h₂ hT hi')
    | break_ => exact .break_
    | continue_ => exact .continue_
    | tryCatch hb hh => exact .tryCatch (.inj hb hT hi') (.inj hh hT hi')
    | tryFinally hb hf => exact .tryFinally (.inj hb hT hi') hf
    | unwrap h₁ hs h₂ h₃ => exact .unwrap h₁ hs (.inj h₂ hT hi') (.inj h₃ hT hi')
    | caseTag h₁ hs h₂ h₃ => exact .caseTag h₁ hs (.inj h₂ hT hi') (.inj h₃ hT hi')
    | lit hl =>
      cases hl <;> simp only [Expr.pushes, decide_eq_true_eq, Bool.false_eq_true] at hp
      have := EntailsS.inject_app hC hi' (Ty.not_maybe_of_whnf hp (by simp)) (fun _ _ e => by rw [hp] at e; cases e)
      exact absurd (TyEq.con (this.trans (TyEq.of_whnf hp))) (by simp)
    | obj hes hks hτs hss hL hargs hfs =>
      rename_i ls ss es ks τs
      simp only [Expr.pushes, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨hts, hnd⟩, hk⟩ := hp
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hts
      rcases objTarget_whnf hP with ⟨L', ys, hw, -⟩ | ⟨l, ts, Ps, hw⟩
      · have hRT := EntailsS.inject_app hC hi' (Ty.not_maybe_of_whnf hw (by simp)) (fun _ _ e => by rw [hw] at e; cases e)
        have hks' : ∀ k ∈ ks, k = .data := fun k hk' => by
          rw [hk] at hk'; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hk'; rfl
        obtain rfl := slots_of_data ks es τs ss hks' (by omega) (by omega) (by omega)
          (fun x hx => hfs x hx)
        obtain ⟨τs', hd, hes'⟩ := Ty.dataFields_build (T := T) ls τs (by omega)
          (fun l τ hm => Ty.dataField_of_tyEq hRT.symm
            (objSlots_field_some hnd (hL l (List.of_mem_zip hm).1)
              (by rw [List.zip_map_right]; exact List.mem_map.mpr ⟨(l, τ), hm, rfl⟩)
              (by simp; omega)) (TyEq.refl _))
        have hτc := Ty.dataFields_closed hT hd
        obtain ⟨hl', hz'⟩ := hes'.zip_of
        have hslots : TyEqs (τs.map fun τ => Ty.slot .pre .data τ)
            (τs'.map fun τ => Ty.slot .pre .data τ) :=
          TyEqs.of_zip (by simp [hl']) (fun x hx => by
            rw [List.zip_map, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) (hz' y hy))
        refine .objCheck .self hnd hk hes hL hd
          (hRT.symm.trans (TyEq.app (objSlots_tyEqs hslots).zip_of.1
            (objSlots_tyEqs hslots).zip_of.2)) (fun p hp => ?_)
        obtain ⟨τ, hm₁, hm₂⟩ := zip_trans_mem₃ es τs τs' (by omega) hl' p hp
        have hc := hτc p.2 (List.of_mem_zip hp).2
        exact .inj (hargs (p.1, τ) hm₁) hc (.inl (Pred.inject_self hc (hz' (τ, p.2) hm₂)))
      · have hRT := EntailsS.inject_app hC hi' (Ty.not_maybe_of_whnf hw (by simp)) (fun _ _ e => by rw [hw] at e; cases e)
        exact absurd (TyEq.con (hRT.trans (TyEq.of_whnf hw))) (by simp)
    | @func _ _ _ ρ' _ _ _ θ' τs' hlen hb =>
      simp only [Expr.pushes, Option.isSome_iff_exists] at hp
      obtain ⟨⟨T', θ, τs, ρ⟩, hft⟩ := hp
      obtain ⟨-, hw, hlen'⟩ := funcTarget_fst hft rfl
      have hfn := Ty.ftv_nil_of_whnf hw hT
      simp only [Ty.ftv, Ty.ftvs_eq, List.flatMap_cons, List.append_eq_nil_iff] at hfn
      have hρc : ρ.ftv = [] := hfn.2.1
      have heq : TyEq (.fn θ' τs' ρ') (.fn θ τs ρ) :=
        (EntailsS.inject_app hC hi' (Ty.not_maybe_of_whnf hw (by simp)) (fun _ _ e => by rw [hw] at e; cases e)).trans (TyEq.of_whnf hw)
      obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp heq
      have hθ : TyEq θ' θ := hz (θ', θ) (by simp)
      have hρ : TyEq ρ' ρ := hz (ρ', ρ) (by simp)
      have hτs : TyEqs τs' τs := TyEqs.of_zip (by simpa using hl)
        (fun x hx => hz x (by simp [hx]))
      refine .funcCheck hw hT hlen' ?_
      have hb' := (hb.checkRet rfl rfl hρ hρc).weaken
        (CtxEq.monos hτs (CtxEq.cons (SchemeEq.of_mono (TyEq.fn_mk hθ hρ hτs))
          (CtxEq.cons (SchemeEq.of_mono hθ) (CtxEq.refl Γ)))).ctxGen (RetEq.refl _) (fun _ => rfl)
      exact .inj hb' hρc (.inl (Pred.inject_self hρc hρ))
    | @arr _ _ _ _ _ σ' hes =>
      simp only [Expr.pushes, Option.isSome_iff_exists] at hp
      obtain ⟨⟨T', σ⟩, hat⟩ := hp
      obtain ⟨-, hw⟩ := arrTarget_fst hat rfl
      have hσc : σ.ftv = [] := by simpa [Ty.ftv] using Ty.ftv_nil_of_whnf hw hT
      have heq : TyEq (.array σ') (.array σ) :=
        (EntailsS.inject_app hC hi' (Ty.not_maybe_of_whnf hw (by simp)) (fun _ _ e => by rw [hw] at e; cases e)).trans (TyEq.of_whnf hw)
      have hσ : TyEq σ' σ := (TyEq.app_iff.mp heq).2.2 (σ', σ) (by simp)
      exact .arrCheck hw hT (fun e he => .inj (hes e he) hσc (.inl (Pred.inject_self hσc hσ)))
    | _ => simp [Expr.pushes] at hp
  | drop h' =>
    -- Dropped: the synthesised derivation's parts are checked against
    -- `unknown` in its place.
    obtain ⟨_, -, ht⟩ := h'.top_synth
    cases ht with
    | cond hc ht he' => exact .cond hc (.drop ht) (.drop he')
    | let_ s F h₁ hv hs ha h₂ => exact .let_ s F h₁ hv hs ha (.drop h₂)
    | letPoly a K h0 hp' hf hr h₁ hv hw h₂ => exact .letPoly a K h0 hp' hf hr h₁ hv hw (.drop h₂)
    | ret h => exact .ret h
    | seq h₁ h₂ => exact .seq h₁ (.drop h₂)
    | break_ => exact .break_
    | continue_ => exact .continue_
    | tryCatch hb hh => exact .tryCatch (.drop hb) (.drop hh)
    | tryFinally hb hf => exact .tryFinally (.drop hb) hf
    | unwrap h₁ hs h₂ h₃ => exact .unwrap h₁ hs (.drop h₂) (.drop h₃)
    | caseTag h₁ hs h₂ h₃ => exact .caseTag h₁ hs (.drop h₂) (.drop h₃)
    | lit hl => cases hl <;> simp [Expr.pushes] at hp
    | _ => simp [Expr.pushes, funcTarget, arrTarget, objTarget] at hp

/-- A derivation in the mode an expected type gives an expression that takes
it in ends, but for conversions, with that expression's rule. -/
theorem HasTypeS.top_ex {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {ex : Option Ty} {e : Expr} {τ' : Ty} (hC : ∀ p ∈ C, p.AssumableAt false)
    (hex : Ex.Closed ex) (hτ : ∀ T ∈ ex, τ' = T) (hp : ∀ T ∈ ex, e.pushes T)
    (h : HasType L C Γ R rm (Ex.mode ex) e τ') :
    ∃ τ₀, TyEq τ₀ τ' ∧ (∀ T ∈ ex, τ₀ = T) ∧ HasTypeTop L C Γ R rm (Ex.mode ex) e τ₀ := by
  match ex, hex with
  | none, _ =>
    obtain ⟨τ₀, he, ht⟩ := h.top_synth
    exact ⟨τ₀, he, (fun _ h => by cases h), ht⟩
  | some T, hex =>
    obtain rfl := hτ T rfl
    exact ⟨τ', TyEq.refl _, (fun _ h => by cases h; rfl), h.check_top hC (hex τ' rfl) (hp τ' rfl)⟩

/-- The type `return`, `break` and `continue` get: the expected one, or a
fresh variable. -/
theorem exTy_tyEq {ex : Option Ty} {τ₀ τ' : Ty} (hex : Ex.Closed ex) (hτT : ∀ T ∈ ex, τ₀ = T)
    (hτ₀ : TyEq τ₀ τ') (m : Nat) (φ : Subst) :
    TyEq ((ex.getD (.var m)).subst ((m, τ₀) :: φ)) τ' := by
  cases ex with
  | none => simp only [Option.getD_none, Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]; exact hτ₀
  | some T =>
    simp only [Option.getD_some, Ty.closed_subst (hex T rfl)]
    rw [← hτT T rfl]; exact hτ₀

theorem infer_complete_lit (L : List String) (l : Lit) :
    (Expr.lit l).PolyOK L → InferComplete L (Expr.lit l) := by
  intro _
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC _ _ ht
  obtain ⟨hmd, hmT⟩ := hm
  by_cases hp : ∃ T, ex = some T ∧ (Expr.lit l).pushes T
  · -- A string literal checked against its own string type.
    obtain ⟨T, rfl, hp⟩ := hp
    have hT := hex T rfl
    simp only [exMode, hp, ↓reduceIte] at hmd; subst hmd
    obtain rfl := hmT T rfl hp
    refine ⟨⟨[], τ', [], n⟩, by simp [infer, Option.filter, hp], ψ, Agree.nil n ψ, ?_,
      by simp [Sat]⟩
    rw [Ty.closed_subst hT]; exact TyEq.refl _
  have hf : (ex.filter fun T => (Expr.lit l).pushes T) = none := by
    cases ex with
    | none => rfl
    | some T => simp only [Option.filter]; split <;> simp_all
  rw [exMode_of_filter_none hf] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | lit hl =>
    refine ⟨⟨[], l.ty, [], n⟩, by simp [infer, hf], ψ, Agree.nil n ψ, ?_, by simp [Sat]⟩
    rw [LitTy.eq_ty hl] at hτ₀
    simpa [Lit.ty_subst] using hτ₀

theorem infer_complete_var (L : List String) (i : Nat) :
    (Expr.var i).PolyOK L → InferComplete L (Expr.var i) := by
  intro _
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR _ hΓ' _ ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @var _ _ s' _ _ _ τs hi hlen hc =>
    have hi' : i < (Ctx.subst ψ Γ).length := hΓ'.1 ▸ (List.getElem?_eq_some_iff.mp hi).1
    have hsg := List.getElem?_eq_getElem hi'
    rw [Ctx.getElem?_subst] at hsg
    cases hs : Γ[i]? with
    | none => simp [hs] at hsg
    | some s =>
      have hse : SchemeEq s' (s.subst ψ) :=
        hΓ'.2 i s' _ hi (by rw [Ctx.getElem?_subst, hs]; rfl)
      have hlen' : τs.length = s.arity := by rw [hlen, hse.1]; simp
      obtain ⟨hte, hpe⟩ := hse.2.2 τs hlen
      refine ⟨⟨[], s.open n, s.openPreds n, n + s.arity⟩, by simp [infer, hs],
        Subst.block n τs ++ ψ, fun a ha => ?_, ?_, fun c hc' => ?_⟩
      · simp only [Ty.subst_nil]
        rw [Ty.subst_block_fresh (Ty.Below.var ha)]; exact TyEq.refl _
      · rw [Scheme.open_block_append (hΓ.lookup hs) hlen']; exact hte.symm.trans hτ₀
      · have hm : c.subst (Subst.block n τs ++ ψ) ∈ (s.subst ψ).instPreds τs := by
          rw [← Scheme.openPreds_block_append (hΓ.lookup hs) hlen']
          exact List.mem_map_of_mem hc'
        obtain ⟨d, hd, hde⟩ := List.exists_of_zip (R := PredEq)
          (by simp [Scheme.instPreds, hse.2.1]) hpe _ hm
        exact (hc d hd).of_predEq hde

theorem infer_complete_func (L : List String) (k : Nat) (body : Expr) (ih : body.PolyOK L → InferComplete L body) :
    (Expr.func k body).PolyOK L → InferComplete L (Expr.func k body) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L body := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' _ ht
  obtain ⟨hmd, hmT⟩ := hm
  cases hft : funcTarget ex k with
  | some x =>
    obtain ⟨T, θ, τs, ρ⟩ := x
    obtain rfl := funcTarget_some hft
    obtain ⟨-, hw, -⟩ := funcTarget_fst hft rfl
    have hT := hex T rfl
    have hp : (Expr.func k body).pushes T = true := by simp [Expr.pushes, hft]
    obtain rfl := hmT T rfl hp
    simp only [exMode, hp, ↓reduceIte] at hmd; subst hmd
    have hfn := Ty.ftv_nil_of_whnf hw hT
    have hf := hfn
    simp only [Ty.ftv, Ty.ftvs_eq, List.flatMap_cons, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff] at hf
    obtain ⟨hθ, hρ, hτs⟩ := hf
    cases ht.check_top hC hT hp with
    | funcCheck hw' _ _ hb =>
      rw [hw] at hw'
      simp only [Ty.fn, Ty.app.injEq, List.cons.injEq, true_and] at hw'
      obtain ⟨rfl, rfl, rfl⟩ := hw'
      have hctx : Ctx.subst ψ (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) =
          τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Ctx.subst ψ Γ := by
        rw [Ctx.subst_append_monos hτs, Ctx.subst_cons, Ctx.subst_cons, Scheme.mono_subst,
          Scheme.mono_subst, Ty.closed_subst hfn, Ty.closed_subst hθ]
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check ih
        (Γ := τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (R := some ρ) (ψ := ψ)
        (RetOk.check hρ) (fun _ => rfl) (Ex.Closed.some hρ) (fun _ h => by cases h; rfl)
        (Ctx.Below.append_mono (fun τ hτ => Ty.Below.closed (hτs τ hτ))
          (Ctx.Below.mono_cons (Ty.Below.closed hfn) (Ctx.Below.mono_cons (Ty.Below.closed hθ) hΓ)))
        (fun a ha => by simp [Ret.ftv, hρ] at ha) hC
        (by rw [hctx]; exact CtxEq.append_left _ (CtxEq.cons (SchemeEq.refl _)
          (CtxEq.cons (SchemeEq.refl _) hΓ')))
        (by simp only [Ret.subst_some, Ty.closed_subst hρ]; exact TyEq.refl _) hb
      refine ⟨⟨o₁.σ, τ', o₁.preds, o₁.next⟩, by simp only [infer, hft, h₁], φ₁, hag₁, ?_, hsat₁⟩
      rw [Ty.closed_subst hT]; exact TyEq.refl _
  | none =>
    have hmd' : md = .synth := by
      rw [hmd]
      cases ex with
      | none => rfl
      | some T => simp [exMode, Expr.pushes, hft]
    subst hmd'
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
    cases ht with
    | @func _ _ _ ρ' _ _ _ θ' τs' hlen hb =>
      subst hlen
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
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none (R := some (.var (n + 1 + τs'.length)))
        (ψ := funSubst n θ' τs' ρ' ψ)
        (Ctx.Below.append_mono hτs (Ctx.Below.mono_cons hfn (Ctx.Below.mono_cons hθ
          (hΓ.mono (by omega)))))
        (fun a ha => hρ a (by simpa [Ret.ftv] using ha)) hC
        (by rw [← hctx]; exact CtxEq.append_left _ (CtxEq.cons (SchemeEq.refl _)
          (CtxEq.cons (SchemeEq.refl _) hΓ')))
        (by simp only [Ret.subst_some, funSubst_ret]; exact TyEq.refl _) hb
      have hu : TyEq (((Ty.var (n + 1 + τs'.length)).subst o₁.σ).subst φ₁) (o₁.τ.subst φ₁) := by
        refine (hag₁ _ (by omega)).trans ?_
        rw [funSubst_ret]; exact hτ₁.symm
      obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, hft, h₁, hσ']; rfl, φ₁, fun a ha => ?_, ?_, ?_⟩
      · refine (hag₁.absorb habs a (by omega)).trans ?_
        simp only [Ty.subst, funSubst_below ha]; exact TyEq.refl _
      · refine ((hag₁.absorb habs).ty hfn).trans ?_
        simp only [Ty.subst_fn, funSubst_this, funSubst_ret, hparams]; exact hτ₀
      · exact Sat.absorb habs hsat₁

theorem infer_complete_app (L : List String) (f : Expr) (args : List Expr) (ihf : f.PolyOK L → InferComplete L f) (iha : ∀ a ∈ args, a.PolyOK L → InferComplete L a) :
    (Expr.app f args).PolyOK L → InferComplete L (Expr.app f args) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ihf : InferComplete L f := ihf hm.1
  replace iha : ∀ a ∈ args, InferComplete L a := fun a ha => iha a ha (hm.2 a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | app hf hlen hargs =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihf (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' hf
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L f (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (by ret_ok) (by ret_eq) .none (fun _ h => nomatch h) (ψ := φ₁)
      hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
    obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) (by ret_ok) .none hΓ₁ hR₁ h₂
    have hu : TyEq ((o₁.τ.subst o₂.σ).subst ((o₂.next, τ₀) :: φ₂))
        ((Ty.fn .undefined o₂.τs (.var o₂.next)).subst ((o₂.next, τ₀) :: φ₂)) := by
      rw [Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono hn₂))]
      refine (hag₂.ty hτb₁).trans (hτ₁.trans ?_)
      simp only [Ty.subst_fn]
      refine TyEq.fn_mk (TyEq.refl _) (by simp [Ty.subst, Subst.find]; exact TyEq.refl _) ?_
      rw [List.map_congr_left (fun τ hτ => Ty.subst_cons_fresh (hτsb₂ τ hτ))]
      exact hτs₂.symm
    obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu hu
    refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, (o₂.next, τ₀) :: φ₂, ?_, ?_, ?_⟩
    · exact Agree.absorb ((hag₁.trans hσ₁ hn₁ hag₂).fresh ((hσ₁.mono hn₂).compose hσ₂)
        (by omega)) habs
    · refine (habs _).trans ?_
      simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]; exact hτ₀
    · refine Sat.absorb habs (Sat.app ?_ ?_)
      · refine Sat.fresh (fun p hp => ?_) (Sat.agree hag₂ hp₁ hsat₁)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact Sat.fresh hp₂ hsat₂

theorem Pred.AssumableAt.rsub {p : Pred} (h : p.AssumableAt false) (ρ : RSubst) :
    (p.rsub ρ).AssumableAt false := by
  obtain ⟨cls, args⟩ := p
  rcases h with ⟨hc, hl, a, rest, ha⟩ | ⟨q, k, τ, s, r, he, -⟩
  · simp only at hc hl ha
    subst ha
    refine .inl ⟨fun e => hc ?_, ?_, a, rest.map (·.rsub ρ), rfl⟩
    · cases cls <;> simp_all [Pred.rsub, Cls.rsub]
    · cases cls <;> simp_all [Pred.rsub, Cls.rsub, Cls.arity]
  · cases he
    exact .inr ⟨q.rsub ρ, k.rsub ρ, τ.rsub ρ, s.rsub ρ, r.rsub ρ, rfl, nofun⟩

/-- The case of a polymorphic annotation: the typing checks the initialiser
at any rigid names outside a finite set; renamed, it checks it at
inference's, inference succeeds there, and where no rigid variable escapes
(`RigidStays`), the rest is typed at the annotation as before. -/
theorem infer_complete_letPoly {L : List String} {mb : Bool} {a : Scheme} {e₁ e₂ : Expr}
    (ih₁ : InferComplete L e₁) (ih₂ : InferComplete L e₂) (hrs : RigidStays L a e₁)
    {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
    {τ₀ : Ty} {Γ' : Ctx} {R' : Option Ty} {K : List Nat}
    (hRo : RetOk rm R) (hRc : rm = .check → R' = R) (hex : Ex.Closed ex) (hτT : ∀ T ∈ ex, τ₀ = T)
    (hΓ : Ctx.Below n Γ) (hR : Ret.Below n R) (hC : ∀ p ∈ C, p.AssumableAt false)
    (hΓ' : CtxEq Γ' (Ctx.subst ψ Γ)) (hR' : RetEq R' (Ret.subst ψ R))
    (h0 : 0 < a.arity) (hp : a.preds = []) (hf : a.ftv = []) (hr : a.rkeys = [])
    (hgen : ∀ k, k ∉ K → HasType L C Γ' R' rm .check e₁ (a.inst (rigids k a.arity)))
    (hv : e₁.IsValue) (hw : e₂.writes 0 = false)
    (h₂ : HasType L C (a :: Γ') R' rm (Ex.mode ex) e₂ τ₀) :
    ∃ o, infer L Γ R rm ex (.let_ mb (some a) e₁ e₂) n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
      TyEq (o.τ.subst φ) τ₀ ∧ Sat C o.preds φ := by
  -- Inference's rigid name, fresh for its context.
  have hkΓ : maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ ctxRkeys Γ := fun h =>
    Nat.lt_irrefl _ (lt_maxPlusOne _ (List.mem_append_left _ h))
  have hkR : maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ Ret.rkeys R := fun h =>
    Nat.lt_irrefl _ (lt_maxPlusOne _ (List.mem_append_right _ h))
  generalize hk : maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) = k at hkΓ hkR
  have hT := Scheme.inst_rigids_closed hf k a.arity
  -- The typing at a name `k'`, renamed to `k`, is one inference completes.
  have key : ∀ k', k' ∉ K → k' ≠ k → k' ∉ ctxRkeys Γ → k' ∉ Ret.rkeys R →
      ∃ o₁, (infer L Γ R rm (some (a.inst (rigids k a.arity))) e₁ n).map
          (checkEx (some (a.inst (rigids k a.arity))) e₁) = some o₁ ∧
        ∃ φ, Agree n o₁.σ φ (Subst.rsub (RSubst.swap k' k) ψ) ∧
          TyEq (o₁.τ.subst φ) (a.inst (rigids k a.arity)) ∧
          Sat (C.map (Pred.rsub (RSubst.swap k' k))) o₁.preds φ := by
    intro k' hK hne hk'Γ hk'R
    have hren := RSubst.swap_renaming k' k
    have hinv := RSubst.swap_invol k' k
    have h := (hgen k' hK).rsub (Sys.narrow_rsubstable hren) [k', k]
      (fun _ _ _ h => RSubst.swap_dom h)
    rw [← Scheme.inst_rsub, Scheme.rsub_of_rkeys_nil _ hr, rigids_rsub_swap] at h
    refine InferComplete.check ih₁ hRo (fun hc => ?_) (Ex.Closed.some hT) (fun _ h => by cases h; rfl)
      hΓ hR (fun p hp => ?_) ?_ ?_ h
    · rw [hRc hc]; exact ret_rsub_off (RSubst.swap_off hk'R hkR)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact (hC q hq).rsub _
    · have := hΓ'.rsub hinv
      rwa [Ctx.subst_rsub hren, ctx_rsub_off (RSubst.swap_off hk'Γ hkΓ)] at this
    · have := hR'.rsub (RSubst.swap k' k)
      rwa [Ret.subst_rsub hren, ret_rsub_off (RSubst.swap_off hk'R hkR)] at this
  -- Inference succeeds on the initialiser, and improvement on what it leaves.
  have fresh : ∀ {l l' : List Nat}, (∀ x ∈ l', x ∈ l) → maxPlusOne l ∉ l' := fun hl h =>
    Nat.lt_irrefl _ (lt_maxPlusOne _ (hl _ h))
  have hC' : ∀ ρ, ∀ c ∈ C.map (Pred.rsub ρ), c.AssumableAt false := fun ρ c hc => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc; exact (hC q hq).rsub _
  have nek : ∀ {l : List Nat}, k ∈ l → maxPlusOne l ≠ k := fun hl e =>
    fresh (l' := [k]) (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hl)
      (List.mem_singleton.mpr e)
  obtain ⟨o₁, h₁o, φ₀, -, -, hsat₀⟩ := key (maxPlusOne (K ++ [k] ++ ctxRkeys Γ ++ Ret.rkeys R))
    (fresh (fun x hx => by simp [hx])) (nek (by simp)) (fresh (fun x hx => by simp [hx]))
    (fresh (fun x hx => by simp [hx]))
  obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check (infer_inv L e₁) hRo (Ex.Closed.some hT) hΓ hR h₁o
  obtain ⟨σi, preds₁, himp, -⟩ := improveAll_complete (hC' _) o₁.preds.length (Nat.le_refl _) hsat₀
  obtain ⟨hnΓ, hnR, hescp⟩ :=
    hk ▸ hrs hRo hRc hΓ hR hC hΓ' hR' hgen (by rw [hk]; exact h₁o) himp
  -- A second name, fresh for what inference found and the typing's
  -- instance too.
  generalize hks : K ++ [k] ++ ctxRkeys Γ ++ Ret.rkeys R ++
    (List.range n).flatMap (fun b => ((Ty.var b).subst (Subst.compose σi o₁.σ)).rkeys) ++
    preds₁.flatMap Pred.rkeys ++ (List.range n).flatMap (fun b => ((Ty.var b).subst ψ).rkeys) = ks
  have hk'σ : ∀ b < n, maxPlusOne ks ∉ ((Ty.var b).subst (Subst.compose σi o₁.σ)).rkeys := by
    intro b hb
    refine fresh (fun x hx => ?_)
    subst hks
    simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inl (.inl (.inr ⟨b, hb, hx⟩))
  have hk'p : maxPlusOne ks ∉ preds₁.flatMap Pred.rkeys :=
    fresh (fun x hx => by subst hks; exact List.mem_append_left _ (List.mem_append_right _ hx))
  have hk'ψ : ∀ b < n, maxPlusOne ks ∉ ((Ty.var b).subst ψ).rkeys := by
    intro b hb
    refine fresh (fun x hx => ?_)
    subst hks
    simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inr ⟨b, hb, hx⟩
  obtain ⟨o₁', h₁o', φ₁, hag₁, -, hsat₁⟩ := key (maxPlusOne ks)
    (fresh (fun x hx => by subst hks; simp [hx])) (nek (by subst hks; simp))
    (fresh (fun x hx => by subst hks; simp [hx])) (fresh (fun x hx => by subst hks; simp [hx]))
  obtain rfl : o₁ = o₁' := Option.some.inj (h₁o.symm.trans h₁o')
  have hk'k : maxPlusOne ks ≠ k := nek (by subst hks; simp)
  generalize maxPlusOne ks = k' at hk'σ hk'p hk'ψ hk'k hag₁ hsat₁
  obtain ⟨σi', preds₁', himp', habsi, hsat₁', -, -⟩ :=
    improveAll_complete (hC' _) o₁.preds.length (Nat.le_refl _) hsat₁
  obtain ⟨rfl, rfl⟩ : σi = σi' ∧ preds₁ = preds₁' := by
    simpa using himp.symm.trans himp'
  obtain ⟨hσi, hpi⟩ := improveAll_inv _ hp₁ himp
  have hσ₁' := hσ₁.compose hσi
  have hagS := hag₁.absorb habsi
  -- Renamed back, `φ₁` is an instance at the typing's names.
  have hren := RSubst.swap_renaming k' k
  have hinv := RSubst.swap_invol k' k
  have hψb : ∀ b, ((Ty.var b).subst (Subst.rsub (RSubst.swap k' k) ψ)).rsub (RSubst.swap k' k) =
      (Ty.var b).subst ψ := fun b => by
    rw [show (Ty.var b).subst (Subst.rsub (RSubst.swap k' k) ψ) =
      ((Ty.var b).rsub (RSubst.swap k' k)).subst (Subst.rsub (RSubst.swap k' k) ψ) from rfl,
      ← Ty.subst_rsub hren, Ty.rsub_invol hinv]
  -- In a context where the typing types the initialiser, the rigid name is
  -- never in the tree of a context variable's instance: renamed, it would
  -- be `k'` in the typing's, which `k'` is fresh for.
  have hstay : ∀ b < n, ¬ ((Ty.var b).subst (Subst.compose σi o₁.σ)).TreeRk k := by
    intro b hb ht
    have h₁ := TyEq.treeRk (hagS b hb) (ht.subst φ₁)
    rw [show (Ty.var b).subst (Subst.rsub (RSubst.swap k' k) ψ) =
      ((Ty.var b).subst ψ).rsub (RSubst.swap k' k) by rw [← hψb b, Ty.rsub_invol hinv]] at h₁
    exact hk'ψ b hb (Ty.TreeRk.of_swap (Ne.symm hk'k) h₁).rkeys
  have hagT : Agree n (Subst.compose σi o₁.σ) (Subst.rsub (RSubst.swap k' k) φ₁) ψ := by
    intro b hb
    have hsw := Ty.rsub_swap_tyEq (hstay b hb) (fun h => hk'σ b hb h.rkeys)
    refine (TyEq.subst _ hsw).symm.trans ?_
    rw [← Ty.subst_rsub hren]
    exact hψb b ▸ TyEq.rsub _ (hagS b hb)
  have hCC : (C.map (Pred.rsub (RSubst.swap k' k))).map (Pred.rsub (RSubst.swap k' k)) = C := by
    simp only [List.map_map]
    exact (List.map_congr_left fun p _ => Pred.rsub_invol hinv p).trans (List.map_id _)
  have hsatT : Sat C preds₁ (Subst.rsub (RSubst.swap k' k) φ₁) := fun p hp => by
    have hoff : (RSubst.swap k' k).Off p.rkeys := RSubst.swap_off
      (fun h => hk'p (List.mem_flatMap.mpr ⟨p, hp, h⟩))
      (fun h => hescp (List.mem_flatMap.mpr ⟨p, hp, h⟩))
    have := (hsat₁' p hp).rsubS (Sys.narrow_rsubstable hren)
    rwa [hCC, Pred.subst_rsub hren, Pred.rsub_off hoff] at this
  -- The rest, typed at the annotation.
  obtain ⟨o₂, h₂o, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂
    (Γ := a :: Ctx.subst (Subst.compose σi o₁.σ) Γ) (R := Ret.subst (Subst.compose σi o₁.σ) R)
    (ψ := Subst.rsub (RSubst.swap k' k) φ₁) (hRo.subst _) (RetOk.eq_subst hRo hRc _) hex hτT
    (Ctx.Below.cons (fun b hb => by simp [hf] at hb) (hσ₁'.ctx_below (hΓ.mono hn₁)))
    (hσ₁'.ret_below (hR.mono hn₁)) hC
    (by
      simp only [Ctx.subst_cons, Scheme.subst_of_ftv_nil _ hf]
      exact CtxEq.cons (SchemeEq.refl _) (hΓ'.trans (hagT.ctx hΓ).symm))
    (hR'.trans (hagT.ret hR).symm) h₂
  refine ⟨⟨Subst.compose o₂.σ (Subst.compose σi o₁.σ), o₂.τ,
    preds₁.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩, ?_, φ₂, hagT.trans hσ₁' hn₁ hag₂, hτ₂,
    Sat.app (Sat.agree hag₂ hpi hsatT) hsat₂⟩
  have hgz : Expr.generalises e₁ e₂ = true := by
    simp [Expr.generalises, Expr.isValue_complete hv, hw]
  subst hk
  simp only [infer, Nat.pos_iff_ne_zero.mp h0, hp, hf, hr, h0, hgz, h₁o, himp, hnΓ, hnR, hescp,
    h₂o, false_and, and_self, ↓reduceIte, or_self]

theorem infer_complete_let_ (L : List String) (mb : Bool) (ann : Option Scheme) (e₁ : Expr) (e₂ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) :
    (Expr.let_ mb ann e₁ e₂).PolyOK L → InferComplete L (Expr.let_ mb ann e₁ e₂) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  obtain ⟨⟨hann, hm₁⟩, hm₂⟩ := hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm₁
  replace ih₂ : InferComplete L e₂ := ih₂ hm₂
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ann with
  | some a =>
    cases ht with
    | let_ s F hgen hval hsimp hann h₂ =>
      subst hmd'
      obtain ⟨hs, har, hap, haf, har₀⟩ := hann a rfl
      subst a
      have hcl : ∀ ψ, s.subst ψ = s := fun ψ => Scheme.subst_of_ftv_nil ψ haf
      have hop : ∀ m, s.open m = s.inst [] := fun m => by simp [Scheme.open, har, varBlock]
      have hopp : ∀ m, s.openPreds m = [] := fun m => by
        simp [Scheme.openPreds, Scheme.instPreds, hap]
      have hT := Scheme.inst_nil_closed haf
      have h₁ := hgen (maxPlusOne F) (fun a ha => lt_maxPlusOne a ha)
      rw [hop, hopp, List.append_nil] at h₁
      obtain ⟨o₁, h₁o, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check ih₁ hRo hRc (Ex.Closed.some hT)
        (fun _ h => by cases h; rfl) hΓ hR hC hΓ' hR' h₁
      obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check (infer_inv L e₁) hRo (Ex.Closed.some hT) hΓ hR h₁o
      obtain ⟨o₂, h₂o, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂
        (Γ := s :: Ctx.subst o₁.σ Γ) (R := Ret.subst o₁.σ R) (ψ := φ₁) (hRo.subst _)
        (RetOk.eq_subst hRo hRc _) hex hτT
        (Ctx.Below.cons (fun b hb => by simp [haf] at hb) (hσ₁.ctx_below (hΓ.mono hn₁)))
        (hσ₁.ret_below (hR.mono hn₁)) hC
        (by
          simp only [Ctx.subst_cons, hcl]
          exact CtxEq.cons (SchemeEq.refl _) (hΓ'.trans (hag₁.ctx hΓ).symm))
        (hR'.trans (hag₁.ret hR).symm) h₂
      refine ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
        ?_, φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂.trans hτ₀, Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩
      simp only [infer, har, hap, haf, har₀, and_self, ↓reduceIte, h₁o, h₂o]
    | letPoly _ K h0 hp hf hr hgen hv hw h₂ =>
      subst hmd'
      obtain ⟨o, ho, φ, hag, hτ, hsat⟩ := infer_complete_letPoly ih₁ ih₂ (hann a rfl h0) hRo hRc hex
        hτT hΓ hR hC hΓ' hR' h0 hp hf hr hgen hv hw h₂
      exact ⟨o, ho, φ, hag, hτ.trans hτ₀, hsat⟩
  | none =>
  cases ht with
  | let_ s F hgen hval hsimp _ h₂ =>
    subst hmd'
    replace hsimp : s.Simple := hsimp.resolve_left (by simp [Sys.narrow])
    -- Open `s` at a block of variables fresh for everything in sight.
    obtain ⟨m, hmF, hms, hmC, hmψ⟩ : ∃ m, (∀ a ∈ F, a < m) ∧ (∀ a ∈ s.ftv, a < m) ∧
        (∀ p ∈ C, ∀ a ∈ p.ftv, a < m) ∧
        (∀ a < n, ∀ b ∈ ((Ty.var a).subst ψ).ftv, b < m) := by
      have h := lt_maxPlusOne (l := F ++ s.ftv ++ C.flatMap Pred.ftv ++
        (List.range n).flatMap (fun a => ((Ty.var a).subst ψ).ftv))
      refine ⟨_, fun a ha => h a (by simp [ha]), fun a ha => h a (by simp [ha]),
        fun p hp a ha => h a ?_, fun a ha b hb => h b ?_⟩
      · simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨p, hp, ha⟩)
      · simp only [List.mem_append, List.mem_flatMap, List.mem_range]; exact .inr ⟨a, ha, hb⟩
    have hC₁ := assumable_open hC hsimp m
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ (by ret_ok) (by ret_eq) .none .none hΓ hR hC₁ hΓ' hR' (hgen m hmF)
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ (by ret_ok) .none hΓ hR h₁
    -- Improvement succeeds, and `φ₁` absorbs it.
    obtain ⟨σi, preds₁, himp, habsi, hsat₁', hkeep, _⟩ :=
      improveAll_complete hC₁ o₁.preds.length (Nat.le_refl _) hsat₁
    obtain ⟨hσi, hpi⟩ := improveAll_inv _ hp₁ himp
    have hσ₁' := hσ₁.compose hσi
    have hagS : Agree n (Subst.compose σi o₁.σ) φ₁ ψ := hag₁.absorb habsi
    have hτ₁' : TyEq ((o₁.τ.subst σi).subst φ₁) (s.open m) := (habsi _).trans hτ₁
    have hτb₁' := hσi.subst_below hτb₁
    have hΓ₁ : Ctx.Below o₁.next (Ctx.subst (Subst.compose σi o₁.σ) Γ) :=
      hσ₁'.ctx_below (hΓ.mono hn₁)
    have hR₁ : Ret.Below o₁.next (Ret.subst (Subst.compose σi o₁.σ) R) :=
      hσ₁'.ret_below (hR.mono hn₁)
    -- The environment's variables are sent below the block.
    have henv : ∀ v ∈ ctxTv (Ctx.subst (Subst.compose σi o₁.σ) Γ) ++
        Ret.tv (Ret.subst (Subst.compose σi o₁.σ) R),
        ∀ b, ((Ty.var v).subst φ₁).TV b → b < m := by
      intro v hv b hb
      obtain ⟨a, ha, hav⟩ : ∃ a, a < n ∧ ((Ty.var a).subst (Subst.compose σi o₁.σ)).TV v := by
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨a, ha, hav⟩ := ctxTv_subst hv; exact ⟨a, hΓ a ha, hav⟩
        · obtain ⟨a, ha, hav⟩ := Ret.tv_subst hv; exact ⟨a, hR a ha, hav⟩
      have := (hagS a ha).tv.mp (Ty.TV.subst_of hav hb)
      exact hmψ a ha b this.ftv
    obtain ⟨hall, hgz, hw, hsatr⟩ := letScheme_complete (e₁ := e₁) (e₂ := e₂) hC hsimp hmC hms
      hτ₁' hsat₁' hkeep henv hval
    have hls := letScheme_below (gen := Expr.generalises e₁ e₂)
      (Γ₁ := Ctx.subst (Subst.compose σi o₁.σ) Γ) (R₁ := Ret.subst (Subst.compose σi o₁.σ) R)
      hτb₁' hpi
    rcases hlsq : letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
      (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁ with ⟨s₁, rest⟩
    rw [hlsq] at hls hall hgz hw hsatr
    -- The rest's typing moves to the more general scheme.
    have h₂' : HasType L C (s₁.subst φ₁ :: Γ') R' rm (Ex.mode ex) e₂ τ₀ := by
      refine h₂.weaken ⟨by simp, fun i t t' ht ht' => ?_⟩ (RetEq.refl _) (fun _ => rfl)
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ht ht'
        subst ht ht'
        exact ⟨hgz, hw⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at ht ht'
        rw [ht] at ht'; cases ht'
        exact ⟨Generalizes.refl C t, .inl id⟩
    obtain ⟨o₂, h₂o, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂
      (Γ := s₁ :: Ctx.subst (Subst.compose σi o₁.σ) Γ)
      (R := Ret.subst (Subst.compose σi o₁.σ) R) (ψ := φ₁) (hRo.subst _) (RetOk.eq_subst hRo hRc _)
      hex hτT (Ctx.Below.cons hls.1 hΓ₁) hR₁ hC
      (by
        simp only [Ctx.subst_cons]
        exact CtxEq.cons (SchemeEq.refl _) (hΓ'.trans (hagS.ctx hΓ).symm))
      (hR'.trans (hagS.ret hR).symm) h₂'
    refine ⟨⟨Subst.compose o₂.σ (Subst.compose σi o₁.σ), o₂.τ,
      rest.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩, ?_, φ₂, hagS.trans hσ₁' hn₁ hag₂,
      hτ₂.trans hτ₀, Sat.app (Sat.agree hag₂ hls.2 hsatr) hsat₂⟩
    simp only [infer, h₁, himp, hlsq, hall, ↓reduceIte, h₂o]

theorem infer_complete_assign (L : List String) (i : Nat) (e : Expr) (ih : e.PolyOK L → InferComplete L e) :
    (Expr.assign i e).PolyOK L → InferComplete L (Expr.assign i e) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L e := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @assign _ _ s' _ _ _ _ hi ha hp he =>
    have hi' : i < (Ctx.subst ψ Γ).length := hΓ'.1 ▸ (List.getElem?_eq_some_iff.mp hi).1
    have hsg := List.getElem?_eq_getElem hi'
    rw [Ctx.getElem?_subst] at hsg
    cases hs : Γ[i]? with
    | none => simp [hs] at hsg
    | some s =>
      have hse : SchemeEq s' (s.subst ψ) :=
        hΓ'.2 i s' _ hi (by rw [Ctx.getElem?_subst, hs]; rfl)
      have ha' : s.arity = 0 := by have := hse.1; simp at this; omega
      have hp' : s.preds = [] := by
        have := hse.2.1; simp [Scheme.subst, hp] at this
        exact List.eq_nil_of_length_eq_zero this.symm
      have hsi : TyEq (s'.inst []) ((s.inst []).subst ψ) := by
        rw [Scheme.inst_nil_subst]; exact (hse.2.2 [] (by simp [ha])).1
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' (he.conv hsi)
      have hsb : (s.inst []).Below n := Scheme.inst_nil_below (hΓ.lookup hs)
      have hu : TyEq (((s.inst []).subst o₁.σ).subst φ₁) (o₁.τ.subst φ₁) :=
        (hag₁.ty hsb).trans hτ₁.symm
      obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, hs, ha', hp', and_self, ↓reduceIte, h₁, hσ']; rfl, φ₁,
        hag₁.absorb habs, ?_, Sat.absorb habs hsat₁⟩
      show TyEq (((s.inst []).subst (Subst.compose σ' o₁.σ)).subst φ₁) _
      rw [Ty.subst_compose]
      exact (habs _).trans ((hag₁.ty hsb).trans (hsi.symm.trans hτ₀))

theorem infer_complete_cond (L : List String) (c : Expr) (t : Expr) (e : Expr) (ihc : c.PolyOK L → InferComplete L c) (iht : t.PolyOK L → InferComplete L t) (ihe : e.PolyOK L → InferComplete L e) :
    (Expr.cond c t e).PolyOK L → InferComplete L (Expr.cond c t e) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihc : InferComplete L c := ihc hm.1.1
  replace iht : InferComplete L t := iht hm.1.2
  replace ihe : InferComplete L e := ihe hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | cond hc htt hte =>
    subst hmd'
    obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' hc
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L c (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
    have hr₁ := hR'.trans (hag₁.ret hR).symm
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check iht (by ret_ok) (by ret_eq) hex hτT
      (ψ := φ₁) hΓ₁ hR₁ hC hc₁ hr₁ htt
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := InferInv.check (infer_inv L t) (by ret_ok) hex hΓ₁ hR₁ h₂
    have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
    have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
    obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := InferComplete.check ihe (by ret_ok) (by ret_eq) hex hτT
      (ψ := φ₂) hΓ₂ hR₂ hC (hc₁.trans (hag₂.ctx hΓ₁).symm) (hr₁.trans (hag₂.ret hR₁).symm) hte
    obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := InferInv.check (infer_inv L e) (by ret_ok) hex hΓ₂ hR₂ h₃
    have hu : TyEq ((o₂.τ.subst o₃.σ).subst φ₃) (o₃.τ.subst φ₃) :=
      (hag₃.ty hτb₂).trans (hτ₂.trans hτ₃.symm)
    obtain ⟨σ₄, hσ₄, habs⟩ := unify_mgu hu
    refine ⟨_, by simp only [infer, h₁, h₂, h₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
    · exact ((hag₁.trans hσ₁ hn₁ hag₂).trans ((hσ₁.mono hn₂).compose hσ₂) (by omega)
        hag₃).absorb habs
    · exact (habs _).trans (hτ₃.trans hτ₀)
    · refine Sat.absorb habs (Sat.app (Sat.agree hag₃ (fun p hp => ?_)
        (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂)) hsat₃)
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp

theorem infer_complete_unwrap (L : List String) (e₁ : Expr) (e₂ : Expr) (e₃ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) (ih₃ : e₃.PolyOK L → InferComplete L e₃) :
    (Expr.unwrap e₁ e₂ e₃).PolyOK L → InferComplete L (Expr.unwrap e₁ e₂ e₃) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm.1.1
  replace ih₂ : InferComplete L e₂ := ih₂ hm.1.2
  replace ih₃ : InferComplete L e₃ := ih₃ hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | @unwrap _ _ _ _ _ τ₁ σ _ _ _ _ h₁ hs h₂ h₃ =>
    subst hmd'
    obtain ⟨o₁, ho₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ (by ret_ok) (by ret_eq) .none .none hΓ hR hC
      hΓ' hR' h₁
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ (by ret_ok) .none hΓ hR ho₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
    have hr₁ := hR'.trans (hag₁.ret hR).symm
    obtain ⟨o₂, ho₂, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂ (by ret_ok) (by ret_eq) hex
      hτT (ψ := φ₁) hΓ₁ hR₁ hC hc₁ hr₁ h₂
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := InferInv.check (infer_inv L e₂) (by ret_ok) hex hΓ₁ hR₁ ho₂
    have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
    have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
    have hc₂ := hc₁.trans (hag₂.ctx hΓ₁).symm
    have hr₂ := hr₁.trans (hag₂.ret hR₁).symm
    have hfr := Agree.cons_fresh o₂.next σ φ₂
    have hβ : (Ty.var o₂.next).Below (o₂.next + 1) := .var (by omega)
    have hΓ₃ : Ctx.Below (o₂.next + 1) (.mono (.var o₂.next) :: Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) :=
      Ctx.Below.mono_cons hβ (hΓ₂.mono (by omega))
    have hR₃ := hR₂.mono (Nat.le_succ o₂.next)
    obtain ⟨o₃, ho₃, φ₃, hag₃, hτ₃, hsat₃⟩ := InferComplete.check ih₃ (by ret_ok) (by ret_eq) hex
      hτT (ψ := (o₂.next, σ) :: φ₂) hΓ₃ hR₃ hC
      (by
        simp only [Ctx.subst_cons, Scheme.mono_subst]
        refine CtxEq.cons (by simp [Ty.subst, Subst.find]; exact SchemeEq.refl _) ?_
        have := hfr.ctx hΓ₂
        simp only [Ctx.subst_nil] at this
        exact hc₂.trans this.symm)
      (by
        have := hfr.ret hR₂
        simp only [Ret.subst_nil] at this
        exact hr₂.trans this.symm) h₃
    obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := InferInv.check (infer_inv L e₃) (by ret_ok) hex hΓ₃ hR₃ ho₃
    have hu : TyEq ((o₂.τ.subst o₃.σ).subst φ₃) (o₃.τ.subst φ₃) :=
      (hag₃.ty (hτb₂.mono (Nat.le_succ _))).trans
        (by rw [Ty.subst_cons_fresh hτb₂]; exact hτ₂.trans hτ₃.symm)
    obtain ⟨σ₄, hσ₄, habs⟩ := unify_mgu hu
    have hσ₁₂ := (hσ₁.mono hn₂).compose hσ₂
    refine ⟨_, by simp only [infer, ho₁, ho₂, ho₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
    · exact (((hag₁.trans hσ₁ hn₁ hag₂).fresh hσ₁₂ (by omega)).trans
        (hσ₁₂.mono (Nat.le_succ _)) (by omega) hag₃).absorb habs
    · exact (habs _).trans (hτ₃.trans hτ₀)
    · -- `Strip`: of `e₁`'s type and the fresh variable, which is `σ`.
      have hstrip : Sat C [(⟨.strip, [o₁.τ.subst o₂.σ, .var o₂.next]⟩ : Pred)]
          ((o₂.next, σ) :: φ₂) := by
        intro c hc
        simp only [List.mem_singleton] at hc; subst hc
        simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst, Subst.find, ↓reduceIte,
          Option.getD_some]
        rw [Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono hn₂))]
        refine hs.of_predEq (PredEq.of_pairs (by simp)
          (zip_tyEq_cons ((hag₂.ty hτb₁).trans hτ₁).symm (zip_tyEq_cons (TyEq.refl _) zip_tyEq_nil)))
      have hb₁ : ∀ p ∈ o₁.preds.map (·.subst o₂.σ), p.Below o₂.next := fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      refine Sat.absorb habs (Sat.app (Sat.agree hag₃ (fun p hp => ?_)
        (Sat.app (Sat.app (Sat.fresh hb₁ (Sat.agree hag₂ hp₁ hsat₁)) (Sat.fresh hp₂ hsat₂))
          hstrip)) hsat₃)
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact (hb₁ p hp).mono (Nat.le_succ _)
        · exact (hp₂ p hp).mono (Nat.le_succ _)
      · simp only [List.mem_singleton] at hp; subst hp
        refine Pred.below_of_args (fun τ hτ => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
        rcases hτ with rfl | rfl
        · exact (hσ₂.subst_below (hτb₁.mono hn₂)).mono (Nat.le_succ _)
        · exact hβ

theorem infer_complete_caseTag (L : List String) (e₁ : Expr) (l : Disc) (t : String) (e₂ : Expr) (e₃ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) (ih₃ : e₃.PolyOK L → InferComplete L e₃) :
    (Expr.caseTag e₁ l t e₂ e₃).PolyOK L → InferComplete L (Expr.caseTag e₁ l t e₂ e₃) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm.1.1
  replace ih₂ : InferComplete L e₂ := ih₂ hm.1.2
  replace ih₃ : InferComplete L e₃ := ih₃ hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | @caseTag _ _ _ _ _ τ₁ _ _ σ ρ _ _ _ _ h₁ hs h₂ h₃ =>
    subst hmd'
    obtain ⟨o₁, ho₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ (by ret_ok) (by ret_eq) .none .none hΓ hR hC
      hΓ' hR' h₁
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ (by ret_ok) .none hΓ hR ho₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
    have hr₁ := hR'.trans (hag₁.ret hR).symm
    -- `e₂` sees the rest, a fresh variable which is `ρ`.
    have hfr₁ := Agree.cons_fresh o₁.next ρ φ₁
    have hρv : (Ty.var o₁.next).Below (o₁.next + 1) := .var (by omega)
    have hΓ₂' : Ctx.Below (o₁.next + 1) (.mono (.var o₁.next) :: Ctx.subst o₁.σ Γ) :=
      Ctx.Below.mono_cons hρv (hΓ₁.mono (by omega))
    have hR₂' := hR₁.mono (Nat.le_succ o₁.next)
    have hfc₁ : CtxEq (Ctx.subst ((o₁.next, ρ) :: φ₁) (Ctx.subst o₁.σ Γ))
        (Ctx.subst φ₁ (Ctx.subst o₁.σ Γ)) := by
      have := hfr₁.ctx hΓ₁
      simp only [Ctx.subst_nil] at this
      exact this
    have hfr₁' : RetEq (Ret.subst ((o₁.next, ρ) :: φ₁) (Ret.subst o₁.σ R))
        (Ret.subst φ₁ (Ret.subst o₁.σ R)) := by
      have := hfr₁.ret hR₁
      simp only [Ret.subst_nil] at this
      exact this
    obtain ⟨o₂, ho₂, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂ (by ret_ok) (by ret_eq) hex
      hτT (ψ := (o₁.next, ρ) :: φ₁) hΓ₂' hR₂' hC
      (by
        simp only [Ctx.subst_cons, Scheme.mono_subst]
        refine CtxEq.cons (by simp [Ty.subst, Subst.find]; exact SchemeEq.refl _) ?_
        exact hc₁.trans hfc₁.symm)
      (hr₁.trans hfr₁'.symm) h₂
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := InferInv.check (infer_inv L e₂) (by ret_ok) hex hΓ₂' hR₂' ho₂
    have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono (by omega))
    have hR₂ := hσ₂.ret_below (hR₁.mono (by omega))
    have hc₂ : CtxEq Γ' (Ctx.subst φ₂ (Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ))) :=
      hc₁.trans ((hag₂.ctx (hΓ₁.mono (Nat.le_succ _))).trans hfc₁).symm
    have hr₂ : RetEq R' (Ret.subst φ₂ (Ret.subst o₂.σ (Ret.subst o₁.σ R))) :=
      hr₁.trans ((hag₂.ret (hR₁.mono (Nat.le_succ _))).trans hfr₁').symm
    -- `e₃` sees the case, another fresh variable which is `σ`.
    have hfr := Agree.cons_fresh o₂.next σ φ₂
    have hσv : (Ty.var o₂.next).Below (o₂.next + 1) := .var (by omega)
    have hΓ₃ : Ctx.Below (o₂.next + 1) (.mono (.var o₂.next) :: Ctx.subst o₂.σ (Ctx.subst o₁.σ Γ)) :=
      Ctx.Below.mono_cons hσv (hΓ₂.mono (by omega))
    have hR₃ := hR₂.mono (Nat.le_succ o₂.next)
    obtain ⟨o₃, ho₃, φ₃, hag₃, hτ₃, hsat₃⟩ := InferComplete.check ih₃ (by ret_ok) (by ret_eq) hex
      hτT (ψ := (o₂.next, σ) :: φ₂) hΓ₃ hR₃ hC
      (by
        simp only [Ctx.subst_cons, Scheme.mono_subst]
        refine CtxEq.cons (by simp [Ty.subst, Subst.find]; exact SchemeEq.refl _) ?_
        have := hfr.ctx hΓ₂
        simp only [Ctx.subst_nil] at this
        exact hc₂.trans this.symm)
      (by
        have := hfr.ret hR₂
        simp only [Ret.subst_nil] at this
        exact hr₂.trans this.symm) h₃
    obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := InferInv.check (infer_inv L e₃) (by ret_ok) hex hΓ₃ hR₃ ho₃
    have hu : TyEq ((o₂.τ.subst o₃.σ).subst φ₃) (o₃.τ.subst φ₃) :=
      (hag₃.ty (hτb₂.mono (Nat.le_succ _))).trans
        (by rw [Ty.subst_cons_fresh hτb₂]; exact hτ₂.trans hτ₃.symm)
    obtain ⟨σ₄, hσ₄, habs⟩ := unify_mgu hu
    have hσ₁₂ : (Subst.compose o₂.σ o₁.σ).Within o₂.next :=
      (hσ₁.mono (by omega)).compose hσ₂
    refine ⟨_, by simp only [infer, ho₁, ho₂, ho₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
    · exact ((((hag₁.fresh hσ₁ hn₁).trans (hσ₁.mono (Nat.le_succ _)) (by omega) hag₂).fresh
        hσ₁₂ (by omega)).trans (hσ₁₂.mono (Nat.le_succ _)) (by omega) hag₃).absorb habs
    · exact (habs _).trans (hτ₃.trans hτ₀)
    · -- `Case`: of `e₁`'s type and the fresh variables, which are `σ` and `ρ`.
      have he₁ : TyEq τ₁ ((o₁.τ.subst o₂.σ).subst φ₂) := by
        have := hag₂.ty (hτb₁.mono (Nat.le_succ _))
        rw [Ty.subst_cons_fresh hτb₁] at this
        exact (this.trans hτ₁).symm
      have hρe : TyEq ρ (((Ty.var o₁.next).subst o₂.σ).subst φ₂) := by
        have := hag₂.ty hρv
        have h' : (Ty.var o₁.next).subst ((o₁.next, ρ) :: φ₁) = ρ := by simp [Ty.subst, Subst.find]
        rw [h'] at this
        exact this.symm
      have hcase : Sat C [(⟨.caseTag l t, [o₁.τ.subst o₂.σ, .var o₂.next,
          (Ty.var o₁.next).subst o₂.σ]⟩ : Pred)] ((o₂.next, σ) :: φ₂) := by
        intro c hc
        simp only [List.mem_singleton] at hc; subst hc
        simp only [Pred.subst, List.map_cons, List.map_nil]
        rw [Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono (by omega))),
          Ty.subst_cons_fresh (hσ₂.subst_below (hρv.mono hn₂))]
        have hσe : (Ty.var o₂.next).subst ((o₂.next, σ) :: φ₂) = σ := by
          simp [Ty.subst, Subst.find]
        rw [hσe]
        exact hs.of_predEq (PredEq.of_pairs (by simp)
          (zip_tyEq_cons he₁ (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons hρe zip_tyEq_nil))))
      have hb₁ : ∀ p ∈ o₁.preds.map (·.subst o₂.σ), p.Below o₂.next := fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono (by omega))
      refine Sat.absorb habs (Sat.app (Sat.agree hag₃ (fun p hp => ?_)
        (Sat.app (Sat.app (Sat.fresh hb₁ (Sat.agree hag₂ (fun p hp => (hp₁ p hp).mono
          (Nat.le_succ _)) (Sat.fresh hp₁ hsat₁))) (Sat.fresh hp₂ hsat₂)) hcase)) hsat₃)
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact (hb₁ p hp).mono (Nat.le_succ _)
        · exact (hp₂ p hp).mono (Nat.le_succ _)
      · simp only [List.mem_singleton] at hp; subst hp
        refine Pred.below_of_args (fun τ hτ => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
        rcases hτ with rfl | rfl | rfl
        · exact (hσ₂.subst_below (hτb₁.mono (by omega))).mono (Nat.le_succ _)
        · exact hσv
        · exact (hσ₂.subst_below (hρv.mono hn₂)).mono (Nat.le_succ _)

theorem infer_complete_unop (L : List String) (op : UnOp) (e : Expr) (ih : e.PolyOK L → InferComplete L e) :
    (Expr.unop op e).PolyOK L → InferComplete L (Expr.unop op e) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L e := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | unop hop he =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    cases hop with
    | not =>
      exact ⟨⟨o₁.σ, .boolean, o₁.preds, o₁.next⟩, by simp only [infer, h₁], φ₁, hag₁, hτ₀,
        hsat₁⟩
    | typeof =>
      exact ⟨⟨o₁.σ, .string, o₁.preds, o₁.next⟩, by simp only [infer, h₁], φ₁, hag₁, hτ₀,
        hsat₁⟩
    | neg =>
      obtain ⟨σ', hσ', habs⟩ := unify_mgu (τ₁ := o₁.τ) (τ₂ := .number) (ψ := φ₁) hτ₁
      exact ⟨_, by simp only [infer, h₁, hσ']; rfl, φ₁, hag₁.absorb habs, by simpa using hτ₀,
        Sat.absorb habs hsat₁⟩

theorem infer_complete_binop (L : List String) (op : BinOp) (e₁ : Expr) (e₂ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) :
    (Expr.binop op e₁ e₂).PolyOK L → InferComplete L (Expr.binop op e₁ e₂) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm.1
  replace ih₂ : InferComplete L e₂ := ih₂ hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | binop hop ht₁ ht₂ =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' ht₁
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (by ret_ok) (by ret_eq) .none .none (ψ := φ₁) hΓ₁ hR₁ hC
      (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) ht₂
    have hag₁₂ := hag₁.trans hσ₁ hn₁ hag₂
    have hsat₁₂ : Sat C (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds) φ₂ :=
      Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂
    have h₁₂ : TyEq ((o₁.τ.subst o₂.σ).subst φ₂) (o₁.τ.subst φ₁) := hag₂.ty hτb₁
    cases hop with
    | plus hent =>
      obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu (τ₁ := o₁.τ.subst o₂.σ) (τ₂ := o₂.τ) (ψ := φ₂)
        (h₁₂.trans (hτ₁.trans hτ₂.symm))
      refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, φ₂, hag₁₂.absorb habs,
        (habs _).trans (hτ₂.trans hτ₀), ?_⟩
      refine Sat.absorb habs (Sat.app hsat₁₂ (fun p hp => ?_))
      simp only [List.mem_singleton] at hp; subst hp
      exact hent.of_predEq (PredEq.of_eqs (.cons hτ₂.symm .nil))
    | strictEq =>
      exact ⟨_, by simp only [infer, h₁, h₂]; rfl, φ₂, hag₁₂, by simpa using hτ₀, hsat₁₂⟩
    | num hn =>
      obtain ⟨σ₃, hσ₃, habs₃⟩ := unify_mgu (τ₁ := o₁.τ.subst o₂.σ) (τ₂ := .number) (ψ := φ₂)
        (h₁₂.trans hτ₁)
      obtain ⟨σ₄, hσ₄, habs₄⟩ := unify_mgu (τ₁ := o₂.τ.subst σ₃) (τ₂ := .number) (ψ := φ₂)
        ((habs₃ _).trans hτ₂)
      cases op <;> simp [BinOp.numeric] at hn <;>
      exact ⟨_, by simp only [infer, h₁, h₂, hσ₃, hσ₄]; rfl, φ₂,
        (hag₁₂.absorb habs₃).absorb habs₄, by simpa [BinOp.resTy] using hτ₀,
        Sat.absorb habs₄ (Sat.absorb habs₃ hsat₁₂)⟩

theorem infer_complete_ret (L : List String) (e : Expr) (ih : e.PolyOK L → InferComplete L e) :
    (Expr.ret e).PolyOK L → InferComplete L (Expr.ret e) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L e := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | @ret _ _ τr' _ _ _ _ he =>
    subst hmd'
    cases R with
    | none => exact hR'.elim
    | some τr =>
      cases rm with
      | synth =>
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih RetOk.synth (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
        obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e RetOk.synth .none hΓ hR h₁
        have hτr : τr.Below n := fun a ha => hR a (by simpa [Ret.ftv] using ha)
        have hR'' : TyEq τr' (τr.subst ψ) := hR'
        obtain ⟨σ', hσ', habs⟩ := unify_mgu (τ₁ := τr.subst o₁.σ) (τ₂ := o₁.τ) (ψ := φ₁)
          ((hag₁.ty hτr).trans (hR''.symm.trans hτ₁.symm))
        have hσ'w := unify_within (hσ₁.subst_below (hτr.mono hn₁)) hτb₁ hσ'
        refine ⟨_, by simp only [infer, h₁, hσ']; rfl, (o₁.next, τ₀) :: φ₁,
          (hag₁.absorb habs).fresh (hσ₁.compose hσ'w) hn₁, exTy_tyEq hex hτT hτ₀ _ _,
          Sat.fresh (fun p hp => ?_) (Sat.absorb habs hsat₁)⟩
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ'w.pred_below (hp₁ q hq)
      | check =>
        have hτc : τr.ftv = [] := hRo rfl τr rfl
        obtain rfl : τr' = τr := Option.some.inj (hRc rfl)
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check ih hRo hRc (Ex.Closed.some hτc)
          (fun _ h => by cases h; rfl) hΓ hR hC hΓ' hR' he
        obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check (infer_inv L e) hRo (Ex.Closed.some hτc) hΓ hR h₁
        exact ⟨⟨o₁.σ, ex.getD (.var o₁.next), o₁.preds, o₁.next + 1⟩, by simp only [infer, h₁],
          (o₁.next, τ₀) :: φ₁, hag₁.fresh hσ₁ hn₁, exTy_tyEq hex hτT hτ₀ _ _, Sat.fresh hp₁ hsat₁⟩

theorem infer_complete_throw_ (L : List String) (e : Expr) (ih : e.PolyOK L → InferComplete L e) :
    (Expr.throw_ e).PolyOK L → InferComplete L (Expr.throw_ e) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L e := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | throw_ he =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    refine ⟨⟨o₁.σ, .var o₁.next, o₁.preds, o₁.next + 1⟩, by simp only [infer, h₁],
      (o₁.next, τ₀) :: φ₁, hag₁.fresh hσ₁ hn₁, ?_, Sat.fresh hp₁ hsat₁⟩
    simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]; exact hτ₀

theorem infer_complete_seq (L : List String) (e₁ : Expr) (e₂ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) :
    (Expr.seq e₁ e₂).PolyOK L → InferComplete L (Expr.seq e₁ e₂) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm.1
  replace ih₂ : InferComplete L e₂ := ih₂ hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | seq ht₁ ht₂ =>
    subst hmd'
    obtain ⟨o₁, h₁, φ₁, hag₁, -, hsat₁⟩ := InferComplete.check ih₁ (by ret_ok) (by ret_eq)
      (Ex.Closed.some rfl) (fun _ h => by cases h; rfl) hΓ hR hC hΓ' hR' ht₁
    obtain ⟨hn₁, hσ₁, -, hp₁⟩ := InferInv.check (infer_inv L e₁) (by ret_ok) (Ex.Closed.some rfl)
      hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ih₂ (by ret_ok) (by ret_eq) hex hτT
      (ψ := φ₁) hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) ht₂
    exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
      by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂.trans hτ₀,
      Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

theorem infer_complete_while_ (L : List String) (c : Expr) (body : Expr) (ihc : c.PolyOK L → InferComplete L c) (ihb : body.PolyOK L → InferComplete L body) :
    (Expr.while_ c body).PolyOK L → InferComplete L (Expr.while_ c body) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihc : InferComplete L c := ihc hm.1
  replace ihb : InferComplete L body := ihb hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | while_ hc hb =>
    obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' hc
    obtain ⟨hn₁, hσ₁, _, hp₁⟩ := infer_inv L c (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := InferComplete.check ihb (by ret_ok) (by ret_eq)
      (Ex.Closed.some rfl) (fun _ h => by cases h; rfl) (ψ := φ₁) hΓ₁ hR₁ hC
      (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hb
    exact ⟨⟨Subst.compose o₂.σ o₁.σ, .undefined, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
      o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₀,
      Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

theorem infer_complete_break_ (L : List String) :
    (Expr.break_).PolyOK L → InferComplete L (Expr.break_) := by
  intro _
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  exact ⟨⟨[], ex.getD (.var n), [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
    fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha]; exact TyEq.refl _,
    exTy_tyEq hex (fun T hT => hm.2 T hT rfl) (TyEq.refl _) n ψ, by simp [Sat]⟩

theorem infer_complete_continue_ (L : List String) :
    (Expr.continue_).PolyOK L → InferComplete L (Expr.continue_) := by
  intro _
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  exact ⟨⟨[], ex.getD (.var n), [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
    fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha]; exact TyEq.refl _,
    exTy_tyEq hex (fun T hT => hm.2 T hT rfl) (TyEq.refl _) n ψ, by simp [Sat]⟩

theorem infer_complete_tryCatch (L : List String) (body : Expr) (handler : Expr) (ihb : body.PolyOK L → InferComplete L body) (ihh : handler.PolyOK L → InferComplete L handler) :
    (Expr.tryCatch body handler).PolyOK L → InferComplete L (Expr.tryCatch body handler) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihb : InferComplete L body := ihb hm.1
  replace ihh : InferComplete L handler := ihh hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | tryCatch hb hh =>
    subst hmd'
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check ihb hRo hRc hex hτT hΓ hR hC hΓ' hR' hb
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := InferInv.check (infer_inv L body) hRo hex hΓ hR h₁
    have hunk : Ty.unknown.Below o₁.next := fun a ha => by simp [Ty.ftv] at ha
    have hΓ₁ := Ctx.Below.mono_cons hunk (hσ₁.ctx_below (hΓ.mono hn₁))
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := InferComplete.check ihh (by ret_ok) (by ret_eq) hex hτT
      (ψ := φ₁) hΓ₁ hR₁ hC
      (by
        simp only [Ctx.subst_cons, Scheme.mono_subst, Ty.subst_app, List.map_nil]
        exact CtxEq.cons (SchemeEq.refl _) (hΓ'.trans (hag₁.ctx hΓ).symm))
      (hR'.trans (hag₁.ret hR).symm) hh
    have hu : TyEq ((o₁.τ.subst o₂.σ).subst φ₂) (o₂.τ.subst φ₂) :=
      (hag₂.ty hτb₁).trans (hτ₁.trans hτ₂.symm)
    obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu hu
    exact ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, φ₂, (hag₁.trans hσ₁ hn₁ hag₂).absorb habs,
      (habs _).trans (hτ₂.trans hτ₀),
      Sat.absorb habs (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂)⟩

theorem infer_complete_tryFinally (L : List String) (body : Expr) (fin : Expr) (ihb : body.PolyOK L → InferComplete L body) (ihf : fin.PolyOK L → InferComplete L fin) :
    (Expr.tryFinally body fin).PolyOK L → InferComplete L (Expr.tryFinally body fin) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihb : InferComplete L body := ihb hm.1
  replace ihf : InferComplete L fin := ihf hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  rw [exMode_pushes (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, hτT, ht⟩ := ht.top_ex hC hex (fun T hT => hmT T hT rfl) (fun _ _ => rfl)
  generalize hmd' : Ex.mode ex = md' at ht
  cases ht with
  | tryFinally hb hf =>
    subst hmd'
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := InferComplete.check ihb hRo hRc hex hτT hΓ hR hC hΓ' hR' hb
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := InferInv.check (infer_inv L body) hRo hex hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := InferComplete.check ihf (by ret_ok) (by ret_eq)
      (Ex.Closed.some rfl) (fun _ h => by cases h; rfl) (ψ := φ₁) hΓ₁ hR₁ hC
      (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hf
    exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
      o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂,
      (hag₂.ty hτb₁).trans (hτ₁.trans hτ₀), Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩

theorem infer_complete_obj (L : List String) (ls : List String) (es : List Expr) (ks : List FieldKind) (ih : ∀ a ∈ es, a.PolyOK L → InferComplete L a) :
    (Expr.obj ls es ks).PolyOK L → InferComplete L (Expr.obj ls es ks) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ih : ∀ a ∈ es, InferComplete L a := fun a ha => ih a ha (hm a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  by_cases hp : ∃ T, ex = some T ∧ (Expr.obj ls es ks).pushes T
  · -- Checked against a record or a variant's case.
    obtain ⟨T, rfl, hp⟩ := hp
    have hT := hex T rfl
    simp only [exMode, hp, ↓reduceIte] at hmd; subst hmd
    obtain rfl := hmT T rfl hp
    have ht' := ht.check_top hC hT hp
    cases ht' with
    | objCheck hc hnd hk hl hL hd he hfs =>
      rename_i P τs
      have hP := objTarget_complete hc he
      have hPc := (objTarget_sound hT hP).2
      have hτc := Ty.dataFields_closed hPc hd
      obtain ⟨σu, hσu, -⟩ := unify_mgu (ψ := []) (by simpa using he)
      obtain ⟨o, h, φ, hag, hsat⟩ := inferFields_complete es τs ih hRo hRc hτc hΓ hR hC hΓ'
        hR' (by rw [hl, Ty.dataFields_length hd]) hfs
      have hcond : (ls.all fun x => decide (x ∈ L)) = true ∧ es.length = ls.length ∧
          (unify P (.record L (objSlots L ls (τs.map fun τ => .slot .pre .data τ)))).isSome =
            true := ⟨List.all_eq_true.mpr (fun l hl => by simpa using hL l hl), hl, by simp [hσu]⟩
      refine ⟨⟨o.σ, τ', o.preds, o.next⟩, ?_, φ, hag, ?_, hsat⟩
      · simp only [infer, Option.filter, hp, ↓reduceIte, hP, hd, hcond, and_self, h]
      · rw [Ty.closed_subst hT]; exact TyEq.refl _
  have hfn : (ex.filter fun T => (Expr.obj ls es ks).pushes T) = none := by
    cases ex with
    | none => rfl
    | some T => simp only [Option.filter]; split <;> simp_all
  rw [exMode_of_filter_none hfn] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @obj _ _ _ _ _ ss' _ _ τs' hes hks hτs hss hL hargs hfs =>
    obtain ⟨o, h, φ, hag, hτs₂, hsat⟩ :=
      inferArgs_complete es _ ih (by ret_ok) (by ret_eq) .none (fun _ h => nomatch h) hΓ hR hC hΓ' hR' (by omega) hargs
    have hc : ls.all (· ∈ L) = true ∧ es.length = ls.length ∧ ks.length = ls.length :=
      ⟨List.all_eq_true.mpr (fun l hl => by simpa using hL l hl), hes, hks⟩
    have hlen : o.τs.length = es.length := by
      have := hτs₂.length; simp only [List.length_map] at this; omega
    obtain ⟨θs, ss, hf, hss₂, hθs⟩ := fieldSlots_complete (inferArgs_shape h) hτs₂
      (by omega) hlen.symm (by omega) hfs
    have hT : TyEq ((Ty.record L (objSlots L ls ss)).subst φ) (.record L (objSlots L ls ss')) := by
      simp only [Ty.subst_app, objSlots_subst]
      exact TyEq.app_eqs (objSlots_tyEqs hss₂)
    obtain ⟨σ', hσ', habs⟩ := unifyThis_complete (θs := θs)
      (T := Ty.record L (objSlots L ls ss)) (φ := φ) (fun θ hθ => (hθs θ hθ).trans hT.symm)
    refine ⟨_, by simp only [infer]; rw [hfn]; simp only [hc, and_self, ↓reduceIte, h, hf, hσ']; rfl, φ,
      hag.absorb habs, (habs _).trans (hT.trans hτ₀), Sat.absorb habs hsat⟩

theorem infer_complete_cls (L : List String) (ls : List String) (es : List Expr) (ks : List ClassKind) (ih : ∀ a ∈ es, a.PolyOK L → InferComplete L a) :
    (Expr.cls ls es ks).PolyOK L → InferComplete L (Expr.cls ls es ks) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ih : ∀ a ∈ es, InferComplete L a := fun a ha => ih a ha (hm a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @cls _ _ _ τs' _ _ ss' _ _ hes hks hτs hss hnd hL hms hslots =>
    have hR₀ : Ret.Below n none := fun a ha => by simp [Ret.ftv] at ha
    obtain ⟨o, h, φ, hag, hτs₂, hsat⟩ := inferMembers_complete es ks τs' ih (Δ := []) (Δ' := [])
      (R := none) (R' := none) hΓ (by simp) hR₀ hC hΓ' .nil trivial (by omega) (by omega)
      (fun i e k τ he hk hτ => by rw [← memberCtx_eq]; exact hms i e k τ he hk hτ)
    obtain ⟨hn, hσ, hτsb, hp⟩ := inferMembers_inv es ks (fun a _ => infer_inv L a) hΓ
      (by simp) hR₀ h
    have hc : ls.all (· ∈ L) = true ∧ ls.Nodup ∧ es.length = ls.length ∧
        ks.length = ls.length :=
      ⟨List.all_eq_true.mpr (fun l hl => by simpa using hL l hl), hnd, hes, hks⟩
    have hlen : o.τs.length = es.length := by
      have := hτs₂.length; simp only [List.length_map] at this; omega
    obtain ⟨θs, ss, m', φ', hm, hm', hφ', hss₂, hθs, hnn⟩ := memberSlots_complete
      (inferMembers_shape h) hτsb hτs₂ (by omega) hlen.symm (by omega) hslots
    have hT : TyEq ((Ty.record L (objSlots L ls ss)).subst φ') (.record L (objSlots L ls ss')) := by
      simp only [Ty.subst_app, objSlots_subst]
      exact TyEq.app_eqs (objSlots_tyEqs hss₂)
    obtain ⟨σ', hσ', habs⟩ := unifyThis_complete (θs := θs)
      (T := Ty.record L (objSlots L ls ss)) (φ := φ') (fun θ hθ => (hθs θ hθ).trans hT.symm)
    have hag' : Agree n o.σ φ' ψ := fun a ha => by
      rw [hφ' _ ((hσ a).1 (by omega))]; exact hag a ha
    have hpφ : ∀ p ∈ o.preds, p.subst φ' = p.subst φ := fun p hp' => by
      obtain ⟨c, args⟩ := p
      simp only [Pred.subst, Pred.mk.injEq, true_and]
      exact List.map_congr_left (fun τ hτ => hφ' τ (fun a ha => hp _ hp' a
        (List.mem_flatMap.mpr ⟨τ, hτ, ha⟩)))
    refine ⟨_, by simp only [infer, hc, and_self, ↓reduceIte, h, hm, hσ']; rfl, φ',
      hag'.absorb habs, (habs _).trans (hT.trans hτ₀),
      Sat.absorb habs (Sat.append.mpr ⟨fun p hp' => ?_, hnn⟩)⟩
    rw [hpφ p hp']; exact hsat p hp'

theorem infer_complete_ctor (L : List String) (k : Nat) (body : Expr) (ih : body.PolyOK L → InferComplete L body) :
    (Expr.ctor k body).PolyOK L → InferComplete L (Expr.ctor k body) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L body := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' _ ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @ctor _ _ _ ρ' _ _ _ τs' hlen hb =>
    subst hlen
    have hψΓ : Ctx.subst (ctorSubst n τs' ρ' ψ) Γ = Ctx.subst ψ Γ :=
      Ctx.subst_congr (fun a ha => ctorSubst_below (hΓ a ha))
    have hparams := ctorSubst_params (n := n) (ρ := ρ') (τs := τs') (ψ := ψ)
    have hτs : ∀ τ ∈ varBlock n τs'.length, τ.Below (n + 1 + τs'.length) := fun τ hτ =>
      (varBlock_below τ hτ).mono (by omega)
    have hρ : (Ty.var (n + τs'.length)).Below (n + 1 + τs'.length) := .var (by omega)
    have hnt : Ty.newTarget.Below (n + 1 + τs'.length) := fun a ha => by simp [Ty.ftv] at ha
    have hfn : (Ty.fn .newTarget (varBlock n τs'.length) (.var (n + τs'.length))).Below
        (n + 1 + τs'.length) := Ty.Below.fn.mpr ⟨hnt, hτs, hρ⟩
    have hctx : τs'.map .mono ++ .mono (.fn .newTarget τs' ρ') :: .mono .newTarget ::
        Ctx.subst ψ Γ = Ctx.subst (ctorSubst n τs' ρ' ψ)
          ((varBlock n τs'.length).map .mono ++
            .mono (.fn .newTarget (varBlock n τs'.length) (.var (n + τs'.length))) ::
            .mono .newTarget :: Γ) := by
      rw [← hψΓ]
      simp only [Ctx.subst, List.map_append, List.map_map, List.map_cons, Function.comp_def,
        Scheme.mono_subst, Ty.subst_fn, ctorSubst_ret, Ty.newTarget_subst]
      have e₁ : List.map (fun x => Scheme.mono (Ty.subst (ctorSubst n τs' ρ' ψ) x))
          (varBlock n τs'.length) = τs'.map Scheme.mono := by
        conv => rhs; rw [← hparams]
        rw [List.map_map]; rfl
      rw [e₁, hparams]
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none (R := some (.var (n + τs'.length)))
      (ψ := ctorSubst n τs' ρ' ψ)
      (Ctx.Below.append_mono hτs (Ctx.Below.mono_cons hfn (Ctx.Below.mono_cons hnt
        (hΓ.mono (by omega)))))
      (fun a ha => hρ a (by simpa [Ret.ftv] using ha)) hC
      (by rw [← hctx]; exact CtxEq.append_left _ (CtxEq.cons (SchemeEq.refl _)
        (CtxEq.cons (SchemeEq.refl _) hΓ')))
      (by simp only [Ret.subst_some, ctorSubst_ret]; exact TyEq.refl _) hb
    have hu : TyEq (((Ty.var (n + τs'.length)).subst o₁.σ).subst φ₁) (o₁.τ.subst φ₁) := by
      refine (hag₁ _ (by omega)).trans ?_
      rw [ctorSubst_ret]; exact hτ₁.symm
    obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
    refine ⟨_, by simp only [infer, h₁, hσ']; rfl, φ₁, fun a ha => ?_, ?_, ?_⟩
    · refine (hag₁.absorb habs a (by omega)).trans ?_
      simp only [Ty.subst, ctorSubst_below ha]; exact TyEq.refl _
    · refine ((hag₁.absorb habs).ty hfn).trans ?_
      rw [Ty.subst_fn, ctorSubst_ret, hparams]; exact hτ₀
    · exact Sat.absorb habs hsat₁

theorem infer_complete_new_ (L : List String) (f : Expr) (args : List Expr) (ihf : f.PolyOK L → InferComplete L f) (iha : ∀ a ∈ args, a.PolyOK L → InferComplete L a) :
    (Expr.new_ f args).PolyOK L → InferComplete L (Expr.new_ f args) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ihf : InferComplete L f := ihf hm.1
  replace iha : ∀ a ∈ args, InferComplete L a := fun a ha => iha a ha (hm.2 a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @new_ _ _ _ _ _ τs' _ ss _ hf hlen hargs hρ hss =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihf (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' hf
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L f (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (by ret_ok) (by ret_eq) .none (fun _ h => nomatch h) (ψ := φ₁)
      hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
    obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) (by ret_ok) .none hΓ₁ hR₁ h₂
    let φ₃ := Subst.block o₂.next ss ++ φ₂
    have hbss : (varBlock o₂.next L.length).map (·.subst φ₃) = ss := by
      rw [← hss]; exact varBlock_subst_block _ _ _
    have hu : TyEq ((o₁.τ.subst o₂.σ).subst φ₃)
        ((Ty.fn .newTarget o₂.τs (.record L (varBlock o₂.next L.length))).subst φ₃) := by
      rw [Ty.subst_block_fresh (hσ₂.subst_below (hτb₁.mono hn₂))]
      refine (hag₂.ty hτb₁).trans (hτ₁.trans ?_)
      rw [Ty.subst_fn]
      refine TyEq.fn_mk (TyEq.refl _) ?_ ?_
      · rw [Ty.subst_app, hbss]; exact hρ
      · rw [List.map_congr_left (fun τ hτ => Ty.subst_block_fresh (hτsb₂ τ hτ))]
        exact hτs₂.symm
    obtain ⟨σ₃, hσ₃, habs⟩ := unify_mgu hu
    refine ⟨_, by simp only [infer, h₁, h₂, hσ₃]; rfl, φ₃, ?_, ?_, ?_⟩
    · exact Agree.absorb ((hag₁.trans hσ₁ hn₁ hag₂).block ((hσ₁.mono hn₂).compose hσ₂)
        (by omega)) habs
    · refine (habs _).trans ?_
      simp only [Ty.subst_app, hbss]; exact hρ.symm.trans hτ₀
    · refine Sat.absorb habs (Sat.app ?_ ?_)
      · refine Sat.block (fun p hp => ?_) (Sat.agree hag₂ hp₁ hsat₁)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact Sat.block hp₂ hsat₂

theorem infer_complete_get (L : List String) (e : Expr) (l : String) (ih : e.PolyOK L → InferComplete L e) :
    (Expr.get e l).PolyOK L → InferComplete L (Expr.get e l) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih : InferComplete L e := ih hm
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | get he hpr =>
    rename_i κ
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    refine ⟨⟨o₁.σ, .var (o₁.next + 1),
        o₁.preds ++ [⟨.hasProp l, [o₁.τ, .var o₁.next, .var (o₁.next + 1)]⟩], o₁.next + 2⟩,
      by simp only [infer, h₁], (o₁.next + 1, τ₀) :: (o₁.next, κ) :: φ₁,
      (hag₁.fresh hσ₁ hn₁).fresh (hσ₁.mono (Nat.le_succ _)) (by omega),
      by simp [Ty.subst, Subst.find]; exact hτ₀, ?_⟩
    refine Sat.app (Sat.fresh (fun p hp => (hp₁ p hp).mono (Nat.le_succ _))
      (Sat.fresh hp₁ hsat₁)) ?_
    intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [Pred.subst, List.map_cons, List.map_nil,
      Ty.subst_cons_fresh (hτb₁.mono (Nat.le_succ _)), Ty.subst_cons_fresh hτb₁]
    refine hpr.of_predEq (PredEq.of_eqs (.cons hτ₁.symm (.cons ?_ (.cons ?_ .nil))))
    · simp [Ty.subst, Subst.find]; exact TyEq.refl _
    · simp [Ty.subst, Subst.find]; exact TyEq.refl _

theorem infer_complete_set (L : List String) (e : Expr) (l : String) (v : Expr) (ihe : e.PolyOK L → InferComplete L e) (ihv : v.PolyOK L → InferComplete L v) :
    (Expr.set e l v).PolyOK L → InferComplete L (Expr.set e l v) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihe : InferComplete L e := ihe hm.1
  replace ihv : InferComplete L v := ihv hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | set he hpr hv =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihv (by ret_ok) (by ret_eq) .none .none (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (hΓ'.trans (hag₁.ctx hΓ).symm)
      (hR'.trans (hag₁.ret hR).symm) hv
    refine ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds ++
        [⟨.hasProp l, [o₁.τ.subst o₂.σ, .data, o₂.τ]⟩], o₂.next⟩,
      by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂.trans hτ₀, ?_⟩
    refine Sat.app (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂) ?_
    intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [Pred.subst, List.map_cons, List.map_nil]
    exact hpr.of_predEq (PredEq.of_eqs (.cons (hτ₁.symm.trans (hag₂.ty hτb₁).symm)
      (.cons (by simp; exact TyEq.refl _) (.cons hτ₂.symm .nil))))

theorem infer_complete_spread (L : List String) (e₁ : Expr) (e₂ : Expr) (ih₁ : e₁.PolyOK L → InferComplete L e₁) (ih₂ : e₂.PolyOK L → InferComplete L e₂) :
    (Expr.spread e₁ e₂).PolyOK L → InferComplete L (Expr.spread e₁ e₂) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ih₁ : InferComplete L e₁ := ih₁ hm.1
  replace ih₂ : InferComplete L e₂ := ih₂ hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | spread hps hks hτs hss hrs he₁ he₂ hm =>
    rename_i ss ps ks τs rs
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he₁
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (by ret_ok) (by ret_eq) .none .none (ψ := φ₁) hΓ₁ hR₁ hC
      (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) he₂
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L e₂ (by ret_ok) .none hΓ₁ hR₁ h₂
    -- The fresh variables, sent to the slots of the derivation.
    let φ₃ := Subst.block o₂.next (ss ++ ps ++ ks ++ τs ++ rs) ++ φ₂
    have hbss : (varBlock o₂.next L.length).map (·.subst φ₃) = ss := by
      have := varBlock_subst_block_mid o₂.next [] ss (ps ++ ks ++ τs ++ rs) φ₂
      simp only [List.length_nil, Nat.add_zero, List.nil_append, ← List.append_assoc,
        hss] at this
      exact this
    have hbps : (varBlock (o₂.next + L.length) L.length).map (·.subst φ₃) = ps := by
      have := varBlock_subst_block_mid o₂.next ss ps (ks ++ τs ++ rs) φ₂
      simp only [← List.append_assoc, hss, hps] at this
      exact this
    have hbks : (varBlock (o₂.next + 2 * L.length) L.length).map (·.subst φ₃) = ks := by
      have := varBlock_subst_block_mid o₂.next (ss ++ ps) ks (τs ++ rs) φ₂
      simp only [List.length_append, hss, hps, hks, ← List.append_assoc] at this
      rw [show L.length + L.length = 2 * L.length by omega] at this
      exact this
    have hbτs : (varBlock (o₂.next + 3 * L.length) L.length).map (·.subst φ₃) = τs := by
      have := varBlock_subst_block_mid o₂.next (ss ++ ps ++ ks) τs rs φ₂
      simp only [List.length_append, hss, hps, hks, hτs] at this
      rw [show L.length + L.length + L.length = 3 * L.length by omega] at this
      exact this
    have hbrs : (varBlock (o₂.next + 4 * L.length) L.length).map (·.subst φ₃) = rs := by
      have := varBlock_subst_block_mid o₂.next (ss ++ ps ++ ks ++ τs) rs [] φ₂
      simp only [List.length_append, hss, hps, hks, hτs, hrs, List.append_nil] at this
      rw [show L.length + L.length + L.length + L.length = 4 * L.length by omega] at this
      exact this
    -- `e₁`'s type is a record over the slots written over.
    have hu₃ : TyEq ((o₁.τ.subst o₂.σ).subst φ₃)
        ((Ty.record L (varBlock o₂.next L.length)).subst φ₃) := by
      rw [Ty.subst_block_fresh (hσ₂.subst_below (hτb₁.mono hn₂))]
      refine (hag₂.ty hτb₁).trans (hτ₁.trans ?_)
      simp only [Ty.subst_app, hbss]; exact TyEq.refl _
    obtain ⟨σ₃, hσ₃, habs₃⟩ := unify_mgu hu₃
    -- `e₂`'s, over the operand's presences, kinds and types.
    have hu₄ : TyEq ((o₂.τ.subst σ₃).subst φ₃) (((Ty.record L (slots3
        (varBlock (o₂.next + L.length) L.length)
        (varBlock (o₂.next + 2 * L.length) L.length)
        (varBlock (o₂.next + 3 * L.length) L.length))).subst σ₃).subst φ₃) := by
      refine (habs₃ _).trans (TyEq.trans ?_ (habs₃ _).symm)
      rw [Ty.subst_block_fresh hτb₂]
      refine hτ₂.trans ?_
      simp only [Ty.subst_app, slots3_subst, hbps, hbks, hbτs]; exact TyEq.refl _
    obtain ⟨σ₄, hσ₄, habs₄⟩ := unify_mgu hu₄
    have habs : Absorbs φ₃ (Subst.compose σ₄ σ₃) := Absorbs.compose habs₃ habs₄
    refine ⟨_, by simp only [infer, h₁, h₂, hσ₃, hσ₄]; rfl, φ₃, ?_, ?_, ?_⟩
    · exact Agree.absorb ((hag₁.trans hσ₁ hn₁ hag₂).block ((hσ₁.mono hn₂).compose hσ₂)
        (by omega)) habs
    · refine (habs _).trans ?_
      simp only [Ty.subst_app, hbrs]; exact hτ₀
    · refine Sat.absorb habs (Sat.app (Sat.app ?_ ?_) ?_)
      · refine Sat.block (fun p hp => ?_) (Sat.agree hag₂ hp₁ hsat₁)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact Sat.block hp₂ hsat₂
      · intro p hp
        have hmem : p.subst φ₃ ∈ mergePreds ps ks τs ss rs := by
          rw [← hbps, ← hbks, ← hbτs, ← hbss, ← hbrs, ← mergePreds_subst]
          exact List.mem_map_of_mem hp
        exact hm _ hmem

theorem infer_complete_arr (L : List String) (es : List Expr) (ih : ∀ a ∈ es, a.PolyOK L → InferComplete L a) :
    (Expr.arr es).PolyOK L → InferComplete L (Expr.arr es) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ih : ∀ a ∈ es, InferComplete L a := fun a ha => ih a ha (hm a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, hmT⟩ := hm
  cases hat : arrTarget ex with
  | some x =>
    obtain ⟨T, σ⟩ := x
    obtain rfl := arrTarget_some hat
    obtain ⟨-, hw⟩ := arrTarget_fst hat rfl
    have hT := hex T rfl
    have hσc : σ.ftv = [] := by simpa [Ty.ftv] using Ty.ftv_nil_of_whnf hw hT
    have hp : (Expr.arr es).pushes T = true := by simp [Expr.pushes, hat]
    obtain rfl := hmT T rfl hp
    simp only [exMode, hp, ↓reduceIte] at hmd; subst hmd
    cases ht.check_top hC hT hp with
    | arrCheck hw' _ hes =>
      rw [hw] at hw'
      simp only [Ty.array, Ty.app.injEq, List.cons.injEq, and_true, true_and] at hw'
      subst hw'
      obtain ⟨o, h, φ, hag, -, hsat⟩ := inferArgs_complete es (List.replicate es.length σ) ih
        hRo hRc (Ex.Closed.some hσc) (fun _ hT' τ hτ => by
          cases hT'; exact List.eq_of_mem_replicate hτ) hΓ hR hC hΓ' hR' (by simp)
        (fun p hp => by
          obtain ⟨a, b⟩ := p
          obtain ⟨ha, hb⟩ : a ∈ es ∧ b = σ := by
            refine ⟨(List.of_mem_zip hp).1, ?_⟩
            exact List.eq_of_mem_replicate (List.of_mem_zip hp).2
          subst hb
          exact hes a ha)
      refine ⟨⟨o.σ, τ', o.preds, o.next⟩, by simp only [infer, hat, h], φ, hag, ?_, hsat⟩
      rw [Ty.closed_subst hT]; exact TyEq.refl _
  | none =>
    have hmd' : md = .synth := by
      rw [hmd]
      cases ex with
      | none => rfl
      | some T => simp [exMode, Expr.pushes, hat]
    subst hmd'
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
    cases ht with
    | arr hes =>
      rename_i τe
      obtain ⟨o, h, φ, hag, hτs, hsat⟩ := inferArgs_complete es (List.replicate es.length τe) ih
        hRo hRc .none (fun _ h => nomatch h) hΓ hR hC hΓ' hR' (by simp) (fun p hp => by
          obtain ⟨a, b⟩ := p
          obtain ⟨ha, hb⟩ : a ∈ es ∧ b = τe := by
            refine ⟨(List.of_mem_zip hp).1, ?_⟩
            have := (List.of_mem_zip hp).2
            exact List.eq_of_mem_replicate this
          subst hb
          exact hes a ha)
      obtain ⟨hn, hσ, hτsb, hp⟩ := inferArgs_inv es (fun a _ => infer_inv L a) (by ret_ok) .none hΓ hR h
      have hlen : o.τs.length = es.length := by simpa using hτs.length
      have hu : TyEq ((Ty.tuple o.τs).subst ((o.next, τe) :: φ))
          ((Ty.tuple (List.replicate o.τs.length (.var o.next))).subst ((o.next, τe) :: φ)) := by
        simp only [Ty.subst_app, List.map_replicate]
        rw [List.map_congr_left (fun τ hτ => Ty.subst_cons_fresh (hτsb τ hτ)), hlen]
        refine TyEq.app_eqs (hτs.trans ?_)
        simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]
        exact TyEqs.refl _
      obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, hat, h, hσ']; rfl, (o.next, τe) :: φ,
        Agree.absorb (hag.fresh hσ hn) habs, ?_, Sat.absorb habs (Sat.fresh hp hsat)⟩
      refine (habs _).trans ?_
      simpa [Ty.subst, Subst.find] using hτ₀

theorem infer_complete_index (L : List String) (e : Expr) (i : Expr) (ihe : e.PolyOK L → InferComplete L e) (ihi : i.PolyOK L → InferComplete L i) :
    (Expr.index e i).PolyOK L → InferComplete L (Expr.index e i) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihe : InferComplete L e := ihe hm.1
  replace ihi : InferComplete L i := ihi hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | index he hi hpr =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihi (by ret_ok) (by ret_eq) .none .none (ψ := φ₁) hΓ₁ hR₁ hC
      (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hi
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L i (by ret_ok) .none hΓ₁ hR₁ h₂
    refine ⟨_, by simp only [infer, h₁, h₂]; rfl, (o₂.next, τ₀) :: φ₂,
      (hag₁.trans hσ₁ hn₁ hag₂).fresh ((hσ₁.mono hn₂).compose hσ₂) (by omega),
      by simp [Ty.subst, Subst.find]; exact hτ₀, ?_⟩
    refine Sat.app (Sat.fresh (fun p hp => ?_) (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂)) ?_
    · simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp
    · intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Pred.subst, List.map_cons, List.map_nil,
        Ty.subst_cons_fresh (hσ₂.subst_below (hτb₁.mono hn₂)), Ty.subst_cons_fresh hτb₂]
      refine hpr.of_predEq (PredEq.of_eqs (.cons (hτ₁.symm.trans (hag₂.ty hτb₁).symm)
        (.cons hτ₂.symm (.cons ?_ .nil))))
      simp [Ty.subst, Subst.find]; exact TyEq.refl _

theorem infer_complete_setIndex (L : List String) (e : Expr) (i : Expr) (v : Expr) (ihe : e.PolyOK L → InferComplete L e) (ihi : i.PolyOK L → InferComplete L i) (ihv : v.PolyOK L → InferComplete L v) :
    (Expr.setIndex e i v).PolyOK L → InferComplete L (Expr.setIndex e i v) := by
  intro hm
  simp only [Expr.PolyOK] at hm
  replace ihe : InferComplete L e := ihe hm.1.1
  replace ihi : InferComplete L i := ihi hm.1.2
  replace ihv : InferComplete L v := ihv hm.2
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | setIndex he hi hpr hw hv =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
    have hr₁ := hR'.trans (hag₁.ret hR).symm
    obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihi (by ret_ok) (by ret_eq) .none .none (ψ := φ₁) hΓ₁ hR₁ hC hc₁ hr₁ hi
    obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L i (by ret_ok) .none hΓ₁ hR₁ h₂
    have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
    have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
    obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := ihv (by ret_ok) (by ret_eq) .none .none (ψ := φ₂) hΓ₂ hR₂ hC
      (hc₁.trans (hag₂.ctx hΓ₁).symm) (hr₁.trans (hag₂.ret hR₁).symm) hv
    have hb₁ : (o₁.τ.subst o₂.σ).Below o₂.next := hσ₂.subst_below (hτb₁.mono hn₂)
    have hP : ∀ p ∈ o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, p.Below o₂.next := by
      intro p hp
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact hp₂ p hp
    have he₁ : TyEq (((o₁.τ.subst o₂.σ).subst o₃.σ).subst φ₃) _ :=
      (hag₃.ty hb₁).trans ((hag₂.ty hτb₁).trans hτ₁)
    refine ⟨⟨Subst.compose o₃.σ (Subst.compose o₂.σ o₁.σ), o₃.τ,
        (o₁.preds.map (·.subst o₂.σ) ++ o₂.preds).map (·.subst o₃.σ) ++ o₃.preds ++
          [⟨.indexable, [(o₁.τ.subst o₂.σ).subst o₃.σ, o₂.τ.subst o₃.σ, o₃.τ]⟩,
            ⟨.indexWrite, [(o₁.τ.subst o₂.σ).subst o₃.σ]⟩], o₃.next⟩,
      by simp only [infer, h₁, h₂, h₃], φ₃,
      (hag₁.trans hσ₁ hn₁ hag₂).trans ((hσ₁.mono hn₂).compose hσ₂) (by omega) hag₃,
      hτ₃.trans hτ₀, ?_⟩
    refine Sat.app (Sat.app (Sat.agree hag₃ hP (Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂))
      hsat₃) ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [Pred.subst, List.map_cons, List.map_nil]
      exact hpr.of_predEq (PredEq.of_eqs (.cons he₁.symm
        (.cons ((hag₃.ty hτb₂).trans hτ₂).symm (.cons hτ₃.symm .nil))))
    · simp only [Pred.subst, List.map_cons, List.map_nil]
      exact hw.of_predEq (PredEq.of_eqs (.cons he₁.symm .nil))

theorem infer_complete_mcall (L : List String) (e : Expr) (l : String) (args : List Expr) (ihe : e.PolyOK L → InferComplete L e) (iha : ∀ a ∈ args, a.PolyOK L → InferComplete L a) :
    (Expr.mcall e l args).PolyOK L → InferComplete L (Expr.mcall e l args) := by
  intro hm
  simp only [Expr.PolyOK, Expr.PolyOKList_eq] at hm
  replace ihe : InferComplete L e := ihe hm.1
  replace iha : ∀ a ∈ args, InferComplete L a := fun a ha => iha a ha (hm.2 a ha)
  intro Γ R rm ex n ψ C md τ' Γ' R' hRo hRc hex hm hΓ hR hC hΓ' hR' ht
  obtain ⟨hmd, -⟩ := hm
  rw [exMode_synth (fun _ => rfl)] at hmd; subst hmd
  obtain ⟨τ₀, hτ₀, ht⟩ := ht.top_synth
  cases ht with
  | @mcall _ _ _ _ _ τe _ κ τs' _ _ he hpr hlen hargs =>
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe (by ret_ok) (by ret_eq) .none .none hΓ hR hC hΓ' hR' he
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (by ret_ok) .none hΓ hR h₁
    have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
    have hR₁ := hσ₁.ret_below (hR.mono hn₁)
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (by ret_ok) (by ret_eq) .none (fun _ h => nomatch h) (ψ := φ₁)
      hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
    obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) (by ret_ok) .none hΓ₁ hR₁ h₂
    have hb₁ : (o₁.τ.subst o₂.σ).Below o₂.next := hσ₂.subst_below (hτb₁.mono hn₂)
    let φ := (o₂.next + 1, τ₀) :: (o₂.next, κ) :: φ₂
    have hfr : ∀ τ : Ty, τ.Below o₂.next → τ.subst φ = τ.subst φ₂ := fun τ hτ => by
      rw [Ty.subst_cons_fresh (hτ.mono (Nat.le_succ _)), Ty.subst_cons_fresh hτ]
    have hrecv : TyEq ((o₁.τ.subst o₂.σ).subst φ) τe := by
      rw [hfr _ hb₁]; exact (hag₂.ty hτb₁).trans hτ₁
    refine ⟨_, by simp only [infer, h₁, h₂]; rfl, φ, ?_, ?_, ?_⟩
    · exact ((hag₁.trans hσ₁ hn₁ hag₂).fresh ((hσ₁.mono hn₂).compose hσ₂) (by omega)).fresh
        (((hσ₁.mono hn₂).compose hσ₂).mono (Nat.le_succ _)) (by omega)
    · simp [φ, Ty.subst, Subst.find]; exact hτ₀
    · refine Sat.app (Sat.app ?_ ?_) ?_
      · refine Sat.fresh (fun p hp => ?_) (Sat.fresh (fun p hp => ?_) (Sat.agree hag₂ hp₁ hsat₁))
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact (hσ₂.pred_below ((hp₁ q hq).mono hn₂)).mono (Nat.le_succ _)
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact hσ₂.pred_below ((hp₁ q hq).mono hn₂)
      · exact Sat.fresh (fun p hp => (hp₂ p hp).mono (Nat.le_succ _)) (Sat.fresh hp₂ hsat₂)
      · intro c hc
        simp only [List.mem_singleton] at hc; subst hc
        simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_fn]
        refine hpr.of_predEq (PredEq.of_eqs (.cons hrecv.symm (.cons ?_ (.cons ?_ .nil))))
        · simp [φ, Ty.subst, Subst.find]; exact TyEq.refl _
        · refine TyEq.fn_mk hrecv.symm (by simp [φ, Ty.subst, Subst.find]; exact TyEq.refl _) ?_
          rw [List.map_congr_left (fun τ hτ => hfr τ (hτsb₂ τ hτ))]
          exact hτs₂.symm


/-- Inference is complete for every program whose annotations are
monomorphic: one lemma per form of expression, each from the induction
hypotheses for its parts. -/
theorem infer_complete_polyOK (L : List String) : ∀ e, e.PolyOK L → InferComplete L e := by
  intro e
  induction e using Expr.ind with
  | lit l => exact infer_complete_lit L l
  | var i => exact infer_complete_var L i
  | func k body ih => exact infer_complete_func L k body ih
  | app f args ihf iha => exact infer_complete_app L f args ihf iha
  | let_ mb ann e₁ e₂ ih₁ ih₂ => exact infer_complete_let_ L mb ann e₁ e₂ ih₁ ih₂
  | assign i e ih => exact infer_complete_assign L i e ih
  | cond c t e ihc iht ihe => exact infer_complete_cond L c t e ihc iht ihe
  | unwrap e₁ e₂ e₃ ih₁ ih₂ ih₃ => exact infer_complete_unwrap L e₁ e₂ e₃ ih₁ ih₂ ih₃
  | caseTag e₁ l t e₂ e₃ ih₁ ih₂ ih₃ => exact infer_complete_caseTag L e₁ l t e₂ e₃ ih₁ ih₂ ih₃
  | unop op e ih => exact infer_complete_unop L op e ih
  | binop op e₁ e₂ ih₁ ih₂ => exact infer_complete_binop L op e₁ e₂ ih₁ ih₂
  | ret e ih => exact infer_complete_ret L e ih
  | throw_ e ih => exact infer_complete_throw_ L e ih
  | seq e₁ e₂ ih₁ ih₂ => exact infer_complete_seq L e₁ e₂ ih₁ ih₂
  | while_ c body ihc ihb => exact infer_complete_while_ L c body ihc ihb
  | break_ => exact infer_complete_break_ L
  | continue_ => exact infer_complete_continue_ L
  | tryCatch body handler ihb ihh => exact infer_complete_tryCatch L body handler ihb ihh
  | tryFinally body fin ihb ihf => exact infer_complete_tryFinally L body fin ihb ihf
  | obj ls es ks ih => exact infer_complete_obj L ls es ks ih
  | cls ls es ks ih => exact infer_complete_cls L ls es ks ih
  | ctor k body ih => exact infer_complete_ctor L k body ih
  | new_ f args ihf iha => exact infer_complete_new_ L f args ihf iha
  | get e l ih => exact infer_complete_get L e l ih
  | set e l v ihe ihv => exact infer_complete_set L e l v ihe ihv
  | spread e₁ e₂ ih₁ ih₂ => exact infer_complete_spread L e₁ e₂ ih₁ ih₂
  | arr es ih => exact infer_complete_arr L es ih
  | index e i ihe ihi => exact infer_complete_index L e i ihe ihi
  | setIndex e i v ihe ihi ihv => exact infer_complete_setIndex L e i v ihe ihi ihv
  | mcall e l args ihe iha => exact infer_complete_mcall L e l args ihe iha

theorem infer_complete (L : List String) : ∀ e, e.monoAnn = true → InferComplete L e :=
  fun e h => infer_complete_polyOK L e (Expr.polyOK_of_monoAnn L h)

/-! ## Programs -/

theorem Ty.whnf_whnf (τ : Ty) : τ.whnf.whnf = τ.whnf := by
  cases hv : τ.view with
  | none => simp [Ty.whnf, hv]
  | some t => rw [Ty.whnf_of_view hv]; exact Ty.whnf_of_view (Ty.view_of_shape (Ty.view_shape hv))

theorem Ty.slotOnVar_complete {s : Ty} (h : s.SlotOnVar) : s.slotOnVar = true := by
  unfold Ty.SlotOnVar at h
  unfold Ty.slotOnVar
  split at h
  · simp
  · rcases h with ⟨a, ha⟩ | ⟨hp, a, ha⟩ <;> simp [Ty.isVar, *]
  · exact h.elim

theorem Pred.mergeOnVar_complete {p : Pred} (h : p.MergeOnVar) : p.mergeOnVar = true := by
  unfold Pred.MergeOnVar at h
  unfold Pred.mergeOnVar
  split at h
  · rcases h with ⟨hq, a, ha⟩ | ⟨hqk, hs⟩
    · simp [hq, ha, Ty.isVar]
    · have := Ty.slotOnVar_complete hs
      rcases hqk with ⟨hq, hk⟩ | hq <;> simp [*]
  · exact h.elim

theorem Pred.decideCopy_keep_inv {s r : Ty} (h : Pred.decideCopy s r = .keep) : s.SlotOnVar := by
  unfold Pred.decideCopy at h
  unfold Ty.SlotOnVar
  split at h
  · rename_i p k τ heq
    rw [heq]; dsimp only
    split at h
    all_goals first
      | (rename_i a ha; exact .inl ⟨a, ha⟩)
      | (rename_i a hp ha; exact .inr ⟨hp, a, ha⟩)
      | cases h
  · rename_i a heq; rw [heq]; trivial
  · cases h

theorem Pred.decidePre_keep {k τ s r : Ty} (h : Pred.decidePre k τ s r = .keep) :
    (∃ a, k.whnf = .var a) ∨ (k.whnf = .proto ∧ Pred.decideCopy s r = .keep) := by
  unfold Pred.decidePre at h
  split at h
  all_goals first | exact .inr ⟨‹_›, h⟩ | (rename_i a ha; exact .inl ⟨a, ha⟩) | cases h

theorem Pred.decide₀_merge_keep {t : Ty} {rest : List Ty} (h : Pred.decide₀ .merge t rest = .keep) :
    ∃ k τ s r, rest = [k, τ, s, r] ∧
      ((t = .pre ∧ Pred.decidePre k τ s r = .keep) ∨ (t = .abs ∧ Pred.decideCopy s r = .keep)) := by
  unfold Pred.decide₀ at h
  split at h
  all_goals first
    | exact ⟨_, _, _, _, rfl, .inl ⟨rfl, h⟩⟩
    | exact ⟨_, _, _, _, rfl, .inr ⟨rfl, h⟩⟩
    | cases h
    | (split at h <;> cases h)
    | exact absurd h Pred.decideInject_ne_keep
    | exact absurd h Pred.decideStrip_ne_keep
    | exact absurd h Pred.decideCase_ne_keep

/-- What improvement leaves at the top level of entailed constraints is
settled: an instance, or on a type variable. -/
theorem Pred.settled_of_keep {C : List Pred} (hC : ∀ c ∈ C, c.OnVarShaped) {p : Pred}
    {φ : Subst} (hk : p.improve true = .keep) (he : Entails C (p.subst φ)) :
    p.settled = true := by
  have hC' : ∀ c ∈ C, c.AssumableAt true := fun c hc => (hC c hc).assumable true
  have hl := he.arity hC'
  simp only [Pred.settled, Bool.or_eq_true]
  obtain ⟨cls, args⟩ := p
  simp only [Pred.subst, List.length_map] at hl
  have hvar : ∀ t rest a, args = t :: rest → t.whnf = .var a →
      Pred.onVar ⟨cls, args⟩ = true := by
    intro t rest a e ha; simp [Pred.onVar, e, ha, Ty.isVar]
  cases cls
  case plus =>
    match args, hl with
    | [t], _ =>
      rcases he with ⟨q₀, hpq, hi⟩ | ⟨c, hc, hpc⟩
      · have hq₀ : q₀ = ⟨.plus, [.number]⟩ ∨ q₀ = ⟨.plus, [.string]⟩ := by
          have hc := hpq.1
          cases hi <;> simp_all [Pred.subst]
        rcases hq₀ with rfl | rfl
        all_goals
          obtain ⟨-, hq⟩ := PredEq.one hpq
          rcases Ty.whnf_con_of_tyEq hq with ⟨a, ha⟩ | hc
          · exact .inr (hvar t [] a rfl ha)
          · left; simp [Pred.whnfArgs, hc, Pred.isInst]
      · rcases hC c hc with ⟨-, -, a, rest, hca⟩ | ⟨q, k, τ, s, r, rfl, -⟩
        · have he' := hpc.args_eqs
          simp only [Pred.subst, List.map_cons, List.map_nil, hca] at he'
          cases he' with
          | cons h₁ _ =>
            obtain ⟨b, hb⟩ := Ty.whnf_var_of_tyEq h₁
            exact .inr (hvar t [] b rfl hb)
        · exact absurd hpc.1 (by simp [Pred.subst])
  case merge =>
    match args, hl with
    | [q, k, τ, s, r], _ =>
      simp only [Pred.improve, ↓reduceIte] at hk
      rw [Pred.improveArgs_cons] at hk
      split at hk
      · rename_i hv
        obtain ⟨a, ha⟩ := Ty.isVar_iff.mp hv
        exact .inr (hvar q _ a rfl ha)
      · right
        simp only [Pred.onVar, Bool.or_eq_true]
        right
        apply Pred.mergeOnVar_complete
        obtain ⟨k', τ', s', r', he, hc⟩ := Pred.decide₀_merge_keep hk
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := he
        simp only [Pred.MergeOnVar]
        rcases hc with ⟨hq, hp⟩ | ⟨hq, hp⟩
        · rcases Pred.decidePre_keep hp with h | ⟨hk', hc'⟩
          · exact .inl ⟨hq, h⟩
          · exact .inr ⟨.inl ⟨hq, hk'⟩, Pred.decideCopy_keep_inv hc'⟩
        · exact .inr ⟨.inr hq, Pred.decideCopy_keep_inv hp⟩
  all_goals
    simp only [Pred.improve] at hk
    match args, hk with
    | t :: rest, hk =>
      rw [Pred.improveArgs_cons] at hk
      split at hk
      · rename_i hv
        obtain ⟨a, ha⟩ := Ty.isVar_iff.mp hv
        exact .inr (hvar t rest a rfl ha)
      · have := Pred.decide₀_keep_merge hk; cases this
    | [], hk => simp [Pred.improveArgs] at hk

/-- Completeness, for a program in a closed context (such as the builtins'):
if it has a type, under assumptions on type variables, passes the scope
checks (`Expr.scoped`) and lets no rigid type variable escape at a
polymorphic annotation (`Expr.PolyOK`), inference accepts it, with a type of
which that one is an instance up to equal types. -/
theorem inferIn_complete_polyOK {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}
    (hΓ : ctxFtv Γ = []) (hC : ∀ p ∈ C, p.OnVarShaped)
    (hm : e.scoped (Γ.map fun _ => false) = true) (hpoly : e.PolyOK L)
    (ht : HasType L C Γ none .synth .synth e τ') :
    ∃ τ, inferIn L Γ e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' := by
  obtain ⟨o, h, φ, _, hτ, hsat⟩ := infer_complete_polyOK L e hpoly (n := 0) (ψ := []) (R := none)
    RetOk.synth nofun .none .none (fun a ha => by rw [hΓ] at ha; cases ha) (fun a ha => by simp [Ret.ftv] at ha)
    (fun p hp => (hC p hp).assumable false) (by rw [Ctx.subst_nil]; exact CtxEq.refl Γ) (RetEq.refl _) ht
  obtain ⟨σi, preds, himp, habs, hsat', hkeep, _⟩ :=
    improveAll_complete (fun p hp => (hC p hp).assumable true) o.preds.length (Nat.le_refl _)
      hsat
  have hall : preds.all Pred.settled = true := List.all_eq_true.mpr (fun p hp =>
    Pred.settled_of_keep hC (hkeep p hp) (hsat' p hp))
  exact ⟨o.τ.subst σi, by simp [inferIn, hm, h, himp, hall], φ, (habs _).trans hτ⟩

/-- Completeness for programs whose annotations are all monomorphic
(`Expr.monoAnn`). -/
theorem inferIn_complete {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}
    (hΓ : ctxFtv Γ = []) (hC : ∀ p ∈ C, p.OnVarShaped)
    (hm : e.scoped (Γ.map fun _ => false) = true) (hmono : e.monoAnn = true)
    (ht : HasType L C Γ none .synth .synth e τ') :
    ∃ τ, inferIn L Γ e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferIn_complete_polyOK hΓ hC hm (Expr.polyOK_of_monoAnn L hmono) ht

/-- Completeness for closed programs: one that has a type, with records over
its labels, passes the scope checks and lets no rigid type variable escape
is accepted, with a type of which that one is an instance up to equal
types. -/
theorem inferProgram_complete_polyOK {e : Expr} {τ' : Ty} (hm : e.scoped [] = true)
    (hpoly : e.PolyOK e.labels.eraseDups)
    (ht : HasType e.labels.eraseDups [] [] none .synth .synth e τ') :
    ∃ τ, inferProgram e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferIn_complete_polyOK (Γ := []) rfl (fun _ h => by cases h) hm hpoly ht

/-- Completeness for closed programs whose annotations are all
monomorphic. -/
theorem inferProgram_complete {e : Expr} {τ' : Ty} (hm : e.scoped [] = true)
    (hmono : e.monoAnn = true) (ht : HasType e.labels.eraseDups [] [] none .synth .synth e τ') :
    ∃ τ, inferProgram e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferProgram_complete_polyOK hm (Expr.polyOK_of_monoAnn _ hmono) ht

end Inty
