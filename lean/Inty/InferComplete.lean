import Inty.InferInv

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
moves to it (`HasType.weaken`).
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


/-! ## Heads through substitution -/

theorem Ty.whnf_cases (t : Ty) :
    (∃ a, t.whnf = .var a) ∨ (∃ c xs, t.whnf = .app c xs ∧ t.view = some (.app c xs)) ∨
      t.view = none := by
  cases hv : t.view with
  | none => exact .inr (.inr rfl)
  | some v =>
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, xs, rfl⟩
    · exact .inl ⟨a, Ty.whnf_of_view hv⟩
    · exact .inr (.inl ⟨c, xs, Ty.whnf_of_view hv, rfl⟩)

theorem Ty.whnf_headless {t : Ty} (h : t.view = none) : t.whnf = t := by simp [Ty.whnf, h]

theorem Ty.view_subst_none {t : Ty} (h : t.view = none) (φ : Subst) : (t.subst φ).view = none := by
  rw [Ty.view_subst, h]; rfl

theorem Ty.view_subst_app {t : Ty} {c : Con} {xs : List Ty} (h : t.view = some (.app c xs))
    (φ : Subst) : (t.subst φ).view = some (.app c (xs.map (·.subst φ))) := by
  rw [Ty.view_subst, h]; simp [Ty.view]

/-- A head through substitution: a variable's is its image's, a constructor
stays. -/
theorem Ty.whnf_subst_app {t : Ty} {φ : Subst} {c : Con} {ys : List Ty}
    (h : (t.subst φ).whnf = .app c ys) :
    (∃ a, t.whnf = .var a) ∨ ∃ xs, t.whnf = .app c xs ∧ ys = xs.map (·.subst φ) := by
  rcases Ty.whnf_cases t with ⟨a, ha⟩ | ⟨c', xs, hw, hv⟩ | hv
  · exact .inl ⟨a, ha⟩
  · rw [Ty.whnf_of_view (Ty.view_subst_app hv φ)] at h
    simp only [Ty.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨xs, hw, rfl⟩
  · rw [Ty.whnf_headless (Ty.view_subst_none hv φ)] at h
    have := Ty.view_subst_none hv φ
    rw [h] at this; cases this

theorem Ty.whnf_subst_var {t : Ty} {φ : Subst} {a : Nat} (h : (t.subst φ).whnf = .var a) :
    ∃ b, t.whnf = .var b := by
  rcases Ty.whnf_cases t with ⟨b, hb⟩ | ⟨c', xs, hw, hv⟩ | hv
  · exact ⟨b, hb⟩
  · rw [Ty.whnf_of_view (Ty.view_subst_app hv φ)] at h; cases h
  · rw [Ty.whnf_headless (Ty.view_subst_none hv φ)] at h
    have := Ty.view_subst_none hv φ
    rw [h] at this; cases this

/-- A type whose image is equal to a constructor application unfolds to a
variable or to that constructor. -/
theorem Ty.whnf_app_of_tyEq {t : Ty} {φ : Subst} {c : Con} {ys : List Ty}
    (h : TyEq (t.subst φ) (.app c ys)) :
    (∃ a, t.whnf = .var a) ∨ ∃ xs, t.whnf = .app c xs ∧ xs.length = ys.length ∧
      ∀ x ∈ xs.zip ys, TyEq (x.1.subst φ) x.2 := by
  obtain ⟨zs, hz, he⟩ := TyEq.whnf_app h.symm rfl
  rcases Ty.whnf_subst_app hz with ⟨a, ha⟩ | ⟨xs, hxs, rfl⟩
  · exact .inl ⟨a, ha⟩
  · obtain ⟨-, hl, hzz⟩ := TyEq.app_iff.mp he
    refine .inr ⟨xs, hxs, by simpa using hl.symm, fun x hx => ?_⟩
    obtain ⟨u, v⟩ := x
    have : (v, u.subst φ) ∈ ys.zip (xs.map (·.subst φ)) := by
      rw [List.zip_map_right]
      exact List.mem_map.mpr ⟨(v, u), zip_symm_mem hx, rfl⟩
    exact (hzz _ this).symm

theorem Ty.whnf_con_of_tyEq {t : Ty} {φ : Subst} {c : Con} (h : TyEq (t.subst φ) (.app c [])) :
    (∃ a, t.whnf = .var a) ∨ t.whnf = .app c [] := by
  rcases Ty.whnf_app_of_tyEq h with h | ⟨xs, hxs, hl, -⟩
  · exact .inl h
  · exact .inr (by rw [hxs, List.eq_nil_of_length_eq_zero hl])

theorem Ty.whnf_var_of_tyEq {t : Ty} {φ : Subst} {a : Nat} (h : TyEq (t.subst φ) (.var a)) :
    ∃ b, t.whnf = .var b :=
  Ty.whnf_subst_var (TyEq.whnf_var h.symm rfl)

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

/-- What `infer_complete` says of one expression: if the expression has a
type in a context equal to an instance of inference's, inference finds a
type of which it is an instance, with the constraints satisfied. -/
def InferComplete (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred} {τ' : Ty} {Γ' : Ctx}
    {R' : Option Ty},
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
    CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → HasType L C Γ' R' e τ' →
    ∃ o, infer L Γ R e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ TyEq (o.τ.subst φ) τ' ∧
      Sat C o.preds φ

theorem inferArgs_complete : ∀ (args : List Expr) (τs' : List Ty), (∀ a ∈ args, InferComplete L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
      {Γ' : Ctx} {R' : Option Ty},
      Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
      CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → args.length = τs'.length →
      (∀ p ∈ args.zip τs', HasType L C Γ' R' p.1 p.2) →
      ∃ o, inferArgs L Γ R args n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧
        TyEqs (o.τs.map (·.subst φ)) τs' ∧ Sat C o.preds φ
  | [], [], _, Γ, R, n, ψ, C, _, _, _, _, _, _, _, _, _ =>
    ⟨⟨[], [], [], n⟩, by simp [inferArgs], ψ, Agree.nil n ψ, .nil, by simp [Sat]⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, τ' :: τs', ih, Γ, R, n, ψ, C, Γ', R', hΓ, hR, hC, hΓ', hR', hlen, hargs => by
    obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ :=
      ih a (by simp) hΓ hR hC hΓ' hR' (hargs (a, τ') (by simp))
    obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L a hΓ hR h₁
    obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete as τs'
      (fun a' ha' => ih a' (by simp [ha'])) (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
      (hσ₁.ret_below (hR.mono hn₁)) hC (hΓ'.trans (hag₁.ctx hΓ).symm)
      (hR'.trans (hag₁.ret hR).symm) (by simpa using hlen) (fun p hp => hargs p (by simp [hp]))
    refine ⟨_, by simp only [inferArgs, h₁, h₂]; rfl, φ₂, hag₁.trans hσ₁ hn₁ hag₂, ?_, ?_⟩
    · simp only [List.map_cons]
      exact .cons ((hag₂.ty hτb₁).trans hτ₁) hτs₂
    · exact Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂

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

theorem infer_func_shape {Γ : Ctx} {R : Option Ty} {k : Nat} {b : Expr} {n : Nat} {o : Out}
    (h : infer L Γ R (.func k b) n = some o) : ∃ θ ps ρ, o.τ = .fn θ ps ρ ∧ ps.length = k := by
  simp only [infer] at h
  split at h
  · cases h
  split at h
  · cases h
  simp only [Option.some.injEq] at h; subst h
  exact ⟨_, _, _, Ty.subst_fn _ _ _ _, by simp [varBlock]⟩

theorem inferArgs_shape : ∀ {es : List Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : OutArgs},
    inferArgs L Γ R es n = some o → FnShaped es o.τs
  | [], _, _, _, o, h => by
    simp only [inferArgs, Option.some.injEq] at h; subst h
    intro i k b τ he; simp at he
  | e :: es, Γ, R, n, o, h => by
    simp only [inferArgs] at h
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
        HasType L C (memberCtxD Δ' Γ' ks τs' i k) R' e τ) →
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
        HasType L C (memberCtxD (if k = .data then τ' :: Δ' else Δ') Γ' ks τs' i k₁) R' e₁ τ₁ := by
      intro i e₁ k₁ τ₁ he₁ hk₁ hτ₁
      have := hms (i + 1) e₁ k₁ τ₁ (by simpa using he₁) (by simpa using hk₁) (by simpa using hτ₁)
      rwa [memberCtxD_succ] at this
    have h₀ := hms 0 e k τ' rfl rfl rfl
    rw [memberCtxD_zero] at h₀
    cases k with
    | data =>
      simp only [↓reduceIte] at h₀ hrest
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih e List.mem_cons_self
        (Γ := Δ.map .mono ++ Γ) (R := R) (n := n) (ψ := ψ)
        (Ctx.Below.append_mono hΔ hΓ) hR hC
        (by
          have := CtxEq.monos hΔ' hΓ'
          simpa [Ctx.subst, List.map_map, Function.comp_def, Scheme.mono_subst] using this)
        hR' h₀
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e (Ctx.Below.append_mono hΔ hΓ) hR h₁
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
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih e List.mem_cons_self hΓ hR hC hΓ' hR' h₀
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
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
theorem memberSlots_complete {T' : Ty} : ∀ {ks : List ClassKind} {es : List Expr}
    {τs τs' ss' : List Ty} {m : Nat} {φ : Subst}, FnShaped es τs → (∀ τ ∈ τs, τ.Below m) →
    TyEqs (τs.map (·.subst φ)) τs' →
    ks.length = es.length → es.length = τs.length → ss'.length = τs'.length →
    (∀ x ∈ ks.zip (es.zip (τs'.zip ss')), MemberSlot T' x.1 x.2.1 x.2.2.1 x.2.2.2) →
    ∃ θs ss m' φ', memberSlots ks es τs m = some (θs, ss, m') ∧ m ≤ m' ∧
      (∀ τ : Ty, τ.Below m → τ.subst φ' = τ.subst φ) ∧
      TyEqs (ss.map (·.subst φ')) ss' ∧ ∀ θ ∈ θs, TyEq (θ.subst φ') T'
  | [], [], [], [], [], m, φ, _, _, _, _, _, _, _ =>
    ⟨[], [], m, φ, rfl, Nat.le_refl _, fun _ _ => rfl, .nil, by simp⟩
  | k :: ks, e :: es, τ :: τs, τ' :: τs', s' :: ss', m, φ, hsh, hb, hτs, hk, he, hs, hf => by
    cases hτs with
    | cons hτ hτs =>
    dsimp only at hτ
    have hb₀ := hb τ List.mem_cons_self
    have hbs : ∀ τ ∈ τs, τ.Below m := fun τ hτ => hb τ (List.mem_cons_of_mem _ hτ)
    have hf₀ := hf (k, e, τ', s') (by simp)
    have hf' : ∀ x ∈ ks.zip (es.zip (τs'.zip ss')), MemberSlot T' x.1 x.2.1 x.2.2.1 x.2.2.2 :=
      fun x hx => hf x (by simp [hx])
    simp only at hf₀
    cases hf₀ with
    | data =>
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      refine ⟨θs, .slot .pre .data τ :: ss, m', φ', by simp [memberSlots, h], hm, hφ',
        .cons ?_ hss, hθs⟩
      dsimp only
      rw [hφ' _ (Ty.Below.app.mpr (by simp [hb₀, Ty.Below.con]))]
      exact TyEq.slot_mk (TyEq.refl _) (TyEq.refl _) hτ
    | @arrow θ' n b τs'' ρ' θ'' hθ =>
      obtain ⟨θ, ps, ρ, rfl, -⟩ := hsh.head rfl
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs⟩ := memberSlots_complete (m := m + 1)
        (φ := (m, θ'') :: φ) hsh.tail (fun τ hτ => (hbs τ hτ).mono (Nat.le_succ _))
        (by rw [List.map_congr_left (fun τ hτ => Ty.subst_cons_fresh (hbs τ hτ))]; exact hτs)
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      obtain ⟨hθb, hpsb, hρb⟩ := Ty.Below.fn.mp hb₀
      have hφm : ∀ τ : Ty, τ.Below m → τ.subst φ' = τ.subst φ := fun τ hτ => by
        rw [hφ' τ (hτ.mono (Nat.le_succ _)), Ty.subst_cons_fresh hτ]
      simp only [Ty.subst_fn] at hτ
      obtain ⟨h₁, h₂, h₃⟩ := TyEq.fn_inv hτ
      refine ⟨θ :: θs, .slot .pre .data (.fn (.var m) ps ρ) :: ss, m', φ',
        by simp [memberSlots, h], by omega, hφm, .cons ?_ hss, ?_⟩
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
    | @method θ' n b τs'' ρ' hθ =>
      obtain ⟨θ, ps, ρ, rfl, -⟩ := hsh.head rfl
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      refine ⟨θ :: θs, .slot .pre .proto (.fn θ ps ρ) :: ss, m', φ', by simp [memberSlots, h], hm,
        hφ', .cons ?_ hss, ?_⟩
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
      obtain ⟨θs, ss, m', φ', h, hm, hφ', hss, hθs⟩ := memberSlots_complete hsh.tail hbs hτs
        (by simpa using hk) (by simpa using he) (by simpa using hs) hf'
      obtain ⟨hθb, -, hρb⟩ := Ty.Below.fn.mp hb₀
      simp only [Ty.subst_fn] at hτ
      obtain ⟨h₁, h₂, -⟩ := TyEq.fn_inv hτ
      refine ⟨θ :: θs, .slot .pre .proto ρ :: ss, m', φ', by simp [memberSlots, h], hm,
        hφ', .cons ?_ hss, ?_⟩
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
  | writeArray =>
    simp only [Pred.fundep, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp at hr

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
theorem Entails.drop_block {C : List Pred} {s : Scheme} (hs : s.Simple) {m : Nat}
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
theorem Entails.arity {top : Bool} {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt top) {p : Pred}
    (h : Entails C p) : p.args.length = p.cls.arity := by
  rcases h with ⟨q, hpq, hi⟩ | ⟨c, hc, hpc⟩
  · rw [hpq.2.1, hpq.1]; cases hi <;> rfl
  · rw [hpc.2.1, hpc.1]
    rcases hC c hc with ⟨-, hl, -⟩ | ⟨q, k, τ, s, r, rfl, -⟩
    · exact hl
    · rfl

theorem Pred.decide₀_keep_merge {c : Cls} {t : Ty} {rest : List Ty}
    (h : Pred.decide₀ c t rest = .keep) : c = .merge := by
  unfold Pred.decide₀ at h
  split at h <;> first | rfl | (split at h <;> cases h) | cases h

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
theorem Entails.first_var_or_inst {C : List Pred} (hC : ∀ c ∈ C, c.AssumableAt false)
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

@[simp] theorem Ty.newTarget_subst (σ : Subst) : Ty.newTarget.subst σ = .newTarget := rfl

theorem infer_complete (L : List String) : ∀ e, InferComplete L e := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR _ _ _ ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | lit hl =>
      refine ⟨⟨[], l.ty, [], n⟩, by simp [infer], ψ, Agree.nil n ψ, ?_, by simp [Sat]⟩
      rw [LitTy.eq_ty hl] at hτ₀
      simpa [Lit.ty_subst] using hτ₀
  | var i =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR _ hΓ' _ ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @var _ _ s' _ _ τs hi hlen hc =>
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
  | func k body ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' _ ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @func _ _ _ ρ' _ _ θ' τs' hlen hb =>
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
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (R := some (.var (n + 1 + τs'.length)))
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
      refine ⟨_, by simp only [infer, h₁, hσ']; rfl, φ₁, fun a ha => ?_, ?_, ?_⟩
      · refine (hag₁.absorb habs a (by omega)).trans ?_
        simp only [Ty.subst, funSubst_below ha]; exact TyEq.refl _
      · refine ((hag₁.absorb habs).ty hfn).trans ?_
        simp only [Ty.subst_fn, funSubst_this, funSubst_ret, hparams]; exact hτ₀
      · exact Sat.absorb habs hsat₁
  | app f args ihf iha =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | app hf hlen hargs =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihf hΓ hR hC hΓ' hR' hf
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L f hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (ψ := φ₁)
        hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
      obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) hΓ₁ hR₁ h₂
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
  | let_ mb e₁ e₂ ih₁ ih₂ =>
    sorry
  | assign i e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @assign _ _ s' _ _ _ hi ha hp he =>
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
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' (he.conv hsi)
        have hsb : (s.inst []).Below n := Scheme.inst_nil_below (hΓ.lookup hs)
        have hu : TyEq (((s.inst []).subst o₁.σ).subst φ₁) (o₁.τ.subst φ₁) :=
          (hag₁.ty hsb).trans hτ₁.symm
        obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
        refine ⟨_, by simp only [infer, hs, ha', hp', and_self, ↓reduceIte, h₁, hσ']; rfl, φ₁,
          hag₁.absorb habs, ?_, Sat.absorb habs hsat₁⟩
        show TyEq (((s.inst []).subst (Subst.compose σ' o₁.σ)).subst φ₁) _
        rw [Ty.subst_compose]
        exact (habs _).trans ((hag₁.ty hsb).trans (hsi.symm.trans hτ₀))
  | cond c t e ihc iht ihe =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | cond hc htt hte =>
      obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc hΓ hR hC hΓ' hR' hc
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L c hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
      have hr₁ := hR'.trans (hag₁.ret hR).symm
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := iht (ψ := φ₁) hΓ₁ hR₁ hC hc₁ hr₁ htt
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L t hΓ₁ hR₁ h₂
      have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
      have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
      obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := ihe (ψ := φ₂) hΓ₂ hR₂ hC
        (hc₁.trans (hag₂.ctx hΓ₁).symm) (hr₁.trans (hag₂.ret hR₁).symm) hte
      obtain ⟨hn₃, hσ₃, hτb₃, hp₃⟩ := infer_inv L e hΓ₂ hR₂ h₃
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
  | unop op e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | unop hop he =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
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
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | binop hop ht₁ ht₂ =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' ht₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
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
      | minus =>
        obtain ⟨σ₃, hσ₃, habs₃⟩ := unify_mgu (τ₁ := o₁.τ.subst o₂.σ) (τ₂ := .number) (ψ := φ₂)
          (h₁₂.trans hτ₁)
        obtain ⟨σ₄, hσ₄, habs₄⟩ := unify_mgu (τ₁ := o₂.τ.subst σ₃) (τ₂ := .number) (ψ := φ₂)
          ((habs₃ _).trans hτ₂)
        exact ⟨_, by simp only [infer, h₁, h₂, hσ₃, hσ₄]; rfl, φ₂,
          (hag₁₂.absorb habs₃).absorb habs₄, by simpa using hτ₀,
          Sat.absorb habs₄ (Sat.absorb habs₃ hsat₁₂)⟩
  | ret e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @ret _ _ τr' _ _ he =>
      cases R with
      | none => exact hR'.elim
      | some τr =>
        obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
        obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
        have hτr : τr.Below n := fun a ha => hR a (by simpa [Ret.ftv] using ha)
        have hR'' : TyEq τr' (τr.subst ψ) := hR'
        obtain ⟨σ', hσ', habs⟩ := unify_mgu (τ₁ := τr.subst o₁.σ) (τ₂ := o₁.τ) (ψ := φ₁)
          ((hag₁.ty hτr).trans (hR''.symm.trans hτ₁.symm))
        have hσ'w := unify_within (hσ₁.subst_below (hτr.mono hn₁)) hτb₁ hσ'
        refine ⟨_, by simp only [infer, h₁, hσ']; rfl, (o₁.next, τ₀) :: φ₁,
          (hag₁.absorb habs).fresh (hσ₁.compose hσ'w) hn₁, ?_,
          Sat.fresh (fun p hp => ?_) (Sat.absorb habs hsat₁)⟩
        · simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]; exact hτ₀
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact hσ'w.pred_below (hp₁ q hq)
  | throw_ e ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | throw_ he =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      refine ⟨⟨o₁.σ, .var o₁.next, o₁.preds, o₁.next + 1⟩, by simp only [infer, h₁],
        (o₁.next, τ₀) :: φ₁, hag₁.fresh hσ₁ hn₁, ?_, Sat.fresh hp₁ hsat₁⟩
      simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]; exact hτ₀
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | seq ht₁ ht₂ =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' ht₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) ht₂
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₂.τ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds, o₂.next⟩,
        by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₂.trans hτ₀,
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩
  | while_ c body ihc ihb =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | while_ hc hb =>
      obtain ⟨o₁, h₁, φ₁, hag₁, _, hsat₁⟩ := ihc hΓ hR hC hΓ' hR' hc
      obtain ⟨hn₁, hσ₁, _, hp₁⟩ := infer_inv L c hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := ihb (ψ := φ₁) hΓ₁ hR₁ hC
        (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hb
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, .undefined, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
        o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂, hτ₀,
        Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩
  | break_ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    exact ⟨⟨[], .var n, [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
      fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha]; exact TyEq.refl _,
      by simp [Ty.subst, Subst.find]; exact TyEq.refl _, by simp [Sat]⟩
  | continue_ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    exact ⟨⟨[], .var n, [], n + 1⟩, by simp only [infer], (n, τ') :: ψ,
      fun a ha => by simp [Ty.subst, Subst.find, Nat.ne_of_lt ha]; exact TyEq.refl _,
      by simp [Ty.subst, Subst.find]; exact TyEq.refl _, by simp [Sat]⟩
  | tryCatch body handler ihb ihh =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | tryCatch hb hh =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihb hΓ hR hC hΓ' hR' hb
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L body hΓ hR h₁
      have hunk : Ty.unknown.Below o₁.next := fun a ha => by simp [Ty.ftv] at ha
      have hΓ₁ := Ctx.Below.mono_cons hunk (hσ₁.ctx_below (hΓ.mono hn₁))
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihh (ψ := φ₁) hΓ₁ hR₁ hC
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
  | tryFinally body fin ihb ihf =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | tryFinally hb hf =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihb hΓ hR hC hΓ' hR' hb
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L body hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, _, hsat₂⟩ := ihf (ψ := φ₁) hΓ₁ hR₁ hC
        (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hf
      exact ⟨⟨Subst.compose o₂.σ o₁.σ, o₁.τ.subst o₂.σ, o₁.preds.map (·.subst o₂.σ) ++ o₂.preds,
        o₂.next⟩, by simp only [infer, h₁, h₂], φ₂, hag₁.trans hσ₁ hn₁ hag₂,
        (hag₂.ty hτb₁).trans (hτ₁.trans hτ₀), Sat.app (Sat.agree hag₂ hp₁ hsat₁) hsat₂⟩
  | obj ls es ks ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @obj _ _ _ _ ss' _ _ τs' hes hks hτs hss hL hargs hfs =>
      obtain ⟨o, h, φ, hag, hτs₂, hsat⟩ :=
        inferArgs_complete es _ ih hΓ hR hC hΓ' hR' (by omega) hargs
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
      refine ⟨_, by simp only [infer, hc, and_self, ↓reduceIte, h, hf, hσ']; rfl, φ,
        hag.absorb habs, (habs _).trans (hT.trans hτ₀), Sat.absorb habs hsat⟩
  | cls ls es ks ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @cls _ _ _ τs' _ _ _ ss' hes hks hτs hss hnd hL hms hslots =>
      obtain ⟨o, h, φ, hag, hτs₂, hsat⟩ := inferMembers_complete es ks τs' ih (Δ := []) (Δ' := [])
        hΓ (by simp) hR hC hΓ' .nil hR' (by omega) (by omega)
        (fun i e k τ he hk hτ => by rw [← memberCtx_eq]; exact hms i e k τ he hk hτ)
      obtain ⟨hn, hσ, hτsb, hp⟩ := inferMembers_inv es ks (fun a _ => infer_inv L a) hΓ
        (by simp) hR h
      have hc : ls.all (· ∈ L) = true ∧ ls.Nodup ∧ es.length = ls.length ∧
          ks.length = ls.length :=
        ⟨List.all_eq_true.mpr (fun l hl => by simpa using hL l hl), hnd, hes, hks⟩
      have hlen : o.τs.length = es.length := by
        have := hτs₂.length; simp only [List.length_map] at this; omega
      obtain ⟨θs, ss, m', φ', hm, hm', hφ', hss₂, hθs⟩ := memberSlots_complete
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
        hag'.absorb habs, (habs _).trans (hT.trans hτ₀), Sat.absorb habs (fun p hp' => ?_)⟩
      rw [hpφ p hp']; exact hsat p hp'
  | ctor k body ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' _ ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @ctor _ _ _ ρ' _ _ τs' hlen hb =>
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
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih (R := some (.var (n + τs'.length)))
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
  | new_ f args ihf iha =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @new_ _ _ _ _ τs' _ ss _ hf hlen hargs hρ hss =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihf hΓ hR hC hΓ' hR' hf
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L f hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (ψ := φ₁)
        hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
      obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) hΓ₁ hR₁ h₂
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
  | get e l ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | get he hpr =>
      rename_i κ
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
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
  | set e l v ihe ihv =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | set he hpr hv =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihv (ψ := φ₁) (hσ₁.ctx_below (hΓ.mono hn₁))
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
  | spread e₁ e₂ ih₁ ih₂ =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | spread hps hks hτs hss hrs he₁ he₂ hm =>
      rename_i ss ps ks τs rs
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ih₁ hΓ hR hC hΓ' hR' he₁
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e₁ hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ih₂ (ψ := φ₁) hΓ₁ hR₁ hC
        (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) he₂
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L e₂ hΓ₁ hR₁ h₂
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
  | arr es ih =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | arr hes =>
      rename_i τe
      obtain ⟨o, h, φ, hag, hτs, hsat⟩ := inferArgs_complete es (List.replicate es.length τe) ih
        hΓ hR hC hΓ' hR' (by simp) (fun p hp => by
          obtain ⟨a, b⟩ := p
          obtain ⟨ha, hb⟩ : a ∈ es ∧ b = τe := by
            refine ⟨(List.of_mem_zip hp).1, ?_⟩
            have := (List.of_mem_zip hp).2
            exact List.eq_of_mem_replicate this
          subst hb
          exact hes a ha)
      obtain ⟨hn, hσ, hτsb, hp⟩ := inferArgs_inv es (fun a _ => infer_inv L a) hΓ hR h
      have hlen : o.τs.length = es.length := by simpa using hτs.length
      have hu : TyEq ((Ty.tuple o.τs).subst ((o.next, τe) :: φ))
          ((Ty.tuple (List.replicate o.τs.length (.var o.next))).subst ((o.next, τe) :: φ)) := by
        simp only [Ty.subst_app, List.map_replicate]
        rw [List.map_congr_left (fun τ hτ => Ty.subst_cons_fresh (hτsb τ hτ)), hlen]
        refine TyEq.app_eqs (hτs.trans ?_)
        simp only [Ty.subst, Subst.find, ↓reduceIte, Option.getD_some]
        exact TyEqs.refl _
      obtain ⟨σ', hσ', habs⟩ := unify_mgu hu
      refine ⟨_, by simp only [infer, h, hσ']; rfl, (o.next, τe) :: φ,
        Agree.absorb (hag.fresh hσ hn) habs, ?_, Sat.absorb habs (Sat.fresh hp hsat)⟩
      refine (habs _).trans ?_
      simpa [Ty.subst, Subst.find] using hτ₀
  | index e i ihe ihi =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | index he hi hpr =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihi (ψ := φ₁) hΓ₁ hR₁ hC
        (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hi
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L i hΓ₁ hR₁ h₂
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
  | setIndex e i v ihe ihi ihv =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | setIndex he hi hpr hw hv =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      have hc₁ := hΓ'.trans (hag₁.ctx hΓ).symm
      have hr₁ := hR'.trans (hag₁.ret hR).symm
      obtain ⟨o₂, h₂, φ₂, hag₂, hτ₂, hsat₂⟩ := ihi (ψ := φ₁) hΓ₁ hR₁ hC hc₁ hr₁ hi
      obtain ⟨hn₂, hσ₂, hτb₂, hp₂⟩ := infer_inv L i hΓ₁ hR₁ h₂
      have hΓ₂ := hσ₂.ctx_below (hΓ₁.mono hn₂)
      have hR₂ := hσ₂.ret_below (hR₁.mono hn₂)
      obtain ⟨o₃, h₃, φ₃, hag₃, hτ₃, hsat₃⟩ := ihv (ψ := φ₂) hΓ₂ hR₂ hC
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
  | mcall e l args ihe iha =>
    intro Γ R n ψ C τ' Γ' R' hΓ hR hC hΓ' hR' ht
    obtain ⟨τ₀, hτ₀, ht⟩ := ht.top
    cases ht with
    | @mcall _ _ _ _ τe _ κ τs' _ _ he hpr hlen hargs =>
      obtain ⟨o₁, h₁, φ₁, hag₁, hτ₁, hsat₁⟩ := ihe hΓ hR hC hΓ' hR' he
      obtain ⟨hn₁, hσ₁, hτb₁, hp₁⟩ := infer_inv L e hΓ hR h₁
      have hΓ₁ := hσ₁.ctx_below (hΓ.mono hn₁)
      have hR₁ := hσ₁.ret_below (hR.mono hn₁)
      obtain ⟨o₂, h₂, φ₂, hag₂, hτs₂, hsat₂⟩ := inferArgs_complete args _ iha (ψ := φ₁)
        hΓ₁ hR₁ hC (hΓ'.trans (hag₁.ctx hΓ).symm) (hR'.trans (hag₁.ret hR).symm) hlen hargs
      obtain ⟨hn₂, hσ₂, hτsb₂, hp₂⟩ := inferArgs_inv args (fun a _ => infer_inv L a) hΓ₁ hR₁ h₂
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

end Inty
