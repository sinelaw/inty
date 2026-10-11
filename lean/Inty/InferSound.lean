import Inty.Infer
import Inty.Soundness
import Inty.Weaken

/-!
# Soundness of inference

Whatever `infer` returns is a valid typing: `inferProgram e = some τ` implies
`HasType L [] [] none e τ`. With `never_stuck` (`Inty.Soundness`), a program inference
accepts never gets stuck.
-/

namespace Inty

/-- Under `φ`, every constraint in `P` is an instance or assumed in `C`. -/
def Sat (C : List Pred) (P : List Pred) (φ : Subst) : Prop := ∀ c ∈ P, Entails C (c.subst φ)

@[simp] theorem Sat.nil (C : List Pred) (φ : Subst) : Sat C [] φ := by simp [Sat]

@[simp] theorem Sat.append {C P Q : List Pred} {φ : Subst} :
    Sat C (P ++ Q) φ ↔ Sat C P φ ∧ Sat C Q φ := by
  simp only [Sat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

@[simp] theorem Sat.map {C P : List Pred} {σ φ : Subst} :
    Sat C (P.map (·.subst σ)) φ ↔ Sat C P (Subst.compose φ σ) := by
  simp [Sat]

@[simp] theorem Sat.singleton {C : List Pred} {p : Pred} {φ : Subst} :
    Sat C [p] φ ↔ Entails C (p.subst φ) := by
  simp [Sat]

theorem Entails.append_right {C : List Pred} (D : List Pred) (h : Entails C p) :
    Entails (C ++ D) p :=
  h.weaken (fun _ h => List.mem_append_left _ h)

theorem Lit.ty_sound (l : Lit) : LitTy l l.ty := by cases l <;> constructor

@[simp] theorem Lit.ty_subst (l : Lit) (σ : Subst) : l.ty.subst σ = l.ty := by
  cases l <;> rfl

theorem Expr.isValue_sound {e : Expr} (h : e.isValue = true) : e.IsValue := by
  cases e <;> first | constructor | simp [Expr.isValue] at h

theorem PPred.isSimple_spec {k : Nat} {p : PPred} (h : p.isSimple k = true) :
    (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ i < k, ∃ rest, p.args = .bound i :: rest) ∨
      ∃ q κ τ t r, p = ⟨.merge, [q, κ, τ, t, r]⟩ ∧
        ∃ i < k, ∃ x ∈ [q, κ, τ, t], x.TreeBound k i := by
  unfold PPred.isSimple at h
  split at h
  · obtain ⟨i, hi, hik⟩ := List.any_eq_true.mp h
    obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hik
    exact .inr ⟨_, _, _, _, _, rfl, i, List.mem_range.mp hi, x, hx, PTy.treeBound_spec.mp hb⟩
  · cases h
  · rename_i c i rest _ hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact .inl ⟨hc, by simpa using h.2, _, h.1, rest, rfl⟩
  · cases h

/-- A scheme whose constraints pass the check is simple. -/
theorem Scheme.simple_of_check {s : Scheme} (h : s.preds.all (PPred.isSimple s.arity) = true) :
    s.Simple := fun p hp => PPred.isSimple_spec (List.all_eq_true.mp h p hp)

/-! ## Improvement -/

theorem Pred.decide₀_record_sound {l : String} {ls : List String} {slots : List Ty} {κ σ s : Ty}
    (hs : Ty.field l ls slots = some s) {ψ : Subst}
    (hab : TyEq (s.subst ψ) ((Ty.slot .pre κ σ).subst ψ)) :
    InstEq (Pred.subst ψ ⟨.hasProp l, [.record ls slots, κ, σ]⟩) := by
  have hs' : Ty.field l ls (slots.map (·.subst ψ)) = some (s.subst ψ) := by
    rw [Ty.field_subst, hs]; rfl
  obtain ⟨fs', hf', hl, hz⟩ := Ty.field_replace hs' hab
  refine InstEq.of_predEq (q := ⟨.hasProp l, [.record ls fs', κ.subst ψ, σ.subst ψ]⟩) ?_
    (Inst.hasProp (by simpa using hf')).instEq
  simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
  exact PredEq.of_pairs (by simp)
    (zip_tyEq_cons (TyEq.app (by simpa using hl) hz)
      (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons (TyEq.refl _) zip_tyEq_nil)))

theorem TyEq.of_whnf {τ t : Ty} (h : τ.whnf = t) : TyEq τ t := h ▸ (TyEq.whnf τ).symm

/-- What `Pred.decideCopy`'s equation says: the result is what is copied
of the slot, up to equal types. -/
theorem Pred.decideCopy_sound {s r a b : Ty} (h : Pred.decideCopy s r = .eq a b) {ψ : Subst}
    (hab : TyEq (a.subst ψ) (b.subst ψ)) :
    ∃ sq rq, TyEq (s.subst ψ) sq ∧ SlotCopy sq rq ∧ TyEq (r.subst ψ) rq := by
  unfold Pred.decideCopy at h
  split at h
  · rename_i p k τ hw
    have hs := TyEq.of_whnf hw
    split at h <;> (try cases h)
    · rename_i hp hk
      have hsq : TyEq s (.slot .pre .data τ) :=
        hs.trans (TyEq.slot_mk (TyEq.of_whnf hp) (TyEq.of_whnf hk) (TyEq.refl _))
      exact ⟨_, _, hsq.subst ψ, by simp only [Ty.subst_app, List.map_cons, List.map_nil]; exact .data,
        hab.trans (hsq.subst ψ)⟩
    · rename_i hp hk
      have hsq : TyEq s (.slot .pre .getter τ) :=
        hs.trans (TyEq.slot_mk (TyEq.of_whnf hp) (TyEq.of_whnf hk) (TyEq.refl _))
      exact ⟨_, _, hsq.subst ψ, by simp only [Ty.subst_app, List.map_cons, List.map_nil]; exact .getter,
        by simpa [Ty.subst_app] using hab⟩
    · rename_i hp hk
      have hsq : TyEq s (.slot .pre .proto τ) :=
        hs.trans (TyEq.slot_mk (TyEq.of_whnf hp) (TyEq.of_whnf hk) (TyEq.refl _))
      exact ⟨_, _, hsq.subst ψ, by simp only [Ty.subst_app, List.map_cons, List.map_nil]; exact .proto,
        by simpa [Ty.subst_app] using hab⟩
    · rename_i hp
      have hsq : TyEq s (.slot .abs k τ) :=
        hs.trans (TyEq.slot_mk (TyEq.of_whnf hp) (TyEq.refl _) (TyEq.refl _))
      exact ⟨_, _, hsq.subst ψ, by simp only [Ty.subst_app, List.map_cons, List.map_nil]; exact .abs,
        hab.trans (hsq.subst ψ)⟩
  · cases h
  · cases h

/-- What `Pred.decideInject`'s equation says. -/
theorem Pred.decideInject_sound {τ T a b : Ty} (h : Pred.decideInject τ T = .eq a b) {ψ : Subst}
    (hab : TyEq (a.subst ψ) (b.subst ψ)) : InstEq (Pred.subst ψ ⟨.inject T, [τ]⟩) := by
  simp only [Pred.subst, List.map_cons, List.map_nil]
  unfold Pred.decideInject at h
  split at h
  rotate_left
  · cases h
  rename_i hT
  have hTψ : T.subst ψ = T := Ty.subst_id (fun x hx => by rw [hT] at hx; cases hx)
  split at h
  · rename_i z σ hw
    have hTm : TyEq T (.maybe z σ) := TyEq.of_whnf hw
    have hσ : σ.ftv = [] := by
      have : ∀ x ∈ σ.ftv, x ∈ T.ftv := fun x hx => Ty.whnf_ftv (by rw [hw]; simp [hx])
      rw [hT] at this
      exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by simpa using this x hx
    have hσψ : σ.subst ψ = σ := Ty.subst_id (fun x hx => by rw [hσ] at hx; cases hx)
    split at h
    · rename_i c args
      split at h
      · cases h; rw [hTψ] at hab; exact Pred.inject_self hT hab
      · split at h
        · rename_i _ hn
          cases h
          obtain ⟨rfl, rfl⟩ := hn
          have : (Ty.app z.con []).subst ψ = z.ty := by simp [Nothing.ty]
          rw [this]
          exact (Inst.injectNothing hTm hT).instEq
        · rename_i hc hn
          cases h
          rw [hσψ] at hab
          -- `b` is a constructor application of the same head.
          obtain ⟨ys, hys, hye⟩ := TyEq.whnf_app (xs := args.map (·.subst ψ)) hab (by rw [Ty.subst_app]; rfl)
          have hl : ys.length = args.length := by
            have := (TyEq.app_iff.mp hye).2.1; simpa using this.symm
          have hσw : TyEq b (.app c ys) := TyEq.of_whnf hys
          have hyf : (Ty.app c ys).ftv = [] := by
            have : ∀ x ∈ (Ty.app c ys).ftv, x ∈ b.ftv := fun x hx => Ty.whnf_ftv (by rw [hys]; exact hx)
            rw [hσ] at this
            exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by simpa using this x hx
          have hn' : ¬ (c = z.con ∧ ys = []) := fun ⟨h₁, h₂⟩ =>
            hn ⟨h₁, List.eq_nil_of_length_eq_zero (by rw [← hl, h₂]; rfl)⟩
          refine InstEq.of_predEq (q := ⟨.inject T, [.app c ys]⟩)
            (PredEq.of_pairs (by simp) (zip_tyEq_cons (hab.trans hσw) zip_tyEq_nil))
            (Inst.injectSome (hTm.trans (TyEq.app (by simp) ?_)) hT hyf hc hn').instEq
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq]
          exact hσw
    · cases h; rw [hTψ] at hab; exact Pred.inject_self hT hab
  · cases h; rw [hTψ] at hab; exact Pred.inject_self hT hab

/-- What `Pred.decideStrip`'s equation says. -/
theorem Pred.decideStrip_sound {t σ a b : Ty} (h : Pred.decideStrip t σ = .eq a b) {ψ : Subst}
    (hab : TyEq (a.subst ψ) (b.subst ψ)) : InstEq (Pred.subst ψ ⟨.strip, [t, σ]⟩) := by
  simp only [Pred.subst, List.map_cons, List.map_nil]
  unfold Pred.decideStrip at h
  split at h
  · cases h
    simp only [Ty.subst_app, List.map_cons, List.map_nil]
    exact InstEq.of_predEq
      (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons hab zip_tyEq_nil)))
      Inst.stripSome.instEq
  · rename_i c args _
    split at h
    · cases h
    · cases h
    · cases h
    · rename_i hm hn hu
      cases h
      simp only [Ty.subst_app] at hab ⊢
      exact InstEq.of_predEq (q := ⟨.strip, [.app c (args.map (·.subst ψ)),
          .app c (args.map (·.subst ψ))]⟩)
        (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons hab zip_tyEq_nil)))
        (Inst.stripSelf (fun z h => hm z h) hn hu).instEq
  · cases h

theorem Pred.merge_instEq {q q' : Pred} (hq : Inst q') (e : PredEq q q') : InstEq q :=
  InstEq.of_predEq e hq.instEq

/-- A decision on a known first argument that is an equation is an instance,
up to equal types, wherever the equation holds. -/
theorem Pred.decide₀_sound {c : Cls} {t : Ty} {rest : List Ty} {a b : Ty}
    (h : Pred.decide₀ c t rest = .eq a b) {ψ : Subst} (hab : TyEq (a.subst ψ) (b.subst ψ)) :
    InstEq (Pred.subst ψ ⟨c, t :: rest⟩) := by
  unfold Pred.decide₀ at h
  split at h
  all_goals first | (cases h; done) | skip
  · -- A record's field.
    split at h
    · rename_i hs
      cases h
      exact Pred.decide₀_record_sound hs hab
    · cases h
  · -- An array's `length`.
    split at h
    · rename_i hl
      cases h; subst hl
      obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp hab
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app] at hz ⊢
      exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons (hz (_, _) (by simp)) (zip_tyEq_cons (hz (_, _) (by simp)) zip_tyEq_nil))))
        Inst.lengthArray.instEq
    · cases h
  · -- A string's `length`.
    split at h
    · rename_i hl
      cases h; subst hl
      obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp hab
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app] at hz ⊢
      exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons (hz (_, _) (by simp)) (zip_tyEq_cons (hz (_, _) (by simp)) zip_tyEq_nil))))
        Inst.lengthString.instEq
    · cases h
  · cases h
    rename_i τ i e
    obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp hab
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app, Ty.substs_eq] at hz ⊢
    exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
      (zip_tyEq_cons (hz (i.subst ψ, .number) (by simp))
        (zip_tyEq_cons (hz (e.subst ψ, τ.subst ψ) (by simp)) zip_tyEq_nil))))
      Inst.indexArray.instEq
  · cases h
    rename_i i e
    obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp hab
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app, Ty.substs_eq] at hz ⊢
    exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
      (zip_tyEq_cons (hz (i.subst ψ, .number) (by simp))
        (zip_tyEq_cons (hz (e.subst ψ, .string) (by simp)) zip_tyEq_nil))))
      Inst.indexString.instEq
  · cases h
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact Inst.writeArray.instEq
  · split at h
    · cases h
    · rename_i hc
      cases h
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
      exact (Inst.notNew hc).instEq
  · -- A `Merge` whose operand's field is present.
    rename_i k τ s r
    unfold Pred.decidePre at h
    split at h
    · rename_i hk
      cases h
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
      exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons ((TyEq.of_whnf hk).subst ψ) (zip_tyEq_cons (TyEq.refl _)
          (zip_tyEq_cons (TyEq.refl _)
          (zip_tyEq_cons (by simpa [Ty.subst_app] using hab) zip_tyEq_nil))))))
        Inst.mergeData.instEq
    · rename_i hk
      cases h
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
      exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons ((TyEq.of_whnf hk).subst ψ) (zip_tyEq_cons (TyEq.refl _)
          (zip_tyEq_cons (TyEq.refl _)
          (zip_tyEq_cons (by simpa [Ty.subst_app] using hab) zip_tyEq_nil))))))
        Inst.mergeGetter.instEq
    · rename_i hk
      obtain ⟨sq, rq, hs, hc, hr⟩ := Pred.decideCopy_sound h hab
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
      exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons ((TyEq.of_whnf hk).subst ψ) (zip_tyEq_cons (TyEq.refl _)
          (zip_tyEq_cons hs (zip_tyEq_cons hr zip_tyEq_nil)))))) (Inst.mergeProto hc).instEq
    · cases h
    · cases h
  · -- A `Merge` whose operand's field is absent.
    obtain ⟨sq, rq, hs, hc, hr⟩ := Pred.decideCopy_sound h hab
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact InstEq.of_predEq (PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _)
      (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons (TyEq.refl _)
        (zip_tyEq_cons hs (zip_tyEq_cons hr zip_tyEq_nil))))))
      (Inst.mergeAbs hc).instEq
  · exact Pred.decideInject_sound h hab
  · exact Pred.decideStrip_sound h hab

theorem Pred.decide_sound {c : Cls} {t : Ty} {rest : List Ty} {a b : Ty}
    (h : Pred.decide c t rest = .eq a b) {ψ : Subst} (hab : TyEq (a.subst ψ) (b.subst ψ)) :
    InstEq (Pred.subst ψ ⟨c, t :: rest⟩) := by
  refine InstEq.of_predEq ?_ (Pred.decide₀_sound h hab)
  simp only [Pred.subst, List.map_cons]
  exact PredEq.of_pairs (by simp)
    (zip_tyEq_cons (((TyEq.whnf t).subst ψ).symm) (zip_self_tyEq _))

theorem Pred.improveArgs_sound {c : Cls} {args : List Ty} {a b : Ty}
    (h : Pred.improveArgs c args = .eq a b) {ψ : Subst} (hab : TyEq (a.subst ψ) (b.subst ψ)) :
    InstEq (Pred.subst ψ ⟨c, args⟩) := by
  unfold Pred.improveArgs at h
  split at h
  · split at h
    · split at h <;> cases h
    · exact Pred.decide_sound h hab
  · cases h

/-- A constraint whose decision is an equation is an instance, up to equal
types, wherever the equation holds. -/
theorem Pred.improve_sound {top : Bool} {p : Pred} {a b : Ty} (h : p.improve top = .eq a b)
    {ψ : Subst} (hab : TyEq (a.subst ψ) (b.subst ψ)) : InstEq (p.subst ψ) := by
  obtain ⟨cls, args⟩ := p
  cases cls <;> simp only [Pred.improve] at h
  case merge =>
    split at h
    · exact Pred.improveArgs_sound h hab
    · cases h
  case plus => cases h
  all_goals exact Pred.improveArgs_sound h hab

theorem improveOne_some {top : Bool} : ∀ {ps : List Pred} {a b : Ty} {rest : List Pred},
    improveOne top ps = some (some ((a, b), rest)) →
      ∃ p, p.improve top = .eq a b ∧ ∀ q ∈ ps, q = p ∨ q ∈ rest
  | [], _, _, _, h => by simp [improveOne] at h
  | p :: ps, a, b, rest, h => by
    simp only [improveOne] at h
    split at h
    · cases h
    · rename_i τ₁ τ₂ hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨p, hp, fun q hq => by simpa using hq⟩
    · split at h
      · cases h
      · cases h
      · rename_i e r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p', hp', hq⟩ := improveOne_some hr
        refine ⟨p', hp', fun q hq' => ?_⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact .inr List.mem_cons_self
        · exact (hq q hq').imp id (List.mem_cons_of_mem _)

/-- What improvement leaves, satisfied, satisfies what it was given, under
the improving substitution. -/
theorem improveAll_sound {top : Bool} :
    ∀ (k : Nat) {ps : List Pred} {σ : Subst} {ps' : List Pred},
    improveAll top k ps = some (σ, ps') → ∀ {C : List Pred} {φ : Subst}, Sat C ps' φ →
      Sat C ps (Subst.compose φ σ)
  | 0, ps, σ, ps', h, C, φ, hs => by
    simp only [improveAll, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [Sat] using hs
  | k + 1, ps, σ, ps', h, C, φ, hs => by
    simp only [improveAll] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [Sat] using hs
    · rename_i a b rest hone
      split at h
      · cases h
      rename_i σu hu
      split at h
      · cases h
      rename_i σ' ps'' hrec
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨p, hp, hq⟩ := improveOne_some hone
      have hrest := Sat.map.mp (improveAll_sound k hrec hs)
      intro q hq'
      rcases hq q hq' with rfl | hq'
      · refine .inl (Pred.improve_sound hp ?_)
        simp only [Ty.subst_compose]
        exact ((unify_sound hu).subst σ').subst φ
      · have := hrest q hq'
        simpa [Pred.subst_compose] using this

/-! ## Generalisation -/

/-- Closing under the dependencies keeps what was fixed. -/
theorem fixLoop_sup {a : Nat} : ∀ (k : Nat) (preds : List Pred) {fixed : List Nat},
    a ∈ fixed → a ∈ fixLoop k preds fixed
  | 0, _, _, h => h
  | k + 1, preds, fixed, h => by
    simp only [fixLoop]
    split
    · exact h
    · exact fixLoop_sup k _ (List.mem_append_left _ h)

/-- No quantified variable is fixed by the environment. -/
theorem genVars_not_env {Γ₁ : Ctx} {R₁ : Option Ty} {τ₁ : Ty} {preds : List Pred} {a : Nat}
    (ha : a ∈ ctxTv Γ₁ ++ Ret.tv R₁) : a ∉ genVars Γ₁ R₁ τ₁ preds := by
  intro hα
  simp only [genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at hα
  exact hα.2 (fixLoop_sup _ _ ha)

/-- A constraint on a type whose head is a variable is one on the variable. -/
theorem Pred.normHead_predEq (p : Pred) : PredEq p p.normHead := by
  obtain ⟨c, args⟩ := p
  unfold Pred.normHead
  match args with
  | [] => exact PredEq.refl _
  | t :: rest =>
    simp only
    split
    · refine ⟨rfl, rfl, fun x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (TyEq.whnf t).symm
      · obtain ⟨y, z⟩ := x; obtain ⟨rfl, -⟩ := mem_zip_self hx; exact TyEq.refl _
    · exact PredEq.refl _

/-- Return types equal through substitutions that agree on their tree
variables. -/
theorem Ret.subst_congr_tv {σ σ' : Subst} {R : Option Ty}
    (h : ∀ a ∈ Ret.tv R, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    RetEq (Ret.subst σ R) (Ret.subst σ' R) := by
  cases R with
  | none => trivial
  | some τ =>
    exact Ty.subst_tyEq_congr_tv (fun a ha => h a (by simpa [Ret.tv] using Ty.mem_tv.mpr ha))

theorem Scheme.inst_nil_closed {s : Scheme} (hs : s.ftv = []) : (s.inst []).ftv = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
    rcases PTy.ftv_inst ha with ha | ⟨τ, hτ, _⟩
    · have h' : a ∈ s.ftv := List.mem_append_left _ ha
      rw [hs] at h'; cases h'
    · cases hτ

theorem RetOk.ret_eq {rm : Mode} {R : Option Ty} (h : RetOk rm R) (σ σ' : Subst) (hm : rm = .check) :
    Ret.subst σ R = Ret.subst σ' R := by
  subst hm; rw [h.subst_eq, h.subst_eq]

theorem Ctx.subst_append_monos {τs : List Ty} (h : ∀ t ∈ τs, t.ftv = []) (σ : Subst) (Γ : Ctx) :
    Ctx.subst σ (τs.map Scheme.mono ++ Γ) = τs.map Scheme.mono ++ Ctx.subst σ Γ := by
  simp only [Ctx.subst, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => by
    simp only [Function.comp_apply, Scheme.mono_subst, Ty.closed_subst (h t ht)]

/-- What `infer_sound` says of one expression. -/
def InferSound (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {o : Out},
    infer L Γ R rm ex e n = some o → RetOk rm R → Ex.Closed ex → ∀ φ C, Sat C o.preds φ →
      HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) rm (exMode ex e) e
        (o.τ.subst φ)

theorem funcTarget_fst {ex : Option Ty} {k : Nat} {T T' θ ρ : Ty} {τs : List Ty}
    (h : funcTarget ex k = some (T', θ, τs, ρ)) (hT : ex = some T) :
    T' = T ∧ T.whnf = .fn θ τs ρ ∧ τs.length = k := by
  subst hT
  simp only [funcTarget] at h
  split at h
  · rename_i θ₀ τs₀ ρ₀ hw
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hw, by assumption⟩
    · cases h
  · cases h

theorem funcTarget_some {ex : Option Ty} {k : Nat} {T' θ ρ : Ty} {τs : List Ty}
    (h : funcTarget ex k = some (T', θ, τs, ρ)) : ex = some T' := by
  cases ex with
  | none => cases h
  | some T => rw [(funcTarget_fst h rfl).1]

theorem arrTarget_fst {ex : Option Ty} {T T' σ : Ty} (h : arrTarget ex = some (T', σ))
    (hT : ex = some T) : T' = T ∧ T.whnf = .array σ := by
  subst hT
  simp only [arrTarget] at h
  split at h
  · rename_i σ₀ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hw⟩
  · cases h

theorem arrTarget_some {ex : Option Ty} {T' σ : Ty} (h : arrTarget ex = some (T', σ)) :
    ex = some T' := by
  cases ex with
  | none => cases h
  | some T => rw [(arrTarget_fst h rfl).1]

theorem checkEx_ty {T : Ty} {e : Expr} {o : Out} (h : e.pushes T → o.τ = T) :
    (checkEx (some T) e o).τ = T := by
  simp only [checkEx]; split <;> simp_all

/-- What `checkEx` leaves unchanged but its type. -/
theorem checkEx_σ (ex : Option Ty) (e : Expr) (o : Out) : (checkEx ex e o).σ = o.σ := by
  cases ex <;> simp only [checkEx] <;> split <;> rfl

theorem checkEx_next (ex : Option Ty) (e : Expr) (o : Out) : (checkEx ex e o).next = o.next := by
  cases ex <;> simp only [checkEx] <;> split <;> rfl

/-- An expression that takes in the expected type has it. -/
theorem infer_pushes {T : Ty} (hT : T.ftv = []) : ∀ {e : Expr} {Γ : Ctx} {R : Option Ty}
    {rm : Mode} {n : Nat} {o : Out}, infer L Γ R rm (some T) e n = some o → e.pushes T → o.τ = T := by
  intro e
  induction e using Expr.ind with
  | func k body _ =>
    intro Γ R rm n o h hp
    simp only [infer] at h
    split at h
    · rename_i T' θ τs ρ hft
      split at h
      · cases h
      simp only [Option.some.injEq] at h; subst h
      exact (funcTarget_fst hft rfl).1
    · rename_i hft
      simp [Expr.pushes, hft] at hp
  | arr es _ =>
    intro Γ R rm n o h hp
    simp only [infer] at h
    split at h
    · rename_i T' σ hat
      split at h
      · cases h
      simp only [Option.some.injEq] at h; subst h
      exact (arrTarget_fst hat rfl).1
    · rename_i hat
      simp [Expr.pushes, hat] at hp
  | let_ m a e₁ e₂ _ ih₂ =>
    intro Γ R rm n o h _
    cases a with
    | some a =>
      simp only [infer] at h
      split at h
      rotate_left
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨o₂', h₂', rfl⟩ := Option.map_eq_some_iff.mp h₂
      exact checkEx_ty (ih₂ h₂')
    | none =>
      simp only [infer] at h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      rotate_left
      · cases h
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨o₂', h₂', rfl⟩ := Option.map_eq_some_iff.mp h₂
      exact checkEx_ty (ih₂ h₂')
  | cond c t e _ _ ihe =>
    intro Γ R rm n o h _
    simp only [infer] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    rename_i o₃ h₃
    split at h
    · cases h
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨o₃', h₃', rfl⟩ := Option.map_eq_some_iff.mp h₃
    simp only [checkEx_ty (ihe h₃'), Ty.closed_subst hT]
  | ret e _ =>
    intro Γ R rm n o h _
    match R, rm with
    | none, _ => simp [infer] at h
    | some τr, .synth =>
      simp only [infer] at h
      split at h
      · cases h
      split at h
      · cases h
      simp only [Option.some.injEq] at h; subst h; rfl
    | some τr, .check =>
      simp only [infer] at h
      split at h
      · cases h
      simp only [Option.some.injEq] at h; subst h; rfl
  | seq e₁ e₂ _ ih₂ =>
    intro Γ R rm n o h _
    simp only [infer] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨o₂', h₂', rfl⟩ := Option.map_eq_some_iff.mp h₂
    exact checkEx_ty (ih₂ h₂')
  | break_ =>
    intro Γ R rm n o h _
    simp only [infer, Option.some.injEq] at h; subst h; rfl
  | continue_ =>
    intro Γ R rm n o h _
    simp only [infer, Option.some.injEq] at h; subst h; rfl
  | tryCatch body handler _ ihh =>
    intro Γ R rm n o h _
    simp only [infer] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨o₂', h₂', rfl⟩ := Option.map_eq_some_iff.mp h₂
    simp only [checkEx_ty (ihh h₂'), Ty.closed_subst hT]
  | tryFinally body fin ihb _ =>
    intro Γ R rm n o h _
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨o₁', h₁', rfl⟩ := Option.map_eq_some_iff.mp h₁
    simp only [checkEx_ty (ihb h₁'), Ty.closed_subst hT]
  | _ => intro _ _ _ _ _ _ hp; simp [Expr.pushes] at hp

/-- Inferring `e` against `ex`, as its caller sees it (`checkEx`): the
expected type, if any. -/
theorem InferSound.check_ty {e : Expr} {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty}
    {n : Nat} {o : Out} (h : (infer L Γ R rm ex e n).map (checkEx ex e) = some o)
    (hex : Ex.Closed ex) : ∀ T ∈ ex, o.τ = T := by
  intro T hT
  cases hT
  obtain ⟨o', h', rfl⟩ := Option.map_eq_some_iff.mp h
  exact checkEx_ty (infer_pushes (hex T rfl) h')

/-- Inferring `e` against `ex`, as its caller sees it (`checkEx`), is
sound: in check mode if `ex` is given, at `ex`. -/
theorem InferSound.check {e : Expr} (ih : InferSound L e) {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {ex : Option Ty} {n : Nat} {o : Out} (h : (infer L Γ R rm ex e n).map (checkEx ex e) = some o)
    (hRo : RetOk rm R) (hex : Ex.Closed ex) : ∀ φ C, Sat C o.preds φ →
      HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) rm (Ex.mode ex) e
        (o.τ.subst φ) := by
  intro φ C hsat
  obtain ⟨o', h', rfl⟩ := Option.map_eq_some_iff.mp h
  match ex, hex with
  | none, hex => simpa using ih h' hRo hex φ C hsat
  | some T, hex =>
    have hs := ih h' hRo hex
    by_cases hp : e.pushes T
    · simp only [checkEx, hp, ↓reduceIte] at hsat ⊢
      simpa [exMode, hp] using hs φ C hsat
    · simp only [checkEx, hp, Bool.false_eq_true, ↓reduceIte, Sat.append] at hsat ⊢
      have hi := hsat.2 _ (List.mem_singleton_self _)
      simp only [Pred.subst, List.map_cons, List.map_nil] at hi
      rw [Ty.closed_subst (hex T rfl)]
      exact .inj (by simpa [exMode, hp] using hs φ C hsat.1) (hex T rfl) hi

/-- Inferring arguments, each sound, is sound: one type per argument, each
a valid typing under the inferred substitution and any further one that
resolves the constraints. -/
theorem inferArgs_sound : ∀ (args : List Expr), (∀ a ∈ args, InferSound L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty} {n : Nat} {o : OutArgs},
      inferArgs L Γ R rm ex args n = some o → RetOk rm R → Ex.Closed ex →
      ∀ φ C, Sat C o.preds φ → o.τs.length = args.length ∧
        ∀ p ∈ args.zip (o.τs.map (·.subst φ)),
          HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) rm (Ex.mode ex)
            p.1 p.2
  | [], _, Γ, R, rm, ex, n, o, h, _, _, φ, C, _ => by
    simp only [inferArgs, Option.some.injEq] at h; subst h; simp
  | a :: as, ih, Γ, R, rm, ex, n, o, h, hRo, hex, φ, C, hsat => by
    simp only [inferArgs] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have ha := InferSound.check (ih a (by simp)) h₁ hRo hex _ C hsat.1
    have has := inferArgs_sound as (fun a' ha' => ih a' (by simp [ha'])) h₂ (by ret_ok) hex φ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at ha has ⊢
    refine ⟨by simp [has.1], fun p hp => ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ha
    · exact has.2 p hp

/-- Arguments inferred against an expected type each have it. -/
theorem inferArgs_ty : ∀ (args : List Expr) {Γ : Ctx} {R : Option Ty} {rm : Mode} {T : Ty}
    {n : Nat} {o : OutArgs}, inferArgs L Γ R rm (some T) args n = some o → T.ftv = [] →
      ∀ τ ∈ o.τs, τ = T
  | [], Γ, R, rm, T, n, o, h, _ => by
    simp only [inferArgs, Option.some.injEq] at h; subst h; simp
  | a :: as, Γ, R, rm, T, n, o, h, hT => by
    simp only [inferArgs] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    intro τ hτ
    simp only [List.mem_cons] at hτ
    rcases hτ with rfl | hτ
    · rw [InferSound.check_ty h₁ (Ex.Closed.some hT) T rfl, Ty.closed_subst hT]
    · exact inferArgs_ty as h₂ hT τ hτ

/-- Pairs with equal second components, when the property they have is
invariant under that. -/
theorem zip_conv {P : Expr → Ty → Prop} :
    ∀ {es : List Expr} {ts us : List Ty}, es.length = ts.length → ts.length = us.length →
      (∀ p ∈ es.zip ts, P p.1 p.2) → (∀ x ∈ ts.zip us, TyEq x.1 x.2) →
      (∀ e t u, P e t → TyEq t u → P e u) → ∀ p ∈ es.zip us, P p.1 p.2
  | [], _, _, _, _, _, _, _, p, hp => by cases hp
  | _ :: _, [], _, h, _, _, _, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _, _, _, _ => by simp at h
  | e :: es, t :: ts, u :: us, h₁, h₂, hp, hz, hc, p, hm => by
    simp only [List.zip_cons_cons, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hc _ _ _ (hp (e, t) (by simp)) (hz (t, u) (by simp))
    · exact zip_conv (by simpa using h₁) (by simpa using h₂) (fun q hq => hp q (by simp [hq]))
        (fun q hq => hz q (by simp [hq])) hc p hm

theorem mem_zip_replicate {α β : Type} {a : α} {b : β} :
    ∀ {l : List α}, a ∈ l → (a, b) ∈ l.zip (List.replicate l.length b)
  | x :: l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [List.replicate_succ]
    · simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons]
      exact .inr (mem_zip_replicate h)

/-- What `fieldSlots` finds: under any substitution that makes each `this`
it lists the literal's type `T`, each field's slot is as its kind says. -/
theorem fieldSlots_sound {ks : List FieldKind} {es : List Expr} {τs θs ss : List Ty}
    (h : fieldSlots ks es τs = some (θs, ss)) :
    ss.length = ks.length ∧ es.length = ks.length ∧ τs.length = ks.length ∧
      ∀ (ψ : Subst) (T : Ty), (∀ θ ∈ θs, TyEq (θ.subst ψ) T) →
        ∀ x ∈ ks.zip (es.zip (τs.zip ss)),
          FieldSlot T x.1 x.2.1 (x.2.2.1.subst ψ) (x.2.2.2.subst ψ) := by
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
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], fun ψ T hθ x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app] using FieldSlot.data (T := T) (e := e) (τ := τ.subst ψ)
      · exact h₄ ψ T hθ x hx
  | case3 ks m b es θ ρ τs' τs ih =>
    simp only [fieldSlots] at h
    cases hr : fieldSlots ks es τs with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss'⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], fun ψ T hθ x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app, Ty.subst_fn] using
          FieldSlot.method (τs := τs'.map (·.subst ψ)) (ρ := ρ.subst ψ) (n := m) (b := b)
            (hθ θ List.mem_cons_self)
      · exact h₄ ψ T (fun θ' h' => hθ θ' (List.mem_cons_of_mem _ h')) x hx
  | case4 ks b es θ σ τs ih =>
    simp only [fieldSlots] at h
    cases hr : fieldSlots ks es τs with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss'⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], fun ψ T hθ x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app, Ty.subst_fn] using
          FieldSlot.getter (σ := σ.subst ψ) (b := b) (hθ θ List.mem_cons_self)
      · exact h₄ ψ T (fun θ' h' => hθ θ' (List.mem_cons_of_mem _ h')) x hx
  | case5 x y z h1 h2 h3 h4 =>
    exfalso
    rw [fieldSlots.eq_def] at h
    split at h
    · exact h1 rfl rfl rfl
    · exact h2 _ _ _ _ _ rfl rfl rfl
    · exact h3 _ _ _ _ _ _ _ _ rfl rfl rfl
    · exact h4 _ _ _ _ _ _ rfl rfl rfl
    · cases h

theorem notNewPreds_succ {n n' : Nat} (h : n < n') :
    notNewPreds n n' = ⟨.notNew, [.var n]⟩ :: notNewPreds (n + 1) n' := by
  unfold notNewPreds
  rw [show n' - n = (n' - (n + 1)) + 1 by omega, List.range'_succ]
  rfl

/-- What `memberSlots` finds: under any substitution that makes each
`this` it lists the instance's type `T`, each member's slot is as its kind
says. -/
theorem memberSlots_sound {ks : List ClassKind} {es : List Expr} {τs : List Ty} {n : Nat}
    {θs ss : List Ty} {n' : Nat} (h : memberSlots ks es τs n = some (θs, ss, n')) :
    ss.length = ks.length ∧ τs.length = ks.length ∧ es.length = ks.length ∧ n ≤ n' ∧
      ∀ (C : List Pred) (ψ : Subst) (T : Ty), (∀ θ ∈ θs, TyEq (θ.subst ψ) T) →
        Sat C (notNewPreds n n') ψ →
        ∀ x ∈ ks.zip (es.zip (τs.zip ss)), MemberSlot C T x.1 x.2.1 (x.2.2.1.subst ψ)
          (x.2.2.2.subst ψ) := by
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
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], h₄, fun C ψ T hθ hn x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app] using MemberSlot.data (T := T) (e := e) (τ := τ.subst ψ)
      · exact h₅ C ψ T hθ hn x hx
  | case3 ks m b es θ ρ τs' τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs (n + 1) with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], by omega, fun C ψ T hθ hn x hx => ?_⟩
      rw [notNewPreds_succ (by omega)] at hn
      simp only [Sat, List.mem_cons, forall_eq_or_imp] at hn
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app, Ty.subst_fn] using
          MemberSlot.arrow (τs := τs'.map (·.subst ψ)) (ρ := ρ.subst ψ) (n := m) (b := b)
            (θ' := (Ty.var n).subst ψ) (hθ θ List.mem_cons_self) (by simpa [Pred.subst] using hn.1)
      · exact h₅ C ψ T (fun θ' h' => hθ θ' (List.mem_cons_of_mem _ h')) hn.2 x hx
  | case4 ks m b es θ ρ τs' τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs n with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], h₄, fun C ψ T hθ hn x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app, Ty.subst_fn] using
          MemberSlot.method (τs := τs'.map (·.subst ψ)) (ρ := ρ.subst ψ) (n := m) (b := b)
            (hθ θ List.mem_cons_self)
      · exact h₅ C ψ T (fun θ' h' => hθ θ' (List.mem_cons_of_mem _ h')) hn x hx
  | case5 ks b es θ σ τs n ih =>
    simp only [memberSlots] at h
    cases hr : memberSlots ks es τs n with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨θs', ss', n''⟩ := r
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih hr
      refine ⟨by simp [h₁], by simp [h₂], by simp [h₃], h₄, fun C ψ T hθ hn x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Ty.subst_app, Ty.subst_fn] using
          MemberSlot.getter (σ := σ.subst ψ) (b := b) (hθ θ List.mem_cons_self)
      · exact h₅ C ψ T (fun θ' h' => hθ θ' (List.mem_cons_of_mem _ h')) hn x hx
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

/-- What `unifyThis` gives: each `this` is the record type. -/
theorem unifyThis_sound {θs : List Ty} {T : Ty} {σ' : Subst} (h : unifyThis θs T = some σ') :
    ∀ θ ∈ θs, ∀ ψ : Subst, TyEq ((θ.subst σ').subst ψ) ((T.subst σ').subst ψ) := by
  unfold unifyThis at h
  split at h
  · intro θ hθ; cases hθ
  · rename_i θ₀ θs₀
    split at h
    · cases h
    rename_i σ₁ hu₁
    split at h
    · cases h
    rename_i σ₂ hu₂
    simp only [Option.some.injEq] at h; subst h
    have h₁' := unify_sound hu₁
    simp only [Ty.subst_app, List.map_replicate] at h₁'
    obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp h₁'
    intro θ' hθ' ψ
    have hz' := hz (θ'.subst σ₁, θ₀.subst σ₁) (by
      have := mem_zip_replicate (b := θ₀.subst σ₁) (List.mem_map_of_mem (f := (·.subst σ₁)) hθ')
      simpa using this)
    simp only [Ty.subst_compose]
    exact ((hz'.subst σ₂).trans (unify_sound hu₂)).subst ψ

theorem memberCtx_succ (Γ : Ctx) (k : ClassKind) (ks : List ClassKind) (τ : Ty) (τs : List Ty)
    (i : Nat) : memberCtx Γ (k :: ks) (τ :: τs) (i + 1) .data =
      if k = .data then memberCtx (.mono τ :: Γ) ks τs i .data else memberCtx Γ ks τs i .data := by
  cases k <;> simp [memberCtx_data, memberCtx_other]

/-- Inferring a class's members, each sound, is sound: one type per member,
each a valid typing in its context (`memberCtx`, a field's after the types
`Δ` of the fields before the members). -/
theorem inferMembers_sound : ∀ (es : List Expr) (ks : List ClassKind), (∀ e ∈ es, InferSound L e) →
    ∀ {Γ : Ctx} {Δ : List Ty} {R : Option Ty} {n : Nat} {o : OutArgs},
      inferMembers L Γ Δ R es ks n = some o → ∀ φ C, Sat C o.preds φ →
        o.τs.length = es.length ∧ es.length = ks.length ∧
        ∀ i e k τ, es[i]? = some e → ks[i]? = some k → (o.τs.map (·.subst φ))[i]? = some τ →
          HasType L C (memberCtx (if k = .data then
              ((Δ.map (·.subst o.σ)).map (·.subst φ)).map Scheme.mono ++
                Ctx.subst φ (Ctx.subst o.σ Γ)
            else Ctx.subst φ (Ctx.subst o.σ Γ)) ks (o.τs.map (·.subst φ)) i k)
            (Ret.subst φ (Ret.subst o.σ R)) .synth .synth e τ
  | [], [], _, Γ, Δ, R, n, o, h, φ, C, _ => by
    simp only [inferMembers, Option.some.injEq] at h; subst h; simp
  | [], _ :: _, _, Γ, Δ, R, n, o, h, _, _, _ | _ :: _, [], _, Γ, Δ, R, n, o, h, _, _, _ => by
    simp [inferMembers] at h
  | e :: es, k :: ks, ih, Γ, Δ, R, n, o, h, φ, C, hsat => by
    have ih' : ∀ e ∈ es, InferSound L e := fun e' he' => ih e' (List.mem_cons_of_mem _ he')
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
      simp only [Sat.map, Sat.append] at hsat
      have he := ih e List.mem_cons_self h₁ RetOk.synth .none _ C hsat.1
      have hr := inferMembers_sound es ks ih' h₂ φ C hsat.2
      simp only [Ty.subst_compose, Ret.subst_compose, Ctx.subst,
        List.map_append, List.map_map, Function.comp_def, Scheme.mono_subst, List.map_cons] at he hr ⊢
      refine ⟨by simp [hr.1], by simp [hr.2.1], fun i e' k τ h₁ h₂ h₃ => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂ h₃
        subst h₁ h₂ h₃
        simpa [memberCtx_zero] using he
      | succ i =>
        simp only [List.getElem?_cons_succ] at h₁ h₂ h₃
        have := hr.2.2 i e' k τ h₁ h₂ (by simpa using h₃)
        by_cases hk : k = .data
        · subst hk
          simp only [ite_true, memberCtx_succ] at this ⊢
          simpa [Function.comp_def] using this
        · simp only [hk, ite_false] at this ⊢
          cases k <;> simp_all [memberCtx]
    all_goals
      simp only [inferMembers] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append] at hsat
      have he := ih e List.mem_cons_self h₁ RetOk.synth .none _ C hsat.1
      have hr := inferMembers_sound es ks ih' h₂ φ C hsat.2
      simp only [Ty.subst_compose, Ret.subst_compose, Ctx.subst,
        List.map_map, Function.comp_def, List.map_cons] at he hr ⊢
      refine ⟨by simp [hr.1], by simp [hr.2.1], fun i e' k τ h₁ h₂ h₃ => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂ h₃
        subst h₁ h₂ h₃
        simpa [memberCtx] using he
      | succ i =>
        simp only [List.getElem?_cons_succ] at h₁ h₂ h₃
        have := hr.2.2 i e' k τ h₁ h₂ (by simpa using h₃)
        by_cases hk : k = .data
        · subst hk
          simp only [ite_true, memberCtx_succ, reduceCtorEq, ite_false] at this ⊢
          simpa [Function.comp_def] using this
        · simp only [hk, ite_false] at this ⊢
          cases k <;> simp_all [memberCtx]

/-- The spread rule, at the types a substitution gives. -/
theorem HasType.spread_subst {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty}
    {e₁ e₂ : Expr} {ψ : Subst} {ps ks τs ss rs : List Ty}
    (hps : ps.length = L.length) (hks : ks.length = L.length) (hτs : τs.length = L.length)
    (hss : ss.length = L.length) (hrs : rs.length = L.length)
    {rm : Mode} (h₁ : HasType L C Γ R rm .synth e₁ ((Ty.record L ss).subst ψ))
    (h₂ : HasType L C Γ R rm .synth e₂ ((Ty.record L (slots3 ps ks τs)).subst ψ))
    (hm : Sat C (mergePreds ps ks τs ss rs) ψ) :
    HasType L C Γ R rm .synth (.spread e₁ e₂) ((Ty.record L rs).subst ψ) := by
  simp only [Ty.subst_app, slots3_subst] at h₁ h₂ ⊢
  refine .spread (by simpa using hps) (by simpa using hks) (by simpa using hτs) (by simpa using hss)
    (by simpa using hrs) h₁ h₂ (fun p hp => ?_)
  rw [← mergePreds_subst] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hm q hq

/-- Soundness of Algorithm W: the inferred type, under the inferred
substitution and any further substitution that resolves the class
constraints, is a valid typing. -/
theorem infer_sound : ∀ {e : Expr}, InferSound L e := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer, Option.some.injEq] at h; subst h
    simpa using HasType.lit (C := C) (Γ := Ctx.subst φ Γ) (Lit.ty_sound l)
  | var i =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · rename_i s hs
      simp only [Option.some.injEq] at h; subst h
      simp only [Ctx.subst_nil, Scheme.open, Scheme.inst_subst]
      refine .var (by rw [Ctx.getElem?_subst, hs]; rfl) (by simp [varBlock]) (fun c hc => ?_)
      rw [← Scheme.instPreds_subst] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
      exact hsat c₀ hc₀
    · cases h
  | func k body ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    simp only [infer] at h
    split at h
    · rename_i T θ τs ρ hft
      obtain rfl := funcTarget_some hft
      obtain ⟨-, hw, hlen⟩ := funcTarget_fst hft rfl
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
      have hb := InferSound.check ih h₁ (RetOk.check hρ) (Ex.Closed.some hρ) φ C hsat
      rw [InferSound.check_ty h₁ (Ex.Closed.some hρ) ρ rfl, Ty.closed_subst hρ] at hb
      have hp : (Expr.func k body).pushes T = true := by simp [Expr.pushes, hft]
      simp only [exMode, hp, ↓reduceIte, Ty.closed_subst hT]
      refine .funcCheck hw hT hlen ?_
      simpa only [Ctx.subst_append_monos hτs, Ctx.subst_cons, Scheme.mono_subst, Ty.closed_subst hfn,
        Ty.closed_subst hθ, Ret.subst_some, Ty.closed_subst hρ, Ex.mode_some] using hb
    · rename_i hft
      rw [show exMode ex (.func k body) = .synth by
        cases ex with
        | none => rfl
        | some T => simp [exMode, Expr.pushes, hft]]
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have := ih h₁ RetOk.synth .none _ C hsat
      simp only [Ctx.subst, List.map_append, List.map_map, List.map_cons, Function.comp_def,
        Scheme.mono_subst, Ty.subst_fn, Ty.subst_compose, Ret.subst_compose,
        Ret.subst_some] at this ⊢
      replace this := this.conv ((unify_sound hu).subst φ).symm
      exact .func (by simp [varBlock]) (by simpa [Function.comp_def] using this)
  | app f args ihf iha =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have hf := ihf h₁ (by ret_ok) .none _ C hsat.1
    have ha := inferArgs_sound args iha h₂ (by ret_ok) .none _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hf ha ⊢
    replace hf := hf.conv ((unify_sound hu).subst φ)
    simp only [Ty.subst_fn, List.map_map, Function.comp_def] at hf ha
    exact .app hf (by simp [ha.1]) ha.2
  | let_ mb ann e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    cases ann with
    | some a =>
      simp only [infer] at h
      split at h
      rotate_left
      · cases h
      rename_i ha
      obtain ⟨har, hap, haf⟩ := ha
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i o₂ h₂
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append] at hsat
      have hcl : ∀ ψ, a.subst ψ = a := fun ψ => Scheme.subst_of_ftv_nil ψ haf
      have hT := Scheme.inst_nil_closed haf
      have he₁ := InferSound.check ih₁ h₁ hRo (Ex.Closed.some hT) _ C hsat.1
      rw [InferSound.check_ty h₁ (Ex.Closed.some hT) _ rfl, Ty.closed_subst hT] at he₁
      have he₂ := InferSound.check ih₂ h₂ (by ret_ok) hex φ C hsat.2
      simp only [Ctx.subst_cons, hcl, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
      refine .let_ a [] (fun m _ => ?_) (.inl ⟨har, hap⟩) (fun p hp => by simp [hap] at hp)
        (fun b hb => by cases hb; exact ⟨rfl, har, hap, haf⟩) he₂
      have hop : a.open m = a.inst [] := by simp [Scheme.open, har, varBlock]
      have hopp : a.openPreds m = [] := by simp [Scheme.openPreds, Scheme.instPreds, hap]
      rw [hop, hopp, List.append_nil]
      simpa only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose, annMode, Ex.mode_some]
        using he₁
    | none =>
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σi preds₁ himp
    generalize hls : letScheme (Expr.generalises e₁ e₂) (Ctx.subst (Subst.compose σi o₁.σ) Γ)
      (Ret.subst (Subst.compose σi o₁.σ) R) (o₁.τ.subst σi) preds₁ = ls at h
    obtain ⟨s, rest⟩ := ls
    split at h
    rotate_left
    · cases h
    rename_i hcheck
    have hs : s.Simple := Scheme.simple_of_check hcheck
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₂ := InferSound.check ih₂ h₂ (by ret_ok) hex φ C hsat.2
    simp only [Ctx.subst_cons, Ctx.subst_compose, Ret.subst_compose] at he₂ ⊢
    -- `e₁`'s typing under a substitution `ψ` satisfying what improvement left.
    have he₁ : ∀ ψ C', Sat C' preds₁ ψ →
        HasType L C' (Ctx.subst ψ (Ctx.subst (Subst.compose σi o₁.σ) Γ))
          (Ret.subst ψ (Ret.subst (Subst.compose σi o₁.σ) R)) rm .synth e₁
          ((o₁.τ.subst σi).subst ψ) :=
      fun ψ C' hψ => by
        have := ih₁ h₁ (by ret_ok) .none (Subst.compose ψ σi) C' (improveAll_sound _ himp hψ)
        simpa only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose, exMode_none] using this
    simp only [letScheme] at hls
    split at hls
    · -- Generalised: rename the generalised variables to the block at `m`.
      rename_i hv
      simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      simp only [Expr.generalises, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      refine .let_ _ [] (fun m _ => ?_) (.inr ⟨Expr.isValue_sound hv.1, hv.2⟩)
        ((hs.subst _).subst _) (fun _ h => by cases h) he₂
      let Γ₁ := Ctx.subst (Subst.compose σi o₁.σ) Γ
      let R₁ := Ret.subst (Subst.compose σi o₁.σ) R
      let ᾱ := genVars Γ₁ R₁ (o₁.τ.subst σi) preds₁
      let φ₀ := Subst.compose φ o₂.σ
      let ψ := renameBlock ᾱ m ++ φ₀
      have hout : ∀ a, a ∈ ctxTv Γ₁ ++ Ret.tv R₁ → a ∉ ᾱ := fun _ ha => genVars_not_env ha
      have hfind : ∀ a, a ∉ ᾱ → TyEq ((Ty.var a).subst ψ) ((Ty.var a).subst φ₀) := fun a ha => by
        simp only [ψ, Ty.subst, renameBlock_append_find m _ ha]; exact TyEq.refl _
      -- Renaming changes the context only where its unfolding doesn't reach.
      have hΓ : CtxEq (Ctx.subst ψ Γ₁) (Ctx.subst φ₀ Γ₁) := Ctx.subst_congr_tv (fun a ha =>
        hfind a (hout a (List.mem_append_left _ ha)))
      have hR : RetEq (Ret.subst ψ R₁) (Ret.subst φ₀ R₁) := Ret.subst_congr_tv (fun a ha =>
        hfind a (hout a (List.mem_append_right _ ha)))
      rw [← Ctx.subst_compose σi o₁.σ Γ, ← Ret.subst_compose σi o₁.σ R]
      rw [← Scheme.subst_compose, ← Ctx.subst_compose, ← Ret.subst_compose,
        ← generalize_open ᾱ m φ₀, ← generalize_openPreds ᾱ m φ₀]
      refine (he₁ ψ _ (fun c hc => ?_)).weaken hΓ.ctxGen hR
        ((hRo.subst (Subst.compose σi o₁.σ)).ret_eq _ _)
      by_cases hg : c.tv.any (· ∈ ᾱ) = true
      · refine Entails.of_predEq ((Pred.normHead_predEq c).subst ψ).symm (Entails.of_mem
          (List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem
            (List.mem_filter.mpr ⟨hc, hg⟩)))))
      · have hr : c ∈ preds₁.filter (fun c => !c.tv.any (· ∈ ᾱ)) :=
          List.mem_filter.mpr ⟨hc, by simpa using hg⟩
        have hc' : PredEq (c.subst ψ) (c.subst φ₀) := Pred.subst_predEq_congr_tv (fun a ha =>
          hfind a (fun hα => hg (List.any_eq_true.mpr ⟨a, ha, by simpa using hα⟩)))
        exact Entails.of_predEq hc'.symm ((hsat.1 c hr).append_right _)
    · simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      refine .let_ _ [] (fun m _ => ?_) (.inl ⟨rfl, by simp [Scheme.mono, Scheme.subst]⟩)
        ((hs.subst _).subst _) (fun _ h => by cases h) he₂
      simpa [annMode] using he₁ _ C hsat.1
  | assign i e ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i s hs
    split at h
    rotate_left
    · cases h
    rename_i hmono
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have he := ih h₁ (by ret_ok) .none _ C hsat
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ⊢
    replace he := he.conv ((unify_sound hu).subst φ).symm
    simp only [Scheme.inst_nil_subst] at he ⊢
    exact .assign (by simp [Ctx.getElem?_subst, hs]) (by simp [hmono.1])
      (by simp [Scheme.subst, hmono.2]) he
  | cond c t e ihc iht ihe =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have hc := ihc h₁ (by ret_ok) .none _ C hsat.1.1
    have ht := InferSound.check iht h₂ (by ret_ok) hex _ C hsat.1.2
    have he := InferSound.check ihe h₃ (by ret_ok) hex _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hc ht he ⊢
    match ex, hex with
    | none, _ =>
      replace ht := ht.conv ((unify_sound hu).subst φ)
      exact .cond hc ht he
    | some T, hex =>
      have hT := hex T rfl
      simp only [InferSound.check_ty h₂ hex T rfl, InferSound.check_ty h₃ hex T rfl,
        Ty.closed_subst hT] at ht he ⊢
      exact .cond hc ht he
  | unop op e ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    cases op with
    | not =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .not (ih h₁ (by ret_ok) .none φ C hsat)
    | typeof =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .typeof (ih h₁ (by ret_ok) .none φ C hsat)
    | neg =>
      simp only at h
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ (by ret_ok) .none _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ⊢
      replace he := he.conv ((unify_sound hu).subst φ)
      exact .unop .neg he
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    cases op with
    | plus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append, Sat.singleton] at hsat
      have he₁ := ih₁ h₁ (by ret_ok) .none _ C hsat.1.1
      have he₂ := ih₂ h₂ (by ret_ok) .none _ C hsat.1.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ hsat ⊢
      replace he₁ := he₁.conv ((unify_sound hu).subst φ)
      exact .binop (.plus (by simpa [Pred.subst] using hsat.2)) he₁ he₂
    | minus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu₃
      split at h
      · cases h
      rename_i σ₄ hu₄
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append] at hsat
      have he₁ := ih₁ h₁ (by ret_ok) .none _ C hsat.1
      have he₂ := ih₂ h₂ (by ret_ok) .none _ C hsat.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
      replace he₁ := he₁.conv (((unify_sound hu₃).subst σ₄).subst φ)
      replace he₂ := he₂.conv ((unify_sound hu₄).subst φ)
      exact .binop .minus (by simpa using he₁) (by simpa using he₂)
  | ret e ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    match R, rm, hRo with
    | none, _, _ => simp [infer] at h
    | some τr, .synth, _ =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ RetOk.synth .none _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_some] at he ⊢
      replace he := he.conv ((unify_sound hu).subst φ).symm
      exact .ret he
    | some τr, .check, hRo =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      simp only [Option.some.injEq] at h; subst h
      have hτ := hRo rfl τr rfl
      have he := InferSound.check ih h₁ hRo (Ex.Closed.some hτ) φ C hsat
      rw [InferSound.check_ty h₁ (Ex.Closed.some hτ) τr rfl] at he
      simp only [Ret.subst_some, Ty.closed_subst hτ, Ex.mode_some] at he ⊢
      exact .ret he
  | throw_ e ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    exact .throw_ (ih h₁ (by ret_ok) .none φ C hsat)
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₁ := ih₁ h₁ (by ret_ok) .none _ C hsat.1
    have he₂ := InferSound.check ih₂ h₂ (by ret_ok) hex _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
    exact .seq he₁ he₂
  | while_ c body ihc ihb =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hc := ihc h₁ (by ret_ok) .none _ C hsat.1
    have hb := ihb h₂ (by ret_ok) .none _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hc hb ⊢
    exact .while_ hc hb
  | break_ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    simp only [infer, Option.some.injEq] at h; subst h
    exact .break_
  | continue_ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    simp only [infer, Option.some.injEq] at h; subst h
    exact .continue_
  | tryCatch body handler ihb ihh =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have hb := InferSound.check ihb h₁ (by ret_ok) hex _ C hsat.1
    have hh := InferSound.check ihh h₂ (by ret_ok) hex _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose, Ctx.subst_cons,
      Scheme.mono_subst, Ty.subst_app] at hb hh ⊢
    match ex, hex with
    | none, _ =>
      replace hb := hb.conv ((unify_sound hu).subst φ)
      exact .tryCatch hb hh
    | some T, hex =>
      have hT := hex T rfl
      simp only [InferSound.check_ty h₁ hex T rfl, InferSound.check_ty h₂ hex T rfl,
        Ty.closed_subst hT] at hb hh ⊢
      exact .tryCatch hb hh
  | tryFinally body fin ihb ihf =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_pushes (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hb := InferSound.check ihb h₁ (by ret_ok) hex _ C hsat.1
    have hf := ihf h₂ (by ret_ok) .none _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hb hf ⊢
    exact .tryFinally hb hf

  | obj ls es ks ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    rename_i hcond
    split at h
    · cases h
    rename_i o₁ h₁
    have hL : ∀ l ∈ ls, l ∈ L := fun l hl => by simpa using List.all_eq_true.mp hcond.1 l hl
    split at h
    · cases h
    rename_i θs ss hfs
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have ha := inferArgs_sound es ih h₁ (by ret_ok) .none _ C hsat
    obtain ⟨hssl, -, hτl, hslot⟩ := fieldSlots_sound hfs
    have hthis := unifyThis_sound hu
    simp only [Ctx.subst_compose, Ret.subst_compose] at ha ⊢
    rw [← Ty.subst_compose]
    have hθ : ∀ θ ∈ θs, TyEq (θ.subst (Subst.compose φ σ'))
        ((Ty.record L (objSlots L ls ss)).subst (Subst.compose φ σ')) := fun θ hθ => by
      simpa only [Ty.subst_compose] using hthis θ hθ φ
    have hslot' := hslot _ _ hθ
    simp only [Ty.subst_app, objSlots_subst] at hslot' ⊢
    refine .obj (by omega) (by omega) (by simp [ha.1]; omega) (by simp; omega) hL ha.2 ?_
    rw [zip4_map]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hslot' y hy
  | cls ls es ks ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    rename_i hcond
    obtain ⟨hcL, hnd, hesl, hksl⟩ := hcond
    have hL : ∀ l ∈ ls, l ∈ L := fun l hl => by simpa using List.all_eq_true.mp hcL l hl
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i θs ss n' hms
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    obtain ⟨hsat, hsatn⟩ := hsat
    have hm := inferMembers_sound es ks ih h₁ _ C hsat
    obtain ⟨hssl, hτl, -, -, hslot⟩ := memberSlots_sound hms
    have hthis := unifyThis_sound hu
    simp only [Ctx.subst_compose, Ret.subst_compose] at hm ⊢
    rw [← Ty.subst_compose]
    have hθ : ∀ θ ∈ θs, TyEq (θ.subst (Subst.compose φ σ'))
        ((Ty.record L (objSlots L ls ss)).subst (Subst.compose φ σ')) := fun θ hθ => by
      simpa only [Ty.subst_compose] using hthis θ hθ φ
    have hslot' := hslot C _ _ hθ hsatn
    simp only [Ty.subst_app, objSlots_subst] at hslot' ⊢
    refine .cls (τs := o₁.τs.map (·.subst (Subst.compose φ σ'))) hesl hksl (by simp; omega)
      (by simp; omega) hnd hL (fun i e k τ h₁ h₂ h₃ => ?_) ?_
    · have := hm.2.2 i e k τ h₁ h₂ h₃
      by_cases hk : k = .data
      · subst hk; simpa using this
      · simpa [hk] using this
    · rw [zip4_map]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hslot' y hy
  | ctor k body ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have := ih h₁ (by ret_ok) .none _ C hsat
    simp only [Ctx.subst, List.map_append, List.map_map, List.map_cons, Function.comp_def,
      Scheme.mono_subst, Ty.subst_fn, Ty.subst_compose, Ret.subst_compose,
      Ret.subst_some] at this ⊢
    replace this := this.conv ((unify_sound hu).subst φ).symm
    exact .ctor (by simp [varBlock]) (by simpa [Function.comp_def] using this)
  | new_ f args ihf iha =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have hf := ihf h₁ (by ret_ok) .none _ C hsat.1
    have ha := inferArgs_sound args iha h₂ (by ret_ok) .none _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hf ha ⊢
    replace hf := hf.conv ((unify_sound hu).subst φ)
    simp only [Ty.subst_fn, List.map_map, Function.comp_def] at hf ha
    exact .new_ hf (by simp [ha.1]) ha.2 (TyEq.refl _) (by simp [varBlock])
  | get e l ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.append, Sat.singleton] at hsat
    exact .get (ih h₁ (by ret_ok) .none φ C hsat.1) (by simpa [Pred.subst] using hsat.2)
  | set e l v ihe ihv =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he := ihe h₁ (by ret_ok) .none _ C hsat.1.1
    have hv := ihv h₂ (by ret_ok) .none φ C hsat.1.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he hv ⊢
    exact .set he (by simpa [Pred.subst, Ty.subst_compose] using hsat.2 _ List.mem_cons_self) hv
  | spread e₁ e₂ ih₁ ih₂ =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have he₁ := ih₁ h₁ (by ret_ok) .none _ C hsat.1.1
    have he₂ := ih₂ h₂ (by ret_ok) .none _ C hsat.1.2
    have hτ₁ : TyEq (Ty.subst ((φ.compose (σ₄.compose σ₃)).compose o₂.σ) o₁.τ)
        ((Ty.record L (varBlock o₂.next L.length)).subst (φ.compose (σ₄.compose σ₃))) := by
      simp only [Ty.subst_compose]; exact ((unify_sound hu₃).subst σ₄).subst φ
    have hτ₂ : TyEq (Ty.subst (φ.compose (σ₄.compose σ₃)) o₂.τ)
        ((Ty.record L (slots3 (varBlock (o₂.next + L.length) L.length)
          (varBlock (o₂.next + 2 * L.length) L.length)
          (varBlock (o₂.next + 3 * L.length) L.length))).subst (φ.compose (σ₄.compose σ₃))) := by
      simp only [Ty.subst_compose]; exact (unify_sound hu₄).subst φ
    replace he₁ := he₁.conv hτ₁
    replace he₂ := he₂.conv hτ₂
    simp only [Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
    rw [← Ty.subst_compose]
    exact HasType.spread_subst (by simp [varBlock]) (by simp [varBlock]) (by simp [varBlock])
      (by simp [varBlock]) (by simp [varBlock]) he₁ he₂ hsat.2

  | arr es ih =>
    intro Γ R rm ex n o h hRo hex φ C hsat
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
      have ha := inferArgs_sound es ih h₁ hRo (Ex.Closed.some hσ) φ C hsat
      have hty := inferArgs_ty es h₁ hσ
      have hp : (Expr.arr es).pushes T = true := by simp [Expr.pushes, hat]
      simp only [exMode, hp, ↓reduceIte, Ty.closed_subst hT]
      refine .arrCheck hw hT fun e he => ?_
      have hrep : o₁.τs.map (·.subst φ) = List.replicate es.length σ := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp [ha.1], fun b hb => ?_⟩
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hb
        rw [hty τ hτ, Ty.closed_subst hσ]
      have := ha.2 _ (hrep ▸ mem_zip_replicate he)
      simpa using this
    · rename_i hat
      rw [show exMode ex (.arr es) = .synth by
        cases ex with
        | none => rfl
        | some T => simp [exMode, Expr.pushes, hat]]
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have ha := inferArgs_sound es ih h₁ (by ret_ok) .none (Subst.compose φ σ') C hsat
      have hu' := (unify_sound hu).subst φ
      simp only [Ty.subst_app, List.map_replicate, List.map_map] at hu'
      obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp hu'
      have hτs : ∀ p ∈ es.zip (List.replicate es.length (((Ty.var o₁.next).subst σ').subst φ)),
          HasType L C (Ctx.subst (Subst.compose φ σ') (Ctx.subst o₁.σ Γ))
            (Ret.subst (Subst.compose φ σ') (Ret.subst o₁.σ R)) rm .synth p.1 p.2 := by
        have hl' : (o₁.τs.map (·.subst (Subst.compose φ σ'))).length =
            (List.replicate es.length (((Ty.var o₁.next).subst σ').subst φ)).length := by
          simp [ha.1]
        have hz' : ∀ x ∈ (o₁.τs.map (·.subst (Subst.compose φ σ'))).zip
            (List.replicate es.length (((Ty.var o₁.next).subst σ').subst φ)), TyEq x.1 x.2 := by
          have : o₁.τs.map (·.subst (Subst.compose φ σ')) =
              o₁.τs.map ((fun x => x.subst φ) ∘ fun x => x.subst σ') := by
            simp [Function.comp_def]
          rw [this, ← ha.1]
          simpa using hz
        exact zip_conv (by simp [ha.1]) hl' ha.2 hz' (fun _ _ _ h e => h.conv e)
      have hargs := fun e (he : e ∈ es) => hτs _ (mem_zip_replicate he)
      simp only [Ctx.subst_compose, Ret.subst_compose] at hargs
      simp only [Ctx.subst_compose, Ret.subst_compose, Ty.subst_app, List.map_cons, List.map_nil]
      exact .arr hargs
  | index e i ihe ihi =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append, Sat.singleton] at hsat
    have he := ihe h₁ (by ret_ok) .none _ C hsat.1.1
    have hi := ihi h₂ (by ret_ok) .none φ C hsat.1.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he hi ⊢
    exact .index he hi (by simpa [Pred.subst, Ty.subst_compose] using hsat.2)
  | setIndex e i v ihe ihi ihv =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
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
    simp only [Sat.map, Sat.append] at hsat
    have he := ihe h₁ (by ret_ok) .none _ C hsat.1.1.1
    have hi := ihi h₂ (by ret_ok) .none _ C hsat.1.1.2
    have hv := ihv h₃ (by ret_ok) .none φ C hsat.1.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he hi hv ⊢
    exact .setIndex he hi
      (by simpa [Pred.subst, Ty.subst_compose] using hsat.2 _ List.mem_cons_self)
      (by simpa [Pred.subst, Ty.subst_compose] using
        hsat.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)) hv
  | mcall e l args ihe iha =>
    intro Γ R rm ex n o h hRo hex φ C hsat
    rw [exMode_synth (fun _ => rfl)]
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append, Sat.singleton] at hsat
    have he := ihe h₁ (by ret_ok) .none _ C hsat.1.1
    have ha := inferArgs_sound args iha h₂ (by ret_ok) .none φ C hsat.1.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ha ⊢
    exact .mcall he (by simpa [Pred.subst, Ty.subst_compose] using hsat.2) (by simp [ha.1]) ha.2

/-- A program inference accepts in a context with no free type variables is
well typed in it, assuming the constraints left, each of which is an
instance or on a type variable. -/
theorem inferIn_sound {Γ : Ctx} {e : Expr} {τ : Ty} (hΓ : ctxFtv Γ = [])
    (h : inferIn L Γ e = some τ) : ∃ C, HoldsOrVar C ∧ HasType L C Γ none .synth .synth e τ := by
  simp only [inferIn] at h
  split at h
  rotate_left
  · cases h
  split at h
  · cases h
  rename_i o ho
  split at h
  · cases h
  rename_i σi preds himp
  split at h
  · rename_i hall
    simp only [Option.some.injEq] at h; subst h
    have hsat : Sat preds o.preds σi := by
      have := improveAll_sound _ himp (C := preds) (φ := []) (fun c hc => Entails.of_mem (by simpa using hc))
      intro c hc
      simpa [Pred.subst_compose] using this c hc
    have hclosed : ∀ σ : Subst, Ctx.subst σ Γ = Γ := fun σ =>
      ctx_subst_id (fun a ha => by simp [hΓ] at ha)
    refine ⟨preds, HoldsOrVar.of_settled hall, ?_⟩
    simpa [hclosed] using infer_sound ho RetOk.synth .none σi preds hsat
  · cases h

/-- A program inference accepts is well typed, with records over its labels,
assuming constraints each an instance or on a type variable. -/
theorem inferProgram_sound {e : Expr} {τ : Ty} (h : inferProgram e = some τ) :
    ∃ C, HoldsOrVar C ∧ HasType e.labels.eraseDups C [] none .synth .synth e τ :=
  inferIn_sound rfl h

/-- A program inference accepts never gets stuck, whatever the clock. -/
theorem inferProgram_never_stuck {e : Expr} {τ : Ty} (h : inferProgram e = some τ)
    (clock : Nat) (s : Stuck) : eval clock [] [] e ≠ .stuck s := by
  obtain ⟨C, hC, ht⟩ := inferProgram_sound h
  exact never_stuck ht hC clock s

end Inty
