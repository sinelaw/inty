import Inty.Infer
import Inty.Soundness

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

theorem Entails.weaken {C : List Pred} (D : List Pred) (h : Entails C p) : Entails (C ++ D) p :=
  h.elim .inl (fun h => .inr (List.mem_append_left _ h))

theorem Lit.ty_sound (l : Lit) : LitTy l l.ty := by cases l <;> constructor

@[simp] theorem Lit.ty_subst (l : Lit) (σ : Subst) : l.ty.subst σ = l.ty := by
  cases l <;> rfl

theorem Expr.isValue_sound {e : Expr} (h : e.isValue = true) : e.IsValue := by
  cases e <;> first | constructor | simp [Expr.isValue] at h

theorem PPred.isSimple_spec {k : Nat} {p : PPred} (h : p.isSimple k = true) :
    ∃ i < k, p = ⟨.plus, [.bound i]⟩ ∨ ∃ l σ, p = ⟨.hasProp l, [.bound i, σ]⟩ := by
  unfold PPred.isSimple at h
  split at h
  · exact ⟨_, of_decide_eq_true h, .inl rfl⟩
  · exact ⟨_, of_decide_eq_true h, .inr ⟨_, _, rfl⟩⟩
  · cases h

/-- A scheme whose constraints pass the check is simple. -/
theorem Scheme.simple_of_check {s : Scheme} (h : s.preds.all (PPred.isSimple s.arity) = true) :
    s.Simple := fun p hp => PPred.isSimple_spec (List.all_eq_true.mp h p hp)

/-! ## Improvement -/

/-- A constraint whose decision is an equation is an instance wherever the
equation holds. -/
theorem Pred.improve_sound {p : Pred} {a b : Ty} (h : p.improve = .eq a b) {ψ : Subst}
    (hab : a.subst ψ = b.subst ψ) : Inst (p.subst ψ) := by
  unfold Pred.improve at h
  split at h
  · cases h
  · split at h
    · rename_i hs
      cases h
      simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
      exact .hasProp (by rw [Ty.field_subst, hs]; simpa using hab)
    · cases h
  · cases h
  · cases h

theorem improveOne_some : ∀ {ps : List Pred} {a b : Ty} {rest : List Pred},
    improveOne ps = some (some ((a, b), rest)) →
      ∃ p, p.improve = .eq a b ∧ ∀ q ∈ ps, q = p ∨ q ∈ rest
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
theorem improveAll_sound : ∀ (k : Nat) {ps : List Pred} {σ : Subst} {ps' : List Pred},
    improveAll k ps = some (σ, ps') → ∀ {C : List Pred} {φ : Subst}, Sat C ps' φ →
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
        simp only [Ty.subst_compose, unify_sound hu]
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
    (ha : a ∈ ctxFtv Γ₁ ++ Ret.ftv R₁) : a ∉ genVars Γ₁ R₁ τ₁ preds := by
  intro hα
  simp only [genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at hα
  exact hα.2 (fixLoop_sup _ _ ha)

/-- What `infer_sound` says of one expression. -/
def InferSound (L : List String) (e : Expr) : Prop :=
  ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out}, infer L Γ R e n = some o →
    ∀ φ C, Sat C o.preds φ →
      HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) e (o.τ.subst φ)

/-- Inferring arguments, each sound, is sound: one type per argument, each
a valid typing under the inferred substitution and any further one that
resolves the constraints. -/
theorem inferArgs_sound : ∀ (args : List Expr), (∀ a ∈ args, InferSound L a) →
    ∀ {Γ : Ctx} {R : Option Ty} {n : Nat} {o : OutArgs}, inferArgs L Γ R args n = some o →
      ∀ φ C, Sat C o.preds φ → o.τs.length = args.length ∧
        ∀ p ∈ args.zip (o.τs.map (·.subst φ)),
          HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) p.1 p.2
  | [], _, Γ, R, n, o, h, φ, C, _ => by
    simp only [inferArgs, Option.some.injEq] at h; subst h; simp
  | a :: as, ih, Γ, R, n, o, h, φ, C, hsat => by
    simp only [inferArgs] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have ha := ih a (by simp) h₁ _ C hsat.1
    have has := inferArgs_sound as (fun a' ha' => ih a' (by simp [ha'])) h₂ φ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at ha has ⊢
    refine ⟨by simp [has.1], fun p hp => ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ha
    · exact has.2 p hp

/-- Soundness of Algorithm W: the inferred type, under the inferred
substitution and any further substitution that resolves the class
constraints, is a valid typing. -/
theorem infer_sound :
    ∀ {e : Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out}, infer L Γ R e n = some o →
      ∀ φ C, Sat C o.preds φ →
        HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) e
          (o.τ.subst φ) := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro Γ R n o h φ C hsat
    simp only [infer, Option.some.injEq] at h; subst h
    simpa using HasType.lit (C := C) (Γ := Ctx.subst φ Γ) (Lit.ty_sound l)
  | var i =>
    intro Γ R n o h φ C hsat
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
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have := ih h₁ _ C hsat
    simp only [Ctx.subst, List.map_append, List.map_map, List.map_cons, Function.comp_def,
      Scheme.mono_subst, Ty.subst_fn, Ty.subst_compose, Ret.subst_compose,
      Ret.subst_some] at this ⊢
    rw [← unify_sound hu] at this
    exact .func (by simp [varBlock]) (by simpa [Function.comp_def] using this)
  | app f args ihf iha =>
    intro Γ R n o h φ C hsat
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
    have hf := ihf h₁ _ C hsat.1
    have ha := inferArgs_sound args iha h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hf ha ⊢
    rw [unify_sound hu] at hf
    simp only [Ty.subst_fn, List.map_map, Function.comp_def] at hf ha
    exact .app hf (by simp [ha.1]) ha.2
  | let_ mb e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
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
    have he₂ := ih₂ h₂ φ C hsat.2
    simp only [Ctx.subst_cons, Ctx.subst_compose, Ret.subst_compose] at he₂ ⊢
    -- `e₁`'s typing under a substitution `ψ` satisfying what improvement left.
    have he₁ : ∀ ψ C', Sat C' preds₁ ψ →
        HasType L C' (Ctx.subst ψ (Ctx.subst (Subst.compose σi o₁.σ) Γ))
          (Ret.subst ψ (Ret.subst (Subst.compose σi o₁.σ) R)) e₁ ((o₁.τ.subst σi).subst ψ) :=
      fun ψ C' hψ => by
        have := ih₁ h₁ (Subst.compose ψ σi) C' (improveAll_sound _ himp hψ)
        simpa only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] using this
    simp only [letScheme] at hls
    split at hls
    · -- Generalised: rename the generalised variables to the block at `m`.
      rename_i hv
      simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      simp only [Expr.generalises, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      refine .let_ _ [] (fun m _ => ?_) (.inr ⟨Expr.isValue_sound hv.1, hv.2⟩)
        ((hs.subst _).subst _) he₂
      let Γ₁ := Ctx.subst (Subst.compose σi o₁.σ) Γ
      let R₁ := Ret.subst (Subst.compose σi o₁.σ) R
      let ᾱ := genVars Γ₁ R₁ (o₁.τ.subst σi) preds₁
      let φ₀ := Subst.compose φ o₂.σ
      let ψ := renameBlock ᾱ m ++ φ₀
      have hout : ∀ a, a ∈ ctxFtv Γ₁ ++ Ret.ftv R₁ → a ∉ ᾱ := fun _ ha => genVars_not_env ha
      have hΓ : Ctx.subst ψ Γ₁ = Ctx.subst φ₀ Γ₁ := Ctx.subst_congr (fun a ha =>
        renameBlock_append_find m _ (hout a (List.mem_append_left _ ha)))
      have hR : Ret.subst ψ R₁ = Ret.subst φ₀ R₁ := Ret.subst_congr (fun a ha =>
        renameBlock_append_find m _ (hout a (List.mem_append_right _ ha)))
      rw [← Ctx.subst_compose σi o₁.σ Γ, ← Ret.subst_compose σi o₁.σ R]
      rw [← Scheme.subst_compose, ← Ctx.subst_compose, ← Ret.subst_compose, ← hΓ, ← hR,
        ← generalize_open ᾱ m φ₀, ← generalize_openPreds ᾱ m φ₀]
      refine he₁ ψ _ (fun c hc => ?_)
      by_cases hg : c.ftv.any (· ∈ ᾱ) = true
      · exact .inr (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, hg⟩)))
      · have hr : c ∈ preds₁.filter (fun c => !c.ftv.any (· ∈ ᾱ)) :=
          List.mem_filter.mpr ⟨hc, by simpa using hg⟩
        have hc' : c.subst ψ = c.subst φ₀ := Pred.subst_congr (fun a ha =>
          renameBlock_append_find m _ (fun hα => hg (List.any_eq_true.mpr ⟨a, ha, by simpa using hα⟩)))
        rw [hc']
        exact (hsat.1 c hr).weaken _
    · simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      refine .let_ _ [] (fun m _ => ?_) (.inl ⟨rfl, by simp [Scheme.mono, Scheme.subst]⟩)
        ((hs.subst _).subst _) he₂
      simpa using he₁ _ C hsat.1
  | assign i e ih =>
    intro Γ R n o h φ C hsat
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
    have he := ih h₁ _ C hsat
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ⊢
    rw [← unify_sound hu] at he
    simp only [Scheme.inst_nil_subst] at he ⊢
    exact .assign (by simp [Ctx.getElem?_subst, hs]) (by simp [hmono.1])
      (by simp [Scheme.subst, hmono.2]) he
  | cond c t e ihc iht ihe =>
    intro Γ R n o h φ C hsat
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
    have hc := ihc h₁ _ C hsat.1.1
    have ht := iht h₂ _ C hsat.1.2
    have he := ihe h₃ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hc ht he ⊢
    rw [unify_sound hu] at ht
    exact .cond hc ht he
  | unop op e ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    cases op with
    | not =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .not (ih h₁ φ C hsat)
    | typeof =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .typeof (ih h₁ φ C hsat)
    | neg =>
      simp only at h
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ⊢
      rw [unify_sound hu] at he
      exact .unop .neg he
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
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
      have he₁ := ih₁ h₁ _ C hsat.1.1
      have he₂ := ih₂ h₂ _ C hsat.1.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ hsat ⊢
      rw [unify_sound hu] at he₁
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
      have he₁ := ih₁ h₁ _ C hsat.1
      have he₂ := ih₂ h₂ _ C hsat.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
      rw [unify_sound hu₃] at he₁
      rw [unify_sound hu₄] at he₂
      exact .binop .minus (by simpa using he₁) (by simpa using he₂)
  | ret e ih =>
    intro Γ R n o h φ C hsat
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
      simp only [Sat.map] at hsat
      have he := ih h₁ _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_some] at he ⊢
      rw [← unify_sound hu] at he
      exact .ret he
  | throw_ e ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    exact .throw_ (ih h₁ φ C hsat)
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₁ := ih₁ h₁ _ C hsat.1
    have he₂ := ih₂ h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
    exact .seq he₁ he₂
  | while_ c body ihc ihb =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hc := ihc h₁ _ C hsat.1
    have hb := ihb h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hc hb ⊢
    exact .while_ hc hb
  | break_ =>
    intro Γ R n o h φ C hsat
    simp only [infer, Option.some.injEq] at h; subst h
    exact .break_
  | continue_ =>
    intro Γ R n o h φ C hsat
    simp only [infer, Option.some.injEq] at h; subst h
    exact .continue_
  | tryCatch body handler ihb ihh =>
    intro Γ R n o h φ C hsat
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
    have hb := ihb h₁ _ C hsat.1
    have hh := ihh h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose, Ctx.subst_cons,
      Scheme.mono_subst, Ty.subst_app] at hb hh ⊢
    rw [unify_sound hu] at hb
    exact .tryCatch hb hh
  | tryFinally body fin ihb ihf =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hb := ihb h₁ _ C hsat.1
    have hf := ihf h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hb hf ⊢
    exact .tryFinally hb hf

  | obj ls es ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    rotate_left
    · cases h
    rename_i hcond
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    have ha := inferArgs_sound es ih h₁ φ C hsat
    simp only [Ty.subst_app, objSlots_subst]
    exact .obj (by simp [ha.1, hcond.2]) (by simp [varBlock])
      (fun l hl => by simpa using List.all_eq_true.mp hcond.1 l hl) hcond.2 ha.2
  | get e l ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.append, Sat.singleton] at hsat
    exact .get (ih h₁ φ C hsat.1) (by simpa [Pred.subst] using hsat.2)
  | set e l v ihe ihv =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append, Sat.singleton] at hsat
    have he := ihe h₁ _ C hsat.1.1
    have hv := ihv h₂ φ C hsat.1.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he hv ⊢
    exact .set he (by simpa [Pred.subst, Ty.subst_compose] using hsat.2) hv

/-- A program inference accepts in a context with no free type variables is
well typed in it, assuming the constraints left, each of which is an
instance or on a type variable. -/
theorem inferIn_sound {Γ : Ctx} {e : Expr} {τ : Ty} (hΓ : ctxFtv Γ = [])
    (h : inferIn L Γ e = some τ) : ∃ C, HoldsOrVar C ∧ HasType L C Γ none e τ := by
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
      have := improveAll_sound _ himp (C := preds) (φ := []) (fun c hc => .inr (by simpa using hc))
      intro c hc
      simpa [Pred.subst_compose] using this c hc
    have hclosed : ∀ σ : Subst, Ctx.subst σ Γ = Γ := fun σ =>
      ctx_subst_id (fun a ha => by simp [hΓ] at ha)
    refine ⟨preds, HoldsOrVar.of_settled hall, ?_⟩
    simpa [hclosed] using infer_sound ho σi preds hsat
  · cases h

/-- A program inference accepts is well typed, with records over its labels,
assuming constraints each an instance or on a type variable. -/
theorem inferProgram_sound {e : Expr} {τ : Ty} (h : inferProgram e = some τ) :
    ∃ C, HoldsOrVar C ∧ HasType e.labels.eraseDups C [] none e τ :=
  inferIn_sound rfl h

/-- A program inference accepts never gets stuck, whatever the clock. -/
theorem inferProgram_never_stuck {e : Expr} {τ : Ty} (h : inferProgram e = some τ)
    (clock : Nat) (s : Stuck) : eval clock [] [] e ≠ .stuck s := by
  obtain ⟨C, hC, ht⟩ := inferProgram_sound h
  exact never_stuck ht hC clock s

end Inty
