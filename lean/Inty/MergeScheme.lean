import Inty.Modes

/-!
# A scheme that keeps a `Merge`

`HasType`'s `let` rule lets a scheme keep a `Merge` (a spread's constraint)
whose determining arguments are quantified (`Scheme.Simple`): a spread over
a parameter's object has no field list until a call gives one. inty instead
decides a spread at once (`merge_spread`). Here is a program for which the
difference matters:

```
const f = (o) => ({...{}, ...o});
f({a: 1});
f({});
```

`HasType` types it (`spreadMerge_typed`), and every typing gives `f` a
scheme with a `Merge` constraint (`spreadMerge_needed`): the two calls need
`o`'s field `a` present and absent, so `f` must quantify over its presence,
and a spread over a field whose presence isn't known holds only by an
assumption, which only the scheme can make. So a `let` rule that decided
each `Merge` at the binding, as inty does, would reject it.
-/

namespace Inty

/-- `(o) => ({...{}, ...o})`. -/
def spreadFn : Expr := .func 1 (.spread (.obj [] [] []) (.var 0))

/-- `f({a: 1}); f({})`, with `f` the variable `0`. -/
def spreadUses : Expr :=
  .seq (.app (.var 0) [.obj ["a"] [.lit (.number 1)] [.data]]) (.app (.var 0) [.obj [] [] []])

def spreadMerge : Expr := .let_ false none spreadFn spreadUses

/-- `f`'s scheme: `∀ θ p k τ r. Merge p k τ absent r ⇒ θ.({a: (p, k, τ)}) → {a: r}`. -/
def spreadScheme : Scheme :=
  ⟨5, .fn (.bound 0) [.app (.record ["a"]) [.app .slot [.bound 1, .bound 2, .bound 3]]]
      (.app (.record ["a"]) [.bound 4]),
    [⟨.merge, [.bound 1, .bound 2, .bound 3, .app .slot [.app .abs [], .app .data [], .app .undefined []],
      .bound 4]⟩]⟩

theorem spreadMerge_typed :
    HasType ["a"] [] [] none .synth .synth spreadMerge (.record ["a"] [.absSlot]) := by
  refine .let_ spreadScheme [] (fun m _ => ?_) (.inr ⟨.func, rfl⟩) (.inr ?_) (fun _ h => by cases h) ?_
  · -- The function, at the scheme opened at `m`.
    show HasType ["a"] ([] ++ spreadScheme.openPreds m) [] none .synth .synth spreadFn
      (.fn (.var m) [.record ["a"] [.slot (.var (m + 1)) (.var (m + 2)) (.var (m + 3))]]
        (.record ["a"] [.var (m + 4)]))
    refine .func rfl (.spread (ps := [.var (m + 1)]) (ks := [.var (m + 2)]) (τs := [.var (m + 3)])
      (ss := [.absSlot]) (rs := [.var (m + 4)]) rfl rfl rfl rfl rfl
      (.obj (τs := []) (ss := []) rfl rfl rfl rfl (by simp) (by simp) (by simp)) (.var_mono rfl)
      fun p hp => ?_)
    simp only [mergePreds, List.mem_singleton] at hp
    subst hp
    exact .inr ⟨_, by simp [Scheme.openPreds, Scheme.instPreds, spreadScheme, PPred.inst, PTy.inst,
      varBlock], PredEq.refl _⟩
  · -- Its `Merge` is on a quantified variable.
    intro p hp
    simp only [spreadScheme, List.mem_singleton] at hp
    subst hp
    exact .inr ⟨_, _, _, _, _, rfl, 1, by decide, .bound 1, by simp,
      PTy.treeBound_spec.mp (by decide)⟩
  · -- The two calls, at the field present and absent.
    have hf₁ : HasType ["a"] [] [spreadScheme] none .synth .synth (.var 0)
        (.fn .undefined [.record ["a"] [.slot .pre .data .number]] (.record ["a"] [.slot .pre .data .number])) :=
      HasTypeS.var (S := Sys.narrow) (C := []) (Γ := [spreadScheme]) (R := none) (rm := .synth)
        (i := 0) (s := spreadScheme) (τs := [.undefined, .pre, .data, .number, .slot .pre .data .number])
        rfl rfl fun c hc => by
          simp [Scheme.instPreds, spreadScheme] at hc
          subst hc
          exact .inl (Inst.instEq .mergeData)
    have hf₂ : HasType ["a"] [] [spreadScheme] none .synth .synth (.var 0)
        (.fn .undefined [.record ["a"] [.absSlot]] (.record ["a"] [.absSlot])) :=
      HasTypeS.var (S := Sys.narrow) (C := []) (Γ := [spreadScheme]) (R := none) (rm := .synth)
        (i := 0) (s := spreadScheme) (τs := [.undefined, .abs, .data, .undefined, .absSlot])
        rfl rfl fun c hc => by
          simp [Scheme.instPreds, spreadScheme] at hc
          subst hc
          exact .inl (Inst.instEq (.mergeAbs .abs))
    refine .seq (.drop (.app hf₁ rfl fun p hp => ?_)) (.app hf₂ rfl fun p hp => ?_)
    · simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hp
      subst hp
      exact .obj (τs := [.number]) (ss := [.slot .pre .data .number]) rfl rfl rfl rfl (by simp)
        (by simp; exact .lit .number) (by simp; exact .data)
    · simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hp
      subst hp
      exact .obj (τs := []) (ss := []) rfl rfl rfl rfl (by simp) (by simp) (by simp)

/-! ## Every typing keeps the `Merge` -/

theorem tyEq_fn_param {θ ρ θ' ρ' x : Ty} {τs : List Ty} (h : TyEq (.fn θ τs ρ) (.fn θ' [x] ρ')) :
    ∃ a, τs = [a] ∧ TyEq a x := by
  obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp h
  match τs, hl with
  | [a], _ => exact ⟨a, rfl, hz (a, x) (by simp)⟩

theorem tyEq_rec1_pres {c : Con} {k τ p k' τ' : Ty}
    (h : TyEq (.record ["a"] [.slot (.app c []) k τ]) (.record ["a"] [.slot p k' τ'])) :
    TyEq (.app c []) p := by
  obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp h
  exact (TyEq.slot (hz (.slot (.app c []) k τ, .slot p k' τ') (by simp))).1

/-- What a call of the variable `0`, of the scheme `s`, on an object
literal of the presence `c` says of `s`'s parameter. -/
theorem call_pres {s : Scheme} {m : Nat} (hs : ∀ a ∈ s.ftv, a < m) {θ x ρ τ : Ty}
    (e₀ : TyEq (.fn θ [x] ρ) (s.open m)) {arg : Expr} {c₀ : Con}
    (harg : ∀ τa, HasType ["a"] [] [s] none .synth .synth arg τa →
      ∃ k τ, TyEq (.record ["a"] [.slot (.app c₀ []) k τ]) τa)
    (h : HasType ["a"] [] [s] none .synth .synth (.app (.var 0) [arg]) τ) :
    ∀ {pr kk tt : Ty}, TyEq x (.record ["a"] [.slot pr kk tt]) →
      ∃ φ : Subst, TyEq (.app c₀ []) (pr.subst φ) := by
  intro pr kk tt hx
  obtain ⟨τ₀, -, ht⟩ := h.top_synth
  cases ht with
  | app hf hlen hargs =>
    obtain ⟨τf, ef, htf⟩ := hf.top_synth
    cases htf with
    | @var _ _ _ _ _ _ τs hi hl _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      -- The instance is the opened scheme, substituted.
      have hinst : s.inst τs = (s.open m).subst (Subst.block m τs) := by
        rw [Scheme.open, ← hl]
        exact (PTy.open_block s.body (fun a ha => hs a (by simp [Scheme.ftv, ha]))).symm
      rw [hinst] at ef
      have e₁ := ef.symm.trans (TyEq.subst (Subst.block m τs) e₀).symm
      simp only [Ty.subst_app, List.map_cons, List.map_nil] at e₁
      obtain ⟨a, rfl, ha⟩ := tyEq_fn_param e₁
      have harg' := hargs (arg, a) (by simp)
      obtain ⟨k₀, τ₀', he⟩ := harg _ harg'
      have hx' := TyEq.subst (Subst.block m τs) hx
      simp only [Ty.subst_app, List.map_cons, List.map_nil] at hx'
      exact ⟨Subst.block m τs, tyEq_rec1_pres (he.trans (ha.trans hx'))⟩

/-- `f`'s scheme has a `Merge` constraint, in every typing of the program. -/
theorem spreadMerge_needed {s : Scheme} {F : List Nat} {τ₂ : Ty}
    (hgen : ∀ m, (∀ a ∈ F, a < m) →
      HasType ["a"] ([] ++ s.openPreds m) [] none .synth .synth spreadFn (s.open m))
    (h₂ : HasType ["a"] [] [s] none .synth .synth spreadUses τ₂) :
    ∃ p ∈ s.preds, p.cls = .merge := by
  refine Classical.byContradiction fun hno => ?_
  simp only [not_exists, not_and] at hno
  obtain ⟨m, hmF, hms⟩ : ∃ m, (∀ a ∈ F, a < m) ∧ ∀ a ∈ s.ftv, a < m :=
    ⟨maxPlusOne (F ++ s.ftv), fun a ha => lt_maxPlusOne _ (by simp [ha]),
      fun a ha => lt_maxPlusOne _ (by simp [ha])⟩
  -- The function's parameter is a record whose field's presence is known.
  obtain ⟨τ₀, e₀, ht⟩ := (hgen m hmF).top_synth
  cases ht with
  | @func _ _ _ ρ _ _ _ θ τsF hlen hbody =>
    match τsF, hlen with
    | [x], _ =>
    obtain ⟨τ₁, -, ht₁⟩ := hbody.top_synth
    cases ht₁ with
    | @spread _ _ _ _ _ ss _ ps ks τs rs hps hks hτs hss hrs _ h₂' hm =>
      match ps, ks, τs, ss, rs, hps, hks, hτs, hss, hrs with
      | [p], [k], [t], [s₀], [r], _, _, _, _, _ =>
      obtain ⟨τ₂', e₂, ht₂⟩ := h₂'.top_synth
      cases ht₂ with
      | @var _ _ _ _ _ _ τs₀ hi hl _ =>
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        have hx : TyEq x (.record ["a"] [.slot p k t]) := by
          have : (Scheme.mono x).inst τs₀ = x := by simp [Scheme.mono, Scheme.inst]
          rw [this] at e₂; exact e₂
        -- The spread's `Merge` holds by an instance: no assumption is one.
        obtain ⟨c₀, hc₀, hp⟩ : ∃ c₀ : Con, (c₀ = .pre ∨ c₀ = .abs) ∧ TyEq (.app c₀ []) p := by
          rcases hm ⟨.merge, [p, k, t, s₀, r]⟩ (by simp [mergePreds]) with ⟨q, hq, hinst⟩ | ⟨c, hc, hpc⟩
          · have hq₀ := fun a b (h : (a, b) ∈ [p, k, t, s₀, r].zip q.args) => hq.2.2 (a, b) h
            cases hinst with
            | mergeData => exact ⟨.pre, .inl rfl, (hq₀ p .pre (by simp)).symm⟩
            | mergeGetter => exact ⟨.pre, .inl rfl, (hq₀ p .pre (by simp)).symm⟩
            | mergeAbs _ => exact ⟨.abs, .inr rfl, (hq₀ p .abs (by simp)).symm⟩
            | mergeProto _ => exact ⟨.pre, .inl rfl, (hq₀ p .pre (by simp)).symm⟩
            | _ => obtain ⟨hcls, -, -⟩ := hq; cases hcls
          · simp only [List.nil_append, Scheme.openPreds, Scheme.instPreds, List.mem_map] at hc
            obtain ⟨pp, hpp, rfl⟩ := hc
            exact (hno pp hpp (by have := hpc.1; simp [PPred.inst] at this; exact this.symm)).elim
        -- Each call fixes that presence: present, then absent.
        obtain ⟨τ₃, -, ht₃⟩ := h₂.top_synth
        cases ht₃ with
        | seq hu₁ hu₂ =>
          obtain ⟨τu, hu₁', -⟩ := hu₁.inj_inv rfl
          obtain ⟨φ₁, h₁⟩ := call_pres hms e₀ (c₀ := .pre) (fun τa ha => by
            obtain ⟨τa', ea, hta⟩ := ha.top_synth
            cases hta with
            | @obj _ _ _ _ _ ss' _ _ τs' hes hks' hτs' hss' _ _ hfs =>
              match τs', ss', hτs', hss' with
              | [τ₁'], [s₁], _, _ =>
                have hf : FieldSlot _ .data (.lit (.number 1)) τ₁' s₁ :=
                  hfs (.data, .lit (.number 1), τ₁', s₁) (by simp)
                cases hf
                exact ⟨_, _, by simpa [objSlots, Ty.field] using ea⟩) hu₁' hx
          obtain ⟨φ₂, h₂⟩ := call_pres hms e₀ (c₀ := .abs) (fun τa ha => by
            obtain ⟨τa', ea, hta⟩ := ha.top_synth
            cases hta with
            | @obj _ _ _ _ _ ss' _ _ τs' hes hks' hτs' hss' _ _ _ =>
              match τs', ss', hτs', hss' with
              | [], [], _, _ => exact ⟨_, _, by simpa [objSlots, Ty.field] using ea⟩) hu₂ hx
          have hp₁ := h₁.trans (TyEq.subst φ₁ hp).symm
          have hp₂ := h₂.trans (TyEq.subst φ₂ hp).symm
          simp only [Ty.subst_app, List.map_nil] at hp₁ hp₂
          have := (TyEq.con hp₁).trans (TyEq.con hp₂).symm
          cases this

/-- So in every typing of the program, `f`'s scheme keeps a `Merge`. -/
theorem spreadMerge_every_typing {τ : Ty}
    (h : HasType ["a"] [] [] none .synth .synth spreadMerge τ) :
    ∃ s : Scheme, (∃ p ∈ s.preds, p.cls = .merge) ∧
      ∃ τ₂, HasType ["a"] [] [s] none .synth .synth spreadUses τ₂ := by
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | let_ s F hgen _ _ _ h₂ => exact ⟨s, spreadMerge_needed hgen h₂, _, h₂⟩

end Inty
