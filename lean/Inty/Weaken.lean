import Inty.Typing
import Inty.TreeVars

/-!
# A more general context

Typing survives replacing each scheme in the context by a more general one
(`Generalizes`, up to equal types), and the enclosing function's return
type by an equal one, as long as a variable the expression assigns keeps a
monotype: an assignment needs its variable's scheme to be one. Inference's
context is more general than a typing's, which is how its completeness
proof relates the two (`Inty.InferComplete`).
-/

namespace Inty

/-- `s'` is at least as general as `s` under the assumptions `C`: each
instance of `s` is equal to an instance of `s'`, whose constraints follow
from `s`'s and `C`. -/
def Generalizes (C : List Pred) (s' s : Scheme) : Prop :=
  ∀ τs, τs.length = s.arity → ∃ τs', τs'.length = s'.arity ∧ TyEq (s'.inst τs') (s.inst τs) ∧
    ∀ c ∈ s'.instPreds τs', Entails (C ++ s.instPreds τs) c

theorem Generalizes.refl (C : List Pred) (s : Scheme) : Generalizes C s s :=
  fun τs hl => ⟨τs, hl, TyEq.refl _, fun _ hc => Entails.of_mem (List.mem_append_right _ hc)⟩

theorem Generalizes.weaken {C D : List Pred} {s' s : Scheme} (h : Generalizes C s' s)
    (hCD : ∀ c ∈ C, c ∈ D) : Generalizes D s' s := fun τs hl => by
  obtain ⟨τs', hl', he, hc⟩ := h τs hl
  refine ⟨τs', hl', he, fun c h => (hc c h).weaken (fun d hd => ?_)⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact List.mem_append_left _ (hCD d hd)
  · exact List.mem_append_right _ hd

/-- Equal return types. -/
def RetEq : Option Ty → Option Ty → Prop
  | none, none => True
  | some τ, some τ' => TyEq τ τ'
  | _, _ => False

theorem RetEq.refl : ∀ R : Option Ty, RetEq R R
  | none => trivial
  | some τ => TyEq.refl τ

/-- `Γ'` is at least as general as `Γ`, scheme by scheme, under `C`, and a
variable `e` assigns has a monotype in `Γ'` if it has one in `Γ`. -/
def CtxGen (C : List Pred) (e : Expr) (Γ Γ' : Ctx) : Prop :=
  Γ.length = Γ'.length ∧ ∀ i s s', Γ[i]? = some s → Γ'[i]? = some s' →
    Generalizes C s' s ∧
      ((s.arity = 0 ∧ s.preds = [] → s'.arity = 0 ∧ s'.preds = []) ∨ e.writes i = false)

theorem CtxGen.weaken {C D : List Pred} {e : Expr} {Γ Γ' : Ctx} (h : CtxGen C e Γ Γ')
    (hCD : ∀ c ∈ C, c ∈ D) : CtxGen D e Γ Γ' :=
  ⟨h.1, fun i s s' hs hs' => (h.2 i s s' hs hs').imp_left (·.weaken hCD)⟩

/-- For a subexpression that assigns only what the expression does. -/
theorem CtxGen.sub {C : List Pred} {e e' : Expr} {Γ Γ' : Ctx} (h : CtxGen C e Γ Γ')
    (hw : ∀ i, e.writes i = false → e'.writes i = false) : CtxGen C e' Γ Γ' :=
  ⟨h.1, fun i s s' hs hs' => (h.2 i s s' hs hs').imp_right (·.imp_right (hw i))⟩

/-- Under binders `Δ`, the same on both sides. -/
theorem CtxGen.prepend {C : List Pred} {e e' : Expr} {Δ Γ Γ' : Ctx} (h : CtxGen C e Γ Γ')
    (hΔ : ∀ j s, Δ[j]? = some s → (s.arity = 0 ∧ s.preds = []) ∨ e'.writes j = false)
    (hw : ∀ i, e.writes i = false → e'.writes (i + Δ.length) = false) :
    CtxGen C e' (Δ ++ Γ) (Δ ++ Γ') := by
  refine ⟨by simp [h.1], fun i s s' hs hs' => ?_⟩
  by_cases hi : i < Δ.length
  · rw [List.getElem?_append_left hi] at hs hs'
    rw [hs] at hs'; cases hs'
    exact ⟨Generalizes.refl C s, (hΔ i s hs).imp (fun h _ => h) id⟩
  · rw [List.getElem?_append_right (by omega)] at hs
    rw [List.getElem?_append_right (by omega)] at hs'
    obtain ⟨hg, hm⟩ := h.2 _ s s' hs hs'
    refine ⟨hg, hm.imp_right fun hwr => ?_⟩
    have := hw _ hwr
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem Scheme.mono_arity (τ : Ty) : (Scheme.mono τ).arity = 0 := rfl
theorem Scheme.mono_preds (τ : Ty) : (Scheme.mono τ).preds = [] := rfl

/-- Monotypes bind nothing assignment needs. -/
theorem monos_mono (τs : List Ty) (rest : List Scheme) (hrest : ∀ s ∈ rest, s.arity = 0 ∧ s.preds = [])
    {e : Expr} : ∀ j s, (τs.map Scheme.mono ++ rest)[j]? = some s →
      (s.arity = 0 ∧ s.preds = []) ∨ e.writes j = false := by
  intro j s hs
  left
  rcases List.mem_append.mp (List.mem_of_getElem? hs) with h | h
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.mp h; exact ⟨rfl, rfl⟩
  · exact hrest s h

theorem Expr.writesList_false' : ∀ {i : Nat} {args : List Expr}, Expr.writesList i args = false →
    ∀ a ∈ args, a.writes i = false
  | _, [], _, _, ha => by cases ha
  | _, b :: bs, h, a, ha => by
    simp only [Expr.writesList, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact Expr.writesList_false' h.2 a ha

/-- A class member's assignments: a field's initialiser sees the fields
before it. -/
theorem Expr.writesCls_false : ∀ {i d : Nat} {es : List Expr} {ks : List ClassKind},
    Expr.writesCls i d es ks = false → ∀ (j : Nat) (e : Expr) (k : ClassKind),
      es[j]? = some e → ks[j]? = some k →
      (k = .data → e.writes (i + d + ((ks.take j).filter (· == ClassKind.data)).length) = false) ∧
      (k ≠ .data → e.writes i = false)
  | _, _, [], _, _, j, e, k, he, _ => by simp at he
  | _, _, _ :: _, [], _, j, e, k, _, hk => by simp at hk
  | i, d, e₀ :: es, k₀ :: ks, h, j, e, k, he, hk => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he hk
      subst he hk
      cases k₀ with
      | data =>
        simp only [Expr.writesCls, Bool.or_eq_false_iff] at h
        exact ⟨fun _ => by simpa using h.1, fun h' => absurd rfl h'⟩
      | arrow | method | getter =>
        simp only [Expr.writesCls, Bool.or_eq_false_iff] at h
        exact ⟨fun h' => (by cases h'), fun _ => h.1⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at he hk
      cases k₀ with
      | data =>
        simp only [Expr.writesCls, Bool.or_eq_false_iff] at h
        have := Expr.writesCls_false h.2 j e k he hk
        refine ⟨fun hd => ?_, this.2⟩
        have h1 := this.1 hd
        simp only [List.take_succ_cons, List.filter_cons, BEq.rfl, ite_true, List.length_cons]
        rw [show ∀ x, i + d + (x + 1) = i + (d + 1) + x from fun x => by omega]
        exact h1
      | arrow | method | getter =>
        simp only [Expr.writesCls, Bool.or_eq_false_iff] at h
        have := Expr.writesCls_false h.2 j e k he hk
        refine ⟨fun hd => ?_, this.2⟩
        simpa [List.take_succ_cons, List.filter_cons] using this.1 hd

/-- The fields a class's member sees, counted from its kinds alone. -/
theorem memberCtx_prefix_length : ∀ {ks : List ClassKind} {τs : List Ty}, ks.length = τs.length →
    ∀ j, (((ks.zip τs).take j).filter (·.1 == ClassKind.data)).length =
      ((ks.take j).filter (· == ClassKind.data)).length
  | [], [], _, j => by simp
  | k :: ks, τ :: τs, hl, j => by
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.zip_cons_cons, List.take_succ_cons, List.filter_cons]
      have := memberCtx_prefix_length (ks := ks) (τs := τs) (by simpa using hl) j
      split <;> simp_all
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-! ## Equal schemes -/

theorem List.exists_of_zip {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ x ∈ l₁.zip l₂, R x.1 x.2) → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | a :: l₁, b' :: l₂, hl, h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, h (a, b) (by simp)⟩
    · obtain ⟨a', ha', hr⟩ := List.exists_of_zip (by simpa using hl)
        (fun x hx => h x (List.mem_cons_of_mem _ hx)) b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩
  | [], [], _, _, _, hb => by cases hb
  | [], _ :: _, hl, _, _, _ | _ :: _, [], hl, _, _, _ => by simp at hl

/-- An equal scheme is as general. -/
theorem SchemeEq.generalizes {s s' : Scheme} (h : SchemeEq s s') (C : List Pred) :
    Generalizes C s' s := fun τs hl => by
  obtain ⟨he, hp⟩ := h.2.2 τs hl
  refine ⟨τs, hl.trans h.1, he.symm, fun c hc => ?_⟩
  obtain ⟨d, hd, hdc⟩ := List.exists_of_zip (by simp [Scheme.instPreds, h.2.1]) hp c hc
  exact Entails.of_predEq hdc (.of_mem (List.mem_append_right _ hd))

theorem SchemeEq.mono {s s' : Scheme} (h : SchemeEq s s') (hm : s.arity = 0 ∧ s.preds = []) :
    s'.arity = 0 ∧ s'.preds = [] :=
  ⟨h.1 ▸ hm.1, List.eq_nil_of_length_eq_zero (h.2.1 ▸ by simp [hm.2])⟩

/-- Equal schemes, one by one, make a context as general. -/
theorem CtxGen.of_schemeEq {C : List Pred} {e : Expr} {Γ Γ' : Ctx} (hl : Γ.length = Γ'.length)
    (h : ∀ (i : Nat) s s', Γ[i]? = some s → Γ'[i]? = some s' → SchemeEq s s') : CtxGen C e Γ Γ' :=
  ⟨hl, fun i s s' hs hs' => ⟨(h i s s' hs hs').generalizes C, .inl (h i s s' hs hs').mono⟩⟩

/-- Pointwise equal schemes. -/
def CtxEq (Γ Γ' : Ctx) : Prop :=
  Γ.length = Γ'.length ∧ ∀ (i : Nat) s s', Γ[i]? = some s → Γ'[i]? = some s' → SchemeEq s s'

theorem CtxEq.refl (Γ : Ctx) : CtxEq Γ Γ :=
  ⟨rfl, fun i s s' hs hs' => by rw [hs] at hs'; cases hs'; exact SchemeEq.refl s⟩

theorem CtxEq.symm {Γ Γ' : Ctx} (h : CtxEq Γ Γ') : CtxEq Γ' Γ :=
  ⟨h.1.symm, fun i s s' hs hs' => (h.2 i s' s hs' hs).symm⟩

theorem CtxEq.trans {Γ Γ' Γ'' : Ctx} (h₁ : CtxEq Γ Γ') (h₂ : CtxEq Γ' Γ'') : CtxEq Γ Γ'' := by
  refine ⟨h₁.1.trans h₂.1, fun i s s'' hs hs'' => ?_⟩
  have hi : i < Γ'.length := h₁.1 ▸ (List.getElem?_eq_some_iff.mp hs).1
  exact (h₁.2 i s _ hs (List.getElem?_eq_getElem hi)).trans
    (h₂.2 i _ s'' (List.getElem?_eq_getElem hi) hs'')

theorem CtxEq.ctxGen {C : List Pred} {e : Expr} {Γ Γ' : Ctx} (h : CtxEq Γ Γ') : CtxGen C e Γ Γ' :=
  CtxGen.of_schemeEq h.1 h.2

theorem CtxEq.cons {s s' : Scheme} {Γ Γ' : Ctx} (hs : SchemeEq s s') (h : CtxEq Γ Γ') :
    CtxEq (s :: Γ) (s' :: Γ') := by
  refine ⟨by simp [h.1], fun i t t' ht ht' => ?_⟩
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ht ht'; subst ht ht'; exact hs
  | succ i => exact h.2 i t t' (by simpa using ht) (by simpa using ht')

/-- Substitutions agreeing on a context's tree variables give equal
contexts. -/
theorem Ctx.subst_congr_tv {σ σ' : Subst} {Γ : Ctx}
    (h : ∀ a ∈ ctxTv Γ, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    CtxEq (Ctx.subst σ Γ) (Ctx.subst σ' Γ) := by
  refine ⟨by simp [Ctx.subst], fun i s s' hs hs' => ?_⟩
  rw [Ctx.getElem?_subst] at hs hs'
  cases hg : Γ[i]? with
  | none => rw [hg] at hs; cases hs
  | some g =>
    rw [hg] at hs hs'
    simp only [Option.map_some, Option.some.injEq] at hs hs'
    subst hs hs'
    exact Scheme.subst_congr_tv (fun a ha => h a (List.mem_flatMap.mpr
      ⟨g, List.mem_of_getElem? hg, ha⟩))

/-! ## Weakening -/

/-- The context a function's body is checked in: its parameters, itself and
`this`, then the enclosing context. -/
theorem CtxGen.func {C : List Pred} {n : Nat} {body : Expr} {Γ Γ' : Ctx} {τs : List Ty} {f θ : Ty}
    (hlen : τs.length = n) (h : CtxGen C (.func n body) Γ Γ') :
    CtxGen C body (τs.map .mono ++ .mono f :: .mono θ :: Γ)
      (τs.map .mono ++ .mono f :: .mono θ :: Γ') := by
  have := h.prepend (e' := body) (Δ := τs.map .mono ++ [.mono f, .mono θ])
    (monos_mono τs [.mono f, .mono θ] (by simp [Scheme.mono]))
    (fun i hw => by simp only [Expr.writes] at hw; simpa [hlen, Nat.add_assoc] using hw)
  simpa using this

theorem CtxGen.ctor {C : List Pred} {n : Nat} {body : Expr} {Γ Γ' : Ctx} {τs : List Ty} {f θ : Ty}
    (hlen : τs.length = n) (h : CtxGen C (.ctor n body) Γ Γ') :
    CtxGen C body (τs.map .mono ++ .mono f :: .mono θ :: Γ)
      (τs.map .mono ++ .mono f :: .mono θ :: Γ') := by
  have := h.prepend (e' := body) (Δ := τs.map .mono ++ [.mono f, .mono θ])
    (monos_mono τs [.mono f, .mono θ] (by simp [Scheme.mono]))
    (fun i hw => by simp only [Expr.writes] at hw; simpa [hlen, Nat.add_assoc] using hw)
  simpa using this

theorem CtxGen.length_some {C : List Pred} {e : Expr} {Γ Γ' : Ctx} (h : CtxGen C e Γ Γ') {i : Nat}
    {s : Scheme} (hs : Γ[i]? = some s) : ∃ s', Γ'[i]? = some s' := by
  have hi : i < Γ'.length := h.1 ▸ (List.getElem?_eq_some_iff.mp hs).1
  exact ⟨Γ'[i], List.getElem?_eq_getElem hi⟩

/-- Typing survives a more general context and an equal return type. -/
theorem HasType.weaken {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {e : Expr}
    {τ : Ty} {rm md : Mode} (h : HasType L C Γ R rm md e τ) :
    ∀ {Γ' : Ctx} {R' : Option Ty}, CtxGen C e Γ Γ' → RetEq R R' → (rm = .check → R' = R) →
      HasType L C Γ' R' rm md e τ := by
  induction h with
  | lit hl => intros; exact .lit hl
  | @var Γ i s C R _ τs hi hlen hc =>
    intro Γ' R' hg _ _
    obtain ⟨s', hs'⟩ := hg.length_some hi
    obtain ⟨hgen, -⟩ := hg.2 i s s' hi hs'
    obtain ⟨τs', hl', he, hc'⟩ := hgen τs hlen
    exact .conv (.var hs' hl' (fun c h => (hc' c h).cut hc)) he
  | func hlen _ ih =>
    intro Γ' R' hg _ _
    exact .func hlen (ih (hg.func hlen) (RetEq.refl _) (fun _ => rfl))
  | funcCheck hT hT₀ hlen _ ih =>
    intro Γ' R' hg _ _
    exact .funcCheck hT hT₀ hlen (ih (hg.func hlen) (RetEq.refl _) (fun _ => rfl))
  | app _ hlen _ ihf iha =>
    intro Γ' R' hg hR hRc
    refine .app (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR hRc)
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    intro Γ' R' hg hR hRc
    refine .let_ s F (fun m hm => ih₁ m hm ((hg.weaken (fun c h => List.mem_append_left _ h)).sub
      fun i hw => by simp_all [Expr.writes]) hR hRc) hv hs ha ?_
    have := hg.prepend (Δ := [s]) (fun j s' hj => by
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          exact hv.imp id (·.2)
        | succ j => simp at hj) (fun i hw => by
          simp only [Expr.writes, Bool.or_eq_false_iff] at hw; simpa using hw.2)
    exact ih₂ (by simpa using this) hR hRc
  | @assign Γ i s C R _ e hi ha hp _ ih =>
    intro Γ' R' hg hR hRc
    obtain ⟨s', hs'⟩ := hg.length_some hi
    obtain ⟨hgen, hm⟩ := hg.2 i s s' hi hs'
    rcases hm with hm | hw
    · obtain ⟨ha', hp'⟩ := hm ⟨ha, hp⟩
      obtain ⟨τs', hl', he, -⟩ := hgen [] (by simp [ha])
      rw [ha'] at hl'
      obtain rfl := List.eq_nil_of_length_eq_zero hl'
      exact .conv (.assign hs' ha' hp' (.conv (ih (hg.sub fun j hw => by simp_all [Expr.writes]) hR hRc)
        he.symm)) he
    · simp [Expr.writes] at hw
  | cond _ _ _ ihc iht ihe =>
    intro Γ' R' hg hR hRc
    exact .cond (ihc (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (iht (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | unop hop _ ih =>
    intro Γ' R' hg hR hRc
    exact .unop hop (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | binop hop _ _ ih₁ ih₂ =>
    intro Γ' R' hg hR hRc
    exact .binop hop (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | @ret C Γ τr rm e md τ _ ih =>
    intro Γ' R' hg hR hRc
    match R', hR, rm with
    | some τr', hR, .synth => exact .ret (.conv (ih (hg.sub fun i hw => by simp_all [Expr.writes])
        (R' := some τr') hR nofun) hR)
    | some τr', _, .check =>
      obtain rfl : τr' = τr := Option.some.inj (hRc rfl)
      exact .ret (ih (hg.sub fun i hw => by simp_all [Expr.writes]) (RetEq.refl _) (fun _ => rfl))
  | throw_ _ ih =>
    intro Γ' R' hg hR hRc
    exact .throw_ (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | seq _ _ ih₁ ih₂ =>
    intro Γ' R' hg hR hRc
    exact .seq (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | while_ _ _ ihc ihb =>
    intro Γ' R' hg hR hRc
    exact .while_ (ihc (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | break_ => intros; exact .break_
  | continue_ => intros; exact .continue_
  | tryCatch _ _ ihb ihh =>
    intro Γ' R' hg hR hRc
    refine .tryCatch (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) ?_
    have := hg.prepend (Δ := [.mono .unknown]) (monos_mono [] [.mono .unknown]
        (by simp [Scheme.mono])) (fun i hw => by
          simp only [Expr.writes, Bool.or_eq_false_iff] at hw; simpa using hw.2)
    exact ihh (by simpa using this) hR hRc
  | tryFinally _ _ ihb ihf =>
    intro Γ' R' hg hR hRc
    exact .tryFinally (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | obj hes hks hτs hss hL _ hfs ih =>
    intro Γ' R' hg hR hRc
    exact .obj hes hks hτs hss hL (fun p hp => ih p hp (hg.sub fun i hw => by
      simp only [Expr.writes] at hw
      exact Expr.writesList_false' hw _ (List.of_mem_zip hp).1) hR hRc) hfs
  | @cls ls es ks τs C Γ ss R _ hes hks hτs hss hnd hL _ hms ih =>
    intro Γ' R' hg hR hRc
    refine .cls hes hks hτs hss hnd hL (fun j e k τ he hk hτ => ih j e k τ he hk hτ ?_ trivial nofun) hms
    have hw := fun i (hw : (Expr.cls ls es ks).writes i = false) => by
      simp only [Expr.writes] at hw
      exact Expr.writesCls_false hw j e k he hk
    cases k with
    | data =>
      have := hg.prepend (e' := e) (Δ := (((ks.zip τs).take j).filter (·.1 == .data)).reverse.map
        (fun p => Scheme.mono p.2)) (fun j' s' hj => .inl (by
          obtain ⟨p, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hj); exact ⟨rfl, rfl⟩))
        (fun i h => by
          have := (hw i h).1 rfl
          simp only [List.length_map, List.length_reverse]
          rw [memberCtx_prefix_length (by omega)]; simpa using this)
      simpa [memberCtx] using this
    | arrow | method | getter =>
      exact hg.sub (fun i h => (hw i h).2 (by simp))
  | ctor hlen _ ih =>
    intro Γ' R' hg _ _
    exact .ctor hlen (ih (hg.ctor hlen) (RetEq.refl _) (fun _ => rfl))
  | new_ _ hlen _ hρ hss ihf iha =>
    intro Γ' R' hg hR hRc
    refine .new_ (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR hRc) hρ hss
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | get _ hp ih =>
    intro Γ' R' hg hR hRc
    exact .get (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hp
  | set _ hp _ ihe ihv =>
    intro Γ' R' hg hR hRc
    exact .set (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hp
      (ihv (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | spread hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    intro Γ' R' hg hR hRc
    exact .spread hps hks hτs hss hrs (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hm
  | arr _ ih =>
    intro Γ' R' hg hR hRc
    exact .arr (fun a ha => ih a ha (hg.sub fun i hw => by
      simp only [Expr.writes] at hw
      exact Expr.writesList_false' hw a ha) hR hRc)
  | arrCheck hT hT₀ _ ih =>
    intro Γ' R' hg hR hRc
    exact .arrCheck hT hT₀ (fun a ha => ih a ha (hg.sub fun i hw => by
      simp only [Expr.writes] at hw
      exact Expr.writesList_false' hw a ha) hR hRc)
  | index _ _ hp ihe ihi =>
    intro Γ' R' hg hR hRc
    exact .index (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ihi (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hp
  | setIndex _ _ hp hw₀ _ ihe ihi ihv =>
    intro Γ' R' hg hR hRc
    exact .setIndex (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
      (ihi (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hp hw₀
      (ihv (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc)
  | mcall _ hp hlen _ ihe iha =>
    intro Γ' R' hg hR hRc
    refine .mcall (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR hRc) hp hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR hRc)
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | conv _ he ih =>
    intro Γ' R' hg hR hRc
    exact .conv (ih hg hR hRc) he
  | inj _ hT hi ih =>
    intro Γ' R' hg hR hRc
    exact .inj (ih hg hR hRc) hT hi

/-- An `Inject` of a type equal to its expected one, which has no type
variables, is an instance. -/
theorem Pred.inject_self {T τ : Ty} (hT : T.ftv = []) (h : TyEq τ T) :
    InstEq ⟨.inject T, [τ]⟩ :=
  InstEq.of_predEq (q := ⟨.inject T, [T]⟩)
    (PredEq.of_pairs (by simp) (zip_tyEq_cons h zip_tyEq_nil)) (Inst.injectSelf hT).instEq

/-- A derivation whose `return`s are synthesised at `ρ'` has one whose
`return`s are checked against an equal type `ρ` with no type variables:
each returned value is injected into it (`HasType.inj`, `Inst.injectSelf`). -/
theorem HasType.checkRet {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {e : Expr}
    {τ : Ty} {rm md : Mode} (h : HasType L C Γ R rm md e τ) :
    ∀ {ρ' ρ : Ty}, rm = .synth → R = some ρ' → TyEq ρ' ρ → ρ.ftv = [] →
      HasType L C Γ (some ρ) .check md e τ := by
  induction h with
  | lit hl => intros; exact .lit hl
  | var hi hlen hc => intros; exact .var hi hlen hc
  | func hlen hb _ => intros; exact .func hlen hb
  | funcCheck hw hT hlen hb _ => intros; exact .funcCheck hw hT hlen hb
  | app _ hlen _ ihf iha =>
    intro ρ' ρ hm hR he hρ
    exact .app (ihf hm hR he hρ) hlen (fun p hp => iha p hp hm hR he hρ)
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    intro ρ' ρ hm hR he hρ
    exact .let_ s F (fun m hm' => ih₁ m hm' hm hR he hρ) hv hs ha (ih₂ hm hR he hρ)
  | assign hi ha hp _ ih => intro ρ' ρ hm hR he hρ; exact .assign hi ha hp (ih hm hR he hρ)
  | cond _ _ _ ihc iht ihe =>
    intro ρ' ρ hm hR he hρ
    exact .cond (ihc hm hR he hρ) (iht hm hR he hρ) (ihe hm hR he hρ)
  | unop hop _ ih => intro ρ' ρ hm hR he hρ; exact .unop hop (ih hm hR he hρ)
  | binop hop _ _ ih₁ ih₂ =>
    intro ρ' ρ hm hR he hρ; exact .binop hop (ih₁ hm hR he hρ) (ih₂ hm hR he hρ)
  | ret _ ih =>
    intro ρ' ρ hm hR he hρ
    subst hm
    cases hR
    exact .ret (.inj (ih rfl rfl he hρ) hρ (.inl (Pred.inject_self hρ he)))
  | throw_ _ ih => intro ρ' ρ hm hR he hρ; exact .throw_ (ih hm hR he hρ)
  | seq _ _ ih₁ ih₂ => intro ρ' ρ hm hR he hρ; exact .seq (ih₁ hm hR he hρ) (ih₂ hm hR he hρ)
  | while_ _ _ ihc ihb =>
    intro ρ' ρ hm hR he hρ; exact .while_ (ihc hm hR he hρ) (ihb hm hR he hρ)
  | break_ => intros; exact .break_
  | continue_ => intros; exact .continue_
  | tryCatch _ _ ihb ihh =>
    intro ρ' ρ hm hR he hρ; exact .tryCatch (ihb hm hR he hρ) (ihh hm hR he hρ)
  | tryFinally _ _ ihb ihf =>
    intro ρ' ρ hm hR he hρ; exact .tryFinally (ihb hm hR he hρ) (ihf hm hR he hρ)
  | obj hes hks hτs hss hL _ hfs ih =>
    intro ρ' ρ hm hR he hρ
    exact .obj hes hks hτs hss hL (fun p hp => ih p hp hm hR he hρ) hfs
  | cls hes hks hτs hss hnd hL hms hs _ => intros; exact .cls hes hks hτs hss hnd hL hms hs
  | ctor hlen hb _ => intros; exact .ctor hlen hb
  | new_ _ hlen _ hρ' hss ihf iha =>
    intro ρ' ρ hm hR he hρ
    exact .new_ (ihf hm hR he hρ) hlen (fun p hp => iha p hp hm hR he hρ) hρ' hss
  | get _ hp ih => intro ρ' ρ hm hR he hρ; exact .get (ih hm hR he hρ) hp
  | set _ hp _ ihe ihv =>
    intro ρ' ρ hm hR he hρ; exact .set (ihe hm hR he hρ) hp (ihv hm hR he hρ)
  | spread hps hks hτs hss hrs _ _ hmg ih₁ ih₂ =>
    intro ρ' ρ hm hR he hρ
    exact .spread hps hks hτs hss hrs (ih₁ hm hR he hρ) (ih₂ hm hR he hρ) hmg
  | arr _ ih => intro ρ' ρ hm hR he hρ; exact .arr (fun a ha => ih a ha hm hR he hρ)
  | arrCheck hw hT _ ih =>
    intro ρ' ρ hm hR he hρ; exact .arrCheck hw hT (fun a ha => ih a ha hm hR he hρ)
  | index _ _ hp ihe ihi =>
    intro ρ' ρ hm hR he hρ; exact .index (ihe hm hR he hρ) (ihi hm hR he hρ) hp
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    intro ρ' ρ hm hR he hρ
    exact .setIndex (ihe hm hR he hρ) (ihi hm hR he hρ) hp hw (ihv hm hR he hρ)
  | mcall _ hp hlen _ ihe iha =>
    intro ρ' ρ hm hR he hρ
    exact .mcall (ihe hm hR he hρ) hp hlen (fun p hp => iha p hp hm hR he hρ)
  | conv _ he' ih => intro ρ' ρ hm hR he hρ; exact .conv (ih hm hR he hρ) he'
  | inj _ hT hi ih => intro ρ' ρ hm hR he hρ; exact .inj (ih hm hR he hρ) hT hi

end Inty
