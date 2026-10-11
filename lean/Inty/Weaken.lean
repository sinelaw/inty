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
    {τ : Ty} (h : HasType L C Γ R e τ) :
    ∀ {Γ' : Ctx} {R' : Option Ty}, CtxGen C e Γ Γ' → RetEq R R' → HasType L C Γ' R' e τ := by
  induction h with
  | lit hl => intros; exact .lit hl
  | @var Γ i s C R τs hi hlen hc =>
    intro Γ' R' hg _
    obtain ⟨s', hs'⟩ := hg.length_some hi
    obtain ⟨hgen, -⟩ := hg.2 i s s' hi hs'
    obtain ⟨τs', hl', he, hc'⟩ := hgen τs hlen
    exact .conv (.var hs' hl' (fun c h => (hc' c h).cut hc)) he
  | func hlen _ ih =>
    intro Γ' R' hg _
    exact .func hlen (ih (hg.func hlen) (RetEq.refl _))
  | app _ hlen _ ihf iha =>
    intro Γ' R' hg hR
    refine .app (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR)
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    intro Γ' R' hg hR
    refine .let_ s F (fun m hm => ih₁ m hm ((hg.weaken (fun c h => List.mem_append_left _ h)).sub
      fun i hw => by simp_all [Expr.writes]) hR) hv hs ha ?_
    have := hg.prepend (Δ := [s]) (fun j s' hj => by
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          exact hv.imp id (·.2)
        | succ j => simp at hj) (fun i hw => by
          simp only [Expr.writes, Bool.or_eq_false_iff] at hw; simpa using hw.2)
    exact ih₂ (by simpa using this) hR
  | @assign Γ i s C R e hi ha hp _ ih =>
    intro Γ' R' hg hR
    obtain ⟨s', hs'⟩ := hg.length_some hi
    obtain ⟨hgen, hm⟩ := hg.2 i s s' hi hs'
    rcases hm with hm | hw
    · obtain ⟨ha', hp'⟩ := hm ⟨ha, hp⟩
      obtain ⟨τs', hl', he, -⟩ := hgen [] (by simp [ha])
      rw [ha'] at hl'
      obtain rfl := List.eq_nil_of_length_eq_zero hl'
      exact .conv (.assign hs' ha' hp' (.conv (ih (hg.sub fun j hw => by simp_all [Expr.writes]) hR)
        he.symm)) he
    · simp [Expr.writes] at hw
  | cond _ _ _ ihc iht ihe =>
    intro Γ' R' hg hR
    exact .cond (ihc (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (iht (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | unop hop _ ih =>
    intro Γ' R' hg hR
    exact .unop hop (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | binop hop _ _ ih₁ ih₂ =>
    intro Γ' R' hg hR
    exact .binop hop (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | @ret Γ e τr C τ _ ih =>
    intro Γ' R' hg hR
    match R', hR with
    | some τr', hR => exact .ret (.conv (ih (hg.sub fun i hw => by simp_all [Expr.writes])
        (R' := some τr') hR) hR)
  | throw_ _ ih =>
    intro Γ' R' hg hR
    exact .throw_ (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | seq _ _ ih₁ ih₂ =>
    intro Γ' R' hg hR
    exact .seq (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | while_ _ _ ihc ihb =>
    intro Γ' R' hg hR
    exact .while_ (ihc (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | break_ => intros; exact .break_
  | continue_ => intros; exact .continue_
  | tryCatch _ _ ihb ihh =>
    intro Γ' R' hg hR
    refine .tryCatch (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR) ?_
    have := hg.prepend (Δ := [.mono .unknown]) (monos_mono [] [.mono .unknown]
        (by simp [Scheme.mono])) (fun i hw => by
          simp only [Expr.writes, Bool.or_eq_false_iff] at hw; simpa using hw.2)
    exact ihh (by simpa using this) hR
  | tryFinally _ _ ihb ihf =>
    intro Γ' R' hg hR
    exact .tryFinally (ihb (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | obj hes hks hτs hss hL _ hfs ih =>
    intro Γ' R' hg hR
    exact .obj hes hks hτs hss hL (fun p hp => ih p hp (hg.sub fun i hw => by
      simp only [Expr.writes] at hw
      exact Expr.writesList_false' hw _ (List.of_mem_zip hp).1) hR) hfs
  | @cls ls es ks τs C Γ ss R hes hks hτs hss hnd hL _ hms ih =>
    intro Γ' R' hg hR
    refine .cls hes hks hτs hss hnd hL (fun j e k τ he hk hτ => ih j e k τ he hk hτ ?_ trivial) hms
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
    intro Γ' R' hg _
    exact .ctor hlen (ih (hg.ctor hlen) (RetEq.refl _))
  | new_ _ hlen _ hρ hss ihf iha =>
    intro Γ' R' hg hR
    refine .new_ (ihf (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR) hρ hss
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | get _ hp ih =>
    intro Γ' R' hg hR
    exact .get (ih (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hp
  | set _ hp _ ihe ihv =>
    intro Γ' R' hg hR
    exact .set (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hp
      (ihv (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | spread hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    intro Γ' R' hg hR
    exact .spread hps hks hτs hss hrs (ih₁ (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ih₂ (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hm
  | arr _ ih =>
    intro Γ' R' hg hR
    exact .arr (fun a ha => ih a ha (hg.sub fun i hw => by
      simp only [Expr.writes] at hw
      exact Expr.writesList_false' hw a ha) hR)
  | index _ _ hp ihe ihi =>
    intro Γ' R' hg hR
    exact .index (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ihi (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hp
  | setIndex _ _ hp hw₀ _ ihe ihi ihv =>
    intro Γ' R' hg hR
    exact .setIndex (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
      (ihi (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hp hw₀
      (ihv (hg.sub fun i hw => by simp_all [Expr.writes]) hR)
  | mcall _ hp hlen _ ihe iha =>
    intro Γ' R' hg hR
    refine .mcall (ihe (hg.sub fun i hw => by simp_all [Expr.writes]) hR) hp hlen
      (fun p hp => iha p hp (hg.sub fun i hw => ?_) hR)
    simp only [Expr.writes, Bool.or_eq_false_iff] at hw
    exact Expr.writesList_false' hw.2 _ (List.of_mem_zip hp).1
  | conv _ he ih =>
    intro Γ' R' hg hR
    exact .conv (ih hg hR) he

end Inty
