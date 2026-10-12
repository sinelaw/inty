import Inty.Builtins
import Inty.InferComplete

/-!
# Pinned statements

The theorems' proofs are checked by Lean, but a theorem can be weakened
without anyone noticing: a hypothesis added, a conclusion dropped. Each
`example` here restates a headline theorem in full, so changing its
statement breaks the build until the statement here is changed too, in the
same diff, where a reviewer sees it.

The rejected programs pin the other direction: the typing rules must not
quietly become too permissive.
-/

namespace Inty.Statements

open Inty

/-! ## Headline theorems -/

example : ∀ (clock : Nat) {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode}
    {W : World} {env : Env} {h : Heap} {e : Expr} {τ : Ty}, HasType L C Γ R rm md e τ → HoldsOrVar C →
      G W (Γ.map Scheme.toW) env → HeapOK clock W h →
      (run clock env h e).2.1 ≤ clock ∧
      ((run clock env h e).1 = .timeout ∨ ∃ W', W <+: W' ∧
        HeapOK (run clock env h e).2.1 W' (run clock env h e).2.2 ∧
        ((∃ v, (run clock env h e).1 = .ok v ∧ V (run clock env h e).2.1 W' τ v) ∨
          (run clock env h e).1.Abrupt ∨
          (∃ v, (run clock env h e).1 = .returned v ∧
            ∃ τr, R = some τr ∧ V (run clock env h e).2.1 W' τr v))) :=
  fun clock _ _ _ _ _ _ _ _ _ _ _ ht hC hG hH => eval_sound clock ht hC hG hH

example : ∀ {L : List String} {C : List Pred} {rm md : Mode} {e : Expr} {τ : Ty},
    HasType L C [] none rm md e τ → HoldsOrVar C → ∀ (clock : Nat) (s : Stuck),
      eval clock [] [] e ≠ .stuck s :=
  never_stuck

example : ∀ {L : List String} {C : List Pred} {rm md : Mode} {e : Expr} {τ : Ty},
    HasType L C builtinCtx none rm md e τ → HoldsOrVar C →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  never_stuck_with_builtins

example : ∀ {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode} {e : Expr}
    {τ : Ty} (σ : Subst), HasType L C Γ R rm md e τ →
      HasType L (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) rm md e
        (τ.subst σ) :=
  fun σ h => h.subst Sys.narrow_substable σ

example : ∀ {τ₁ τ₂ : Ty} {σ : Subst}, unify τ₁ τ₂ = some σ → TyEq (τ₁.subst σ) (τ₂.subst σ) :=
  unify_sound

example : ∀ {τ₁ τ₂ : Ty} {ψ : Subst}, TyEq (τ₁.subst ψ) (τ₂.subst ψ) →
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, TyEq ((τ.subst σ).subst ψ) (τ.subst ψ) :=
  unify_mgu

example : ∀ {L : List String} {e : Expr} {Γ : Ctx} {R : Option Ty} {rm : Mode} {ex : Option Ty}
    {n : Nat} {o : Out}, infer L Γ R rm ex e n = some o →
    (rm = .check → ∀ τ ∈ R, τ.ftv = []) → (∀ T ∈ ex, T.ftv = []) →
    ∀ φ C, (∀ c ∈ o.preds, Entails C (c.subst φ)) →
      HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) rm (exMode ex e) e
        (o.τ.subst φ) :=
  infer_sound

example : exMode ex e = if ∃ T ∈ ex, e.pushes T then .check else .synth := by
  cases ex <;> simp [exMode]

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∃ C, HoldsOrVar C ∧ HasType e.labels.eraseDups C [] none .synth .synth e τ :=
  inferProgram_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock [] [] e ≠ .stuck s :=
  inferProgram_never_stuck

example : ∀ {L : List String} {e : Expr} {τ : Ty}, inferIn L builtinCtx e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  inferIn_builtins_never_stuck

example : ∀ (L : List String) (e : Expr), e.monoAnn = true → ∀ {Γ : Ctx} {R : Option Ty} {rm : Mode}
    {ex : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred} {md : Mode} {τ' : Ty} {Γ' : Ctx} {R' : Option Ty},
    (rm = .check → ∀ τ ∈ R, τ.ftv = []) → (rm = .check → R' = R) → (∀ T ∈ ex, T.ftv = []) →
    md = exMode ex e ∧ (∀ T ∈ ex, e.pushes T → τ' = T) →
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
    CtxEq Γ' (Ctx.subst ψ Γ) → RetEq R' (Ret.subst ψ R) → HasType L C Γ' R' rm md e τ' →
    ∃ o, infer L Γ R rm ex e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ TyEq (o.τ.subst φ) τ' ∧
      Sat C o.preds φ :=
  infer_complete

example : ∀ {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}, ctxFtv Γ = [] →
    (∀ p ∈ C, p.OnVarShaped) → e.scoped (Γ.map fun _ => false) = true → e.monoAnn = true →
    HasType L C Γ none .synth .synth e τ' →
    ∃ τ, inferIn L Γ e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferIn_complete

example : ∀ {e : Expr} {τ' : Ty}, e.scoped [] = true → e.monoAnn = true →
    HasType e.labels.eraseDups [] [] none .synth .synth e τ' →
    ∃ τ, inferProgram e = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferProgram_complete

/-- A statement's value is dropped: an expression is checked against
`unknown`, whatever type it synthesises, and `e₁` of `e₁; e₂` is so checked. -/
example : HasType L C Γ R rm .synth e τ → HasType L C Γ R rm .check e .unknown := .drop

example : HasType L C Γ R rm .check e₁ .unknown → HasType L C Γ R rm md e₂ τ →
    HasType L C Γ R rm md (.seq e₁ e₂) τ := .seq

/-- Completeness is for programs whose annotations are all monomorphic. -/
example : (Expr.let_ m ann e₁ e₂).monoAnn =
    ((ann.all fun a => a.arity == 0) && e₁.monoAnn && e₂.monoAnn) := by
  simp [Expr.monoAnn]

example : Agree n σ φ ψ ↔ ∀ a < n, TyEq (((Ty.var a).subst σ).subst φ) ((Ty.var a).subst ψ) :=
  Iff.rfl

example : SchemeEq s s' ↔ s.arity = s'.arity ∧ s.preds.length = s'.preds.length ∧
    ∀ τs, τs.length = s.arity → TyEq (s.inst τs) (s'.inst τs) ∧
      ∀ x ∈ (s.instPreds τs).zip (s'.instPreds τs), PredEq x.1 x.2 := Iff.rfl

example : Pred.OnVarShaped p ↔
    (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
      ∃ q k τ s r, p = ⟨.merge, [q, k, τ, s, r]⟩ ∧ ((∃ a, q = .var a) ∨ p.MergeOnVar) := Iff.rfl

example : Pred.AssumableAt top p ↔
    (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
      ∃ q k τ s r, p = ⟨.merge, [q, k, τ, s, r]⟩ ∧
        (top = true → (∃ a, q = .var a) ∨ p.MergeOnVar) := Iff.rfl

example : Cls.arity c = match c with
    | .plus | .indexWrite | .notNew | .inject _ => 1
    | .strip | .injectW => 2
    | .hasProp _ | .indexable | .caseTag _ _ => 3
    | .merge => 5 := by
  cases c <;> rfl

example : ∀ (c : Nat) (env : Env) (h : Heap) (e : Expr), (run c env h e).2.1 ≤ c :=
  run_clock_le

example : ∀ (c : Nat) (env : Env) (h : Heap) (e : Expr) (k : Nat), (run c env h e).1 ≠ .timeout →
    run (c + k) env h e = ((run c env h e).1, (run c env h e).2.1 + k, (run c env h e).2.2) :=
  run_mono

example : ∀ (n : Nat) {env : Env} {h : Heap} {e : Expr} (k : Nat), eval n env h e ≠ .timeout →
    eval (n + k) env h e = eval n env h e :=
  eval_mono

/-! ## The value relation

`eval_sound` is only as strong as `V`: a `V` that holds of everything would
make it trivial. So its clauses are pinned too. -/

example : V k W .number v ↔ ∃ n, v = .number n := V_number
example : V k W .string v ↔ ∃ s, v = .string s := V_string
example : V k W .boolean v ↔ ∃ b, v = .boolean b := V_boolean
example : V k W .undefined v ↔ v = .undefined := V_undefined
example : V k W .null v ↔ v = .null := V_null
example : V k W .unknown v ↔ True := V_unknown
example : V k W (.var a) v ↔ False := V_var
example : V k W (.record ls slots) v ↔ ∃ ℓ τc, v = .obj ℓ ∧
    W[ℓ]? = some (.obj τc) ∧ TyEq (.record ls slots) τc := V_record
example : V k W (.array τ) v ↔ ∃ ℓ τc, v = .arr ℓ ∧ W[ℓ]? = some (.arr τc) ∧ TyEq τ τc :=
  V_array
example : V k W (.mu i sys) v ↔
    ∃ c args, (Ty.mu i sys).view = some (.app c args) ∧ V k W (.app c args) v := V_mu
example : CellV k W (.obj (.record ls slots)) v ↔ ∃ fs, v = .fields fs ∧
    (∀ l s, Ty.field l ls slots = some s → MemberP (V k W) (.record ls slots) fs l s) ∧
    ∀ l, Ty.field l ls slots = none → fs.lookup l = none := CellV_obj
example : MemberP P T fs l s ↔
    (∃ σ, TyEq s (.slot .pre .data σ) ∧ ∃ v, fs.lookup l = some (.data, v) ∧ P σ v) ∨
    (∃ σ, TyEq s (.slot .pre .getter σ) ∧ ∃ g, fs.lookup l = some (.getter, g) ∧
      P (.fn T [] σ) g) ∨
    (∃ σ, TyEq s (.slot .pre .proto σ) ∧
      ((∃ v, fs.lookup l = some (.method, v) ∧ P σ v) ∨
       (∃ g, fs.lookup l = some (.protoGetter, g) ∧ P (.fn T [] σ) g))) ∨
    (∃ k σ, TyEq s (.slot .abs k σ) ∧ fs.lookup l = none) := Iff.rfl
example : CellV k W (.obj (.var a)) v ↔ False := Iff.rfl
example : CellV k W (.arr τ) v ↔ ∃ vs, v = .items vs ∧ ∀ w ∈ vs, V k W τ w := CellV_arr
example : CellV k W (.scheme s) v ↔
    ∀ τs, τs.length = s.arity → HoldsOrVarW (s.instPreds τs) → V k W (s.inst τs) v := Iff.rfl
example : Result.Abrupt r ↔
    (∃ v, r = .thrown v) ∨ r = .broke ∨ r = .continued ∨ ∃ f, r = .fault f := by
  cases r <;> simp [Result.Abrupt] <;> exact ⟨.outOfBounds, trivial⟩
example : V k W (.fn θ τs ρ) f ↔ (TyEq θ .newTarget → f.isCtor = true) ∧
    ∀ j ≤ k, ∀ W', W <+: W' → ∀ h thisv args,
    args.length = τs.length → (∀ i < j, HeapOK i W' h) → (∀ i < j, V i W' θ thisv) →
    (∀ i < j, VList i W' τs args) →
    (call j h f thisv args).2.1 ≤ j ∧ ((call j h f thisv args).1 = .timeout ∨
      ((call j h f thisv args).2.1 < j ∧ ∃ W'', W' <+: W'' ∧
        HeapOK (call j h f thisv args).2.1 W'' (call j h f thisv args).2.2 ∧
        ((∃ v, (call j h f thisv args).1 = .ok v ∧ V (call j h f thisv args).2.1 W'' ρ v) ∨
          (call j h f thisv args).1.Abrupt))) := by
  rw [V_fn]
  constructor
  · rintro ⟨hn, H⟩
    refine ⟨hn, ?_⟩
    intro j hj W' hW h thisv args hl hh ht ha
    obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H j hj W' hW h thisv args hl hh ht ha
    · exact ⟨hc, .inl H⟩
    · exact ⟨hc, .inr ⟨hlt, W'', hW'', hH hlt, hr.imp (fun ⟨v, e, hv⟩ => ⟨v, e, hv hlt⟩) id⟩⟩
  · rintro ⟨hn, H⟩
    refine ⟨hn, ?_⟩
    intro j hj W' hW h thisv args hl hh ht ha
    obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H j hj W' hW h thisv args hl hh ht ha
    · exact ⟨hc, .inl H⟩
    · exact ⟨hc, .inr ⟨hlt, W'', hW'', fun _ => hH,
        hr.imp (fun ⟨v, e, hv⟩ => ⟨v, e, fun _ => hv⟩) id⟩⟩
example : VList k W [] vs ↔ vs = [] := by cases vs <;> simp
example : VList k W (τ :: τs) vs ↔ ∃ v vs', vs = v :: vs' ∧ V k W τ v ∧ VList k W τs vs' := by
  cases vs with
  | nil => simp
  | cons v vs =>
    simp only [VList_cons]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨v, vs, rfl, h₁, h₂⟩, fun ⟨_, _, e, h₁, h₂⟩ => by
      cases e; exact ⟨h₁, h₂⟩⟩
example : HeapOK k W h ↔ h.length = W.length ∧ ∀ (ℓ : Nat) c, W[ℓ]? = some c →
    ∃ v, h[ℓ]? = some v ∧ CellV k W c v := Iff.rfl
example : G W (s :: Γ) (ℓ :: env) ↔ W[ℓ]? = some (.scheme s) ∧ G W Γ env := Iff.rfl
example : G W [] env ↔ env = [] := by cases env <;> simp [G]

/-! ## The class instances

As with `V`, a larger instance table weakens what `eval_sound` says. -/

example : Entails C p ↔ (∃ q, PredEq p q ∧ Inst q) ∨ ∃ q ∈ C, PredEq p q := Iff.rfl
example : PredEq p q ↔ p.cls = q.cls ∧ p.args.length = q.args.length ∧
    ∀ x ∈ p.args.zip q.args, TyEq x.1 x.2 := Iff.rfl
example : TyEq s t ↔ ∀ n, s.approx n = t.approx n := Iff.rfl

example : SlotCopy s r ↔ (∃ τ, s = .slot .pre .data τ ∧ r = .slot .pre .data τ) ∨
    (∃ τ, s = .slot .pre .getter τ ∧ r = .slot .pre .data τ) ∨
    (∃ τ, s = .slot .pre .proto τ ∧ r = .absSlot) ∨ (∃ k τ, s = .slot .abs k τ ∧ r = s) :=
  ⟨fun h => by
    cases h with
    | data => exact .inl ⟨_, rfl, rfl⟩
    | getter => exact .inr (.inl ⟨_, rfl, rfl⟩)
    | proto => exact .inr (.inr (.inl ⟨_, rfl, rfl⟩))
    | abs => exact .inr (.inr (.inr ⟨_, _, rfl, rfl⟩)),
   fun h => by
    rcases h with ⟨τ, rfl, rfl⟩ | ⟨τ, rfl, rfl⟩ | ⟨τ, rfl, rfl⟩ | ⟨k, τ, rfl, rfl⟩
    · exact .data
    · exact .getter
    · exact .proto
    · exact .abs⟩

example : Inst p ↔ p = ⟨.plus, [.number]⟩ ∨ p = ⟨.plus, [.string]⟩ ∨
    (∃ l ls fs k σ, Ty.field l ls fs = some (.slot .pre k σ) ∧
      p = ⟨.hasProp l, [.record ls fs, k, σ]⟩) ∨
    (∃ τ s, p = ⟨.merge, [.pre, .data, τ, s, .slot .pre .data τ]⟩) ∨
    (∃ τ s, p = ⟨.merge, [.pre, .getter, τ, s, .slot .pre .data τ]⟩) ∨
    (∃ k τ s r, SlotCopy s r ∧ p = ⟨.merge, [.abs, k, τ, s, r]⟩) ∨
    (∃ τ s r, SlotCopy s r ∧ p = ⟨.merge, [.pre, .proto, τ, s, r]⟩) ∨
    (∃ τ, p = ⟨.hasProp "length", [.array τ, .getter, .number]⟩) ∨
    p = ⟨.hasProp "length", [.string, .getter, .number]⟩ ∨
    (∃ τ, p = ⟨.indexable, [.array τ, .number, τ]⟩) ∨
    p = ⟨.indexable, [.string, .number, .string]⟩ ∨
    (∃ τ, p = ⟨.indexWrite, [.array τ]⟩) ∨
    (∃ c args, ¬ (c = .newTarget ∨ c.isRigid) ∧ p = ⟨.notNew, [.app c args]⟩) ∨
    (∃ T, T.ftv = [] ∧ p = ⟨.inject T, [T]⟩) ∨
    (∃ T z σ, TyEq T (.maybe z σ) ∧ T.ftv = [] ∧ p = ⟨.inject T, [z.ty]⟩) ∨
    (∃ T z c args, TyEq T (.maybe z (.app c args)) ∧ T.ftv = [] ∧ (Ty.app c args).ftv = [] ∧
      c ≠ .maybe z ∧ ¬ (c = z.con ∧ args = []) ∧ p = ⟨.inject T, [.app c args]⟩) ∨
    (∃ z σ, p = ⟨.strip, [.maybe z σ, σ]⟩) ∨
    (∃ c args, (∀ z, c ≠ .maybe z) ∧ c ≠ .null ∧ c ≠ .undefined ∧
      p = ⟨.strip, [.app c args, .app c args]⟩) ∨
    ∃ l ts Rs t R, ∃ i : Nat, ts.Nodup ∧ ts[i]? = some t ∧ Rs[i]? = some R ∧
      p = ⟨.caseTag l t, [.variant l ts Rs, R, variantRest l (ts.eraseIdx i) (Rs.eraseIdx i)]⟩ :=
  ⟨fun h => by
    cases h with
    | plusNumber => exact .inl rfl
    | plusString => exact .inr (.inl rfl)
    | hasProp hf => exact .inr (.inr (.inl ⟨_, _, _, _, _, hf, rfl⟩))
    | mergeData => exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    | mergeGetter => exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
    | mergeAbs hc => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, hc, rfl⟩)))))
    | mergeProto hc => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, hc, rfl⟩))))))
    | lengthArray => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))
    | lengthString => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
    | indexArray =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))
    | indexString =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))))
    | writeArray =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))))
    | notNew hc =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, hc, rfl⟩))))))))))))
    | injectSelf hT =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, hT, rfl⟩)))))))))))))
    | injectNothing he hT =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, he, hT, rfl⟩))))))))))))))
    | injectSome he hT ha hc hn =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, he, hT, ha, hc, hn, rfl⟩)))))))))))))))
    | stripSome =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))))))))))))))
    | stripSelf hm hn hu =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, hm, hn, hu, rfl⟩)))))))))))))))))
    | caseHit hn hi hR =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, _, _, _, _, hn, hi, hR, rfl⟩))))))))))))))))),
   fun h => by
    rcases h with rfl | rfl | ⟨l, ls, fs, k, σ, hf, rfl⟩ | ⟨τ, s, rfl⟩ | ⟨τ, s, rfl⟩ |
      ⟨k, τ, s, r, hc, rfl⟩ | ⟨τ, s, r, hc, rfl⟩ | ⟨τ, rfl⟩ | rfl | ⟨τ, rfl⟩ | rfl | ⟨τ, rfl⟩ |
      ⟨c, args, hc, rfl⟩ | ⟨T, hT, rfl⟩ | ⟨T, z, σ, he, hT, rfl⟩ |
      ⟨T, z, c, args, he, hT, ha, hc, hn, rfl⟩ | ⟨z, σ, rfl⟩ | ⟨c, args, hm, hn, hu, rfl⟩ |
      ⟨l, ts, Rs, t, R, i, hnd, hi, hR, rfl⟩
    · exact .plusNumber
    · exact .plusString
    · exact .hasProp hf
    · exact .mergeData
    · exact .mergeGetter
    · exact .mergeAbs hc
    · exact .mergeProto hc
    · exact .lengthArray
    · exact .lengthString
    · exact .indexArray
    · exact .indexString
    · exact .writeArray
    · exact .notNew hc
    · exact .injectSelf hT
    · exact .injectNothing he hT
    · exact .injectSome he hT ha hc hn
    · exact .stripSome
    · exact .stripSelf hm hn hu
    · exact .caseHit hnd hi hR⟩

/-- A constraint left on a type variable, or a `Merge` waiting on one (each
looked at unfolded), is all `HoldsOrVar` allows beside the instances. -/
example : HoldsOrVar C ↔ ∀ p ∈ C, (∃ q, PredEq p q ∧ Inst q) ∨
    (∃ t a rest, p.args = t :: rest ∧ t.whnf = .var a) ∨ p.MergeOnVar :=
  Iff.rfl

example : Pred.MergeOnVar p ↔ match p with
    | ⟨.merge, [q, k, _, s, _]⟩ =>
      (q.whnf = .pre ∧ ∃ a, k.whnf = .var a) ∨
        (((q.whnf = .pre ∧ k.whnf = .proto) ∨ q.whnf = .abs) ∧ s.SlotOnVar)
    | _ => False := Iff.rfl

example : Ty.SlotOnVar s ↔ match s.whnf with
    | .var _ => True
    | .slot p k _ => (∃ a, p.whnf = .var a) ∨ (p.whnf = .pre ∧ ∃ a, k.whnf = .var a)
    | _ => False := Iff.rfl

/-- A simple scheme's constraint is on one of its variables, or is a `Merge`
with one of them in the trees of its determining arguments. -/
example : Scheme.Simple s ↔ ∀ p ∈ s.preds, (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧
      ∃ i < s.arity, ∃ rest, p.args = .bound i :: rest) ∨
    ∃ q k τ t r, p = ⟨.merge, [q, k, τ, t, r]⟩ ∧
      ∃ i < s.arity, ∃ x ∈ [q, k, τ, t], x.TreeBound s.arity i := Iff.rfl

example : PTy.TreeBound k p i ↔
    (p.inst (varBlock (maxPlusOne p.ftv) k)).TV (maxPlusOne p.ftv + i) := Iff.rfl

example : Ty.TV τ a ↔ ∃ n, (τ.approx n).HasVar a := Iff.rfl

example : ∀ {τ : Ty} {a : Nat}, a ∈ τ.tv ↔ τ.TV a := Ty.mem_tv

/-- The builtins' types, which their soundness proofs establish. -/
example : builtinCtx =
    [⟨1, .fn .undefined [.bound 0] .boolean, []⟩, .mono (.fn .undefined [.number] .number)] :=
  rfl

/-- An object literal's field written as a method is a function expression
whose `this` is the literal's type, up to unfolding; a getter's is too, of
no parameters, and its slot is what it gives. -/
example : FieldSlot T k e τ s ↔ (k = .data ∧ s = .slot .pre .data τ) ∨
    (k = .method ∧ ∃ n b θ ps ρ, e = .func n b ∧ τ = .fn θ ps ρ ∧ s = .slot .pre .data τ ∧
      TyEq θ T) ∨
    (k = .getter ∧ ∃ b θ σ, e = .func 0 b ∧ τ = .fn θ [] σ ∧ s = .slot .pre .getter σ ∧
      TyEq θ T) :=
  ⟨fun h => by
    cases h with
    | data => exact .inl ⟨rfl, rfl⟩
    | method he => exact .inr (.inl ⟨rfl, _, _, _, _, _, rfl, rfl, rfl, he⟩)
    | getter he => exact .inr (.inr ⟨rfl, _, _, _, rfl, rfl, rfl, he⟩),
   fun h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, n, b, θ, ps, ρ, rfl, rfl, rfl, he⟩ |
      ⟨rfl, b, θ, σ, rfl, rfl, rfl, he⟩
    · exact .data
    · exact .method he
    · exact .getter he⟩

/-- A class's member: a field holds a value; an arrow field is a function
of the instance's `this`, bound to it, so callable with any, but not by
`new`; a method and a getter are on the prototype, of the instance's
`this`. -/
example : MemberSlot C T k e τ s ↔ (k = .data ∧ s = .slot .pre .data τ) ∨
    (k = .arrow ∧ ∃ n b θ θ' ps ρ, e = .func n b ∧ τ = .fn θ ps ρ ∧
      s = .slot .pre .data (.fn θ' ps ρ) ∧ TyEq θ T ∧ Entails C ⟨.notNew, [θ']⟩) ∨
    (k = .method ∧ ∃ n b θ ps ρ, e = .func n b ∧ τ = .fn θ ps ρ ∧
      s = .slot .pre .proto τ ∧ TyEq θ T) ∨
    (k = .getter ∧ ∃ b θ σ, e = .func 0 b ∧ τ = .fn θ [] σ ∧ s = .slot .pre .proto σ ∧
      TyEq θ T) :=
  ⟨fun h => by
    cases h with
    | data => exact .inl ⟨rfl, rfl⟩
    | arrow he hn => exact .inr (.inl ⟨rfl, _, _, _, _, _, _, rfl, rfl, rfl, he, hn⟩)
    | method he => exact .inr (.inr (.inl ⟨rfl, _, _, _, _, _, rfl, rfl, rfl, he⟩))
    | getter he => exact .inr (.inr (.inr ⟨rfl, _, _, _, rfl, rfl, rfl, he⟩)),
   fun h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, n, b, θ, θ', ps, ρ, rfl, rfl, rfl, he, hn⟩ |
      ⟨rfl, n, b, θ, ps, ρ, rfl, rfl, rfl, he⟩ | ⟨rfl, b, θ, σ, rfl, rfl, rfl, he⟩
    · exact .data
    · exact .arrow he hn
    · exact .method he
    · exact .getter he⟩

/-! ## Programs the typing rules reject -/

private def num (n : Float) : Expr := .lit (.number n)
private def str (s : String) : Expr := .lit (.string s)

/-- `break;` outside a loop is rejected, by the scope check, as JavaScript
rejects it. -/
example : Expr.break_.scoped [] = false := rfl

/-- `const x = 1; x = 2`: assigning to a `const` is rejected, by the scope
check beside the typing rules. -/
example : (Expr.let_ false none (num 1) (.assign 0 (num 2))).assignsMutable [] = false := rfl

/-- Distinct constructors make distinct types. -/
private theorem ne_con {c c' : Con} {ts ts' : List Ty} (h : c ≠ c') :
    ¬ TyEq (.app c ts) (.app c' ts') := fun e => h (TyEq.con e)

/-- `x = 1` for a variable whose scheme is polymorphic: an assigned variable
is a monotype. -/
example : ¬ HasType L [] [⟨1, .bound 0, []⟩] none .synth .synth (.assign 0 (num 1)) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with | assign hi ha _ _ => simp at hi; subst hi; simp at ha

/-- An unbound variable. -/
example : ¬ HasType L [] [] none .synth .synth (.var 0) τ := by
  intro h; obtain ⟨_, -, h⟩ := h.top_synth; cases h with | var hi _ _ => simp at hi

/-- `1 + "a"`: `+` never mixes a `Number` with a `String`. -/
example : ¬ HasType L [] [] none .synth .synth (.binop .plus (num 1) (str "a")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top_synth
      obtain ⟨_, e₂, h₂⟩ := h₂.top_synth
      cases h₁ with
      | lit hl =>
        cases hl
        cases h₂ with
        | lit hl => cases hl; exact ne_con (by decide) (e₁.trans e₂.symm)

/-- `true + true`: `Boolean` is not a `Plus` instance, and nothing assumes it. -/
example : ¬ HasType L [] [] none .synth .synth (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | binop hop h₁ _ =>
    cases hop with
    | plus hc =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top_synth
      cases h₁ with
      | lit hl =>
        cases hl
        rcases hc with ⟨q, hq, hi⟩ | hc
        · cases hi
          case plusNumber => exact ne_con (by decide) (e₁.trans (PredEq.one hq).2)
          case plusString => exact ne_con (by decide) (e₁.trans (PredEq.one hq).2)
          all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
        · obtain ⟨_, hm, -⟩ := hc; cases hm

/-- `"a" - 1`: `-` is `Number` only. -/
example : ¬ HasType L [] [] none .synth .synth (.binop .minus (str "a") (num 1)) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | binop hop h₁ _ =>
    cases hop
    obtain ⟨_, e₁, h₁⟩ := h₁.top_synth
    cases h₁ with | lit hl => cases hl; exact ne_con (by decide) e₁

/-- `-"a"`: unary `-` is `Number` only. -/
example : ¬ HasType L [] [] none .synth .synth (.unop .neg (str "a")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | unop hop h₁ =>
    cases hop
    obtain ⟨_, e₁, h₁⟩ := h₁.top_synth
    cases h₁ with | lit hl => cases hl; exact ne_con (by decide) e₁

/-- `({x: 1}).y`: an object literal has only its own fields. -/
example : ¬ HasType L [] [] none .synth .synth (.get (.obj ["x"] [num 1] [.data]) "y") τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | get he hp =>
    obtain ⟨_, e₁, he⟩ := he.top_synth
    cases he with
    | obj _ _ _ hss _ _ _ =>
      rcases hp with ⟨q, hq, hi⟩ | hi
      · cases hi
        case hasProp l ls fs k σ' hf =>
          obtain ⟨hcls, hτ, -, -⟩ := PredEq.three hq
          cases hcls
          obtain ⟨hc, hl, hz⟩ := TyEq.app_iff.mp (e₁.trans hτ)
          cases hc
          obtain ⟨s, hs, hss'⟩ := Ty.field_tyEq hl.symm (zip_tyEq_symm hz) hf
          have := objSlots_field hs (by rw [hss])
          obtain ⟨_, rfl⟩ := List.length_eq_one_iff.mp hss
          simp at this; subst this
          exact absurd (TyEq.slot hss').1 TyEq.pre_abs
        case lengthArray =>
          exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        case lengthString =>
          exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · obtain ⟨_, hm, -⟩ := hi; cases hm

/-- `({get x() { return 1; }}).x = 2`: a getter takes no store. -/
example : ¬ HasType L [] [] none .synth .synth
    (.set (.obj ["x"] [.func 0 (.ret (num 1))] [.getter]) "x" (num 2)) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | set he hp _ =>
    obtain ⟨_, e₁, he⟩ := he.top_synth
    cases he with
    | obj _ hks hτs hss _ _ hfs =>
      rcases hp with ⟨q, hq, hi⟩ | hi
      · cases hi
        case hasProp l ls fs k σ' hf =>
          obtain ⟨hcls, hτ, hk, -⟩ := PredEq.three hq
          cases hcls
          obtain ⟨hc, hl, hz⟩ := TyEq.app_iff.mp (e₁.trans hτ)
          cases hc
          obtain ⟨s, hs, hss'⟩ := Ty.field_tyEq hl.symm (zip_tyEq_symm hz) hf
          have := objSlots_field hs (by rw [hss])
          obtain ⟨τ₁, rfl⟩ := List.length_eq_one_iff.mp hτs
          obtain ⟨s₁, rfl⟩ := List.length_eq_one_iff.mp hss
          simp at this; subst this
          have hfs₁ := hfs (.getter, .func 0 (.ret (num 1)), τ₁, s) (by simp)
          cases hfs₁
          exact ne_con (by decide) (hk.trans (TyEq.slot hss').2.1)
        case lengthArray => exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        case lengthString => exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · obtain ⟨_, hm, -⟩ := hi; cases hm

/-- `(1).x`: a number has no fields. -/
example : ¬ HasType L [] [] none .synth .synth (.get (num 1) "x") τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | get he hp =>
    obtain ⟨_, e₁, he⟩ := he.top_synth
    cases he with
    | lit hl =>
      cases hl
      rcases hp with ⟨q, hq, hi⟩ | hi
      · cases hi
        case hasProp => exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        case lengthArray => exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        case lengthString => exact ne_con (by simp) (e₁.trans (PredEq.three hq).2.1)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · obtain ⟨_, hm, -⟩ := hi; cases hm

/-- `1(2)`: a number is not a function. -/
example : ¬ HasType L [] [] none .synth .synth (.app (num 1) [num 2]) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | app hf _ _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top_synth
    cases hf with | lit hl => cases hl; exact ne_con (by simp) e₁

/-- `"ab"[0] = "c"`: strings take no stores. -/
example : ¬ HasType L [] [] none .synth .synth (.setIndex (str "ab") (num 0) (str "c")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | setIndex he _ _ hw _ =>
    obtain ⟨_, e₁, he⟩ := he.top_synth
    cases he with
    | lit hl =>
      cases hl
      rcases hw with ⟨q, hq, hi⟩ | hi
      · cases hi
        case writeArray => exact ne_con (by simp) (e₁.trans (PredEq.one hq).2)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · obtain ⟨_, hm, -⟩ := hi; cases hm

/-- `(function f(x) { return x; })(1, 2)`: one argument per parameter. -/
example : ¬ HasType L [] [] none .synth .synth (.app (.func 1 (.var 0)) [num 1, num 2]) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | app hf hlen _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top_synth
    cases hf with
    | func hn _ =>
      have := (TyEq.app_iff.mp e₁).2.1
      simp at hlen this; omega

/-- `(function f() { return -this; })()`: a call outside a receiver makes
`this` `undefined`, which `-` doesn't take. -/
example : ¬ HasType L [] [] none .synth .synth (.app (.func 0 (.unop .neg (.var 1))) []) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | app hf _ _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top_synth
    cases hf with
    | func hn hb =>
      rw [List.length_eq_zero_iff] at hn; subst hn
      have hθ := (TyEq.app_iff.mp e₁).2.2 _ (List.mem_cons_self)
      obtain ⟨_, e₂, hb⟩ := hb.top_synth
      cases hb with
      | unop hop he =>
        cases hop
        obtain ⟨_, e₃, he⟩ := he.top_synth
        cases he with
        | var hi _ _ =>
          simp at hi; subst hi
          simp only [Scheme.mono_inst] at e₃
          exact ne_con (by simp) (hθ.symm.trans e₃)

/-! ## Variants tagged by a field -/

/-- A variant's values: one of its cases, a record with its tag. -/
example : V k W (.variant l ts Rs) v ↔ ∃ i : Nat, ∃ R t ls slots ℓ τc,
    Rs[i]? = some R ∧ ts[i]? = some t ∧ R.tagOf l = some t ∧ TyEq R (.record ls slots) ∧
      v = .obj ℓ ∧ W[ℓ]? = some (.obj τc) ∧ TyEq (.record ls slots) τc := V_variant_def

/-- What an object literal checked against `T` is checked against. -/
example : ObjCase ls es T P ↔ P = T ∨ ∃ l ts Ps t, ∃ i : Nat, T.whnf = .variant l ts Ps ∧
    litTag l ls es = some t ∧ firstIdx t ts = some i ∧ Ps[i]? = some P ∧ P.tagOf l = some t :=
  ⟨fun h => by
    cases h with
    | self => exact .inl rfl
    | variant hw hl hi hP ht => exact .inr ⟨_, _, _, _, _, hw, hl, hi, hP, ht⟩,
   fun h => by
    rcases h with rfl | ⟨l, ts, Ps, t, i, hw, hl, hi, hP, ht⟩
    · exact .self
    · exact .variant hw hl hi hP ht⟩

end Inty.Statements
