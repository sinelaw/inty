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
quietly become too permissive. And the last two sections restate every
typing rule and every equation of the interpreter, where a wrong model
would hide: a theorem about the wrong rules is still a theorem.
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

example : ∀ {L : List String} {e : Expr} {τ : Ty}, inferIn L [] e = some τ →
    ∀ clock s, eval clock [] [] e ≠ .stuck s :=
  inferIn_never_stuck

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
example : V k W (.fn θ τs ρ) f ↔ (f.typeString = "function" ∧ (TyEq θ .newTarget → f.isCtor = true)) ∧
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
    (∃ d ts Rs t R, ∃ i : Nat, ts.Nodup ∧ ts[i]? = some t ∧ Rs[i]? = some R ∧
      p = ⟨.caseTag d t, [.variant d ts Rs, R, variantRest d (ts.eraseIdx i) (Rs.eraseIdx i)]⟩) ∨
    ∃ T ts Rs c t R args, ∃ i : Nat, T.ftv = [] ∧ T.whnf = .variant .typeOf ts Rs ∧ ts.Nodup ∧
      c.typeTag = some t ∧ ts[i]? = some t ∧ Rs[i]? = some R ∧ TyEq (.app c args) R ∧
      (Ty.app c args).ftv = [] ∧ p = ⟨.inject T, [.app c args]⟩ :=
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
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, hn, hi, hR, rfl⟩))))))))))))))))))
    | injectArm hT hw hn htag hi hR he ha =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, hT, hw, hn, htag, hi, hR, he, ha, rfl⟩)))))))))))))))))),
   fun h => by
    rcases h with rfl | rfl | ⟨l, ls, fs, k, σ, hf, rfl⟩ | ⟨τ, s, rfl⟩ | ⟨τ, s, rfl⟩ |
      ⟨k, τ, s, r, hc, rfl⟩ | ⟨τ, s, r, hc, rfl⟩ | ⟨τ, rfl⟩ | rfl | ⟨τ, rfl⟩ | rfl | ⟨τ, rfl⟩ |
      ⟨c, args, hc, rfl⟩ | ⟨T, hT, rfl⟩ | ⟨T, z, σ, he, hT, rfl⟩ |
      ⟨T, z, c, args, he, hT, ha, hc, hn, rfl⟩ | ⟨z, σ, rfl⟩ | ⟨c, args, hm, hn, hu, rfl⟩ |
      ⟨l, ts, Rs, t, R, i, hnd, hi, hR, rfl⟩ |
      ⟨T, ts, Rs, c, t, R, args, i, hT, hw, hn, htag, hti, hR', he, ha, rfl⟩
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
    · exact .caseHit hnd hi hR
    · exact .injectArm hT hw hn htag hti hR' he ha⟩

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
example : V k W (.variant (.field l) ts Rs) v ↔ ∃ i : Nat, ∃ R t ls slots ℓ τc,
    Rs[i]? = some R ∧ ts[i]? = some t ∧ R.tagOf l = some t ∧ TyEq R (.record ls slots) ∧
      v = .obj ℓ ∧ W[ℓ]? = some (.obj τc) ∧ TyEq (.record ls slots) τc := V_variant_def

/-- A variant told apart by `typeof`'s values: those of a case whose
`typeof` is its tag, the case's head of a `typeof`. -/
example : V k W (.variant .typeOf ts Rs) v ↔ ∃ i : Nat, ∃ R t,
    Rs[i]? = some R ∧ ts[i]? = some t ∧ v.typeString = t ∧ R.whnf.rank = 0 ∧
      V k W R.whnf v := V_tsum_def

/-- The `typeof` of a type's head's values. -/
example : Con.typeTag c = match c with
    | .number => some "number"
    | .string | .strLit _ => some "string"
    | .boolean => some "boolean"
    | .undefined => some "undefined"
    | .null | .record _ | .array | .variant (.field _) _ => some "object"
    | .fn => some "function"
    | _ => none := by
  cases c <;> rfl

/-- What an object literal checked against `T` is checked against. -/
example : ObjCase ls es T P ↔ P = T ∨ ∃ l ts Ps t, ∃ i : Nat, T.whnf = .variant (.field l) ts Ps ∧
    litTag l ls es = some t ∧ firstIdx t ts = some i ∧ Ps[i]? = some P ∧ P.tagOf l = some t :=
  ⟨fun h => by
    cases h with
    | self => exact .inl rfl
    | variant hw hl hi hP ht => exact .inr ⟨_, _, _, _, _, hw, hl, hi, hP, ht⟩,
   fun h => by
    rcases h with rfl | ⟨l, ts, Ps, t, i, hw, hl, hi, hP, ht⟩
    · exact .self
    · exact .variant hw hl hi hP ht⟩

section Generated

-- (The printed binders keep their names, used or not.)
set_option linter.unusedVariables false

/-! ## The typing rules

Every rule of the typing judgement (`HasTypeS`), of literals' and
operators' types (`LitTy`, `UnOpTy`, `BinOpTyS`) and of an object literal's
case (`ObjCase`), restated: a rule changed, added to or dropped from these
families breaks the build here until its statement here changes too, so
a review sees each change to what the model types. (Printed by
`scripts/PrintPins.lean`.) -/

example : ∀ {S : Sys} {L : List String} {l : Lit} {τ : Ty} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode},
      LitTy l τ → HasTypeS S L C Γ R rm Mode.synth (Expr.lit l) τ :=
  @HasTypeS.lit

example : ∀ {S : Sys} {L : List String} {Γ : Ctx} {i : Nat} {s : Scheme} {C : List Pred} {R : Option Ty} {rm : Mode}
      {τs : List Ty},
      Γ[i]? = some s →
        List.length τs = Scheme.arity s →
          (∀ (c : Pred), c ∈ Scheme.instPreds s τs → EntailsS S C c) →
            HasTypeS S L C Γ R rm Mode.synth (Expr.var i) (Scheme.inst s τs) :=
  @HasTypeS.var

example : ∀ {S : Sys} {L : List String} {n : Nat} {C : List Pred} {Γ : List Scheme} {ρ : Ty} {body : Expr} {R : Option Ty}
      {rm : Mode} {θ : Ty} {τs : List Ty},
      List.length τs = n →
        HasTypeS S L C (List.map Scheme.mono τs ++ Scheme.mono (Ty.fn θ τs ρ) :: Scheme.mono θ :: Γ) (some ρ) Mode.synth
            Mode.synth body ρ →
          HasTypeS S L C Γ R rm Mode.synth (Expr.func n body) (Ty.fn θ τs ρ) :=
  @HasTypeS.func

example : ∀ {S : Sys} {L : List String} {T : Ty} {n : Nat} {C : List Pred} {Γ : List Scheme} {θ : Ty} {τs : List Ty} {ρ : Ty}
      {body : Expr} {R : Option Ty} {rm : Mode},
      Ty.whnf T = Ty.fn θ τs ρ →
        Sys.closed S T →
          List.length τs = n →
            HasTypeS S L C (List.map Scheme.mono τs ++ Scheme.mono (Ty.fn θ τs ρ) :: Scheme.mono θ :: Γ) (some ρ) Mode.check
                Mode.check body ρ →
              HasTypeS S L C Γ R rm Mode.check (Expr.func n body) T :=
  @HasTypeS.funcCheck

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {f : Expr} {τs : List Ty} {ρ : Ty}
      {args : List Expr},
      HasTypeS S L C Γ R rm Mode.synth f (Ty.fn Ty.undefined τs ρ) →
        List.length args = List.length τs →
          (∀ (p : Expr × Ty), p ∈ List.zip args τs → HasTypeS S L C Γ R rm Mode.synth (Prod.fst p) (Prod.snd p)) →
            HasTypeS S L C Γ R rm Mode.synth (Expr.app f args) ρ :=
  @HasTypeS.app

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {ann : Option Scheme} {e₁ : Expr}
      {md : Mode} {e₂ : Expr} {τ₂ : Ty} {mb : Bool} (s : Scheme) (F : List Nat),
      (∀ (m : Nat),
          (∀ (a : Nat), a ∈ F → a < m) →
            HasTypeS S L (C ++ Scheme.openPreds s m) Γ R rm (annMode ann) e₁ (Scheme.open s m)) →
        Scheme.arity s = 0 ∧ Scheme.preds s = [] ∨ Expr.IsValue e₁ ∧ Expr.writes 0 e₂ = false →
          Scheme.Simple s →
            Annotated ann s → HasTypeS S L C (s :: Γ) R rm md e₂ τ₂ → HasTypeS S L C Γ R rm md (Expr.let_ mb ann e₁ e₂) τ₂ :=
  @HasTypeS.let_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e₁ : Expr} {md : Mode} {e₂ : Expr}
      {τ₂ : Ty} {mb : Bool} (a : Scheme) (K : List Nat),
      0 < Scheme.arity a →
        Scheme.preds a = [] →
          Scheme.ftv a = [] →
            Scheme.rkeys a = [] →
              (∀ (k : Nat), ¬k ∈ K → HasTypeS S L C Γ R rm Mode.check e₁ (Scheme.inst a (rigids k (Scheme.arity a)))) →
                Expr.IsValue e₁ →
                  Expr.writes 0 e₂ = false →
                    HasTypeS S L C (a :: Γ) R rm md e₂ τ₂ → HasTypeS S L C Γ R rm md (Expr.let_ mb (some a) e₁ e₂) τ₂ :=
  @HasTypeS.letPoly

example : ∀ {S : Sys} {L : List String} {Γ : Ctx} {i : Nat} {s : Scheme} {C : List Pred} {R : Option Ty} {rm : Mode} {e : Expr},
      Γ[i]? = some s →
        Scheme.arity s = 0 →
          Scheme.preds s = [] →
            HasTypeS S L C Γ R rm Mode.synth e (Scheme.inst s []) →
              HasTypeS S L C Γ R rm Mode.synth (Expr.assign i e) (Scheme.inst s []) :=
  @HasTypeS.assign

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {c : Expr} {τc : Ty} {md : Mode}
      {t : Expr} {τ : Ty} {e : Expr},
      HasTypeS S L C Γ R rm Mode.synth c τc →
        HasTypeS S L C Γ R rm md t τ → HasTypeS S L C Γ R rm md e τ → HasTypeS S L C Γ R rm md (Expr.cond c t e) τ :=
  @HasTypeS.cond

example : ∀ {S : Sys} {L : List String} {op : UnOp} {τ₁ τ : Ty} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr},
      UnOpTy op τ₁ τ → HasTypeS S L C Γ R rm Mode.synth e τ₁ → HasTypeS S L C Γ R rm Mode.synth (Expr.unop op e) τ :=
  @HasTypeS.unop

example : ∀ {S : Sys} {L : List String} {C : List Pred} {op : BinOp} {τ₁ τ₂ τ : Ty} {Γ : Ctx} {R : Option Ty} {rm : Mode}
      {e₁ e₂ : Expr},
      BinOpTyS S C op τ₁ τ₂ τ →
        HasTypeS S L C Γ R rm Mode.synth e₁ τ₁ →
          HasTypeS S L C Γ R rm Mode.synth e₂ τ₂ → HasTypeS S L C Γ R rm Mode.synth (Expr.binop op e₁ e₂) τ :=
  @HasTypeS.binop

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {τr : Ty} {rm : Mode} {e : Expr} {md : Mode} {τ : Ty},
      HasTypeS S L C Γ (some τr) rm rm e τr → HasTypeS S L C Γ (some τr) rm md (Expr.ret e) τ :=
  @HasTypeS.ret

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τe τ : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τe → HasTypeS S L C Γ R rm Mode.synth (Expr.throw_ e) τ :=
  @HasTypeS.throw_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e₁ : Expr} {md : Mode} {e₂ : Expr}
      {τ : Ty},
      HasTypeS S L C Γ R rm Mode.check e₁ Ty.unknown →
        HasTypeS S L C Γ R rm md e₂ τ → HasTypeS S L C Γ R rm md (Expr.seq e₁ e₂) τ :=
  @HasTypeS.seq

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {c : Expr} {τc : Ty} {body : Expr},
      HasTypeS S L C Γ R rm Mode.synth c τc →
        HasTypeS S L C Γ R rm Mode.check body Ty.unknown →
          HasTypeS S L C Γ R rm Mode.synth (Expr.while_ c body) Ty.undefined :=
  @HasTypeS.while_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode} {τ : Ty},
      HasTypeS S L C Γ R rm md Expr.break_ τ :=
  @HasTypeS.break_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode} {τ : Ty},
      HasTypeS S L C Γ R rm md Expr.continue_ τ :=
  @HasTypeS.continue_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode} {body : Expr} {τ : Ty}
      {handler : Expr},
      HasTypeS S L C Γ R rm md body τ →
        HasTypeS S L C (Scheme.mono Ty.unknown :: Γ) R rm md handler τ →
          HasTypeS S L C Γ R rm md (Expr.tryCatch body handler) τ :=
  @HasTypeS.tryCatch

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode} {body : Expr} {τ : Ty}
      {fin : Expr},
      HasTypeS S L C Γ R rm md body τ →
        HasTypeS S L C Γ R rm Mode.check fin Ty.unknown → HasTypeS S L C Γ R rm md (Expr.tryFinally body fin) τ :=
  @HasTypeS.tryFinally

example : ∀ {S : Sys} {L ls : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {ss : List Ty} {es : List Expr}
      {ks : List FieldKind} {τs : List Ty},
      List.length es = List.length ls →
        List.length ks = List.length ls →
          List.length τs = List.length ls →
            List.length ss = List.length ls →
              (∀ (l : String), l ∈ ls → l ∈ L) →
                (∀ (p : Expr × Ty), p ∈ List.zip es τs → HasTypeS S L C Γ R rm Mode.synth (Prod.fst p) (Prod.snd p)) →
                  (∀ (x : FieldKind × Expr × Ty × Ty),
                      x ∈ List.zip ks (List.zip es (List.zip τs ss)) →
                        FieldSlot (Ty.record L (objSlots L ls ss)) (Prod.fst x) (Prod.fst (Prod.snd x))
                          (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) →
                    HasTypeS S L C Γ R rm Mode.synth (Expr.obj ls es ks) (Ty.record L (objSlots L ls ss)) :=
  @HasTypeS.obj

example : ∀ {S : Sys} {L ls : List String} {es : List Expr} {ks : List ClassKind} {τs : List Ty} {C : List Pred} {Γ : Ctx}
      {ss : List Ty} {R : Option Ty} {rm : Mode},
      List.length es = List.length ls →
        List.length ks = List.length ls →
          List.length τs = List.length ls →
            List.length ss = List.length ls →
              List.Nodup ls →
                (∀ (l : String), l ∈ ls → l ∈ L) →
                  (∀ (i : Nat) (e : Expr) (k : ClassKind) (τ : Ty),
                      es[i]? = some e →
                        ks[i]? = some k →
                          τs[i]? = some τ → HasTypeS S L C (memberCtx Γ ks τs i k) none Mode.synth Mode.synth e τ) →
                    (∀ (x : ClassKind × Expr × Ty × Ty),
                        x ∈ List.zip ks (List.zip es (List.zip τs ss)) →
                          MemberSlotS S C (Ty.record L (objSlots L ls ss)) (Prod.fst x) (Prod.fst (Prod.snd x))
                            (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) →
                      HasTypeS S L C Γ R rm Mode.synth (Expr.cls ls es ks) (Ty.record L (objSlots L ls ss)) :=
  @HasTypeS.cls

example : ∀ {S : Sys} {L : List String} {n : Nat} {C : List Pred} {Γ : List Scheme} {ρ : Ty} {body : Expr} {R : Option Ty}
      {rm : Mode} {τs : List Ty},
      List.length τs = n →
        HasTypeS S L C (List.map Scheme.mono τs ++ Scheme.mono (Ty.fn Ty.newTarget τs ρ) :: Scheme.mono Ty.newTarget :: Γ)
            (some ρ) Mode.synth Mode.synth body ρ →
          HasTypeS S L C Γ R rm Mode.synth (Expr.ctor n body) (Ty.fn Ty.newTarget τs ρ) :=
  @HasTypeS.ctor

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {f : Expr} {τs : List Ty} {ρ : Ty}
      {ss : List Ty} {args : List Expr},
      HasTypeS S L C Γ R rm Mode.synth f (Ty.fn Ty.newTarget τs ρ) →
        List.length args = List.length τs →
          (∀ (p : Expr × Ty), p ∈ List.zip args τs → HasTypeS S L C Γ R rm Mode.synth (Prod.fst p) (Prod.snd p)) →
            TyEq ρ (Ty.record L ss) → List.length ss = List.length L → HasTypeS S L C Γ R rm Mode.synth (Expr.new_ f args) ρ :=
  @HasTypeS.new_

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty} {l : String}
      {k σ : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        EntailsS S C { cls := Cls.hasProp l, args := [τ, k, σ] } → HasTypeS S L C Γ R rm Mode.synth (Expr.get e l) σ :=
  @HasTypeS.get

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty} {l : String}
      {σ : Ty} {v : Expr},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        EntailsS S C { cls := Cls.hasProp l, args := [τ, Ty.data, σ] } →
          HasTypeS S L C Γ R rm Mode.synth v σ → HasTypeS S L C Γ R rm Mode.synth (Expr.set e l v) σ :=
  @HasTypeS.set

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e₁ : Expr} {ss : List Ty}
      {e₂ : Expr} {ps ks τs rs : List Ty},
      List.length ps = List.length L →
        List.length ks = List.length L →
          List.length τs = List.length L →
            List.length ss = List.length L →
              List.length rs = List.length L →
                HasTypeS S L C Γ R rm Mode.synth e₁ (Ty.record L ss) →
                  HasTypeS S L C Γ R rm Mode.synth e₂ (Ty.record L (slots3 ps ks τs)) →
                    (∀ (p : Pred), p ∈ mergePreds ps ks τs ss rs → EntailsS S C p) →
                      HasTypeS S L C Γ R rm Mode.synth (Expr.spread e₁ e₂) (Ty.record L rs) :=
  @HasTypeS.spread

example : ∀ {S : Sys} {L : List String} {es : List Expr} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {τ : Ty},
      (∀ (e : Expr), e ∈ es → HasTypeS S L C Γ R rm Mode.synth e τ) →
        HasTypeS S L C Γ R rm Mode.synth (Expr.arr es) (Ty.array τ) :=
  @HasTypeS.arr

example : ∀ {S : Sys} {L : List String} {T : Ty} {es : List Expr} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {σ : Ty},
      Ty.whnf T = Ty.array σ →
        Sys.closed S T →
          (∀ (e : Expr), e ∈ es → HasTypeS S L C Γ R rm Mode.check e σ) → HasTypeS S L C Γ R rm Mode.check (Expr.arr es) T :=
  @HasTypeS.arrCheck

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty} {i : Expr}
      {ι σ : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        HasTypeS S L C Γ R rm Mode.synth i ι →
          EntailsS S C { cls := Cls.indexable, args := [τ, ι, σ] } → HasTypeS S L C Γ R rm Mode.synth (Expr.index e i) σ :=
  @HasTypeS.index

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty} {i : Expr}
      {ι σ : Ty} {v : Expr},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        HasTypeS S L C Γ R rm Mode.synth i ι →
          EntailsS S C { cls := Cls.indexable, args := [τ, ι, σ] } →
            EntailsS S C { cls := Cls.indexWrite, args := [τ] } →
              HasTypeS S L C Γ R rm Mode.synth v σ → HasTypeS S L C Γ R rm Mode.synth (Expr.setIndex e i v) σ :=
  @HasTypeS.setIndex

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty} {l : String}
      {k : Ty} {τs : List Ty} {ρ : Ty} {args : List Expr},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        EntailsS S C { cls := Cls.hasProp l, args := [τ, k, Ty.fn τ τs ρ] } →
          List.length args = List.length τs →
            (∀ (p : Expr × Ty), p ∈ List.zip args τs → HasTypeS S L C Γ R rm Mode.synth (Prod.fst p) (Prod.snd p)) →
              HasTypeS S L C Γ R rm Mode.synth (Expr.mcall e l args) ρ :=
  @HasTypeS.mcall

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e₁ : Expr} {τ₁ σ : Ty} {md : Mode}
      {e₂ : Expr} {τ : Ty} {e₃ : Expr},
      HasTypeS S L C Γ R rm Mode.synth e₁ τ₁ →
        EntailsS S C { cls := Cls.strip, args := [τ₁, σ] } →
          HasTypeS S L C Γ R rm md e₂ τ →
            HasTypeS S L C (Scheme.mono σ :: Γ) R rm md e₃ τ → HasTypeS S L C Γ R rm md (Expr.unwrap e₁ e₂ e₃) τ :=
  @HasTypeS.unwrap

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {s : String} {T : Ty},
      Ty.whnf T = Ty.strLit s → HasTypeS S L C Γ R rm Mode.check (Expr.lit (Lit.string s)) T :=
  @HasTypeS.litStr

example : ∀ {S : Sys} {L ls : List String} {es : List Expr} {T P : Ty} {ks : List FieldKind} {τs : List Ty} {C : List Pred}
      {Γ : Ctx} {R : Option Ty} {rm : Mode},
      ObjCase ls es T P →
        List.Nodup ls →
          ks = List.map (fun _ => FieldKind.data) ls →
            List.length es = List.length ls →
              (∀ (l : String), l ∈ ls → l ∈ L) →
                Ty.dataFields P ls = some τs →
                  TyEq P (Ty.record L (objSlots L ls (List.map (fun τ => Ty.slot Ty.pre Ty.data τ) τs))) →
                    (∀ (p : Expr × Ty), p ∈ List.zip es τs → HasTypeS S L C Γ R rm Mode.check (Prod.fst p) (Prod.snd p)) →
                      HasTypeS S L C Γ R rm Mode.check (Expr.obj ls es ks) T :=
  @HasTypeS.objCheck

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e₁ : Expr} {τ₁ : Ty} {d : Disc}
      {t : String} {σ ρ : Ty} {md : Mode} {e₂ : Expr} {τ : Ty} {e₃ : Expr},
      HasTypeS S L C Γ R rm Mode.synth e₁ τ₁ →
        EntailsS S C { cls := Cls.caseTag d t, args := [τ₁, σ, ρ] } →
          HasTypeS S L C (Scheme.mono ρ :: Γ) R rm md e₂ τ →
            HasTypeS S L C (Scheme.mono σ :: Γ) R rm md e₃ τ → HasTypeS S L C Γ R rm md (Expr.caseTag e₁ d t e₂ e₃) τ :=
  @HasTypeS.caseTag

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ τ' : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τ → TyEq τ τ' → HasTypeS S L C Γ R rm Mode.synth e τ' :=
  @HasTypeS.conv

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ T : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τ →
        Sys.closed S T → EntailsS S C (Sys.injPred S τ T) → HasTypeS S L C Γ R rm Mode.check e T :=
  @HasTypeS.inj

example : ∀ {S : Sys} {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm : Mode} {e : Expr} {τ : Ty},
      HasTypeS S L C Γ R rm Mode.synth e τ → HasTypeS S L C Γ R rm Mode.check e Ty.unknown :=
  @HasTypeS.drop

example : ∀ {n : Float}, LitTy (Lit.number n) Ty.number :=
  @LitTy.number

example : ∀ {s : String}, LitTy (Lit.string s) Ty.string :=
  @LitTy.string

example : ∀ {b : Bool}, LitTy (Lit.boolean b) Ty.boolean :=
  @LitTy.boolean

example : LitTy Lit.undefined Ty.undefined :=
  @LitTy.undefined

example : LitTy Lit.null Ty.null :=
  @LitTy.null

example : ∀ {τ : Ty}, UnOpTy UnOp.not τ Ty.boolean :=
  @UnOpTy.not

example : ∀ {τ : Ty}, UnOpTy UnOp.typeof τ Ty.string :=
  @UnOpTy.typeof

example : UnOpTy UnOp.neg Ty.number Ty.number :=
  @UnOpTy.neg

example : ∀ {S : Sys} {C : List Pred} {τ : Ty}, EntailsS S C { cls := Cls.plus, args := [τ] } → BinOpTyS S C BinOp.plus τ τ τ :=
  @BinOpTyS.plus

example : ∀ {S : Sys} {C : List Pred}, BinOpTyS S C BinOp.minus Ty.number Ty.number Ty.number :=
  @BinOpTyS.minus

example : ∀ {ls : List String} {es : List Expr} {T : Ty}, ObjCase ls es T T :=
  @ObjCase.self

example : ∀ {ls : List String} {es : List Expr} {l t : String} {ts : List String} {i : Nat} {Ps : List Ty} {P T : Ty},
      Ty.whnf T = Ty.variant (Disc.field l) ts Ps →
        litTag l ls es = some t → firstIdx t ts = some i → Ps[i]? = some P → Ty.tagOf l P = some t → ObjCase ls es T P :=
  @ObjCase.variant

/-! ## The interpreter

Every defining equation of the interpreter (`run` and the functions it
calls, down to a literal's and an operator's value), restated, so a change
to what a program does shows here too. (Printed by
`scripts/PrintPins.lean`.) -/

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (l : Lit),
      run clock env heap (Expr.lit l) = (Result.ok (Lit.eval l), clock, heap) :=
  @run.eq_1

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (i : Nat),
      run clock env heap (Expr.var i) =
        match env[i]? with
        | some ℓ =>
          match heap[ℓ]? with
          | some v => (Result.ok v, clock, heap)
          | none => (Result.stuck Stuck.undefinedVariable, clock, heap)
        | none => (Result.stuck Stuck.undefinedVariable, clock, heap) :=
  @run.eq_2

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (n : Nat) (body : Expr),
      run clock env heap (Expr.func n body) = (Result.ok (Value.closure env n body), clock, heap) :=
  @run.eq_3

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (n : Nat) (body : Expr),
      run clock env heap (Expr.ctor n body) = (Result.ok (Value.closure env n body), clock, heap) :=
  @run.eq_4

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (f : Expr) (args : List Expr),
      run clock env heap (Expr.app f args) =
        bindC (run clock env heap f) fun vf c₁ h₁ =>
          bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ => call (min c₂ clock) h₂ vf Value.undefined vs :=
  @run.eq_5

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (f : Expr) (args : List Expr),
      run clock env heap (Expr.new_ f args) =
        bindC (run clock env heap f) fun vf c₁ h₁ =>
          bindArgs (runArgs (min c₁ clock) env h₁ args) fun vs c₂ h₂ =>
            match call (min c₂ clock) (h₂ ++ [Value.fields []]) (Value.asCtor vf) (Value.obj (List.length h₂)) vs with
            | (Result.ok v, c₃, h₃) =>
              (Result.ok (if Value.isObject v = true then v else Value.obj (List.length h₂)), c₃, h₃)
            | p => p :=
  @run.eq_6

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (mutable : Bool) (ann : Option Scheme) (e₁ e₂ : Expr),
      run clock env heap (Expr.let_ mutable ann e₁ e₂) =
        bindC (run clock env heap e₁) fun v c₁ h₁ => run (min c₁ clock) (List.length h₁ :: env) (h₁ ++ [v]) e₂ :=
  @run.eq_7

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (i : Nat) (e_2 : Expr),
      run clock env heap (Expr.assign i e_2) =
        bindC (run clock env heap e_2) fun v c₁ h₁ =>
          match env[i]? with
          | some ℓ =>
            if ℓ < List.length h₁ then (Result.ok v, c₁, List.set h₁ ℓ v)
            else (Result.stuck Stuck.undefinedVariable, c₁, h₁)
          | none => (Result.stuck Stuck.undefinedVariable, c₁, h₁) :=
  @run.eq_8

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (c t e_2 : Expr),
      run clock env heap (Expr.cond c t e_2) =
        bindC (run clock env heap c) fun v c₁ h₁ =>
          if Value.truthy v = true then run (min c₁ clock) env h₁ t else run (min c₁ clock) env h₁ e_2 :=
  @run.eq_9

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (op : UnOp) (e_2 : Expr),
      run clock env heap (Expr.unop op e_2) = bindC (run clock env heap e_2) fun v c₁ h₁ => (UnOp.eval op v, c₁, h₁) :=
  @run.eq_10

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (op : BinOp) (e₁ e₂ : Expr),
      run clock env heap (Expr.binop op e₁ e₂) =
        bindC (run clock env heap e₁) fun v₁ c₁ h₁ =>
          bindC (run (min c₁ clock) env h₁ e₂) fun v₂ c₂ h₂ => (BinOp.eval op v₁ v₂, c₂, h₂) :=
  @run.eq_11

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 : Expr),
      run clock env heap (Expr.ret e_2) = bindC (run clock env heap e_2) fun v c₁ h₁ => (Result.returned v, c₁, h₁) :=
  @run.eq_12

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 : Expr),
      run clock env heap (Expr.throw_ e_2) = bindC (run clock env heap e_2) fun v c₁ h₁ => (Result.thrown v, c₁, h₁) :=
  @run.eq_13

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e₁ e₂ : Expr),
      run clock env heap (Expr.seq e₁ e₂) = bindC (run clock env heap e₁) fun x c₁ h₁ => run (min c₁ clock) env h₁ e₂ :=
  @run.eq_14

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (test body : Expr),
      run clock env heap (Expr.while_ test body) =
        bindC (run clock env heap test) fun v c₁ h₁ =>
          if Value.truthy v = true then
            match run (min c₁ clock) env h₁ body with
            | (Result.ok v, c₂, h₂) =>
              match _h : min c₂ clock with
              | 0 => (Result.timeout, 0, h₂)
              | Nat.succ c => run c env h₂ (Expr.while_ test body)
            | (Result.continued, c₂, h₂) =>
              match _h : min c₂ clock with
              | 0 => (Result.timeout, 0, h₂)
              | Nat.succ c => run c env h₂ (Expr.while_ test body)
            | (Result.broke, c₂, h₂) => (Result.ok Value.undefined, c₂, h₂)
            | p => p
          else (Result.ok Value.undefined, c₁, h₁) :=
  @run.eq_15

example : ∀ (clock : Nat) (env : Env) (heap : Heap), run clock env heap Expr.break_ = (Result.broke, clock, heap) :=
  @run.eq_16

example : ∀ (clock : Nat) (env : Env) (heap : Heap), run clock env heap Expr.continue_ = (Result.continued, clock, heap) :=
  @run.eq_17

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e₁ e₂ e₃ : Expr),
      run clock env heap (Expr.unwrap e₁ e₂ e₃) =
        bindC (run clock env heap e₁) fun v c₁ h₁ =>
          if Value.isNothing v = true then run (min c₁ clock) env h₁ e₂
          else run (min c₁ clock) (List.length h₁ :: env) (h₁ ++ [v]) e₃ :=
  @run.eq_18

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e₁ : Expr) (d : Disc) (t : String) (e₂ e₃ : Expr),
      run clock env heap (Expr.caseTag e₁ d t e₂ e₃) =
        bindC (run clock env heap e₁) fun v c₁ h₁ =>
          bindC
            (match d with
            | Disc.field l => getter (min c₁ clock) h₁ v (Value.read h₁ l v)
            | Disc.typeOf => (Result.ok (Value.string (Value.typeString v)), min c₁ clock, h₁))
            fun w c₂ h₂ =>
            match w with
            | Value.string s =>
              if s = t then run (min c₂ clock) (List.length h₂ :: env) (h₂ ++ [v]) e₃
              else run (min c₂ clock) (List.length h₂ :: env) (h₂ ++ [v]) e₂
            | x => run (min c₂ clock) (List.length h₂ :: env) (h₂ ++ [v]) e₂ :=
  @run.eq_19

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (body handler : Expr),
      run clock env heap (Expr.tryCatch body handler) =
        match run clock env heap body with
        | (Result.thrown v, c₁, h₁) => run (min c₁ clock) (List.length h₁ :: env) (h₁ ++ [v]) handler
        | p => p :=
  @run.eq_20

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (body fin : Expr),
      run clock env heap (Expr.tryFinally body fin) =
        match run clock env heap body with
        | (Result.timeout, c₁, h₁) => (Result.timeout, c₁, h₁)
        | (Result.stuck s, c₁, h₁) => (Result.stuck s, c₁, h₁)
        | (Result.fault f, c₁, h₁) => (Result.fault f, c₁, h₁)
        | (r, c₁, h₁) =>
          match run (min c₁ clock) env h₁ fin with
          | (Result.ok v, c₂, h₂) => (r, c₂, h₂)
          | p => p :=
  @run.eq_21

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (ls : List String) (es : List Expr) (ks : List FieldKind),
      run clock env heap (Expr.obj ls es ks) =
        bindArgs (runArgs clock env heap es) fun vs c₁ h₁ =>
          (Result.ok (Value.obj (List.length h₁)), c₁, h₁ ++ [objFields ls ks vs]) :=
  @run.eq_22

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (ls : List String) (es : List Expr) (ks : List ClassKind),
      run clock env heap (Expr.cls ls es ks) =
        bindArgs (runInits clock env heap es ks) fun vs c₁ h₁ =>
          match clsMembers env (Value.obj (List.length h₁)) ls es ks vs with
          | some fs => (Result.ok (Value.obj (List.length h₁)), c₁, h₁ ++ [Value.fields (List.reverse fs)])
          | none => (Result.stuck Stuck.typeMismatch, c₁, h₁) :=
  @run.eq_23

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 : Expr) (l : String),
      run clock env heap (Expr.get e_2 l) =
        bindC (run clock env heap e_2) fun vo c₁ h₁ => getter (min c₁ clock) h₁ vo (Value.read h₁ l vo) :=
  @run.eq_24

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 : Expr) (l : String) (v : Expr),
      run clock env heap (Expr.set e_2 l v) =
        bindC (run clock env heap e_2) fun vo c₁ h₁ =>
          bindC (run (min c₁ clock) env h₁ v) fun vv c₂ h₂ =>
            have p := Value.setProp vo h₂ l vv;
            (Prod.fst p, c₂, Prod.snd p) :=
  @run.eq_25

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e₁ e₂ : Expr),
      run clock env heap (Expr.spread e₁ e₂) =
        bindC (run clock env heap e₁) fun v₁ c₁ h₁ =>
          bindFields (own (min c₁ clock) h₁ v₁) fun fs₁ c₂ h₂ =>
            bindC (run (min c₂ clock) env h₂ e₂) fun v₂ c₃ h₃ =>
              bindFields (own (min c₃ clock) h₃ v₂) fun fs₂ c₄ h₄ =>
                (Result.ok (Value.obj (List.length h₄)), c₄, h₄ ++ [Value.fields (fs₂ ++ fs₁)]) :=
  @run.eq_26

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (es : List Expr),
      run clock env heap (Expr.arr es) =
        bindArgs (runArgs clock env heap es) fun vs c₁ h₁ =>
          (Result.ok (Value.arr (List.length h₁)), c₁, h₁ ++ [Value.items vs]) :=
  @run.eq_27

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 i : Expr),
      run clock env heap (Expr.index e_2 i) =
        bindC (run clock env heap e_2) fun vo c₁ h₁ =>
          bindC (run (min c₁ clock) env h₁ i) fun vi c₂ h₂ => getter (min c₂ clock) h₂ vo (Value.index h₂ vo vi) :=
  @run.eq_28

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 i v : Expr),
      run clock env heap (Expr.setIndex e_2 i v) =
        bindC (run clock env heap e_2) fun vo c₁ h₁ =>
          bindC (run (min c₁ clock) env h₁ i) fun vi c₂ h₂ =>
            bindC (run (min c₂ clock) env h₂ v) fun vv c₃ h₃ =>
              have p := Value.setIndex vo h₃ vi vv;
              (Prod.fst p, c₃, Prod.snd p) :=
  @run.eq_29

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e_2 : Expr) (l : String) (args : List Expr),
      run clock env heap (Expr.mcall e_2 l args) =
        bindC (run clock env heap e_2) fun vo c₁ h₁ =>
          bindC (getter (min c₁ clock) h₁ vo (Value.read h₁ l vo)) fun vf c₂ h₂ =>
            bindArgs (runArgs (min c₂ clock) env h₂ args) fun vs c₃ h₃ => call (min c₃ clock) h₃ vf vo vs :=
  @run.eq_30

example : ∀ (clock : Nat) (h : Heap) (thisv : Value) (args : List Value) (cenv : List Nat) (n : Nat) (body : Expr),
      call clock h (Value.closure cenv n body) thisv args =
        callClosure clock h (Value.closure cenv n body) cenv n body thisv args :=
  @call.eq_1

example : ∀ (clock : Nat) (h : Heap) (thisv : Value) (args : List Value) (cenv : List Nat) (n : Nat) (body : Expr) (t : Value),
      call clock h (Value.bound (Value.closure cenv n body) t) thisv args =
        callClosure clock h (Value.closure cenv n body) cenv n body t args :=
  @call.eq_2

example : ∀ (h : Heap) (thisv : Value) (args : List Value) (p : Prim), call 0 h (Value.prim p) thisv args = (Result.timeout, 0, h) :=
  @call.eq_3

example : ∀ (h : Heap) (thisv : Value) (args : List Value) (p : Prim) (c : Nat),
      call (Nat.succ c) h (Value.prim p) thisv args = (Prim.apply p args, c, h) :=
  @call.eq_4

example : ∀ (clock : Nat) (h : Heap) (vf thisv : Value) (args : List Value),
      (∀ (cenv : List Nat) (n : Nat) (body : Expr), vf = Value.closure cenv n body → False) →
        (∀ (cenv : List Nat) (n : Nat) (body : Expr) (t : Value), vf = Value.bound (Value.closure cenv n body) t → False) →
          (∀ (p : Prim), vf = Value.prim p → False) →
            call clock h vf thisv args = (Result.stuck Stuck.notCallable, clock, h) :=
  @call.eq_5

example : ∀ (h : Heap) (vf : Value) (cenv : Env) (n : Nat) (body : Expr) (thisv : Value) (args : List Value),
      callClosure 0 h vf cenv n body thisv args =
        if n ≤ List.length args then (Result.timeout, 0, h) else (Result.stuck Stuck.arityMismatch, 0, h) :=
  @callClosure.eq_1

example : ∀ (h : Heap) (vf : Value) (cenv : Env) (n : Nat) (body : Expr) (thisv : Value) (args : List Value) (c : Nat),
      callClosure (Nat.succ c) h vf cenv n body thisv args =
        if n ≤ List.length args then
          have p := run c (callEnv h n cenv) (h ++ List.take n args ++ [vf, thisv]) body;
          (Result.catchReturn (Prod.fst p), Prod.snd p)
        else (Result.stuck Stuck.arityMismatch, Nat.succ c, h) :=
  @callClosure.eq_2

example : ∀ (clock : Nat) (h : Heap) (vo v : Value), getter clock h vo (Read.value v) = (Result.ok v, clock, h) :=
  @getter.eq_1

example : ∀ (clock : Nat) (h : Heap) (vo g : Value), getter clock h vo (Read.getter g) = call clock h g vo [] :=
  @getter.eq_2

example : ∀ (clock : Nat) (h : Heap) (vo : Value) (r : Result), getter clock h vo (Read.fail r) = (r, clock, h) :=
  @getter.eq_3

example : ∀ (clock : Nat) (h : Heap) (ℓ : Nat),
      own clock h (Value.obj ℓ) =
        match h[ℓ]? with
        | some (Value.fields fs) =>
          match copyOwn clock h (Value.obj ℓ) (List.reverse (dedupLabels fs)) with
          | (Except.ok cs, c, h') => (Except.ok (List.reverse cs), c, h')
          | p => p
        | x => (Except.error (Result.stuck Stuck.notSpreadable), clock, h) :=
  @own.eq_1

example : ∀ (clock : Nat) (h : Heap) (v : Value),
      (∀ (ℓ : Nat), v = Value.obj ℓ → False) → own clock h v = (Except.error (Result.stuck Stuck.notSpreadable), clock, h) :=
  @own.eq_2

example : ∀ (clock : Nat) (h : Heap) (vo : Value), copyOwn clock h vo [] = (Except.ok [], clock, h) :=
  @copyOwn.eq_1

example : ∀ (clock : Nat) (h : Heap) (vo : Value) (l : String) (m : MemberKind) (snd : Value)
      (fs_2 : List (String × MemberKind × Value)),
      copyOwn clock h vo ((l, m, snd) :: fs_2) =
        if MemberKind.isOwn m = true then
          match getter clock h vo (Value.read h l vo) with
          | (Result.ok v, c₁, h₁) =>
            match copyOwn (min c₁ clock) h₁ vo fs_2 with
            | (Except.ok cs, c, h') => (Except.ok ((l, MemberKind.data, v) :: cs), c, h')
            | p => p
          | (r, c₁, h₁) => (Except.error r, c₁, h₁)
        else copyOwn clock h vo fs_2 :=
  @copyOwn.eq_2

example : ∀ (clock : Nat) (env : Env) (heap : Heap), runArgs clock env heap [] = (Except.ok [], clock, heap) :=
  @runArgs.eq_1

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e : Expr) (es : List Expr),
      runArgs clock env heap (e :: es) =
        match run clock env heap e with
        | (Result.ok v, c₁, h₁) =>
          match runArgs (min c₁ clock) env h₁ es with
          | (Except.ok vs, c₂, h₂) => (Except.ok (v :: vs), c₂, h₂)
          | (Except.error r, c₂, h₂) => (Except.error r, c₂, h₂)
        | (r, c₁, h₁) => (Except.error r, c₁, h₁) :=
  @runArgs.eq_2

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (e : Expr) (es_2 : List Expr) (ks_2 : List ClassKind),
      runInits clock env heap (e :: es_2) (ClassKind.data :: ks_2) =
        match run clock env heap e with
        | (Result.ok v, c₁, h₁) =>
          match runInits (min c₁ clock) (List.length h₁ :: env) (h₁ ++ [v]) es_2 ks_2 with
          | (Except.ok vs, c₂, h₂) => (Except.ok (v :: vs), c₂, h₂)
          | (Except.error r, c₂, h₂) => (Except.error r, c₂, h₂)
        | (r, c₁, h₁) => (Except.error r, c₁, h₁) :=
  @runInits.eq_1

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (head : Expr) (es_2 : List Expr) (head_1 : ClassKind) (ks_2 : List ClassKind),
      (head_1 = ClassKind.data → False) →
        runInits clock env heap (head :: es_2) (head_1 :: ks_2) = runInits clock env heap es_2 ks_2 :=
  @runInits.eq_2

example : ∀ (clock : Nat) (env : Env) (heap : Heap) (es : List Expr) (ks : List ClassKind),
      (∀ (e : Expr) (es_1 : List Expr) (ks_1 : List ClassKind), es = e :: es_1 → ks = ClassKind.data :: ks_1 → False) →
        (∀ (head : Expr) (es_1 : List Expr) (head_1 : ClassKind) (ks_1 : List ClassKind),
            es = head :: es_1 → ks = head_1 :: ks_1 → False) →
          runInits clock env heap es ks = (Except.ok [], clock, heap) :=
  @runInits.eq_3

example : ∀ (k : Value → Nat → Heap → Ran) (v : Value) (c : Nat) (h : Heap), bindC (Result.ok v, c, h) k = k v c h :=
  @bindC.eq_1

example : ∀ (p : Ran) (k : Value → Nat → Heap → Ran),
      (∀ (v : Value) (c : Nat) (h : Heap), p = (Result.ok v, c, h) → False) → bindC p k = p :=
  @bindC.eq_2

example : ∀ (k : List Value → Nat → Heap → Ran) (vs : List Value) (c : Nat) (h : Heap), bindArgs (Except.ok vs, c, h) k = k vs c h :=
  @bindArgs.eq_1

example : ∀ (k : List Value → Nat → Heap → Ran) (r : Result) (c : Nat) (h : Heap), bindArgs (Except.error r, c, h) k = (r, c, h) :=
  @bindArgs.eq_2

example : ∀ (k : List (String × MemberKind × Value) → Nat → Heap → Ran) (fs : List (String × MemberKind × Value)) (c : Nat)
      (h : Heap), bindFields (Except.ok fs, c, h) k = k fs c h :=
  @bindFields.eq_1

example : ∀ (k : List (String × MemberKind × Value) → Nat → Heap → Ran) (r : Result) (c : Nat) (h : Heap),
      bindFields (Except.error r, c, h) k = (r, c, h) :=
  @bindFields.eq_2

example : ∀ (h : Heap) (n : Nat) (cenv : Env), callEnv h n cenv = List.range' (List.length h) (n + 2) ++ cenv :=
  @callEnv.eq_1

example : ∀ (clock : Nat) (k : Nat → Heap → Ran) (v : Value) (c₂ : Nat) (h₂ : Heap),
      loopNext clock (Result.ok v, c₂, h₂) k =
        match min c₂ clock with
        | 0 => (Result.timeout, 0, h₂)
        | Nat.succ c => k c h₂ :=
  @loopNext.eq_1

example : ∀ (clock : Nat) (k : Nat → Heap → Ran) (c₂ : Nat) (h₂ : Heap),
      loopNext clock (Result.continued, c₂, h₂) k =
        match min c₂ clock with
        | 0 => (Result.timeout, 0, h₂)
        | Nat.succ c => k c h₂ :=
  @loopNext.eq_2

example : ∀ (clock : Nat) (k : Nat → Heap → Ran) (c₂ : Nat) (h₂ : Heap),
      loopNext clock (Result.broke, c₂, h₂) k = (Result.ok Value.undefined, c₂, h₂) :=
  @loopNext.eq_3

example : ∀ (clock : Nat) (p : Ran) (k : Nat → Heap → Ran),
      (∀ (v : Value) (c₂ : Nat) (h₂ : Heap), p = (Result.ok v, c₂, h₂) → False) →
        (∀ (c₂ : Nat) (h₂ : Heap), p = (Result.continued, c₂, h₂) → False) →
          (∀ (c₂ : Nat) (h₂ : Heap), p = (Result.broke, c₂, h₂) → False) → loopNext clock p k = p :=
  @loopNext.eq_4

example : ∀ (h : Heap) (l : String) (ℓ : Nat),
      Value.read h l (Value.obj ℓ) =
        match h[ℓ]? with
        | some (Value.fields fs) => Option.getD (readMember fs l) (Read.fail (Result.stuck Stuck.propertyNotFound))
        | x => Read.fail (Result.stuck Stuck.notIndexable) :=
  @Value.read.eq_1

example : ∀ (h : Heap) (l : String) (ℓ : Nat),
      Value.read h l (Value.arr ℓ) =
        match h[ℓ]? with
        | some (Value.items vs) =>
          if l = "length" then Read.value (Value.number (Nat.toFloat (List.length vs)))
          else Read.fail (Result.stuck Stuck.propertyNotFound)
        | x => Read.fail (Result.stuck Stuck.notIndexable) :=
  @Value.read.eq_2

example : ∀ (h : Heap) (l s : String),
      Value.read h l (Value.string s) =
        if l = "length" then Read.value (Value.number (Nat.toFloat (String.length s)))
        else Read.fail (Result.stuck Stuck.propertyNotFound) :=
  @Value.read.eq_3

example : ∀ (h : Heap) (l : String) (x : Value),
      (∀ (ℓ : Nat), x = Value.obj ℓ → False) →
        (∀ (ℓ : Nat), x = Value.arr ℓ → False) →
          (∀ (s : String), x = Value.string s → False) → Value.read h l x = Read.fail (Result.stuck Stuck.notIndexable) :=
  @Value.read.eq_4

example : ∀ (n : Float), Value.typeString (Value.number n) = "number" :=
  @Value.typeString.eq_1

example : ∀ (s : String), Value.typeString (Value.string s) = "string" :=
  @Value.typeString.eq_2

example : ∀ (b : Bool), Value.typeString (Value.boolean b) = "boolean" :=
  @Value.typeString.eq_3

example : Value.typeString Value.undefined = "undefined" :=
  @Value.typeString.eq_4

example : Value.typeString Value.null = "object" :=
  @Value.typeString.eq_5

example : ∀ (ℓ : Nat), Value.typeString (Value.obj ℓ) = "object" :=
  @Value.typeString.eq_6

example : ∀ (fs : List (String × MemberKind × Value)), Value.typeString (Value.fields fs) = "object" :=
  @Value.typeString.eq_7

example : ∀ (ℓ : Nat), Value.typeString (Value.arr ℓ) = "object" :=
  @Value.typeString.eq_8

example : ∀ (vs : List Value), Value.typeString (Value.items vs) = "object" :=
  @Value.typeString.eq_9

example : ∀ (env : List Nat) (arity : Nat) (body : Expr), Value.typeString (Value.closure env arity body) = "function" :=
  @Value.typeString.eq_10

example : ∀ (p : Prim), Value.typeString (Value.prim p) = "function" :=
  @Value.typeString.eq_11

example : ∀ (f thisv : Value), Value.typeString (Value.bound f thisv) = "function" :=
  @Value.typeString.eq_12

example : ∀ (n : Float), Lit.eval (Lit.number n) = Value.number n :=
  @Lit.eval.eq_1

example : ∀ (s : String), Lit.eval (Lit.string s) = Value.string s :=
  @Lit.eval.eq_2

example : ∀ (b : Bool), Lit.eval (Lit.boolean b) = Value.boolean b :=
  @Lit.eval.eq_3

example : Lit.eval Lit.undefined = Value.undefined :=
  @Lit.eval.eq_4

example : Lit.eval Lit.null = Value.null :=
  @Lit.eval.eq_5

example : ∀ (x : Value), UnOp.eval UnOp.not x = Result.ok (Value.boolean !Value.truthy x) :=
  @UnOp.eval.eq_1

example : ∀ (x : Value), UnOp.eval UnOp.typeof x = Result.ok (Value.string (Value.typeString x)) :=
  @UnOp.eval.eq_2

example : ∀ (n : Float), UnOp.eval UnOp.neg (Value.number n) = Result.ok (Value.number (-n)) :=
  @UnOp.eval.eq_3

example : ∀ (x : Value), (∀ (n : Float), x = Value.number n → False) → UnOp.eval UnOp.neg x = Result.stuck Stuck.typeMismatch :=
  @UnOp.eval.eq_4

example : ∀ (a b : Float), BinOp.eval BinOp.plus (Value.number a) (Value.number b) = Result.ok (Value.number (a + b)) :=
  @BinOp.eval.eq_1

example : ∀ (a b : String), BinOp.eval BinOp.plus (Value.string a) (Value.string b) = Result.ok (Value.string (a ++ b)) :=
  @BinOp.eval.eq_2

example : ∀ (a b : Float), BinOp.eval BinOp.minus (Value.number a) (Value.number b) = Result.ok (Value.number (a - b)) :=
  @BinOp.eval.eq_3

example : ∀ (x : BinOp) (x_1 x_2 : Value),
      (∀ (a b : Float), x = BinOp.plus → x_1 = Value.number a → x_2 = Value.number b → False) →
        (∀ (a b : String), x = BinOp.plus → x_1 = Value.string a → x_2 = Value.string b → False) →
          (∀ (a b : Float), x = BinOp.minus → x_1 = Value.number a → x_2 = Value.number b → False) →
            BinOp.eval x x_1 x_2 = Result.stuck Stuck.typeMismatch :=
  @BinOp.eval.eq_4

end Generated

end Inty.Statements
