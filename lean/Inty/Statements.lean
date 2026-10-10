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

example : ∀ (clock : Nat) {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty}
    {W : World} {env : Env} {h : Heap} {e : Expr} {τ : Ty}, HasType L C Γ R e τ → HoldsOrVar C →
      G W Γ env → HeapOK clock W h →
      (run clock env h e).2.1 ≤ clock ∧
      ((run clock env h e).1 = .timeout ∨ ∃ W', W <+: W' ∧
        HeapOK (run clock env h e).2.1 W' (run clock env h e).2.2 ∧
        ((∃ v, (run clock env h e).1 = .ok v ∧ V (run clock env h e).2.1 W' τ v) ∨
          (run clock env h e).1.Abrupt ∨
          (∃ v, (run clock env h e).1 = .returned v ∧
            ∃ τr, R = some τr ∧ V (run clock env h e).2.1 W' τr v))) :=
  fun clock _ _ _ _ _ _ _ _ _ ht hC hG hH => eval_sound clock ht hC hG hH

example : ∀ {L : List String} {C : List Pred} {e : Expr} {τ : Ty}, HasType L C [] none e τ →
    HoldsOrVar C → ∀ (clock : Nat) (s : Stuck), eval clock [] [] e ≠ .stuck s :=
  never_stuck

example : ∀ {L : List String} {C : List Pred} {e : Expr} {τ : Ty},
    HasType L C builtinCtx none e τ → HoldsOrVar C →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  never_stuck_with_builtins

example : ∀ {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {e : Expr} {τ : Ty}
    (σ : Subst), HasType L C Γ R e τ →
      HasType L (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) :=
  fun σ h => h.subst σ

example : ∀ {τ₁ τ₂ : Ty} {σ : Subst}, unify τ₁ τ₂ = some σ → TyEq (τ₁.subst σ) (τ₂.subst σ) :=
  unify_sound

example : ∀ {τ₁ τ₂ : Ty} {σ : Subst}, unify₀ τ₁ τ₂ = some σ → τ₁.subst σ = τ₂.subst σ :=
  unify₀_sound

example : ∀ {τ₁ τ₂ : Ty} {ψ : Subst}, τ₁.subst ψ = τ₂.subst ψ →
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, (τ.subst σ).subst ψ = τ.subst ψ :=
  unify_mgu

example : ∀ {L : List String} {e : Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out},
    infer L Γ R e n = some o → ∀ φ C, (∀ c ∈ o.preds, Entails C (c.subst φ)) →
      HasType L C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) e
        (o.τ.subst φ) :=
  infer_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∃ C, HoldsOrVar C ∧ HasType e.labels.eraseDups C [] none e τ :=
  inferProgram_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock [] [] e ≠ .stuck s :=
  inferProgram_never_stuck

example : ∀ {L : List String} {e : Expr} {τ : Ty}, inferIn L builtinCtx e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  inferIn_builtins_never_stuck

example : ∀ (L : List String) (e : Expr) {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst}
    {C : List Pred} {τ' : Ty} {Γ' : Ctx} {R' : Option Ty},
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, p.AssumableAt false) →
    Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → HasType₀ L C Γ' R' e τ' →
    ∃ o, infer L Γ R e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ o.τ.subst φ = τ' ∧ Sat₀ C o.preds φ :=
  infer_complete

example : ∀ {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}, ctxFtv Γ = [] →
    (∀ p ∈ C, p.OnVarShaped) → e.scoped (Γ.map fun _ => false) = true →
    HasType₀ L C Γ none e τ' →
    ∃ o, infer L Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ ∃ τ, inferIn L Γ e = some τ :=
  inferIn_complete

example : ∀ {e : Expr} {τ' : Ty}, e.scoped [] = true → HasType₀ e.labels.eraseDups [] [] none e τ' →
    ∃ τ, inferProgram e = some τ :=
  inferProgram_complete

example : Pred.OnVarShaped p ↔
    (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
      ∃ a τ s r, p = ⟨.merge, [.var a, τ, s, r]⟩ := Iff.rfl

example : Pred.AssumableAt top p ↔
    (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧ ∃ a rest, p.args = .var a :: rest) ∨
      ∃ q τ s r, p = ⟨.merge, [q, τ, s, r]⟩ ∧ (top = true → ∃ a, q = .var a) := Iff.rfl

example : Cls.arity c = match c with
    | .plus | .indexWrite | .fieldWrite => 1
    | .hasProp _ => 2
    | .indexable => 3
    | .merge => 4 := by
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
    ∀ l s, Ty.field l ls slots = some s →
      (∃ σ, TyEq s (.slot .pre σ) ∧ ∃ v', fs.lookup l = some v' ∧ V k W σ v') ∨
      (∃ σ, TyEq s (.slot .abs σ) ∧ fs.lookup l = none) := CellV_obj
example : CellV k W (.obj (.var a)) v ↔ False := Iff.rfl
example : CellV k W (.arr τ) v ↔ ∃ vs, v = .items vs ∧ ∀ w ∈ vs, V k W τ w := CellV_arr
example : CellV k W (.scheme s) v ↔
    ∀ τs, τs.length = s.arity → HoldsOrVar (s.instPreds τs) → V k W (s.inst τs) v := Iff.rfl
example : Result.Abrupt r ↔
    (∃ v, r = .thrown v) ∨ r = .broke ∨ r = .continued ∨ ∃ f, r = .fault f := by
  cases r <;> simp [Result.Abrupt] <;> exact ⟨.outOfBounds, trivial⟩
example : V k W (.fn θ τs ρ) f ↔ ∀ j ≤ k, ∀ W', W <+: W' → ∀ h thisv args,
    args.length = τs.length → (∀ i < j, HeapOK i W' h) → (∀ i < j, V i W' θ thisv) →
    (∀ i < j, VList i W' τs args) →
    (call j h f thisv args).2.1 ≤ j ∧ ((call j h f thisv args).1 = .timeout ∨
      ((call j h f thisv args).2.1 < j ∧ ∃ W'', W' <+: W'' ∧
        HeapOK (call j h f thisv args).2.1 W'' (call j h f thisv args).2.2 ∧
        ((∃ v, (call j h f thisv args).1 = .ok v ∧ V (call j h f thisv args).2.1 W'' ρ v) ∨
          (call j h f thisv args).1.Abrupt))) := by
  rw [V_fn]
  constructor
  · intro H j hj W' hW h thisv args hl hh ht ha
    obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H j hj W' hW h thisv args hl hh ht ha
    · exact ⟨hc, .inl H⟩
    · exact ⟨hc, .inr ⟨hlt, W'', hW'', hH hlt, hr.imp (fun ⟨v, e, hv⟩ => ⟨v, e, hv hlt⟩) id⟩⟩
  · intro H j hj W' hW h thisv args hl hh ht ha
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

example : Entails C p ↔ (∃ q, PredEq p q ∧ Inst q) ∨ p ∈ C := Iff.rfl
example : PredEq p q ↔ p.cls = q.cls ∧ p.args.length = q.args.length ∧
    ∀ x ∈ p.args.zip q.args, TyEq x.1 x.2 := Iff.rfl
example : TyEq s t ↔ ∀ n, s.approx n = t.approx n := Iff.rfl

example : Inst p ↔ p = ⟨.plus, [.number]⟩ ∨ p = ⟨.plus, [.string]⟩ ∨
    (∃ l ls fs σ, Ty.field l ls fs = some (.slot .pre σ) ∧ p = ⟨.hasProp l, [.record ls fs, σ]⟩) ∨
    (∃ τ s, p = ⟨.merge, [.pre, τ, s, .slot .pre τ]⟩) ∨ (∃ τ s, p = ⟨.merge, [.abs, τ, s, s]⟩) ∨
    (∃ τ, p = ⟨.hasProp "length", [.array τ, .number]⟩) ∨
    p = ⟨.hasProp "length", [.string, .number]⟩ ∨
    (∃ τ, p = ⟨.indexable, [.array τ, .number, τ]⟩) ∨
    p = ⟨.indexable, [.string, .number, .string]⟩ ∨
    (∃ τ, p = ⟨.indexWrite, [.array τ]⟩) ∨
    ∃ ls slots, p = ⟨.fieldWrite, [.record ls slots]⟩ :=
  ⟨fun h => by
    cases h with
    | plusNumber => exact .inl rfl
    | plusString => exact .inr (.inl rfl)
    | hasProp hf => exact .inr (.inr (.inl ⟨_, _, _, _, hf, rfl⟩))
    | mergePre => exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    | mergeAbs => exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
    | lengthArray => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))
    | lengthString => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
    | indexArray => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))
    | indexString => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
    | writeArray =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))
    | writeRecord =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, rfl⟩))))))))),
   fun h => by
    rcases h with rfl | rfl | ⟨l, ls, fs, σ, hf, rfl⟩ | ⟨τ, s, rfl⟩ | ⟨τ, s, rfl⟩ | ⟨τ, rfl⟩ |
      rfl | ⟨τ, rfl⟩ | rfl | ⟨τ, rfl⟩ | ⟨ls, slots, rfl⟩
    · exact .plusNumber
    · exact .plusString
    · exact .hasProp hf
    · exact .mergePre
    · exact .mergeAbs
    · exact .lengthArray
    · exact .lengthString
    · exact .indexArray
    · exact .indexString
    · exact .writeArray
    · exact .writeRecord⟩

/-- A constraint left on a type variable is all `HoldsOrVar` allows beside
the instances. -/
example : HoldsOrVar C ↔ ∀ p ∈ C, (∃ q, PredEq p q ∧ Inst q) ∨ ∃ a rest, p.args = .var a :: rest :=
  Iff.rfl

/-- The builtins' types, which their soundness proofs establish. -/
example : builtinCtx =
    [⟨1, .fn .undefined [.bound 0] .boolean, []⟩, .mono (.fn .undefined [.number] .number)] :=
  rfl

/-! ## Programs the typing rules reject -/

private def num (n : Float) : Expr := .lit (.number n)
private def str (s : String) : Expr := .lit (.string s)

/-- `break;` outside a loop is rejected, by the scope check, as JavaScript
rejects it. -/
example : Expr.break_.scoped [] = false := rfl

/-- `const x = 1; x = 2`: assigning to a `const` is rejected, by the scope
check beside the typing rules. -/
example : (Expr.let_ false (num 1) (.assign 0 (num 2))).assignsMutable [] = false := rfl

/-- Distinct constructors make distinct types. -/
private theorem ne_con {c c' : Con} {ts ts' : List Ty} (h : c ≠ c') :
    ¬ TyEq (.app c ts) (.app c' ts') := fun e => h (TyEq.con e)

/-- `x = 1` for a variable whose scheme is polymorphic: an assigned variable
is a monotype. -/
example : ¬ HasType L [] [⟨1, .bound 0, []⟩] none (.assign 0 (num 1)) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with | assign hi ha _ _ => simp at hi; subst hi; simp at ha

/-- An unbound variable. -/
example : ¬ HasType L [] [] none (.var 0) τ := by
  intro h; obtain ⟨_, -, h⟩ := h.top; cases h with | var hi _ _ => simp at hi

/-- `1 + "a"`: `+` never mixes a `Number` with a `String`. -/
example : ¬ HasType L [] [] none (.binop .plus (num 1) (str "a")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top
      obtain ⟨_, e₂, h₂⟩ := h₂.top
      cases h₁ with
      | lit hl =>
        cases hl
        cases h₂ with
        | lit hl => cases hl; exact ne_con (by decide) (e₁.trans e₂.symm)

/-- `true + true`: `Boolean` is not a `Plus` instance, and nothing assumes it. -/
example : ¬ HasType L [] [] none (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | binop hop h₁ _ =>
    cases hop with
    | plus hc =>
      obtain ⟨_, e₁, h₁⟩ := h₁.top
      cases h₁ with
      | lit hl =>
        cases hl
        rcases hc with ⟨q, hq, hi⟩ | hc
        · cases hi
          case plusNumber => exact ne_con (by decide) (e₁.trans (PredEq.one hq).2)
          case plusString => exact ne_con (by decide) (e₁.trans (PredEq.one hq).2)
          all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
        · cases hc

/-- `"a" - 1`: `-` is `Number` only. -/
example : ¬ HasType L [] [] none (.binop .minus (str "a") (num 1)) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | binop hop h₁ _ =>
    cases hop
    obtain ⟨_, e₁, h₁⟩ := h₁.top
    cases h₁ with | lit hl => cases hl; exact ne_con (by decide) e₁

/-- `-"a"`: unary `-` is `Number` only. -/
example : ¬ HasType L [] [] none (.unop .neg (str "a")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | unop hop h₁ =>
    cases hop
    obtain ⟨_, e₁, h₁⟩ := h₁.top
    cases h₁ with | lit hl => cases hl; exact ne_con (by decide) e₁

/-- `({x: 1}).y`: an object literal has only its own fields. -/
example : ¬ HasType L [] [] none (.get (.obj ["x"] [num 1]) "y") τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | get he hp =>
    obtain ⟨_, e₁, he⟩ := he.top
    cases he with
    | obj hτs _ _ _ _ =>
      rcases hp with ⟨q, hq, hi⟩ | hi
      · cases hi
        case hasProp l ls fs σ' hf =>
          obtain ⟨hcls, hτ, -⟩ := PredEq.two hq
          cases hcls
          obtain ⟨hc, hl, hz⟩ := TyEq.app_iff.mp (e₁.trans hτ)
          cases hc
          obtain ⟨s, hs, hss⟩ := Ty.field_tyEq hl.symm (zip_tyEq_symm hz) hf
          rcases objSlots_field_cases hs with ⟨σ, rfl⟩ | ⟨σ, rfl, -⟩
          · have := objSlots_field hs
            obtain ⟨_, rfl⟩ := List.length_eq_one_iff.mp hτs
            simp [Ty.field] at this
          · exact absurd (TyEq.slot hss).1 TyEq.pre_abs
        case lengthArray =>
          exact ne_con (by simp) (e₁.trans (PredEq.two hq).2.1)
        case lengthString =>
          exact ne_con (by simp) (e₁.trans (PredEq.two hq).2.1)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · cases hi

/-- `(1).x`: a number has no fields. -/
example : ¬ HasType L [] [] none (.get (num 1) "x") τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | get he hp =>
    obtain ⟨_, e₁, he⟩ := he.top
    cases he with
    | lit hl =>
      cases hl
      rcases hp with ⟨q, hq, hi⟩ | hi
      · cases hi
        case hasProp => exact ne_con (by simp) (e₁.trans (PredEq.two hq).2.1)
        case lengthArray => exact ne_con (by simp) (e₁.trans (PredEq.two hq).2.1)
        case lengthString => exact ne_con (by simp) (e₁.trans (PredEq.two hq).2.1)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · cases hi

/-- `1(2)`: a number is not a function. -/
example : ¬ HasType L [] [] none (.app (num 1) [num 2]) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | app hf _ _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top
    cases hf with | lit hl => cases hl; exact ne_con (by simp) e₁

/-- `"ab"[0] = "c"`: strings take no stores. -/
example : ¬ HasType L [] [] none (.setIndex (str "ab") (num 0) (str "c")) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | setIndex he _ _ hw _ =>
    obtain ⟨_, e₁, he⟩ := he.top
    cases he with
    | lit hl =>
      cases hl
      rcases hw with ⟨q, hq, hi⟩ | hi
      · cases hi
        case writeArray => exact ne_con (by simp) (e₁.trans (PredEq.one hq).2)
        all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
      · cases hi

/-- `(function f(x) { return x; })(1, 2)`: one argument per parameter. -/
example : ¬ HasType L [] [] none (.app (.func 1 (.var 0)) [num 1, num 2]) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | app hf hlen _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top
    cases hf with
    | func hn _ =>
      have := (TyEq.app_iff.mp e₁).2.1
      simp at hlen this; omega

/-- `(function f() { return -this; })()`: a call outside a receiver makes
`this` `undefined`, which `-` doesn't take. -/
example : ¬ HasType L [] [] none (.app (.func 0 (.unop .neg (.var 1))) []) τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top
  cases h with
  | app hf _ _ =>
    obtain ⟨_, e₁, hf⟩ := hf.top
    cases hf with
    | func hn hb =>
      rw [List.length_eq_zero_iff] at hn; subst hn
      have hθ := (TyEq.app_iff.mp e₁).2.2 _ (List.mem_cons_self)
      obtain ⟨_, e₂, hb⟩ := hb.top
      cases hb with
      | unop hop he =>
        cases hop
        obtain ⟨_, e₃, he⟩ := he.top
        cases he with
        | var hi _ _ =>
          simp at hi; subst hi
          simp only [Scheme.mono_inst] at e₃
          exact ne_con (by simp) (hθ.symm.trans e₃)

end Inty.Statements
