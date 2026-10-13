import Inty.Principal

/-!
# Completeness with polymorphic annotations

Inference checks a polymorphic annotation's initialiser at fresh rigid type
variables and rejects the program if one escapes: into the context, the
return type, or a constraint it leaves. Completeness needs that check to
pass only where the rules type the initialiser: in every context in which
the initialiser has the annotation's type at every rigid name outside a
finite set (`RigidStays`, collected over a program by `Expr.PolyOK`). There,
inference finds every typing (`infer_complete_polyOK`,
`inferProgram_complete_polyOK`) and its constrained type is principal
(`inferProgramC_principal_polyOK`). In such a context the rigid variable is
never in the tree of a context variable's instance (the proof of
`infer_complete_letPoly`), so the check can fire there only on a constraint
left, as in `polyGap`, or on an equation of a recursive type its unfolding
never reaches.

`PolyOK` is still about the algorithm, and quantifies over contexts, so it
has to be proved program by program; it holds of every program whose
annotations are all monomorphic. For `polyApp`, which inference accepts
(`polyApp_accepted`), it isn't proved here: it would need what unification
does in an arbitrary context.

Three programs show what is and isn't covered:

* `polyId`, `/** const id: <a>(a) => a */ const id = (y) => y; id(1)`, lets
  no rigid variable escape, in any context (`polyId_polyOK`), so inference
  finds every typing it has.
* `polyApp`, `const h = (x) => x; /** const f: <a>(a) => a */
  const f = (y) => h(y); f(1)`, is accepted by inference, but whether it is
  `PolyOK` is open.
* `polyGap` has a typing that inference rejects (`polyGap_separates`):

  ```
  /** const f: <a>(a) => a */
  const f = (y) => { const g = true ? (o) => o.l : (o) => y; return y; };
  1
  ```

  The conditional's two functions have the same type, so the first's
  `o.l` has the rigid type `a` of `y`. That leaves `HasProp l` on `o`'s
  type, a variable nothing else fixes, with the field's type `a`: the rigid
  variable escapes into a constraint left. A typing picks `o`'s type
  `{l: a}` at each rigid name, which the algorithm can't, as it would have
  to keep a constraint on the rigid variable waiting on a type variable
  (an implication constraint, as in GHC's OutsideIn(X)). So `polyGap`
  isn't `PolyOK` (`polyGap_not_polyOK`).
-/

namespace Inty

/-- `<a>(a) => a`, an annotation's function type (`this` is `undefined`). -/
def idAnn : Scheme := ⟨1, .fn .undefined [.bound 0] (.bound 0), []⟩

/-! ## A program inference is complete for -/

/-- `/** const id: <a>(a) => a */ const id = (y) => y; id(1)`. -/
def polyId : Expr :=
  .let_ false (some idAnn) (.func 1 (.var 0)) (.app (.var 0) [.lit (.number 1)])

/-- Checking `(y) => y` against `<a>(a) => a` leaves `Inject a a`, which
improvement decides, in any context. -/
theorem polyId_rigidStays (L : List String) : RigidStays L idAnn (.func 1 (.var 0)) := by
  intro Γ R rm n _ _ _ _ _ o₁ σi preds₁ _ _ _ _ _ _ _ _ h₁ himp
  have hkΓ : maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ ctxRkeys Γ := fun h =>
    Nat.lt_irrefl _ (lt_maxPlusOne _ (List.mem_append_left _ h))
  have hkR : maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) ∉ Ret.rkeys R := fun h =>
    Nat.lt_irrefl _ (lt_maxPlusOne _ (List.mem_append_right _ h))
  generalize maxPlusOne (ctxRkeys Γ ++ Ret.rkeys R) = k at h₁ hkΓ hkR ⊢
  simp [infer, funcTarget, idAnn, Scheme.inst, rigids, PTy.inst, checkEx, Expr.pushes] at h₁
  subst h₁
  have hb : ∀ p ∈ [(⟨.inject (.app (.rigid k 0) []), [.app (.rigid k 0) []]⟩ : Pred)], p.Below 0 :=
    fun p hp => by simp at hp; subst hp; simp [Pred.Below, Pred.ftv, Ty.ftv]
  obtain ⟨hσ, -⟩ := improveAll_inv _ hb himp
  -- Improvement binds no type variable, so the context and return type
  -- keep their rigid variables.
  have hid : ∀ b, k ∉ ((Ty.var b).subst (Subst.compose σi [])).rkeys := fun b => by
    simp [Ty.subst_compose, (hσ b).2 (Nat.zero_le b), Ty.rkeys]
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · rcases ctxRkeys_subst h with h | ⟨b, -, h⟩
    · exact hkΓ h
    · exact hid b h
  · rcases Ret.rkeys_subst h with h | ⟨b, -, h⟩
    · exact hkR h
    · exact hid b h
  simp [improveAll, improveOne, Pred.improve, Pred.improveArgs, Pred.decide, Pred.decide₀,
    Pred.decideInject, Pred.decideInject₀, Ty.isVar] at himp
  split at himp
  · cases himp
  · simp only [Option.some.injEq, Prod.mk.injEq] at himp
    simp [← himp.2]

theorem polyId_polyOK (L : List String) : polyId.PolyOK L := by
  simp only [polyId, Expr.PolyOK, Expr.PolyOKList_eq]
  exact ⟨⟨fun a ha _ => by cases ha; exact polyId_rigidStays L, trivial⟩, trivial,
    fun e he => by simp at he; subst he; trivial⟩

/-- Every typing of `polyId` is an instance of the type inference finds. -/
theorem polyId_complete {τ' : Ty} (ht : HasType polyId.labels.eraseDups [] [] none .synth .synth polyId τ') :
    ∃ τ, inferProgram polyId = some τ ∧ ∃ φ, TyEq (τ.subst φ) τ' :=
  inferProgram_complete_polyOK (by decide +kernel) (polyId_polyOK _) ht

/-! ## A program the hypothesis isn't proved for -/

/-- `const h = (x) => x; /** const f: <a>(a) => a */ const f = (y) => h(y);
f(1)`: the initialiser passes its rigid-typed parameter to a variable of the
context. -/
def polyApp : Expr :=
  .let_ false none (.func 1 (.var 0))
    (.let_ false (some idAnn) (.func 1 (.app (.var 3) [.var 0])) (.app (.var 0) [.lit (.number 1)]))

/-- Inference accepts `polyApp`. -/
theorem polyApp_accepted : inferProgram polyApp = some .number := by decide +kernel

/-! ## A program inference is incomplete for -/

/-- `/** const f: <a>(a) => a */
const f = (y) => { const g = true ? (o) => o.l : (o) => y; return y; }; 1`. -/
def polyGap : Expr :=
  .let_ false (some idAnn)
    (.func 1 (.let_ false none
      (.cond (.lit (.boolean true)) (.func 1 (.get (.var 0) "l")) (.func 1 (.var 3)))
      (.ret (.var 1))))
    (.lit (.number 1))

/-- `polyGap` has a type: at each rigid name `k`, `o` has the type `{l: k}`. -/
theorem polyGap_typed : HasType L [] [] none .synth .synth polyGap .number := by
  refine .letPoly idAnn [] (by decide) rfl rfl rfl (fun k _ => ?_) .func rfl (.lit .number)
  let r : Ty := .app (.rigid k 0) []
  let P : Ty := .record ["l"] [.slot .pre .data r]
  let F : Ty := .fn .undefined [P] r
  refine .funcCheck (θ := .undefined) (τs := [r]) (ρ := r) rfl rfl rfl ?_
  refine .let_ (.mono F) [] (fun _ _ => ?_) (.inl ⟨rfl, rfl⟩)
    (.inr fun _ h => by simp [Scheme.mono] at h) (fun _ h => by cases h)
    (.ret (.inj (.var_mono rfl) rfl (.inl (Inst.instEq (.injectSelf rfl)))))
  simp only [Scheme.open, Scheme.openPreds, Scheme.instPreds, Scheme.mono, Scheme.inst, annMode,
    List.append_nil, List.map_nil]
  refine .cond (.lit .boolean) ?_ ?_
  · refine .func (τs := [P]) rfl (.get (.var_mono rfl) (k := .data) (.inl (Inst.instEq (.hasProp ?_))))
    rfl
  · exact .func (τs := [P]) rfl (.var_mono rfl)

/-- Inference rejects `polyGap`: the rigid variable escapes into the
`HasProp` left on `o`'s type. -/
theorem polyGap_rejected : inferProgram polyGap = none := by decide +kernel

/-- So inference is incomplete for polymorphic annotations. -/
theorem polyGap_separates :
    HasType polyGap.labels.eraseDups [] [] none .synth .synth polyGap .number ∧
      inferProgram polyGap = none :=
  ⟨polyGap_typed, polyGap_rejected⟩

/-- And a rigid variable escapes in `polyGap`, as completeness says it must. -/
theorem polyGap_not_polyOK : ¬ polyGap.PolyOK polyGap.labels.eraseDups := fun h => by
  obtain ⟨τ, hτ, -⟩ := inferProgram_complete_polyOK (by decide +kernel) h polyGap_typed
  rw [polyGap_rejected] at hτ
  cases hτ

end Inty
