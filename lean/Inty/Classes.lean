import Inty.Heads

/-!
# Type classes

The class instances, mirroring the instance tables in `src/classes`, and
entailment: a constraint holds when it is an instance, or when it is
assumed (a scheme's constraints, while its body is checked). Each class
added to `Cls` gets its instances here, and the soundness proof gets a case
for the operators that use it.
-/

namespace Inty

/-- The slot of the label `l` in a record with the labels `ls` and the
slots `fs`. -/
def Ty.field (l : String) : List String → List Ty → Option Ty
  | l' :: ls, τ :: τs => if l' = l then some τ else Ty.field l ls τs
  | _, _ => none

theorem Ty.field_subst (σ : Subst) (l : String) :
    ∀ (ls : List String) (fs : List Ty),
      Ty.field l ls (fs.map (·.subst σ)) = (Ty.field l ls fs).map (·.subst σ)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, τ :: τs => by
    simp only [List.map_cons, Ty.field]
    split
    · rfl
    · exact Ty.field_subst σ l ls τs

/-- The slot of `l` is one of the record's. -/
theorem Ty.field_mem {l : String} : ∀ {ls : List String} {fs : List Ty} {τ : Ty},
    Ty.field l ls fs = some τ → (l, τ) ∈ ls.zip fs
  | [], _, _, h => by simp [Ty.field] at h
  | _ :: _, [], _, h => by simp [Ty.field] at h
  | l' :: ls, τ' :: τs, τ, h => by
    simp only [Ty.field] at h
    split at h
    · cases h; subst_vars; simp
    · exact List.mem_cons_of_mem _ (Ty.field_mem h)

/-- The fields of records with pairwise equal slots. -/
theorem Ty.field_tyEq {l : String} : ∀ {ls : List String} {fs fs' : List Ty},
    fs.length = fs'.length → (∀ x ∈ fs.zip fs', TyEq x.1 x.2) → ∀ {s : Ty},
      Ty.field l ls fs = some s → ∃ s', Ty.field l ls fs' = some s' ∧ TyEq s s'
  | [], _, _, _, _, _, h => by simp [Ty.field] at h
  | _ :: _, [], _, _, _, _, h => by simp [Ty.field] at h
  | _ :: _, _ :: _, [], hl, _, _, _ => by simp at hl
  | l' :: ls, f :: fs, f' :: fs', hl, hz, s, h => by
    simp only [Ty.field] at h ⊢
    split
    · simp_all
    · simp only [*, ite_false] at h
      exact Ty.field_tyEq (by simpa using hl) (fun x hx => hz x (by simp [hx])) h


/-- A record's slot replaced by an equal one, the others kept. -/
theorem Ty.field_replace {l : String} {s s' : Ty} : ∀ {ls : List String} {fs : List Ty},
    Ty.field l ls fs = some s → TyEq s s' →
      ∃ fs', Ty.field l ls fs' = some s' ∧ fs.length = fs'.length ∧
        ∀ x ∈ fs.zip fs', TyEq x.1 x.2
  | [], _, h, _ => by simp [Ty.field] at h
  | _ :: _, [], h, _ => by simp [Ty.field] at h
  | l' :: ls, f :: fs, h, he => by
    simp only [Ty.field] at h
    split at h
    · cases h
      refine ⟨s' :: fs, by simp [Ty.field, *], rfl, fun x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact he
      · obtain ⟨a, b⟩ := x
        have : a = b := by
          induction fs with
          | nil => cases hx
          | cons y ys ih =>
            simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hx
            rcases hx with ⟨rfl, rfl⟩ | hx
            · rfl
            · exact ih hx
        subst this; exact TyEq.refl _
    · obtain ⟨fs', h₁, h₂, h₃⟩ := Ty.field_replace h he
      refine ⟨f :: fs', by simp [Ty.field, *], by simp [h₂], fun x hx => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyEq.refl _
      · exact h₃ x hx

/-- The slots of an object's record type over the labels `L`, the object
having the fields `ls` with the slots `ss`. A field it has is that of its
last occurrence (a later one overrides an earlier, as in JavaScript); one
it doesn't is absent (`Ty.absSlot`). -/
def objSlots (L ls : List String) (ss : List Ty) : List Ty :=
  L.map fun l => (Ty.field l ls.reverse ss.reverse).getD .absSlot

/-- What a spread copies of a slot its operand doesn't write over: a field
that holds a value, as it is; a getter, as what it gives; a prototype
member, nothing; an absent field stays absent. -/
inductive SlotCopy : Ty → Ty → Prop where
  | data : SlotCopy (.slot .pre .data τ) (.slot .pre .data τ)
  | getter : SlotCopy (.slot .pre .getter τ) (.slot .pre .data τ)
  | proto : SlotCopy (.slot .pre .proto τ) .absSlot
  | abs : SlotCopy (.slot .abs k τ) (.slot .abs k τ)

theorem SlotCopy.subst (σ : Subst) (h : SlotCopy s r) : SlotCopy (s.subst σ) (r.subst σ) := by
  cases h <;> simp only [Ty.subst_app, List.map_cons, List.map_nil] <;> constructor

/-- The tag of a variant's case `R` over its field `l`: the string of the
type of `R`'s field `l`, present and holding a value (each looked at
unfolded). -/
def Ty.tagOf (l : String) (R : Ty) : Option String :=
  match R.whnf with
  | .app (.record ls) slots =>
    match Ty.field l ls slots with
    | some s =>
      match s.whnf with
      | .app .slot [p, k, τ] =>
        if p.whnf = .pre ∧ k.whnf = .data then
          match τ.whnf with
          | .app (.strLit t) [] => some t
          | _ => none
        else none
      | _ => none
    | none => none
  | _ => none

/-- The rest of a variant tagged by `l` once a case is taken out, its tags
`ts` and its cases `Rs` left: the one case left as it is (so that its
fields can be read), or a variant of them. -/
def variantRest (d : Disc) (ts : List String) : List Ty → Ty
  | [R] => R
  | Rs => .variant d ts Rs

/-- The first index of `t` in `ts`. -/
def firstIdx (t : String) : List String → Option Nat
  | [] => none
  | x :: xs => if x = t then some 0 else (firstIdx t xs).map (· + 1)

theorem firstIdx_getElem {t : String} : ∀ {ts : List String} {i : Nat},
    firstIdx t ts = some i → ts[i]? = some t
  | [], _, h => by simp [firstIdx] at h
  | x :: xs, i, h => by
    simp only [firstIdx] at h
    split at h
    · cases h; simp_all
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using firstIdx_getElem hj

theorem Ty.tagOf_subst {l : String} {R : Ty} {t : String} (h : R.tagOf l = some t) (σ : Subst) :
    (R.subst σ).tagOf l = some t := by
  unfold Ty.tagOf at h ⊢
  split at h
  · rename_i ls slots hR
    rw [Ty.whnf_subst_of_app hR σ]
    simp only
    rw [Ty.field_subst]
    split at h
    · rename_i s hs
      rw [hs]
      simp only [Option.map_some]
      split at h
      · rename_i p k τ hsw
        rw [Ty.whnf_subst_of_app hsw σ]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_subst_of_app hp σ, Ty.whnf_subst_of_app hk σ]
          simp only [List.map_nil, and_self, ↓reduceIte]
          split at h
          · rename_i t' hτ
            rw [Ty.whnf_subst_of_app hτ σ]
            simpa using h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem eraseIdx_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    (l.map f).eraseIdx i = (l.eraseIdx i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by simp [eraseIdx_map f l i]

theorem variantRest_subst (σ : Subst) (d : Disc) (ts : List String) (Rs : List Ty) :
    (variantRest d ts Rs).subst σ = variantRest d ts (Rs.map (·.subst σ)) := by
  match Rs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp [variantRest]

/-- The instances, as `classes::instances` (and, for `HasProp`, inty's
`resolve_has_prop`). -/
inductive Inst : Pred → Prop where
  /-- `Plus Number`. -/
  | plusNumber : Inst ⟨.plus, [.number]⟩
  /-- `Plus String`. -/
  | plusString : Inst ⟨.plus, [.string]⟩
  /-- `HasProp l {…, l: σ, …} k σ`: a record has the fields that are
  present, of their kind (a getter's type is what it gives). -/
  | hasProp : Ty.field l ls fs = some (.slot .pre k σ) →
      Inst ⟨.hasProp l, [.record ls fs, k, σ]⟩
  /-- `Merge pre data τ s (pre data τ)`: the operand's field wins. -/
  | mergeData : Inst ⟨.merge, [.pre, .data, τ, s, .slot .pre .data τ]⟩
  /-- `Merge pre getter τ s (pre data τ)`: the operand's getter runs, and
  what it gives is copied, as a field that holds a value. -/
  | mergeGetter : Inst ⟨.merge, [.pre, .getter, τ, s, .slot .pre .data τ]⟩
  /-- `Merge abs k τ s r`: the operand hasn't the field, so the slot it is
  written over is copied (`SlotCopy s r`). -/
  | mergeAbs : SlotCopy s r → Inst ⟨.merge, [.abs, k, τ, s, r]⟩
  /-- `Merge pre proto τ s r`: a prototype member isn't copied either. -/
  | mergeProto : SlotCopy s r → Inst ⟨.merge, [.pre, .proto, τ, s, r]⟩
  /-- An array's and a string's `length` (`builtins::resolve_has_prop`),
  which a program reads but doesn't store to, as a getter's. -/
  | lengthArray : Inst ⟨.hasProp "length", [.array τ, .getter, .number]⟩
  | lengthString : Inst ⟨.hasProp "length", [.string, .getter, .number]⟩
  /-- `Indexable τ[] Number τ` and `Indexable String Number String`
  (`resolve_indexable`). -/
  | indexArray : Inst ⟨.indexable, [.array τ, .number, τ]⟩
  | indexString : Inst ⟨.indexable, [.string, .number, .string]⟩
  /-- `IndexWrite τ[]` (`resolve_index_write`). -/
  | writeArray : Inst ⟨.indexWrite, [.array τ]⟩
  /-- `NotNew τ`, for every type but `newTarget`, and but a rigid type
  variable, which may stand for it. -/
  | notNew : ¬ (c = .newTarget ∨ c.isRigid) → Inst ⟨.notNew, [.app c args]⟩
  /-- `Inject T T`, for a `T` without type variables. -/
  | injectSelf : T.ftv = [] → Inst ⟨.inject T, [T]⟩
  /-- `Inject (Nullable σ) Null` and `Inject (Optional σ) Undefined`. -/
  | injectNothing : TyEq T (.maybe z σ) → T.ftv = [] → Inst ⟨.inject T, [z.ty]⟩
  /-- `Inject (Nullable τ) τ`, for a `τ` whose head is known and is neither
  the sum's nor `Null` (and alike for `Optional`): the instances don't
  overlap, so the heads decide which one holds. -/
  | injectSome : TyEq T (.maybe z (.app c args)) → T.ftv = [] → (Ty.app c args).ftv = [] →
      c ≠ .maybe z → ¬ (c = z.con ∧ args = []) → Inst ⟨.inject T, [.app c args]⟩
  /-- `Inject T τ`, `T` a variant told apart by `typeof` (`Number | String`)
  and `τ` its case of the tag `τ`'s head's values have. -/
  | injectArm : T.ftv = [] → T.whnf = .variant .typeOf ts Rs → ts.Nodup → c.typeTag = some t →
      ts[(i : Nat)]? = some t → Rs[i]? = some R → TyEq (.app c args) R →
      (Ty.app c args).ftv = [] → Inst ⟨.inject T, [.app c args]⟩
  /-- `Inject T "s"`, for a `T` a `String` is injected into: a value of a
  string literal type is a string (`subsume`'s `Lit(l) ≤ Base`). -/
  | injectLit : Inst ⟨.inject T, [x]⟩ → TyEq x .string → Inst ⟨.inject T, [.strLit s]⟩
  /-- `Strip (Nullable σ) σ` and `Strip (Optional σ) σ`. -/
  | stripSome : Inst ⟨.strip, [.maybe z σ, σ]⟩
  /-- `Strip τ τ`, for a `τ` whose head is known and is neither a sum nor
  `Null` or `Undefined` (whose values are all nothing). -/
  | stripSelf : (∀ z, c ≠ .maybe z) → c ≠ .null → c ≠ .undefined →
      Inst ⟨.strip, [.app c args, .app c args]⟩
  /-- `Case_{d,t} (variant d ts Rs) R ρ`: the variant's tags differ, `R` is
  the case of the tag `t` and `ρ` the rest. -/
  | caseHit : ts.Nodup → ts[i]? = some t → Rs[i]? = some R →
      Inst ⟨.caseTag d t, [.variant d ts Rs, R, variantRest d (ts.eraseIdx i) (Rs.eraseIdx i)]⟩

/-- Instances are closed under substitution. -/
theorem Inst.subst (σ : Subst) (h : Inst p) : Inst (p.subst σ) := by
  induction h with
  | plusNumber => exact .plusNumber
  | plusString => exact .plusString
  | hasProp hf =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact .hasProp (by rw [Ty.field_subst, hf]; rfl)
  | mergeData => exact .mergeData
  | mergeGetter => exact .mergeGetter
  | mergeAbs hc => exact .mergeAbs (hc.subst σ)
  | mergeProto hc => exact .mergeProto (hc.subst σ)
  | lengthArray => exact .lengthArray
  | lengthString => exact .lengthString
  | indexArray => exact .indexArray
  | indexString => exact .indexString
  | writeArray => exact .writeArray
  | notNew hc => exact .notNew hc
  | injectSelf hT =>
    simp only [Pred.subst, List.map_cons, List.map_nil]
    rw [Ty.subst_id (by simp [hT])]
    exact .injectSelf hT
  | injectNothing he hT =>
    simp only [Pred.subst, List.map_cons, List.map_nil]
    rw [Ty.subst_id (by simp [Nothing.ty])]
    exact .injectNothing he hT
  | injectSome he hT ha hc hn =>
    simp only [Pred.subst, List.map_cons, List.map_nil]
    rw [Ty.subst_id (by simp [ha])]
    exact .injectSome he hT ha hc hn
  | injectArm hT hw hn hc hi hR he ha =>
    simp only [Pred.subst, List.map_cons, List.map_nil]
    rw [Ty.subst_id (by simp [ha])]
    exact .injectArm hT hw hn hc hi hR he ha
  | injectLit _ hx ih =>
    simpa [Pred.subst] using Inst.injectLit ih (by simpa using hx.subst σ)
  | stripSome =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact .stripSome
  | stripSelf hm hn hu =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact .stripSelf hm hn hu
  | caseHit hn hi hR =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app, variantRest_subst,
      ← eraseIdx_map]
    exact .caseHit hn hi (by simp [hR])

/-- The `Merge` constraints of a spread, label by label: the operand's
presences `ps`, kinds `ks` and types `τs`, the slots `ss` it is written
over, and the slots `rs` it gives. -/
def mergePreds : List Ty → List Ty → List Ty → List Ty → List Ty → List Pred
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs =>
    ⟨.merge, [p, k, τ, s, r]⟩ :: mergePreds ps ks τs ss rs
  | _, _, _, _, _ => []

theorem mergePreds_subst (σ : Subst) : ∀ (ps ks τs ss rs : List Ty),
    (mergePreds ps ks τs ss rs).map (·.subst σ) =
      mergePreds (ps.map (·.subst σ)) (ks.map (·.subst σ)) (τs.map (·.subst σ))
        (ss.map (·.subst σ)) (rs.map (·.subst σ))
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs => by
    simp only [mergePreds, List.map_cons, ← mergePreds_subst σ ps ks τs ss rs]; rfl
  | [], _, _, _, _ | _ :: _, [], _, _, _ | _ :: _, _ :: _, [], _, _
  | _ :: _, _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, _ :: _, [] => by
    simp [mergePreds]

/-- The slots of a record, from a presence, a kind and a type each. -/
def slots3 : List Ty → List Ty → List Ty → List Ty
  | p :: ps, k :: ks, τ :: τs => .slot p k τ :: slots3 ps ks τs
  | _, _, _ => []

theorem slots3_subst (σ : Subst) : ∀ (ps ks τs : List Ty),
    (slots3 ps ks τs).map (·.subst σ) =
      slots3 (ps.map (·.subst σ)) (ks.map (·.subst σ)) (τs.map (·.subst σ))
  | p :: ps, k :: ks, τ :: τs => by
    simp only [slots3, List.map_cons, Ty.subst_app, List.map_nil, slots3_subst σ ps ks τs]
  | [], _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] => by simp [slots3]

theorem slots3_length : ∀ (ps ks τs : List Ty), ps.length = ks.length →
    ks.length = τs.length → (slots3 ps ks τs).length = ps.length
  | p :: ps, k :: ks, τ :: τs, h₁, h₂ => by
    simp only [slots3, List.length_cons, slots3_length ps ks τs (by simpa using h₁)
      (by simpa using h₂)]
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h

/-- `p` is an instance up to equal types: a `HasProp` on a recursive type
holds of its unfolding. -/
def InstEq (p : Pred) : Prop := ∃ q, PredEq p q ∧ Inst q

theorem Inst.instEq (h : Inst p) : InstEq p := ⟨p, PredEq.refl p, h⟩

theorem InstEq.subst (σ : Subst) (h : InstEq p) : InstEq (p.subst σ) := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.subst σ, hpq.subst σ, hq.subst σ⟩

theorem zip_tyEq_trans : ∀ {xs ys zs : List Ty}, xs.length = ys.length →
    ys.length = zs.length → (∀ x ∈ xs.zip ys, TyEq x.1 x.2) →
    (∀ x ∈ ys.zip zs, TyEq x.1 x.2) → ∀ x ∈ xs.zip zs, TyEq x.1 x.2
  | [], _, _, _, _, _, _, _, hx => by cases hx
  | _ :: _, [], _, h, _, _, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _, _, _ => by simp at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂, hxy, hyz, w, hw => by
    simp only [List.zip_cons_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact (hxy (x, y) (by simp)).trans (hyz (y, z) (by simp))
    · exact zip_tyEq_trans (by simpa using h₁) (by simpa using h₂)
        (fun a ha => hxy a (by simp [ha])) (fun a ha => hyz a (by simp [ha])) w hw

theorem PredEq.trans {p q r : Pred} (h₁ : PredEq p q) (h₂ : PredEq q r) : PredEq p r :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    zip_tyEq_trans h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2⟩

theorem InstEq.of_predEq {p q : Pred} (h : PredEq p q) (hq : InstEq q) : InstEq p := by
  obtain ⟨r, hqr, hr⟩ := hq
  exact ⟨r, h.trans hqr, hr⟩

/-- Constraints of one class on pairwise equal arguments, given pair by
pair. -/
theorem PredEq.of_pairs {c : Cls} : ∀ {xs ys : List Ty}, xs.length = ys.length →
    (∀ x ∈ xs.zip ys, TyEq x.1 x.2) → PredEq ⟨c, xs⟩ ⟨c, ys⟩ :=
  fun hl h => ⟨rfl, hl, h⟩

theorem zip_tyEq_cons {x y : Ty} {xs ys : List Ty} (h : TyEq x y)
    (hs : ∀ p ∈ xs.zip ys, TyEq p.1 p.2) : ∀ p ∈ (x :: xs).zip (y :: ys), TyEq p.1 p.2 := by
  intro p hp
  simp only [List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact h
  · exact hs p hp

theorem zip_tyEq_nil : ∀ p ∈ ([] : List Ty).zip [], TyEq p.1 p.2 := by simp

/-- A typing system: which constraints hold as instances, and which
expected types it checks against. The narrow system (`Sys.narrow`) is the
one inference implements; the wide one (`Inty.Soundness`) holds of every
instance of a narrow derivation's rigid type variables. -/
structure Sys where
  inst : Pred → Prop
  closed : Ty → Prop
  /-- Instances are up to equal types. -/
  inst_eq : ∀ {p q : Pred}, PredEq p q → inst q → inst p
  /-- The constraint that a value of `τ` is one of `T` (`HasType.inj`). -/
  injPred : Ty → Ty → Pred
  /-- It is up to equal types. -/
  injPred_eq : ∀ {τ τ' T : Ty}, TyEq τ τ' → PredEq (injPred τ T) (injPred τ' T)
  /-- Whether a `let` may give its binding a scheme with any constraints
  (Jones's rule for qualified types), or only one whose constraints are on
  its quantified variables (`Scheme.Simple`), as inty's generalisation
  gives. -/
  anyScheme : Bool
  /-- Whether an assignment to a variable whose type has no type variables
  checks its value against that type (`HasTypeS.assignCheck`), as inty
  subsumes the value into the variable's type. -/
  assignSub : Bool

/-- `p` holds in the system `S` as an instance, or is assumed in `C`, up to
equal types. -/
def EntailsS (S : Sys) (C : List Pred) (p : Pred) : Prop := S.inst p ∨ ∃ q ∈ C, PredEq p q

/-- The system inference implements: its instances (`Inst`, up to equal
types), and expected types without type variables. -/
def Sys.narrow : Sys :=
  ⟨InstEq, fun T => T.ftv = [], fun h hq => InstEq.of_predEq h hq, fun τ T => ⟨.inject T, [τ]⟩,
    fun h => PredEq.of_pairs (by simp) (zip_tyEq_cons h zip_tyEq_nil), false, false⟩

/-- A system whose instances, expected types and injections survive
substitution. -/
structure Sys.Substable (S : Sys) : Prop where
  inst : ∀ (σ : Subst) {p : Pred}, S.inst p → S.inst (p.subst σ)
  closed : ∀ (σ : Subst) {T : Ty}, S.closed T → S.closed (T.subst σ)
  injPred : ∀ (σ : Subst) (τ : Ty) {T : Ty}, S.closed T →
    (S.injPred τ T).subst σ = S.injPred (τ.subst σ) (T.subst σ)

theorem EntailsS.substS {S : Sys} (hS : S.Substable) (σ : Subst) {C : List Pred} {p : Pred}
    (h : EntailsS S C p) : EntailsS S (C.map (·.subst σ)) (p.subst σ) :=
  h.elim (fun h => .inl (hS.inst σ h))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.subst σ, List.mem_map_of_mem hq, hpq.subst σ⟩)

theorem EntailsS.of_predEq {S : Sys} {C : List Pred} {p p' : Pred} (h : PredEq p p')
    (he : EntailsS S C p) : EntailsS S C p' :=
  he.elim (fun hi => .inl (S.inst_eq h.symm hi))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q, hq, h.symm.trans hpq⟩)

theorem EntailsS.of_mem {S : Sys} {C : List Pred} {p : Pred} (h : p ∈ C) : EntailsS S C p :=
  .inr ⟨p, h, PredEq.refl p⟩

/-- `p` is an instance up to equal types, or assumed in `C` up to equal
types. -/
abbrev Entails (C : List Pred) (p : Pred) : Prop := EntailsS Sys.narrow C p

theorem EntailsS.subst (σ : Subst) (h : Entails C p) :
    Entails (C.map (·.subst σ)) (p.subst σ) :=
  h.elim (fun h => .inl (h.subst σ))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.subst σ, List.mem_map_of_mem hq, hpq.subst σ⟩)

theorem EntailsS.of_inst (h : Inst p) : Entails C p := .inl h.instEq



/-- Entailment from more assumptions, each entailed. -/
theorem EntailsS.cut {C D : List Pred} {p : Pred} (h : Entails (C ++ D) p)
    (hD : ∀ d ∈ D, Entails C d) : Entails C p := by
  rcases h with hi | ⟨q, hq, hpq⟩
  · exact .inl hi
  · rcases List.mem_append.mp hq with hq | hq
    · exact .inr ⟨q, hq, hpq⟩
    · exact (hD q hq).of_predEq hpq.symm

theorem EntailsS.weaken {C D : List Pred} {p : Pred} (h : Entails C p) (hCD : ∀ c ∈ C, c ∈ D) :
    Entails D p :=
  h.elim .inl (fun ⟨q, hq, hpq⟩ => .inr ⟨q, hCD q hq, hpq⟩)

/-- Decides `SlotCopy s r`. -/
def slotCopy? : Ty → Ty → Bool
  | .slot .pre .data τ, r => decide (r = .slot .pre .data τ)
  | .slot .pre .getter τ, r => decide (r = .slot .pre .data τ)
  | .slot .pre .proto _, r => decide (r = .absSlot)
  | .slot .abs k τ, r => decide (r = .slot .abs k τ)
  | _, _ => false

theorem slotCopy?_sound {s r : Ty} (h : slotCopy? s r = true) : SlotCopy s r := by
  unfold slotCopy? at h
  split at h <;> first | (cases h; done) | skip
  all_goals (have := of_decide_eq_true h; subst this; constructor)


/-- Decides `Inst` for an `Inject`, on the expected type as it is. -/
def Pred.injectInst (T τ : Ty) : Bool :=
  decide (T.ftv = []) &&
    (decide (τ = T) ||
      match T with
      | .app (.maybe z) [σ] =>
        decide (τ = z.ty) ||
          (decide (σ = τ) &&
            match τ with
            | .app c args => decide (c ≠ .maybe z) && !decide (c = z.con ∧ args = [])
            | _ => false)
      | _ => false)

theorem Pred.injectInst_sound {T τ : Ty} (h : Pred.injectInst T τ = true) :
    Inst ⟨.inject T, [τ]⟩ := by
  unfold Pred.injectInst at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hT, h⟩ := h
  rcases h with rfl | h
  · exact .injectSelf hT
  split at h
  · rename_i z σ
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with rfl | ⟨rfl, h⟩
    · exact .injectNothing (TyEq.refl _) hT
    · split at h
      · rename_i c args
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at h
        refine .injectSome (TyEq.refl _) hT ?_ h.1 h.2
        simpa [Ty.ftv] using hT
      · cases h
  · cases h

/-- Decides `Inst` for a `Strip`. -/
def Pred.stripInst (τ σ : Ty) : Bool :=
  match τ with
  | .app (.maybe _) [σ'] => decide (σ' = σ)
  | .app c args =>
    match c with
    | .maybe _ | .null | .undefined => false
    | _ => decide (σ = .app c args)
  | _ => false

theorem Pred.stripInst_sound {τ σ : Ty} (h : Pred.stripInst τ σ = true) :
    Inst ⟨.strip, [τ, σ]⟩ := by
  unfold Pred.stripInst at h
  split at h
  · have := of_decide_eq_true h; subst this; exact .stripSome
  · rename_i c args _
    split at h
    · cases h
    · cases h
    · cases h
    · rename_i hm hn hu
      have := of_decide_eq_true h; subst this
      exact .stripSelf (fun z h => hm z h) hn hu
  · cases h

/-- Decides `Inst`. -/
def Pred.isInst : Pred → Bool
  | ⟨.plus, [.number]⟩ | ⟨.plus, [.string]⟩ => true
  | ⟨.hasProp l, [.record ls fs, k, σ]⟩ => decide (Ty.field l ls fs = some (.slot .pre k σ))
  | ⟨.merge, [.pre, .data, τ, _, r]⟩ => decide (r = .slot .pre .data τ)
  | ⟨.merge, [.pre, .getter, τ, _, r]⟩ => decide (r = .slot .pre .data τ)
  | ⟨.merge, [.pre, .proto, _, s, r]⟩ => slotCopy? s r
  | ⟨.merge, [.abs, _, _, s, r]⟩ => slotCopy? s r
  | ⟨.hasProp l, [.array _, .getter, .number]⟩ | ⟨.hasProp l, [.string, .getter, .number]⟩ =>
    decide (l = "length")
  | ⟨.indexable, [.array τ, .number, e]⟩ => decide (e = τ)
  | ⟨.indexable, [.string, .number, .string]⟩ => true
  | ⟨.indexWrite, [.array _]⟩ => true
  | ⟨.notNew, [.app c _]⟩ => decide ¬ (c = .newTarget ∨ c.isRigid)
  | ⟨.inject T, [τ]⟩ => Pred.injectInst T τ
  | ⟨.strip, [τ, σ]⟩ => Pred.stripInst τ σ
  | _ => false

theorem Pred.isInst_sound {p : Pred} (h : p.isInst = true) : Inst p := by
  unfold Pred.isInst at h
  split at h
  · exact .plusNumber
  · exact .plusString
  · exact .hasProp (of_decide_eq_true h)
  · rw [of_decide_eq_true h]; exact .mergeData
  · rw [of_decide_eq_true h]; exact .mergeGetter
  · exact .mergeProto (slotCopy?_sound h)
  · exact .mergeAbs (slotCopy?_sound h)
  · rw [of_decide_eq_true h]; exact .lengthArray
  · rw [of_decide_eq_true h]; exact .lengthString
  · rw [of_decide_eq_true h]; exact .indexArray
  · exact .indexString
  · exact .writeArray
  · exact .notNew (by simpa using h)
  · exact Pred.injectInst_sound h
  · exact Pred.stripInst_sound h
  · cases h

theorem List.eq_five_of_length {α : Type} : ∀ {l : List α}, l.length = 5 →
    ∃ a b c d e, l = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

/-- A slot whose presence is a type variable, or present and of a kind
that is one: what is copied of it isn't known. (Each is looked at unfolded.) -/
def Ty.SlotOnVar (s : Ty) : Prop :=
  match s.whnf with
  | .var _ => True
  | .slot p k _ => (∃ a, p.whnf = .var a) ∨ (p.whnf = .pre ∧ ∃ a, k.whnf = .var a)
  | _ => False

/-- Decides `Ty.SlotOnVar`. -/
def Ty.slotOnVar (s : Ty) : Bool :=
  match s.whnf with
  | .var _ => true
  | .slot p k _ => p.whnf.isVar || (decide (p.whnf = .pre) && k.whnf.isVar)
  | _ => false

theorem Ty.isVar_iff {τ : Ty} : τ.isVar = true ↔ ∃ a, τ = .var a := by
  cases τ <;> simp [Ty.isVar]

theorem Ty.slotOnVar_sound {s : Ty} (h : s.slotOnVar = true) : s.SlotOnVar := by
  unfold Ty.slotOnVar at h
  unfold Ty.SlotOnVar
  generalize s.whnf = w at h ⊢
  split at h
  · trivial
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Ty.isVar_iff] at h
    exact h
  · cases h

/-- Equal slots wait alike. -/
theorem Ty.SlotOnVar.tyEq {s s' : Ty} (h : TyEq s s') (hs : s.SlotOnVar) : s'.SlotOnVar := by
  unfold Ty.SlotOnVar at hs ⊢
  generalize hw : s.whnf = w at hs
  match w, hs with
  | .var a, _ => rw [TyEq.whnf_var h hw]; trivial
  | .slot p k τ, hs =>
    obtain ⟨p', k', τ', hw', hp, hk, -⟩ := TyEq.whnf_slot h hw
    rw [hw']
    rcases hs with ⟨a, ha⟩ | ⟨hpre, a, ha⟩
    · exact .inl ⟨a, TyEq.whnf_var hp ha⟩
    · exact .inr ⟨TyEq.whnf_const hp hpre, a, TyEq.whnf_var hk ha⟩

/-- A `Merge` whose decision waits on a type variable: the operand's
field is present, of a kind that is a type variable, or it is a prototype
member or absent and the slot it is written over waits on one. (Each is
looked at unfolded.) -/
def Pred.MergeOnVar (p : Pred) : Prop :=
  match p with
  | ⟨.merge, [q, k, _, s, _]⟩ =>
    (q.whnf = .pre ∧ ∃ a, k.whnf = .var a) ∨
      (((q.whnf = .pre ∧ k.whnf = .proto) ∨ q.whnf = .abs) ∧ s.SlotOnVar)
  | _ => False

/-- Decides `Pred.MergeOnVar`. -/
def Pred.mergeOnVar (p : Pred) : Bool :=
  match p with
  | ⟨.merge, [q, k, _, s, _]⟩ =>
    (decide (q.whnf = .pre) && k.whnf.isVar) ||
      (((decide (q.whnf = .pre) && decide (k.whnf = .proto)) || decide (q.whnf = .abs)) &&
        s.slotOnVar)
  | _ => false

theorem Pred.mergeOnVar_sound {p : Pred} (h : p.mergeOnVar = true) : p.MergeOnVar := by
  unfold Pred.mergeOnVar at h
  unfold Pred.MergeOnVar
  split at h
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Ty.isVar_iff] at h
    exact h.imp id (fun ⟨h₁, h₂⟩ => ⟨h₁, Ty.slotOnVar_sound h₂⟩)
  · cases h

/-- Equal constraints wait alike. -/
theorem Pred.MergeOnVar.predEq {p p' : Pred} (h : PredEq p p') (hp : p.MergeOnVar) :
    p'.MergeOnVar := by
  obtain ⟨c, args⟩ := p
  obtain ⟨c', args'⟩ := p'
  obtain ⟨hc, hl, hz⟩ := h
  simp only at hc hl hz
  subst hc
  unfold Pred.MergeOnVar at hp ⊢
  split at hp
  · rename_i q k τ s r heq
    simp only [Pred.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨q', k', τ', s', r', rfl⟩ := List.eq_five_of_length hl.symm
    · have hq : TyEq q q' := hz (q, q') (by simp)
      have hk : TyEq k k' := hz (k, k') (by simp)
      have hs : TyEq s s' := hz (s, s') (by simp)
      simp only
      rcases hp with ⟨hpre, a, ha⟩ | ⟨hqk, hsv⟩
      · exact .inl ⟨TyEq.whnf_const hq hpre, a, TyEq.whnf_var hk ha⟩
      · refine .inr ⟨?_, hsv.tyEq hs⟩
        rcases hqk with ⟨hpre, hpro⟩ | habs
        · exact .inl ⟨TyEq.whnf_const hq hpre, TyEq.whnf_const hk hpro⟩
        · exact .inr (TyEq.whnf_const hq habs)
  · exact hp.elim

/-- The constraint is on a type variable: its first argument (`Plus`'s
type, `HasProp`'s receiver, `Merge`'s presence) unfolds to one, or it is a
`Merge` waiting on one (`Pred.MergeOnVar`). -/
def Pred.OnVar (p : Pred) : Prop :=
  (∃ t a rest, p.args = t :: rest ∧ t.whnf = .var a) ∨ p.MergeOnVar

/-- Decides `Pred.OnVar`. -/
def Pred.onVar (p : Pred) : Bool :=
  (match p.args with
    | t :: _ => t.whnf.isVar
    | [] => false) || p.mergeOnVar

theorem Pred.onVar_sound {p : Pred} (h : p.onVar = true) : p.OnVar := by
  unfold Pred.onVar at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i t rest he
      obtain ⟨a, ha⟩ := Ty.isVar_iff.mp h
      exact .inl ⟨t, a, rest, he, ha⟩
    · cases h
  · exact .inr (Pred.mergeOnVar_sound h)

/-- Equal constraints are on type variables alike. -/
theorem Pred.OnVar.predEq {p p' : Pred} (h : PredEq p p') (hp : p.OnVar) : p'.OnVar := by
  rcases hp with ⟨t, a, rest, he, ha⟩ | hm
  · obtain ⟨-, hl, hz⟩ := h
    rw [he] at hl hz
    cases hp' : p'.args with
    | nil => rw [hp'] at hl; simp at hl
    | cons t' rest' =>
      rw [hp'] at hz
      exact .inl ⟨t', a, rest', hp', TyEq.whnf_var (hz (t, t') (by simp)) ha⟩
  · exact .inr (hm.predEq h)

/-- Each constraint is an instance (up to equal types) or is on a type
variable. A constraint on
a type variable can't fail: no value has a type variable's type (`V` in
`Inty.Soundness`), so the code that relies on it never runs. inty leaves
such a constraint in place (`Plus a`), or reads a property access on a
receiver nothing pinned down as a field of some object
(`default_has_prop`). -/
def HoldsOrVarS (S : Sys) (C : List Pred) : Prop := ∀ p ∈ C, S.inst p ∨ p.OnVar

/-- In the narrow system. -/
abbrev HoldsOrVar (C : List Pred) : Prop := HoldsOrVarS Sys.narrow C

theorem HoldsOrVarS.append {S : Sys} {C D : List Pred} (hC : HoldsOrVarS S C)
    (hD : HoldsOrVarS S D) : HoldsOrVarS S (C ++ D) :=
  fun c hc => (List.mem_append.mp hc).elim (hC c) (hD c)

theorem EntailsS.holdsOrVar {S : Sys} {C : List Pred} (hC : HoldsOrVarS S C) (h : EntailsS S C p) :
    S.inst p ∨ p.OnVar := by
  rcases h with hi | ⟨q, hq, hpq⟩
  · exact .inl hi
  · exact (hC q hq).imp (S.inst_eq hpq) (Pred.OnVar.predEq hpq.symm)

/-- A constraint of a class other than `Merge` that holds or is on a type
variable: an instance, or its first argument is one. -/
theorem EntailsS.instOrVar {S : Sys} {C : List Pred} (hC : HoldsOrVarS S C) (h : EntailsS S C p)
    (hc : p.cls ≠ .merge) : S.inst p ∨ ∃ t a rest, p.args = t :: rest ∧ t.whnf = .var a := by
  rcases h.holdsOrVar hC with h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨c, args⟩ := p
    exfalso
    unfold Pred.MergeOnVar at h
    split at h <;> simp_all

/-- A constraint with its arguments unfolded. -/
def Pred.whnfArgs (p : Pred) : Pred := ⟨p.cls, p.args.map Ty.whnf⟩

theorem Pred.predEq_whnfArgs (p : Pred) : PredEq p p.whnfArgs := by
  refine ⟨rfl, by simp [Pred.whnfArgs], fun x hx => ?_⟩
  simp only [Pred.whnfArgs] at hx
  rw [List.zip_map_right] at hx
  obtain ⟨⟨y, z⟩, hyz, rfl⟩ := List.mem_map.mp hx
  obtain ⟨rfl, -⟩ := mem_zip_self hyz
  exact (TyEq.whnf y).symm

/-- Decides whether a constraint left at the top level is fine: an instance
(its arguments unfolded), or on a type variable. -/
def Pred.settled (p : Pred) : Bool := p.whnfArgs.isInst || p.onVar

theorem HoldsOrVar.of_settled {C : List Pred} (h : C.all Pred.settled = true) : HoldsOrVar C :=
  fun p hp => by
    have := List.all_eq_true.mp h p hp
    simp only [Pred.settled, Bool.or_eq_true] at this
    exact this.imp (fun h => InstEq.of_predEq (Pred.predEq_whnfArgs p)
      (Pred.isInst_sound h).instEq) Pred.onVar_sound

theorem Subst.find_mem : ∀ {σ : Subst} {a : Nat} {τ : Ty}, σ.find a = some τ → (a, τ) ∈ σ
  | [], _, _, h => by simp [Subst.find] at h
  | (b, τ') :: σ, a, τ, h => by
    simp only [Subst.find] at h
    split at h
    · cases h; subst_vars; simp
    · exact List.mem_cons_of_mem _ (Subst.find_mem h)

theorem Subst.find_of_mem : ∀ {σ : Subst} {a : Nat} {τ : Ty}, (a, τ) ∈ σ →
    ∃ τ', σ.find a = some τ'
  | [], _, _, h => by cases h
  | (b, τ') :: σ, a, τ, h => by
    simp only [Subst.find]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      rcases List.mem_cons.mp h with h | h
      · cases h; exact absurd rfl hne
      · exact Subst.find_of_mem h

end Inty
