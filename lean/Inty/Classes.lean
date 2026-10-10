import Inty.Equi

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


/-- The slots of an object literal's record type over the labels `L`, the
literal having the fields `ls` of the types `τs`. A field it has is
present, at the type of its last occurrence (a later one overrides an
earlier, as in JavaScript); one it doesn't is absent, at any type
(`absent`), as in Rémy's rows, where an absent field has no type. -/
def objSlots (L ls : List String) (τs absent : List Ty) : List Ty :=
  (L.zip absent).map fun p =>
    match Ty.field p.1 ls.reverse τs.reverse with
    | some τ => .slot .pre τ
    | none => .slot .abs p.2

/-- The instances, as `classes::instances` (and, for `HasProp`, inty's
`resolve_has_prop`). -/
inductive Inst : Pred → Prop where
  /-- `Plus Number`. -/
  | plusNumber : Inst ⟨.plus, [.number]⟩
  /-- `Plus String`. -/
  | plusString : Inst ⟨.plus, [.string]⟩
  /-- `HasProp l {…, l: σ, …} σ`: a record has the fields that are
  present. -/
  | hasProp : Ty.field l ls fs = some (.slot .pre σ) → Inst ⟨.hasProp l, [.record ls fs, σ]⟩
  /-- `Merge pre τ s (pre τ)`: the operand's field wins. -/
  | mergePre : Inst ⟨.merge, [.pre, τ, s, .slot .pre τ]⟩
  /-- `Merge abs τ s s`: the operand hasn't the field, so the slot it is
  written over stays. -/
  | mergeAbs : Inst ⟨.merge, [.abs, τ, s, s]⟩
  /-- An array's and a string's `length` (`builtins::resolve_has_prop`). -/
  | lengthArray : Inst ⟨.hasProp "length", [.array τ, .number]⟩
  | lengthString : Inst ⟨.hasProp "length", [.string, .number]⟩
  /-- `Indexable τ[] Number τ` and `Indexable String Number String`
  (`resolve_indexable`). -/
  | indexArray : Inst ⟨.indexable, [.array τ, .number, τ]⟩
  | indexString : Inst ⟨.indexable, [.string, .number, .string]⟩
  /-- `IndexWrite τ[]` (`resolve_index_write`). -/
  | writeArray : Inst ⟨.indexWrite, [.array τ]⟩
  /-- `FieldWrite {…}` (`resolve_field_write`). -/
  | writeRecord : Inst ⟨.fieldWrite, [.record ls slots]⟩

/-- Instances are closed under substitution. -/
theorem Inst.subst (σ : Subst) (h : Inst p) : Inst (p.subst σ) := by
  cases h with
  | plusNumber => exact .plusNumber
  | plusString => exact .plusString
  | hasProp hf =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst_app]
    exact .hasProp (by rw [Ty.field_subst, hf]; rfl)
  | mergePre => exact .mergePre
  | mergeAbs => exact .mergeAbs
  | lengthArray => exact .lengthArray
  | lengthString => exact .lengthString
  | indexArray => exact .indexArray
  | indexString => exact .indexString
  | writeArray => exact .writeArray
  | writeRecord => exact .writeRecord

/-- The `Merge` constraints of a spread, label by label: the operand's
presences `ps` and types `τs`, the slots `ss` it is written over, and the
slots `rs` it gives. -/
def mergePreds : List Ty → List Ty → List Ty → List Ty → List Pred
  | p :: ps, τ :: τs, s :: ss, r :: rs => ⟨.merge, [p, τ, s, r]⟩ :: mergePreds ps τs ss rs
  | _, _, _, _ => []

theorem mergePreds_subst (σ : Subst) : ∀ (ps τs ss rs : List Ty),
    (mergePreds ps τs ss rs).map (·.subst σ) =
      mergePreds (ps.map (·.subst σ)) (τs.map (·.subst σ)) (ss.map (·.subst σ))
        (rs.map (·.subst σ))
  | p :: ps, τ :: τs, s :: ss, r :: rs => by
    simp only [mergePreds, List.map_cons, ← mergePreds_subst σ ps τs ss rs]; rfl
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, [] => by
    simp [mergePreds]

theorem zipWith_slot_subst (σ : Subst) (ps τs : List Ty) :
    (List.zipWith Ty.slot ps τs).map (·.subst σ) =
      List.zipWith Ty.slot (ps.map (·.subst σ)) (τs.map (·.subst σ)) := by
  simp [List.map_zipWith, List.zipWith_map]

/-- `p` is an instance up to equal types: a `HasProp` on a recursive type
holds of its unfolding. -/
def InstEq (p : Pred) : Prop := ∃ q, PredEq p q ∧ Inst q

theorem Inst.instEq (h : Inst p) : InstEq p := ⟨p, PredEq.refl p, h⟩

theorem InstEq.subst (σ : Subst) (h : InstEq p) : InstEq (p.subst σ) := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.subst σ, hpq.subst σ, hq.subst σ⟩

/-- `p` is an instance up to equal types, or assumed in `C`. -/
def Entails (C : List Pred) (p : Pred) : Prop := InstEq p ∨ p ∈ C

theorem Entails.subst (σ : Subst) (h : Entails C p) :
    Entails (C.map (·.subst σ)) (p.subst σ) :=
  h.elim (fun h => .inl (h.subst σ)) (fun h => .inr (List.mem_map_of_mem h))

theorem Entails.of_inst (h : Inst p) : Entails C p := .inl h.instEq

/-- `p` is an instance, or assumed in `C`: entailment with types compared
syntactically, the fragment inference is complete for (`HasType₀`). -/
def Entails₀ (C : List Pred) (p : Pred) : Prop := Inst p ∨ p ∈ C

theorem Entails₀.subst (σ : Subst) (h : Entails₀ C p) :
    Entails₀ (C.map (·.subst σ)) (p.subst σ) :=
  h.elim (fun h => .inl (h.subst σ)) (fun h => .inr (List.mem_map_of_mem h))

theorem Entails₀.entails (h : Entails₀ C p) : Entails C p := h.imp Inst.instEq id

/-- Decides `Inst`. -/
def Pred.isInst : Pred → Bool
  | ⟨.plus, [.number]⟩ | ⟨.plus, [.string]⟩ => true
  | ⟨.hasProp l, [.record ls fs, σ]⟩ => decide (Ty.field l ls fs = some (.slot .pre σ))
  | ⟨.merge, [.pre, τ, _, r]⟩ => decide (r = .slot .pre τ)
  | ⟨.merge, [.abs, _, s, r]⟩ => decide (r = s)
  | ⟨.hasProp l, [.array _, .number]⟩ | ⟨.hasProp l, [.string, .number]⟩ => decide (l = "length")
  | ⟨.indexable, [.array τ, .number, e]⟩ => decide (e = τ)
  | ⟨.indexable, [.string, .number, .string]⟩ => true
  | ⟨.indexWrite, [.array _]⟩ => true
  | ⟨.fieldWrite, [.record _ _]⟩ => true
  | _ => false

theorem Pred.isInst_sound {p : Pred} (h : p.isInst = true) : Inst p := by
  unfold Pred.isInst at h
  split at h
  · exact .plusNumber
  · exact .plusString
  · exact .hasProp (of_decide_eq_true h)
  · rw [of_decide_eq_true h]; exact .mergePre
  · rw [of_decide_eq_true h]; exact .mergeAbs
  · rw [of_decide_eq_true h]; exact .lengthArray
  · rw [of_decide_eq_true h]; exact .lengthString
  · rw [of_decide_eq_true h]; exact .indexArray
  · exact .indexString
  · exact .writeArray
  · exact .writeRecord
  · cases h

/-- The constraint is on a type variable: its first argument (`Plus`'s
type, `HasProp`'s receiver, `Merge`'s presence) is one. -/
def Pred.OnVar (p : Pred) : Prop := ∃ a rest, p.args = .var a :: rest

/-- Decides `Pred.OnVar`. -/
def Pred.onVar (p : Pred) : Bool :=
  match p.args with
  | .var _ :: _ => true
  | _ => false

theorem Pred.onVar_sound {p : Pred} (h : p.onVar = true) : p.OnVar := by
  unfold Pred.onVar at h
  split at h
  · exact ⟨_, _, ‹_›⟩
  · cases h

/-- Each constraint is an instance (up to equal types) or is on a type
variable. A constraint on
a type variable can't fail: no value has a type variable's type (`V` in
`Inty.Soundness`), so the code that relies on it never runs. inty leaves
such a constraint in place (`Plus a`), or reads a property access on a
receiver nothing pinned down as a field of some object
(`default_has_prop`). -/
def HoldsOrVar (C : List Pred) : Prop := ∀ p ∈ C, InstEq p ∨ p.OnVar

theorem HoldsOrVar.append {C D : List Pred} (hC : HoldsOrVar C) (hD : HoldsOrVar D) :
    HoldsOrVar (C ++ D) :=
  fun c hc => (List.mem_append.mp hc).elim (hC c) (hD c)

theorem Entails.holdsOrVar {C : List Pred} (hC : HoldsOrVar C) (h : Entails C p) :
    InstEq p ∨ p.OnVar :=
  h.elim .inl (hC p)

/-- Decides whether a constraint left at the top level is fine: an instance,
or on a type variable. -/
def Pred.settled (p : Pred) : Bool := p.isInst || p.onVar

theorem HoldsOrVar.of_settled {C : List Pred} (h : C.all Pred.settled = true) : HoldsOrVar C :=
  fun p hp => by
    have := List.all_eq_true.mp h p hp
    simp only [Pred.settled, Bool.or_eq_true] at this
    exact this.imp (fun h => (Pred.isInst_sound h).instEq) Pred.onVar_sound

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
