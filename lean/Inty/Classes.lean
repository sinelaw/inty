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

/-- Instances are closed under substitution. -/
theorem Inst.subst (σ : Subst) (h : Inst p) : Inst (p.subst σ) := by
  cases h with
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
  · cases h

/-- A slot whose presence is a type variable, or present and of a kind
that is one: what is copied of it isn't known. -/
def Ty.SlotOnVar : Ty → Prop
  | .var _ => True
  | .slot (.var _) _ _ => True
  | .slot .pre (.var _) _ => True
  | _ => False

/-- Decides `Ty.SlotOnVar`. -/
def Ty.slotOnVar : Ty → Bool
  | .var _ => true
  | .slot (.var _) _ _ => true
  | .slot .pre (.var _) _ => true
  | _ => false

theorem Ty.slotOnVar_sound {s : Ty} (h : s.slotOnVar = true) : s.SlotOnVar := by
  unfold Ty.slotOnVar at h
  split at h <;> first | trivial | cases h

/-- A `Merge` whose decision waits on a type variable: the operand's
field is present, of a kind that is a type variable, or it is a prototype
member or absent and the slot it is written over waits on one. -/
def Pred.MergeOnVar : Pred → Prop
  | ⟨.merge, [.pre, .var _, _, _, _]⟩ => True
  | ⟨.merge, [.pre, .proto, _, s, _]⟩ => s.SlotOnVar
  | ⟨.merge, [.abs, _, _, s, _]⟩ => s.SlotOnVar
  | _ => False

/-- Decides `Pred.MergeOnVar`. -/
def Pred.mergeOnVar : Pred → Bool
  | ⟨.merge, [.pre, .var _, _, _, _]⟩ => true
  | ⟨.merge, [.pre, .proto, _, s, _]⟩ => s.slotOnVar
  | ⟨.merge, [.abs, _, _, s, _]⟩ => s.slotOnVar
  | _ => false

theorem Pred.mergeOnVar_sound {p : Pred} (h : p.mergeOnVar = true) : p.MergeOnVar := by
  unfold Pred.mergeOnVar at h
  split at h
  · trivial
  · exact Ty.slotOnVar_sound h
  · exact Ty.slotOnVar_sound h
  · cases h

/-- The constraint is on a type variable: its first argument (`Plus`'s
type, `HasProp`'s receiver, `Merge`'s presence) is one, or it is a `Merge`
waiting on one (`Pred.MergeOnVar`). -/
def Pred.OnVar (p : Pred) : Prop := (∃ a rest, p.args = .var a :: rest) ∨ p.MergeOnVar

/-- Decides `Pred.OnVar`. -/
def Pred.onVar (p : Pred) : Bool :=
  match p.args with
  | .var _ :: _ => true
  | _ => p.mergeOnVar

theorem Pred.onVar_sound {p : Pred} (h : p.onVar = true) : p.OnVar := by
  unfold Pred.onVar at h
  split at h
  · exact .inl ⟨_, _, ‹_›⟩
  · exact .inr (Pred.mergeOnVar_sound h)

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

/-- A constraint of a class other than `Merge` that holds or is on a type
variable: an instance, or its first argument is one. -/
theorem Entails.instOrVar {C : List Pred} (hC : HoldsOrVar C) (h : Entails C p)
    (hc : p.cls ≠ .merge) : InstEq p ∨ ∃ a rest, p.args = .var a :: rest := by
  rcases h.holdsOrVar hC with h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨c, args⟩ := p
    exfalso
    unfold Pred.MergeOnVar at h
    split at h <;> simp_all

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
