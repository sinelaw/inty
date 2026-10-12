import Inty.Clock

/-!
# Programs that can't run out of clock

The clock counts calls and loop iterations (`call`, `callClosure`, the
`while` rule), and nothing else times out. So a program that makes no call,
runs no loop and defines no getter (a getter is a call made by a read) never
times out, whatever the clock, even none (`run_noClock`, `eval_noClock`):
soundness's timeout case can't hold of every program for want of clock.
-/

namespace Inty

mutual
/-- Whether a program makes no call (no call, method call or `new`), runs no
loop, and defines no getter, in an object literal or a class. A function's
body never runs in such a program, so it may be anything. -/
def Expr.noClock : Expr → Bool
  | .app .. | .new_ .. | .mcall .. | .while_ .. => false
  | .lit _ | .var _ | .break_ | .continue_ | .func .. | .ctor .. => true
  | .let_ _ _ e₁ e₂ => e₁.noClock && e₂.noClock
  | .assign _ e | .unop _ e | .ret e | .throw_ e | .get e _ => e.noClock
  | .cond c t e | .setIndex c t e | .unwrap c t e | .caseTag c _ _ t e =>
    c.noClock && t.noClock && e.noClock
  | .binop _ e₁ e₂ | .seq e₁ e₂ | .tryFinally e₁ e₂ | .spread e₁ e₂ | .index e₁ e₂
  | .tryCatch e₁ e₂ | .set e₁ _ e₂ => e₁.noClock && e₂.noClock
  | .arr es => Expr.noClockList es
  | .obj _ es ks => Expr.noClockList es && !ks.contains .getter
  | .cls _ es ks => Expr.noClockList es && !ks.contains .getter
/-- `noClock`, for a list of expressions. -/
def Expr.noClockList : List Expr → Bool
  | [] => true
  | e :: es => e.noClock && Expr.noClockList es
end

@[simp] theorem Expr.noClockList_eq (es : List Expr) : Expr.noClockList es = es.all Expr.noClock := by
  induction es <;> simp_all [Expr.noClockList]

/-! ## The invariant

The values a program computes are never a cell's contents (`Value.plain`);
an object's cell has no getter, and its members and an array's elements are
plain; and the variables' cells hold plain values. -/

/-- A value a program computes, not an object's or an array's cell. -/
def Value.plain : Value → Bool
  | .fields _ | .items _ => false
  | _ => true

/-- A cell without getters, holding plain values. -/
def Value.CellOK : Value → Prop
  | .fields fs => ∀ m ∈ fs, m.2.1 ≠ .getter ∧ m.2.1 ≠ .protoGetter ∧ m.2.2.plain = true
  | .items vs => ∀ v ∈ vs, v.plain = true
  | _ => True

def NoGetterHeap (h : Heap) : Prop := ∀ c ∈ h, c.CellOK

/-- The variables' cells hold plain values. -/
def PlainEnv (env : Env) (h : Heap) : Prop := ∀ ℓ ∈ env, ∃ v, h[ℓ]? = some v ∧ v.plain = true

/-- A cell holding a plain value still holds one. -/
def HeapExt (h h' : Heap) : Prop :=
  ∀ (ℓ : Nat) (v : Value), h[ℓ]? = some v → v.plain = true →
    ∃ v' : Value, h'[ℓ]? = some v' ∧ v'.plain = true

/-- An outcome that isn't a timeout, with a plain value if any. -/
def Result.Good : Result → Prop
  | .timeout => False
  | .ok v | .returned v | .thrown v => v.plain = true
  | _ => True

def Ran.Good (h₀ : Heap) (p : Ran) : Prop := p.1.Good ∧ NoGetterHeap p.2.2 ∧ HeapExt h₀ p.2.2

def RanArgs.Good (h₀ : Heap) (p : RanArgs) : Prop :=
  (match p.1 with
    | .ok vs => ∀ v ∈ vs, v.plain = true
    | .error r => r.Good) ∧ NoGetterHeap p.2.2 ∧ HeapExt h₀ p.2.2

def RanFields.Good (h₀ : Heap) (p : RanFields) : Prop :=
  (match p.1 with
    | .ok fs => ∀ m ∈ fs, m.2.1 = .data ∧ m.2.2.plain = true
    | .error r => r.Good) ∧ NoGetterHeap p.2.2 ∧ HeapExt h₀ p.2.2

theorem HeapExt.refl (h : Heap) : HeapExt h h := fun _ v hv hp => ⟨v, hv, hp⟩

theorem HeapExt.trans {h₁ h₂ h₃ : Heap} (a : HeapExt h₁ h₂) (b : HeapExt h₂ h₃) : HeapExt h₁ h₃ :=
  fun ℓ v hv hp => let ⟨v', hv', hp'⟩ := a ℓ v hv hp; b ℓ v' hv' hp'

theorem PlainEnv.mono {env : Env} {h h' : Heap} (he : PlainEnv env h) (hx : HeapExt h h') : PlainEnv env h' :=
  fun ℓ hℓ => let ⟨v, hv, hp⟩ := he ℓ hℓ; hx ℓ v hv hp

theorem HeapExt.append (h : Heap) (v : Value) : HeapExt h (h ++ [v]) := fun ℓ w hw hp =>
  ⟨w, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1]; exact hw, hp⟩

theorem NoGetterHeap.append {h : Heap} (hh : NoGetterHeap h) {v : Value} (hv : v.CellOK) : NoGetterHeap (h ++ [v]) :=
  fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hh c hc
    · simp at hc; subst hc; exact hv

theorem Value.CellOK.of_plain {v : Value} (h : v.plain = true) : v.CellOK := by
  cases v <;> simp_all [Value.plain, Value.CellOK]

theorem PlainEnv.push {env : Env} {h : Heap} (he : PlainEnv env h) {v : Value} (hv : v.plain = true) :
    PlainEnv (h.length :: env) (h ++ [v]) := by
  intro ℓ hℓ
  rcases List.mem_cons.mp hℓ with rfl | hℓ
  · exact ⟨v, by simp, hv⟩
  · exact (he.mono (HeapExt.append h v)) ℓ hℓ

/-! ## Each step keeps it -/

theorem bindC_good {h₀ : Heap} {p : Ran} {K : Value → Nat → Heap → Ran} (hp : p.Good h₀)
    (hK : ∀ v c h, p = (.ok v, c, h) → v.plain = true → NoGetterHeap h → HeapExt h₀ h →
      (K v c h).Good h₀) : (bindC p K).Good h₀ := by
  obtain ⟨r, c, h⟩ := p
  cases r with
  | ok v => exact hK v c h rfl hp.1 hp.2.1 hp.2.2
  | _ => exact hp

theorem bindArgs_good {h₀ : Heap} {p : RanArgs} {K : List Value → Nat → Heap → Ran}
    (hp : p.Good h₀)
    (hK : ∀ vs c h, p = (.ok vs, c, h) → (∀ v ∈ vs, v.plain = true) → NoGetterHeap h → HeapExt h₀ h →
      (K vs c h).Good h₀) : (bindArgs p K).Good h₀ := by
  obtain ⟨r, c, h⟩ := p
  cases r with
  | ok vs => exact hK vs c h rfl hp.1 hp.2.1 hp.2.2
  | error r => exact hp

theorem bindFields_good {h₀ : Heap} {p : RanFields}
    {K : List (String × MemberKind × Value) → Nat → Heap → Ran} (hp : p.Good h₀)
    (hK : ∀ fs c h, p = (.ok fs, c, h) → (∀ m ∈ fs, m.2.1 = .data ∧ m.2.2.plain = true) →
      NoGetterHeap h → HeapExt h₀ h → (K fs c h).Good h₀) : (bindFields p K).Good h₀ := by
  obtain ⟨r, c, h⟩ := p
  cases r with
  | ok fs => exact hK fs c h rfl hp.1 hp.2.1 hp.2.2
  | error r => exact hp

theorem lookup_mem_of_some {fs : List (String × MemberKind × Value)} {l : String}
    {m : MemberKind × Value} (h : fs.lookup l = some m) : (l, m) ∈ fs := by
  induction fs with
  | nil => simp at h
  | cons p fs ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk; simp at h hk; subst h hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_mem_of_some' {α : Type} {fs : List (String × α)} {l : String} {m : α}
    (h : fs.lookup l = some m) : (l, m) ∈ fs := by
  induction fs with
  | nil => simp at h
  | cons p fs ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk; simp at h hk; subst h hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- A member read from a cell without getters is a plain value. -/
theorem readMember_good {fs : List (String × MemberKind × Value)} (hc : (Value.fields fs).CellOK)
    {l : String} {r : Read} (h : readMember fs l = some r) : ∃ w, r = .value w ∧ w.plain = true := by
  unfold readMember at h
  split at h
  · rename_i v hl
    cases h; exact ⟨v, rfl, (hc _ (lookup_mem_of_some hl)).2.2⟩
  · rename_i v hl
    cases h; exact ⟨v, rfl, (hc _ (lookup_mem_of_some hl)).2.2⟩
  · rename_i v hl
    exact absurd rfl (hc _ (lookup_mem_of_some hl)).1
  · rename_i v hl
    exact absurd rfl (hc _ (lookup_mem_of_some hl)).2.1
  · cases h

/-- A read in a heap without getters finds a plain value, or fails without
running out of clock. -/
theorem Value.read_good {h : Heap} (hh : NoGetterHeap h) (v : Value) (l : String) :
    (∃ w, v.read h l = .value w ∧ w.plain = true) ∨
      ∃ r, v.read h l = .fail r ∧ r.Good ∧ ∀ w, r ≠ .ok w := by
  unfold Value.read
  split
  · split
    · rename_i fs hfs
      cases hr : readMember fs l with
      | none => exact .inr ⟨_, rfl, trivial, nofun⟩
      | some r =>
        obtain ⟨w, rfl, hw⟩ := readMember_good (hh _ (List.mem_of_getElem? hfs)) hr
        exact .inl ⟨w, rfl, hw⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · split
    · split
      · exact .inl ⟨_, rfl, rfl⟩
      · exact .inr ⟨_, rfl, trivial, nofun⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · split
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · exact .inr ⟨_, rfl, trivial, nofun⟩

theorem Value.index_good {h : Heap} (hh : NoGetterHeap h) (v i : Value) :
    (∃ w, v.index h i = .value w ∧ w.plain = true) ∨
      ∃ r, v.index h i = .fail r ∧ r.Good ∧ ∀ w, r ≠ .ok w := by
  unfold Value.index
  split
  · split
    · rename_i vs hvs
      split
      · rename_i w hw
        simp only [Option.bind_eq_some_iff] at hw
        obtain ⟨k, -, hk⟩ := hw
        exact .inl ⟨w, rfl, hh _ (List.mem_of_getElem? hvs) w (List.mem_of_getElem? hk)⟩
      · exact .inr ⟨_, rfl, trivial, nofun⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · split
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · split
    · rename_i fs hfs
      cases hr : readMember fs _ with
      | none => exact .inl ⟨_, rfl, rfl⟩
      | some r =>
        obtain ⟨w, rfl, hw⟩ := readMember_good (hh _ (List.mem_of_getElem? hfs)) hr
        exact .inl ⟨w, rfl, hw⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · split
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl, trivial, nofun⟩
  · exact .inr ⟨_, rfl, trivial, nofun⟩

theorem getter_good {h : Heap} (hh : NoGetterHeap h) {r : Read}
    (hr : (∃ w, r = .value w ∧ w.plain = true) ∨ ∃ res, r = .fail res ∧ res.Good ∧ ∀ w, res ≠ .ok w)
    (clock : Nat) (vo : Value) : (getter clock h vo r).Good h := by
  rcases hr with ⟨w, rfl, hw⟩ | ⟨res, rfl, hres, -⟩
  · rw [getter]; exact ⟨hw, hh, HeapExt.refl h⟩
  · rw [getter]; exact ⟨hres, hh, HeapExt.refl h⟩

theorem Ran.Good.weaken {h₀ h₁ : Heap} {p : Ran} (hx : HeapExt h₀ h₁) (hp : p.Good h₁) : p.Good h₀ :=
  ⟨hp.1, hp.2.1, hx.trans hp.2.2⟩

theorem RanArgs.Good.weaken {h₀ h₁ : Heap} {p : RanArgs} (hx : HeapExt h₀ h₁) (hp : p.Good h₁) :
    p.Good h₀ :=
  ⟨hp.1, hp.2.1, hx.trans hp.2.2⟩

theorem RanFields.Good.weaken {h₀ h₁ : Heap} {p : RanFields} (hx : HeapExt h₀ h₁)
    (hp : p.Good h₁) : p.Good h₀ :=
  ⟨hp.1, hp.2.1, hx.trans hp.2.2⟩

/-- Replacing a cell that isn't a plain value. -/
theorem HeapExt.set_cell {h : Heap} {ℓ : Nat} {c₀ c : Value} (h₀ : h[ℓ]? = some c₀)
    (hc₀ : c₀.plain = false) : HeapExt h (h.set ℓ c) := fun ℓ' v hv hp => by
  refine ⟨v, ?_, hp⟩
  rw [List.getElem?_set]
  split
  · subst_vars; rw [h₀] at hv; cases hv; simp_all
  · exact hv

/-- Replacing a cell with a plain value. -/
theorem HeapExt.set_plain {h : Heap} {ℓ : Nat} {c : Value} (hc : c.plain = true) :
    HeapExt h (h.set ℓ c) := fun ℓ' v hv hp => by
  rw [List.getElem?_set]
  split
  · rename_i he; subst he
    exact ⟨c, by simp [(List.getElem?_eq_some_iff.mp hv).1], hc⟩
  · exact ⟨v, hv, hp⟩

theorem NoGetterHeap.set {h : Heap} (hh : NoGetterHeap h) {ℓ : Nat} {c : Value} (hc : c.CellOK) :
    NoGetterHeap (h.set ℓ c) := fun x hx =>
  (List.mem_or_eq_of_mem_set hx).elim (hh x) (fun e => e ▸ hc)

theorem Value.setProp_good {h : Heap} (hh : NoGetterHeap h) (o : Value) (l : String) {v : Value}
    (hv : v.plain = true) :
    (o.setProp h l v).1.Good ∧ NoGetterHeap (o.setProp h l v).2 ∧ HeapExt h (o.setProp h l v).2 := by
  unfold Value.setProp
  split
  · split
    · rename_i ℓ fs hfs
      have hc := hh _ (List.mem_of_getElem? hfs)
      split
      · exact ⟨trivial, hh, HeapExt.refl h⟩
      · exact ⟨trivial, hh, HeapExt.refl h⟩
      · refine ⟨hv, hh.set fun m hm => ?_, HeapExt.set_cell hfs rfl⟩
        simp only [replaceField, List.mem_map] at hm
        obtain ⟨p, hp, rfl⟩ := hm
        split
        · exact ⟨nofun, nofun, hv⟩
        · exact hc p hp
      · refine ⟨hv, hh.set fun m hm => ?_, HeapExt.set_cell hfs rfl⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨nofun, nofun, hv⟩
        · exact hc m ((List.mem_filter.mp hm).1)
    · exact ⟨trivial, hh, HeapExt.refl h⟩
  · exact ⟨trivial, hh, HeapExt.refl h⟩

theorem Value.setIndex_good {h : Heap} (hh : NoGetterHeap h) (o i : Value) {v : Value}
    (hv : v.plain = true) :
    (o.setIndex h i v).1.Good ∧ NoGetterHeap (o.setIndex h i v).2 ∧ HeapExt h (o.setIndex h i v).2 := by
  unfold Value.setIndex
  split
  · split
    · rename_i ℓ n vs hvs
      have hc := hh _ (List.mem_of_getElem? hvs)
      split
      · split
        · refine ⟨hv, hh.set fun x hx => ?_, HeapExt.set_cell hvs rfl⟩
          exact (List.mem_or_eq_of_mem_set hx).elim (hc x) (fun e => e ▸ hv)
        · split
          · refine ⟨hv, hh.set fun x hx => ?_, HeapExt.set_cell hvs rfl⟩
            rcases List.mem_append.mp hx with hx | hx
            · exact hc x hx
            · simp at hx; subst hx; exact hv
          · exact ⟨trivial, hh, HeapExt.refl h⟩
      · exact ⟨trivial, hh, HeapExt.refl h⟩
    · exact ⟨trivial, hh, HeapExt.refl h⟩
  · exact Value.setProp_good hh _ _ hv
  · exact ⟨trivial, hh, HeapExt.refl h⟩

theorem copyOwn_good {h : Heap} (hh : NoGetterHeap h) (vo : Value) :
    ∀ (fs : List (String × MemberKind × Value)) (clock : Nat), (copyOwn clock h vo fs).Good h
  | [], clock => by rw [copyOwn]; exact ⟨by simp, hh, HeapExt.refl h⟩
  | (l, m, _) :: fs, clock => by
    rw [copyOwn]
    split
    · rcases Value.read_good hh vo l with ⟨w, hw, hwp⟩ | ⟨r, hr, hrg, hrok⟩
      · have ih := copyOwn_good hh vo fs (min clock clock)
        rcases hcp : copyOwn (min clock clock) h vo fs with ⟨r, c, h'⟩
        rw [hcp] at ih
        cases r with
        | ok cs =>
          simp only [hw, getter, hcp]
          refine ⟨fun x hx => ?_, ih.2.1, ih.2.2⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨rfl, hwp⟩
          · exact ih.1 x hx
        | error r => simp only [hw, getter, hcp]; exact ih
      · cases r with
        | ok w => exact absurd rfl (hrok w)
        | _ => simp only [hr, getter]; exact ⟨hrg, hh, HeapExt.refl h⟩
    · exact copyOwn_good hh vo fs clock

theorem own_good {h : Heap} (hh : NoGetterHeap h) (clock : Nat) (v : Value) : (own clock h v).Good h := by
  rw [own.eq_def]
  split
  next ℓ =>
    split
    next fs hfs =>
      have := copyOwn_good hh (.obj ℓ) (dedupLabels fs).reverse clock
      rcases hcp : copyOwn clock h (.obj ℓ) (dedupLabels fs).reverse with ⟨r, c, h'⟩
      rw [hcp] at this
      cases r with
      | ok cs =>
        simp only
        exact ⟨fun x hx => this.1 x (List.mem_reverse.mp hx), this.2.1, this.2.2⟩
      | error r => simp only; exact this
    next => exact ⟨trivial, hh, HeapExt.refl h⟩
  next => exact ⟨trivial, hh, HeapExt.refl h⟩

theorem mergeLabels_mem {α : Type} : ∀ {xs : List (String × α)} {m : String × α},
    m ∈ mergeLabels xs → ∃ x ∈ xs, m.2 = x.2
  | [], _, h => by simp [mergeLabels] at h
  | (l, a) :: xs, m, h => by
    simp only [mergeLabels, List.mem_cons] at h
    rcases h with rfl | h
    · cases hl : (mergeLabels xs).lookup l with
      | none => exact ⟨(l, a), List.mem_cons_self, by simp⟩
      | some b =>
        obtain ⟨x, hx, he⟩ := mergeLabels_mem (lookup_mem_of_some' hl)
        exact ⟨x, List.mem_cons_of_mem _ hx, by simpa using he⟩
    · obtain ⟨x, hx, he⟩ := mergeLabels_mem (List.mem_filter.mp h).1
      exact ⟨x, List.mem_cons_of_mem _ hx, he⟩

theorem objFields_ok {ls : List String} {ks : List FieldKind} {vs : List Value}
    (hk : ks.contains .getter = false) (hv : ∀ v ∈ vs, v.plain = true) :
    (objFields ls ks vs).CellOK := by
  intro m hm
  obtain ⟨x, hx, he⟩ := mergeLabels_mem (List.mem_reverse.mp hm)
  have hx₂ := (List.of_mem_zip hx).2
  obtain ⟨hmk, hv'⟩ := List.of_mem_zip (show (x.2.1, x.2.2) ∈ _ from hx₂)
  obtain ⟨fk, hfk, hfe⟩ := List.mem_map.mp hmk
  have hne : fk ≠ .getter := fun e => by subst e; simp_all
  have hdata : x.2.1 = .data := by
    rw [← hfe]; cases fk <;> first | rfl | exact absurd rfl hne
  rw [he, hdata]
  exact ⟨nofun, nofun, hv _ hv'⟩

theorem clsMembers_ok {env : Env} {self : Value} :
    ∀ {ls : List String} {es : List Expr} {ks : List ClassKind} {vs : List Value}
      {fs : List (String × MemberKind × Value)},
      ks.contains .getter = false → (∀ v ∈ vs, v.plain = true) → self.plain = true →
      clsMembers env self ls es ks vs = some fs →
      ∀ m ∈ fs, m.2.1 ≠ .getter ∧ m.2.1 ≠ .protoGetter ∧ m.2.2.plain = true := by
  intro ls es ks vs
  induction ls, es, ks, vs using clsMembers.induct with
  | case1 l ls e es ks v vs ih =>
    intro fs hk hv hs h m hm
    simp only [clsMembers, Option.map_eq_some_iff] at h
    obtain ⟨fs', h', rfl⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨nofun, nofun, hv v (by simp)⟩
    · exact ih (by simp_all) (fun w hw => hv w (by simp [hw])) hs h' m hm
  | case2 l ls n b es ks vs ih =>
    intro fs hk hv hs h m hm
    simp only [clsMembers, Option.map_eq_some_iff] at h
    obtain ⟨fs', h', rfl⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨nofun, nofun, rfl⟩
    · exact ih (by simp_all) hv hs h' m hm
  | case3 l ls n b es ks vs ih =>
    intro fs hk hv hs h m hm
    simp only [clsMembers, Option.map_eq_some_iff] at h
    obtain ⟨fs', h', rfl⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨nofun, nofun, rfl⟩
    · exact ih (by simp_all) hv hs h' m hm
  | case4 l ls n b es ks vs ih => intro fs hk; simp at hk
  | case5 => intro fs _ _ _ h; simp [clsMembers] at h; subst h; simp
  | case6 t x x₁ x₂ h₁ h₂ h₃ h₄ h₅ =>
    intro fs _ _ _ h
    rw [clsMembers.eq_def] at h
    split at h <;> first
      | exact absurd (h₅ rfl rfl rfl rfl) id
      | (cases h; done)
      | (exfalso; first
          | exact h₁ _ _ _ _ _ _ _ rfl rfl rfl rfl
          | exact h₂ _ _ _ _ _ _ rfl rfl rfl
          | exact h₃ _ _ _ _ _ _ rfl rfl rfl
          | exact h₄ _ _ _ _ _ _ rfl rfl rfl
          | exact h₅ rfl rfl rfl rfl)

theorem Lit.eval_plain (l : Lit) : l.eval.plain = true := by cases l <;> rfl

theorem UnOp.eval_good (op : UnOp) (v : Value) : (op.eval v).Good := by
  unfold UnOp.eval; split <;> simp [Result.Good, Value.plain]

theorem BinOp.eval_good (op : BinOp) (a b : Value) : (op.eval a b).Good := by
  unfold BinOp.eval; split <;> simp [Result.Good, Value.plain]

/-- What the main theorem says of one expression. -/
def NoClockGood (e : Expr) : Prop :=
  e.noClock = true → ∀ (clock : Nat) (env : Env) (heap : Heap), NoGetterHeap heap → PlainEnv env heap →
    (run clock env heap e).Good heap

theorem runArgs_good {es : List Expr} (ih : ∀ e ∈ es, NoClockGood e)
    (hn : es.all Expr.noClock = true) :
    ∀ (clock : Nat) (env : Env) (heap : Heap), NoGetterHeap heap → PlainEnv env heap →
      (runArgs clock env heap es).Good heap := by
  induction es with
  | nil => intro clock env heap hh _; rw [runArgs]; exact ⟨by simp, hh, HeapExt.refl _⟩
  | cons e es ihs =>
    intro clock env heap hh he
    simp only [List.all_cons, Bool.and_eq_true] at hn
    have h₁ := ih e (by simp) hn.1 clock env heap hh he
    rw [runArgs]
    rcases hr : run clock env heap e with ⟨r, c₁, h₁'⟩
    rw [hr] at h₁
    cases r with
    | ok v =>
      have h₂ := ihs (fun x hx => ih x (by simp [hx])) hn.2 (min c₁ clock) env h₁' h₁.2.1
        (he.mono h₁.2.2)
      rcases hr₂ : runArgs (min c₁ clock) env h₁' es with ⟨r₂, c₂, h₂'⟩
      rw [hr₂] at h₂
      cases r₂ with
      | ok vs =>
        simp only [hr₂]
        refine ⟨fun x hx => ?_, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h₁.1
        · exact h₂.1 x hx
      | error r₂ => simp only [hr₂]; exact ⟨h₂.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
    | _ => exact h₁

theorem runInits_good {es : List Expr} (ih : ∀ e ∈ es, NoClockGood e)
    (hn : es.all Expr.noClock = true) :
    ∀ (ks : List ClassKind) (clock : Nat) (env : Env) (heap : Heap), NoGetterHeap heap →
      PlainEnv env heap → (runInits clock env heap es ks).Good heap := by
  induction es with
  | nil =>
    intro ks clock env heap hh _
    have : runInits clock env heap [] ks = (.ok [], clock, heap) := by
      cases ks <;> simp [runInits]
    rw [this]; exact ⟨by simp, hh, HeapExt.refl _⟩
  | cons e es ihs =>
    intro ks clock env heap hh he
    simp only [List.all_cons, Bool.and_eq_true] at hn
    have ihs' := ihs (fun x hx => ih x (by simp [hx])) hn.2
    cases ks with
    | nil =>
      have : runInits clock env heap (e :: es) [] = (.ok [], clock, heap) := by simp [runInits]
      rw [this]; exact ⟨by simp, hh, HeapExt.refl _⟩
    | cons k ks =>
      cases k with
      | data =>
        have h₁ := ih e (by simp) hn.1 clock env heap hh he
        rw [runInits]
        rcases hr : run clock env heap e with ⟨r, c₁, h₁'⟩
        rw [hr] at h₁
        cases r with
        | ok v =>
          have h₂ := ihs' ks (min c₁ clock) (h₁'.length :: env) (h₁' ++ [v])
            (h₁.2.1.append (Value.CellOK.of_plain h₁.1)) ((he.mono h₁.2.2).push h₁.1)
          have hx := h₁.2.2.trans (HeapExt.append h₁' v)
          rcases hr₂ : runInits (min c₁ clock) (h₁'.length :: env) (h₁' ++ [v]) es ks with
            ⟨r₂, c₂, h₂'⟩
          rw [hr₂] at h₂
          cases r₂ with
          | ok vs =>
            simp only [hr₂]
            refine ⟨fun x hx => ?_, h₂.2.1, hx.trans h₂.2.2⟩
            rcases List.mem_cons.mp hx with rfl | hx
            · exact h₁.1
            · exact h₂.1 x hx
          | error r₂ => simp only [hr₂]; exact ⟨h₂.1, h₂.2.1, hx.trans h₂.2.2⟩
        | _ => exact h₁
      | _ => simp only [runInits]; exact ihs' ks clock env heap hh he

/-- A program that makes no call, runs no loop and defines no getter never
runs out of clock, whatever the clock. -/
theorem run_good : ∀ e, NoClockGood e := by
  intro e
  induction e using Expr.ind with
  | lit l =>
    intro _ clock env heap hh _; rw [run]; exact ⟨Lit.eval_plain l, hh, HeapExt.refl _⟩
  | var i =>
    intro _ clock env heap hh he
    rw [run]
    split
    · rename_i ℓ hℓ
      split
      · rename_i v hv
        obtain ⟨w, hw, hp⟩ := he ℓ (List.mem_of_getElem? hℓ)
        rw [hv] at hw; cases hw
        exact ⟨hp, hh, HeapExt.refl _⟩
      · exact ⟨trivial, hh, HeapExt.refl _⟩
    · exact ⟨trivial, hh, HeapExt.refl _⟩
  | func n body _ => intro _ clock env heap hh _; rw [run]; exact ⟨rfl, hh, HeapExt.refl _⟩
  | ctor n body _ => intro _ clock env heap hh _; rw [run]; exact ⟨rfl, hh, HeapExt.refl _⟩
  | app f args _ _ => intro hn; simp [Expr.noClock] at hn
  | new_ f args _ _ => intro hn; simp [Expr.noClock] at hn
  | mcall e l args _ _ => intro hn; simp [Expr.noClock] at hn
  | while_ c body _ _ => intro hn; simp [Expr.noClock] at hn
  | break_ => intro _ clock env heap hh _; rw [run]; exact ⟨trivial, hh, HeapExt.refl _⟩
  | continue_ => intro _ clock env heap hh _; rw [run]; exact ⟨trivial, hh, HeapExt.refl _⟩
  | let_ mb ann e₁ e₂ ih₁ ih₂ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ih₁ hn.1 clock env heap hh he) fun v c h₁ _ hv hh₁ hx₁ => ?_
    exact (ih₂ hn.2 _ _ _ (hh₁.append (Value.CellOK.of_plain hv)) ((he.mono hx₁).push hv)).weaken
      (hx₁.trans (HeapExt.append h₁ v))
  | assign i e ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock] at hn
    rw [run]
    refine bindC_good (ih hn clock env heap hh he) fun v c h₁ _ hv hh₁ hx₁ => ?_
    split
    · rename_i ℓ hℓ
      split
      · exact ⟨hv, hh₁.set (Value.CellOK.of_plain hv), hx₁.trans (HeapExt.set_plain hv)⟩
      · exact ⟨trivial, hh₁, hx₁⟩
    · exact ⟨trivial, hh₁, hx₁⟩
  | cond c t e ihc iht ihe =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ihc hn.1.1 clock env heap hh he) fun v c₁ h₁ _ _ hh₁ hx₁ => ?_
    split
    · exact (iht hn.1.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁
    · exact (ihe hn.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁
  | unop op e ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock] at hn
    rw [run]
    exact bindC_good (ih hn clock env heap hh he) fun v c₁ h₁ _ _ hh₁ hx₁ =>
      ⟨UnOp.eval_good op v, hh₁, hx₁⟩
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ih₁ hn.1 clock env heap hh he) fun v₁ c₁ h₁ _ _ hh₁ hx₁ => ?_
    exact bindC_good ((ih₂ hn.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁)
      fun v₂ c₂ h₂ _ _ hh₂ hx₂ => ⟨BinOp.eval_good op v₁ v₂, hh₂, hx₂⟩
  | ret e ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock] at hn
    rw [run]
    exact bindC_good (ih hn clock env heap hh he) fun v c₁ h₁ _ hv hh₁ hx₁ => ⟨hv, hh₁, hx₁⟩
  | throw_ e ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock] at hn
    rw [run]
    exact bindC_good (ih hn clock env heap hh he) fun v c₁ h₁ _ hv hh₁ hx₁ => ⟨hv, hh₁, hx₁⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    exact bindC_good (ih₁ hn.1 clock env heap hh he) fun v c₁ h₁ _ _ hh₁ hx₁ =>
      (ih₂ hn.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁
  | unwrap e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ih₁ hn.1.1 clock env heap hh he) fun v c₁ h₁ _ hv hh₁ hx₁ => ?_
    split
    · exact (ih₂ hn.1.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁
    · exact (ih₃ hn.2 _ _ _ (hh₁.append (Value.CellOK.of_plain hv)) ((he.mono hx₁).push hv)).weaken
        (hx₁.trans (HeapExt.append h₁ v))
  | caseTag e₁ d t e₂ e₃ ih₁ ih₂ ih₃ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ih₁ hn.1.1 clock env heap hh he) fun v c₁ h₁ _ hv hh₁ hx₁ => ?_
    have hd : (match d with
        | .field l => getter (min c₁ clock) h₁ v (v.read h₁ l)
        | .typeOf => (.ok (.string v.typeString), min c₁ clock, h₁) : Ran).Good h₁ := by
      cases d with
      | field l => exact getter_good hh₁ (Value.read_good hh₁ v l) _ v
      | typeOf => exact ⟨rfl, hh₁, HeapExt.refl _⟩
    refine bindC_good (hd.weaken hx₁) fun w c₂ h₂ _ _ hh₂ hx₂ => ?_
    have hx := hx₂.trans (HeapExt.append h₂ v)
    have hh' := hh₂.append (Value.CellOK.of_plain hv)
    have he' := (he.mono hx₂).push hv
    split
    · split
      · exact (ih₃ hn.2 _ _ _ hh' he').weaken hx
      · exact (ih₂ hn.1.2 _ _ _ hh' he').weaken hx
    · exact (ih₂ hn.1.2 _ _ _ hh' he').weaken hx
  | tryCatch body handler ihb ihh =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    have hb := ihb hn.1 clock env heap hh he
    rw [run]
    rcases hr : run clock env heap body with ⟨r, c₁, h₁⟩
    rw [hr] at hb
    cases r with
    | thrown v =>
      simp only
      exact (ihh hn.2 _ _ _ (hb.2.1.append (Value.CellOK.of_plain hb.1))
        ((he.mono hb.2.2).push hb.1)).weaken (hb.2.2.trans (HeapExt.append h₁ v))
    | _ => exact hb
  | tryFinally body fin ihb ihf =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    have hb := ihb hn.1 clock env heap hh he
    rw [run]
    rcases hr : run clock env heap body with ⟨r, c₁, h₁⟩
    rw [hr] at hb
    have hfin : ∀ r' : Result, r'.Good →
        Ran.Good heap (match run (min c₁ clock) env h₁ fin with
          | (.ok _, c₂, h₂) => (r', c₂, h₂)
          | p => p) := by
      intro r' hr'
      have hf := ihf hn.2 (min c₁ clock) env h₁ hb.2.1 (he.mono hb.2.2)
      rcases hr₂ : run (min c₁ clock) env h₁ fin with ⟨r₂, c₂, h₂⟩
      rw [hr₂] at hf
      cases r₂ with
      | ok _ => exact ⟨hr', hf.2.1, hb.2.2.trans hf.2.2⟩
      | _ => exact hf.weaken hb.2.2
    cases r with
    | timeout => exact absurd hb.1 id
    | stuck _ => exact hb
    | fault _ => exact hb
    | ok v => exact hfin _ hb.1
    | returned v => exact hfin _ hb.1
    | thrown v => exact hfin _ hb.1
    | broke => exact hfin _ hb.1
    | continued => exact hfin _ hb.1
  | obj ls es ks ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true, Bool.not_eq_true', Expr.noClockList_eq] at hn
    rw [run]
    exact bindArgs_good (runArgs_good ih hn.1 clock env heap hh he)
      fun vs c₁ h₁ _ hvs hh₁ hx₁ =>
        ⟨rfl, hh₁.append (objFields_ok hn.2 hvs), hx₁.trans (HeapExt.append _ _)⟩
  | cls ls es ks ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true, Bool.not_eq_true', Expr.noClockList_eq] at hn
    rw [run]
    refine bindArgs_good (runInits_good ih hn.1 ks clock env heap hh he)
      fun vs c₁ h₁ _ hvs hh₁ hx₁ => ?_
    split
    · rename_i fs hfs
      refine ⟨rfl, hh₁.append fun m hm => ?_, hx₁.trans (HeapExt.append _ _)⟩
      exact clsMembers_ok hn.2 hvs rfl hfs m (List.mem_reverse.mp hm)
    · exact ⟨trivial, hh₁, hx₁⟩
  | get e l ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock] at hn
    rw [run]
    exact bindC_good (ih hn clock env heap hh he) fun vo c₁ h₁ _ _ hh₁ hx₁ =>
      (getter_good hh₁ (Value.read_good hh₁ vo l) _ vo).weaken hx₁
  | set e l v ihe ihv =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ihe hn.1 clock env heap hh he) fun vo c₁ h₁ _ _ hh₁ hx₁ => ?_
    refine bindC_good ((ihv hn.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁)
      fun vv c₂ h₂ _ hvv hh₂ hx₂ => ?_
    have := Value.setProp_good hh₂ vo l hvv
    exact ⟨this.1, this.2.1, hx₂.trans this.2.2⟩
  | spread e₁ e₂ ih₁ ih₂ =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ih₁ hn.1 clock env heap hh he) fun v₁ c₁ h₁ _ _ hh₁ hx₁ => ?_
    refine bindFields_good ((own_good hh₁ _ v₁).weaken hx₁) fun fs₁ c₂ h₂ _ hfs₁ hh₂ hx₂ => ?_
    refine bindC_good ((ih₂ hn.2 _ _ _ hh₂ (he.mono hx₂)).weaken hx₂)
      fun v₂ c₃ h₃ _ _ hh₃ hx₃ => ?_
    refine bindFields_good ((own_good hh₃ _ v₂).weaken hx₃) fun fs₂ c₄ h₄ _ hfs₂ hh₄ hx₄ => ?_
    refine ⟨rfl, hh₄.append fun m hm => ?_, hx₄.trans (HeapExt.append _ _)⟩
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hd, hp⟩ := hfs₂ m hm; rw [hd]; exact ⟨nofun, nofun, hp⟩
    · obtain ⟨hd, hp⟩ := hfs₁ m hm; rw [hd]; exact ⟨nofun, nofun, hp⟩
  | arr es ih =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Expr.noClockList_eq] at hn
    rw [run]
    exact bindArgs_good (runArgs_good ih hn clock env heap hh he)
      fun vs c₁ h₁ _ hvs hh₁ hx₁ => ⟨rfl, hh₁.append hvs, hx₁.trans (HeapExt.append _ _)⟩
  | index e i ihe ihi =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ihe hn.1 clock env heap hh he) fun vo c₁ h₁ _ _ hh₁ hx₁ => ?_
    exact bindC_good ((ihi hn.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁) fun vi c₂ h₂ _ _ hh₂ hx₂ =>
      (getter_good hh₂ (Value.index_good hh₂ vo vi) _ vo).weaken hx₂
  | setIndex e i v ihe ihi ihv =>
    intro hn clock env heap hh he
    simp only [Expr.noClock, Bool.and_eq_true] at hn
    rw [run]
    refine bindC_good (ihe hn.1.1 clock env heap hh he) fun vo c₁ h₁ _ _ hh₁ hx₁ => ?_
    refine bindC_good ((ihi hn.1.2 _ _ _ hh₁ (he.mono hx₁)).weaken hx₁)
      fun vi c₂ h₂ _ _ hh₂ hx₂ => ?_
    refine bindC_good ((ihv hn.2 _ _ _ hh₂ (he.mono hx₂)).weaken hx₂)
      fun vv c₃ h₃ _ hvv hh₃ hx₃ => ?_
    have := Value.setIndex_good hh₃ vo vi hvv
    exact ⟨this.1, this.2.1, hx₃.trans this.2.2⟩

/-- A closed program that makes no call, runs no loop and defines no getter
never runs out of clock, whatever the clock, even none. -/
theorem eval_noClock {e : Expr} (h : e.noClock = true) (clock : Nat) :
    eval clock [] [] e ≠ .timeout := by
  have := run_good e h clock [] [] (fun _ h => by cases h) (fun _ h => by cases h)
  intro he
  unfold eval at he
  have h₁ := this.1
  rw [he] at h₁
  exact h₁

end Inty
