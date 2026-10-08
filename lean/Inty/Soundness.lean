import Inty.TypeSubst
import Inty.Clock

/-!
# Type soundness

A well-typed program never gets stuck: with any clock, `run` either runs out
of clock or returns a value of the expected type. This is the theorem
`src/meta/soundness.rs` tests by sampling ("Whenever inty accepts a program,
the operational semantics must not get stuck on it"), proved for every
program of the calculus.

Values are typed semantically, by what they do rather than by how they were
written: a step-indexed Kripke logical relation `V k W τ v` (Appel and
McAllester, TOPLAS 2001; Ahmed, ESOP 2006; Ahmed, Appel and Virga's model of
general references), with the interpreter's clock as the step index, as in
CakeML. The world `W` gives each cell of the heap its scheme. Cells are
never freed and never change scheme, so worlds only grow, by extension
(`<+:`). A function has type `θ, (τs) => ρ` at index `k` in `W` when calling
it with any clock `j ≤ k`, in any larger world, on any heap that world
describes and on arguments of its types, gives back a result of type `ρ`
in a still larger world that describes the heap after. So a native function
(`Prim`), which no typing derivation describes, has a type all the same
(`Inty.Builtins`).

The heap a call starts from need only be described one tick down, and the
one it ends with at the clock left, which is below the clock it was called
with: a call takes a tick. So `V` at index `k` refers to `V` at arbitrary
types only at indices below `k`, and is defined by well-founded recursion on
the index and then the type. Since a world maps cells to syntactic schemes,
not to semantic types, there is no circularity to solve.

The fundamental lemma (`run_sound`) says a well-typed expression is in the
relation.
-/

namespace Inty

/-- Every constraint in `C` is an instance. -/
def Holds (C : List Pred) : Prop := ∀ p ∈ C, Inst p

theorem Holds.append {C D : List Pred} (hC : Holds C) (hD : Holds D) : Holds (C ++ D) :=
  fun c hc => (List.mem_append.mp hc).elim (hC c) (hD c)

theorem Entails.holds {C : List Pred} (hC : Holds C) (h : Entails C p) : Inst p :=
  h.elim id (hC p)

/-- A world: the scheme of each cell allocated so far. -/
abbrev World := List Scheme

/-- The heap `h` has a cell for each of `W`'s, holding a value that `P`
relates to its scheme. -/
def HeapInv (P : Scheme → Value → Prop) (W : World) (h : Heap) : Prop :=
  h.length = W.length ∧ ∀ (ℓ : Nat) s, W[ℓ]? = some s → ∃ v, h[ℓ]? = some v ∧ P s v

/-- What a call does, from a clock of `j` in the world `W`: it runs out of
clock, or it takes a tick and ends in a larger world, with a heap `Hp`
accepts, giving back a value `Q` accepts or throwing. -/
def Lands (p : Ran) (j : Nat) (W : World) (Hp : Nat → World → Heap → Prop)
    (Q : Nat → World → Value → Prop) : Prop :=
  p.2.1 ≤ j ∧ (p.1 = .timeout ∨ (p.2.1 < j ∧ ∃ W', W <+: W' ∧ Hp p.2.1 W' p.2.2 ∧
    ((∃ v, p.1 = .ok v ∧ Q p.2.1 W' v) ∨ ∃ v, p.1 = .thrown v)))

private theorem lex_le {c c' s s' : Nat} (hc : c' ≤ c) (hs : s' < s) :
    Prod.Lex (· < ·) (· < ·) (c', s') (c, s) := by
  rcases Nat.lt_or_eq_of_le hc with h | rfl
  · exact .left _ _ h
  · exact .right _ hs

mutual
/-- `V k W τ v`: the value `v` has type `τ` for `k` more calls, in the world
`W`. A base type has its values. A type variable has none: a closed program
can't make a value of a type it knows nothing about. A function type is what
calling the function does (see the module docs). -/
def V (k : Nat) (W : World) : Ty → Value → Prop
  | .number, v => ∃ n, v = .number n
  | .string, v => ∃ s, v = .string s
  | .boolean, v => ∃ b, v = .boolean b
  | .undefined, v => v = .undefined
  | .null, v => v = .null
  | .var _, _ => False
  | .fn θ τs ρ, f => ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args,
      (∀ i, i < j → HeapInv (fun s v => ∀ τs', τs'.length = s.arity →
        Holds (s.instPreds τs') → V i W' (s.inst τs') v) W' h) →
      V j W' θ thisv → VList j W' τs args →
      Lands (call j h f thisv args) j W'
        (fun c W'' h'' => c < j → HeapInv (fun s v => ∀ τs', τs'.length = s.arity →
          Holds (s.instPreds τs') → V c W'' (s.inst τs') v) W'' h'')
        (fun c W'' v => c < j → V c W'' ρ v)
termination_by τ => (k, sizeOf τ)
decreasing_by
  all_goals first
    | exact .left _ _ (by omega)
    | exact lex_le (by omega) (by simp; omega)
/-- `VList k W τs vs`: one value of each type. -/
def VList (k : Nat) (W : World) : List Ty → List Value → Prop
  | [], [] => True
  | τ :: τs, v :: vs => V k W τ v ∧ VList k W τs vs
  | _, _ => False
termination_by τs => (k, sizeOf τs)
decreasing_by
  all_goals first
    | exact .left _ _ (by omega)
    | exact lex_le (by omega) (by simp; omega)
end

/-- A value has every instance of the scheme whose constraints hold. -/
def SchemeV (k : Nat) (W : World) (s : Scheme) (v : Value) : Prop :=
  ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) → V k W (s.inst τs) v

/-- The heap is described by the world, at index `k`. -/
def HeapOK (k : Nat) (W : World) (h : Heap) : Prop := HeapInv (SchemeV k W) W h

/-- The function clause of `V`, in terms of `HeapOK`. -/
theorem V_fn {k : Nat} {W : World} {θ ρ : Ty} {τs : List Ty} {f : Value} :
    V k W (.fn θ τs ρ) f ↔ ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args,
      (∀ i, i < j → HeapOK i W' h) → V j W' θ thisv → VList j W' τs args →
      Lands (call j h f thisv args) j W' (fun c W'' h'' => c < j → HeapOK c W'' h'')
        (fun c W'' v => c < j → V c W'' ρ v) := by
  rw [V]; rfl

@[simp] theorem V_number : V k W .number v ↔ ∃ n, v = .number n := by rw [V]
@[simp] theorem V_string : V k W .string v ↔ ∃ s, v = .string s := by rw [V]
@[simp] theorem V_boolean : V k W .boolean v ↔ ∃ b, v = .boolean b := by rw [V]
@[simp] theorem V_undefined : V k W .undefined v ↔ v = .undefined := by rw [V]
@[simp] theorem V_null : V k W .null v ↔ v = .null := by rw [V]
@[simp] theorem V_var : V k W (.var a) v ↔ False := by rw [V]

@[simp] theorem VList_nil : VList k W [] [] := by rw [VList]; trivial
@[simp] theorem VList_cons : VList k W (τ :: τs) (v :: vs) ↔ V k W τ v ∧ VList k W τs vs := by
  rw [VList]
@[simp] theorem VList_nil_cons : ¬ VList k W [] (v :: vs) := by simp [VList]
@[simp] theorem VList_cons_nil : ¬ VList k W (τ :: τs) [] := by simp [VList]

/-- A value good for `k` calls in `W` is good for fewer, in a larger world. -/
theorem V.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') :
    ∀ {τ : Ty} {v : Value}, V k W τ v → V j W' τ v
  | .fn _ _ _, _, hv => by
    rw [V_fn] at hv ⊢
    intro i hi W'' hW'' h thisv args hh ht ha
    exact hv i (Nat.le_trans hi hjk) W'' (hW.trans hW'') h thisv args hh ht ha
  | .number, _, hv | .string, _, hv | .boolean, _, hv | .undefined, _, hv | .null, _, hv
  | .var _, _, hv => by rw [V] at hv ⊢; exact hv

theorem VList.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') :
    ∀ {τs : List Ty} {vs : List Value}, VList k W τs vs → VList j W' τs vs
  | [], [], _ => by simp
  | _ :: _, _ :: _, h => by
    rw [VList_cons] at h ⊢; exact ⟨V.mono hjk hW h.1, VList.mono hjk hW h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem VList.length : ∀ {τs : List Ty} {vs : List Value}, VList k W τs vs →
    vs.length = τs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by rw [VList_cons] at h; simp [VList.length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem SchemeV.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W')
    (h : SchemeV k W s v) : SchemeV j W' s v :=
  fun τs hl hp => V.mono hjk hW (h τs hl hp)

theorem SchemeV.mono_iff {k : Nat} {τ : Ty} {v : Value} :
    SchemeV k W (.mono τ) v ↔ V k W τ v :=
  ⟨fun h => by simpa using h [] rfl (by simp [Holds, Scheme.instPreds, Scheme.mono]),
    fun h τs _ _ => by simpa using h⟩

/-- A scheme with no quantified variables has one instance. -/
theorem SchemeV.of_arity_zero {k : Nat} {s : Scheme} (ha : s.arity = 0)
    (h : V k W (s.inst []) v) : SchemeV k W s v := fun τs hl _ => by
  rw [ha] at hl; rw [List.eq_nil_of_length_eq_zero hl]; exact h

theorem prefix_getElem? {W W' : World} (hW : W <+: W') {ℓ : Nat} {s : Scheme}
    (hs : W[ℓ]? = some s) : W'[ℓ]? = some s := by
  obtain ⟨t, rfl⟩ := hW
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1, hs]

theorem HeapOK.mono {j k : Nat} {W : World} {h : Heap} (hjk : j ≤ k) (hH : HeapOK k W h) :
    HeapOK j W h :=
  ⟨hH.1, fun ℓ s hs => by
    obtain ⟨v, hv, hsv⟩ := hH.2 ℓ s hs
    exact ⟨v, hv, hsv.mono hjk (List.prefix_refl W)⟩⟩

/-- New cells at the end of the heap, holding values of their schemes. -/
theorem HeapOK.alloc {k : Nat} {W : World} {h : Heap} {ss : World} {vs : List Value}
    (hH : HeapOK k W h) (hlen : vs.length = ss.length)
    (hnew : ∀ (i : Nat) s v, ss[i]? = some s → vs[i]? = some v → SchemeV k (W ++ ss) s v) :
    HeapOK k (W ++ ss) (h ++ vs) := by
  refine ⟨by simp [hH.1, hlen], fun ℓ s hs => ?_⟩
  by_cases hℓ : ℓ < W.length
  · rw [List.getElem?_append_left hℓ] at hs
    obtain ⟨v, hv, hsv⟩ := hH.2 ℓ s hs
    refine ⟨v, ?_, hsv.mono (Nat.le_refl k) (List.prefix_append W ss)⟩
    rw [List.getElem?_append_left (by rw [hH.1]; exact hℓ), hv]
  · rw [List.getElem?_append_right (by omega)] at hs
    have hi : ℓ - W.length < vs.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hs).1
    obtain ⟨v, hv⟩ : ∃ v, vs[ℓ - W.length]? = some v := ⟨_, List.getElem?_eq_getElem hi⟩
    refine ⟨v, ?_, hnew _ s v hs hv⟩
    rw [List.getElem?_append_right (by rw [hH.1]; omega), hH.1, hv]

/-- Storing a value of a cell's scheme in it. -/
theorem HeapOK.set {k : Nat} {W : World} {h : Heap} {ℓ : Nat} {s : Scheme} {v : Value}
    (hH : HeapOK k W h) (hs : W[ℓ]? = some s) (hv : SchemeV k W s v) :
    HeapOK k W (h.set ℓ v) := by
  refine ⟨by simp [hH.1], fun ℓ' s' hs' => ?_⟩
  by_cases e : ℓ = ℓ'
  · subst e
    rw [hs] at hs'; cases hs'
    have : ℓ < h.length := by rw [hH.1]; exact (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨v, by simp [this], hv⟩
  · obtain ⟨v', hv', hsv'⟩ := hH.2 ℓ' s' hs'
    exact ⟨v', by rw [List.getElem?_set_ne e]; exact hv', hsv'⟩

/-! ## Environments -/

/-- `G W Γ env`: each variable's cell has the scheme `Γ` gives it. -/
def G (W : World) : Ctx → Env → Prop
  | [], [] => True
  | s :: Γ, ℓ :: env => W[ℓ]? = some s ∧ G W Γ env
  | _, _ => False

theorem G.mono {W W' : World} (hW : W <+: W') : ∀ {Γ : Ctx} {env : Env}, G W Γ env → G W' Γ env
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hs, hG⟩ => ⟨prefix_getElem? hW hs, G.mono hW hG⟩

theorem G.lookup : ∀ {i : Nat} {Γ : Ctx} {env : Env} {s : Scheme}, G W Γ env →
    Γ[i]? = some s → ∃ ℓ, env[i]? = some ℓ ∧ W[ℓ]? = some s
  | _, [], _, _, _, hi => by simp at hi
  | 0, _ :: _, _ :: _, _, ⟨hs, _⟩, hi => by simp at hi; subst hi; exact ⟨_, rfl, hs⟩
  | i + 1, _ :: _, _ :: _, _, ⟨_, hG⟩, hi => by simpa using G.lookup hG (by simpa using hi)

/-- Variables for a block of cells. -/
theorem G.block {W : World} {Γ : Ctx} {env : Env} :
    ∀ (ss : List Scheme) (base : Nat), (∀ (i : Nat) (hi : i < ss.length), W[base + i]? = some ss[i]) →
      G W Γ env → G W (ss ++ Γ) (List.range' base ss.length ++ env)
  | [], _, _, hG => hG
  | s :: ss, base, h, hG => by
    refine ⟨h 0 (by simp), ?_⟩
    exact G.block ss (base + 1) (fun i hi => by
      rw [show base + 1 + i = base + (i + 1) by omega]; exact h (i + 1) (by simp; omega)) hG

theorem VList.getElem? : ∀ {τs : List Ty} {vs : List Value} {i : Nat} {τ : Ty} {v : Value},
    VList k W τs vs → τs[i]? = some τ → vs[i]? = some v → V k W τ v
  | [], _, _, _, _, _, hτ, _ => by simp at hτ
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, 0, _, _, h, hτ, hv => by
    rw [VList_cons] at h; simp at hτ hv; subst hτ hv; exact h.1
  | _ :: _, _ :: _, i + 1, _, _, h, hτ, hv => by
    rw [VList_cons] at h; simp at hτ hv; exact VList.getElem? h.2 hτ hv

/-- Cells for values of a list of types. -/
theorem HeapOK.allocList {k : Nat} {W : World} {h : Heap} {τs : List Ty} {vs : List Value}
    (hH : HeapOK k W h) (hvs : VList k (W ++ τs.map .mono) τs vs) :
    HeapOK k (W ++ τs.map .mono) (h ++ vs) :=
  hH.alloc (by simp [hvs.length]) (fun i s v hs hv => by
    simp only [List.getElem?_map] at hs
    cases hτ : τs[i]? with
    | none => simp [hτ] at hs
    | some τ =>
      simp only [hτ, Option.map_some, Option.some.injEq] at hs; subst hs
      exact SchemeV.mono_iff.mpr (hvs.getElem? hτ hv))

/-! ## Safe outcomes -/

/-- A safe outcome at `τ`, in a function returning `R`, from a clock of `k`
in the world `W`: out of clock, or a larger world describing the heap
after, with a value of `τ`, a `throw` of any value, or a `return` of a value
of the return type. -/
def Safe (p : Ran) (k : Nat) (W : World) (τ : Ty) (R : Option Ty) : Prop :=
  p.2.1 ≤ k ∧ (p.1 = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧
    ((∃ v, p.1 = .ok v ∧ V p.2.1 W' τ v) ∨ (∃ v, p.1 = .thrown v) ∨
      (∃ v, p.1 = .returned v ∧ ∃ τr, R = some τr ∧ V p.2.1 W' τr v)))

theorem Safe.ok {W' : World} (hc : c ≤ k) (hW : W <+: W') (hH : HeapOK c W' h)
    (hv : V c W' τ v) : Safe (.ok v, c, h) k W τ R :=
  ⟨hc, .inr ⟨W', hW, hH, .inl ⟨v, rfl, hv⟩⟩⟩

theorem Safe.weaken {W' : World} (h : Safe p c W' τ R) (hc : c ≤ k) (hW : W <+: W') :
    Safe p k W τ R := by
  obtain ⟨hp, h | ⟨W'', hW'', hH, hr⟩⟩ := h
  · exact ⟨Nat.le_trans hp hc, .inl h⟩
  · exact ⟨Nat.le_trans hp hc, .inr ⟨W'', hW.trans hW'', hH, hr⟩⟩

theorem Safe.not_stuck (h : Safe p k W τ R) : p.1 ≠ .stuck s := by
  rcases h.2 with h | ⟨_, _, _, ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩⟩ <;> rw [h] <;> simp

/-- Continuing a safe outcome with a safe continuation is safe. -/
theorem Safe.bindC {K : Value → Nat → Heap → Ran} (h : Safe p k W τ₁ R)
    (hK : ∀ v W', p.1 = .ok v → W <+: W' → HeapOK p.2.1 W' p.2.2 → V p.2.1 W' τ₁ v →
      Safe (K v p.2.1 p.2.2) p.2.1 W' τ R) : Safe (Inty.bindC p K) k W τ R := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  rcases h with h | ⟨W', hW, hH, ⟨v, h, hv⟩ | ⟨v, h⟩ | ⟨v, h, hv⟩⟩ <;> simp only at h <;> subst h
  · exact ⟨hc, .inl rfl⟩
  · exact (hK v W' rfl hW hH hv).weaken hc hW
  · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl ⟨v, rfl⟩)⟩⟩
  · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr ⟨v, rfl, hv⟩)⟩⟩

/-- A call's outcome is safe at its result type, in any function. -/
theorem Lands.safe (h : Lands p j W (fun c W' h' => c < j → HeapOK c W' h')
    (fun c W' v => c < j → V c W' τ v)) : Safe p j W τ R := by
  obtain ⟨hc, h | ⟨hlt, W', hW, hH, ⟨v, hr, hv⟩ | ⟨v, hr⟩⟩⟩ := h
  · exact ⟨hc, .inl h⟩
  · exact ⟨hc, .inr ⟨W', hW, hH hlt, .inl ⟨v, hr, hv hlt⟩⟩⟩
  · exact ⟨hc, .inr ⟨W', hW, hH hlt, .inr (.inl ⟨v, hr⟩)⟩⟩

/-- A call's body, run with a tick less than the call was given, returns
its function's result type, by `return` or as its value. -/
theorem Safe.catchReturn {W₁ : World} (h : Safe p i W₁ ρ (some ρ)) (hij : i < j)
    (hW : W <+: W₁) :
    Lands (p.1.catchReturn, p.2) j W (fun c W' h' => c < j → HeapOK c W' h')
      (fun c W' v => c < j → V c W' ρ v) := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  simp only at hc
  rcases h with h | ⟨W', hW', hH, ⟨v, h, hv⟩ | ⟨v, h⟩ | ⟨v, h, τr, hR, hv⟩⟩ <;>
    simp only at h <;> subst h
  · exact ⟨by simp only; omega, .inl rfl⟩
  · exact ⟨by simp only; omega, .inr ⟨by simp only; omega, W', hW.trans hW', fun _ => hH,
      .inl ⟨v, rfl, fun _ => hv⟩⟩⟩
  · exact ⟨by simp only; omega, .inr ⟨by simp only; omega, W', hW.trans hW', fun _ => hH,
      .inr ⟨v, rfl⟩⟩⟩
  · cases hR
    exact ⟨by simp only; omega, .inr ⟨by simp only; omega, W', hW.trans hW', fun _ => hH,
      .inl ⟨v, rfl, fun _ => hv⟩⟩⟩

/-! ## Operators -/

theorem Lit.eval_sound (h : LitTy l τ) : V k W τ l.eval := by
  cases h <;> simp [Lit.eval]

theorem UnOp.eval_sound {W' : World} (hop : UnOpTy op τ₁ τ) (hv : V c W' τ₁ v) (hc : c ≤ k)
    (hW : W <+: W') (hH : HeapOK c W' h) : Safe (op.eval v, c, h) k W τ R := by
  cases hop with
  | not => exact Safe.ok hc hW hH (by simp)
  | typeof => exact Safe.ok hc hW hH (by simp)
  | neg => simp at hv; obtain ⟨n, rfl⟩ := hv; exact Safe.ok hc hW hH (by simp)

theorem BinOp.eval_sound {W' : World} (hC : Holds C) (hop : BinOpTy C op τ₁ τ₂ τ)
    (hv₁ : V c W' τ₁ v₁) (hv₂ : V c W' τ₂ v₂) (hc : c ≤ k) (hW : W <+: W')
    (hH : HeapOK c W' h) : Safe (op.eval v₁ v₂, c, h) k W τ R := by
  cases hop with
  | plus hp =>
    cases hp.holds hC with
    | plusNumber =>
      simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
      exact Safe.ok hc hW hH (by simp)
    | plusString =>
      simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
      exact Safe.ok hc hW hH (by simp)
  | minus =>
    simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
    exact Safe.ok hc hW hH (by simp)

/-- Running a syntactic value gives a value, and takes no clock and no
cell. -/
theorem IsValue.run_value (hv : e.IsValue) (ht : HasType C Γ R e τ) (hG : G W Γ env)
    (hH : HeapOK k W h) : ∃ v, run k env h e = (.ok v, k, h) := by
  cases hv with
  | lit => rename_i l; exact ⟨l.eval, by simp [run]⟩
  | func => rename_i n body; exact ⟨.closure env n body, by simp [run]⟩
  | var =>
    cases ht with
    | var hi _ _ =>
      obtain ⟨ℓ, hℓ, hs⟩ := G.lookup hG hi
      obtain ⟨v, hv, _⟩ := hH.2 ℓ _ hs
      exact ⟨v, by simp [run, hℓ, hv]⟩

/-! ## Arguments -/

/-- A safe outcome of running arguments of the types `τs`: their values,
or an outcome other than a value that is safe. -/
def SafeArgs (p : RanArgs) (k : Nat) (W : World) (τs : List Ty) (R : Option Ty) : Prop :=
  p.2.1 ≤ k ∧ match p.1 with
    | .ok vs => ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧ VList p.2.1 W' τs vs
    | .error r => r = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧
        ((∃ v, r = .thrown v) ∨ (∃ v, r = .returned v ∧ ∃ τr, R = some τr ∧ V p.2.1 W' τr v))

/-- Continuing safe arguments with a safe continuation is safe. -/
theorem Safe.bindArgs {p : RanArgs} {K : List Value → Nat → Heap → Ran}
    (h : SafeArgs p k W τs R)
    (hK : ∀ vs W', p.1 = .ok vs → W <+: W' → HeapOK p.2.1 W' p.2.2 → VList p.2.1 W' τs vs →
      Safe (K vs p.2.1 p.2.2) p.2.1 W' τ R) :
    Safe (Inty.bindArgs p K) k W τ R := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  cases r with
  | ok vs =>
    obtain ⟨W', hW, hH, hvs⟩ := h
    exact (hK vs W' rfl hW hH hvs).weaken hc hW
  | error r =>
    simp only [Inty.bindArgs]
    rcases h with rfl | ⟨W', hW, hH, ⟨v, rfl⟩ | ⟨v, rfl, hv⟩⟩
    · exact ⟨hc, .inl rfl⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl ⟨v, rfl⟩)⟩⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr ⟨v, rfl, hv⟩)⟩⟩

/-- What the fundamental lemma says of one expression. -/
def RunSound (e : Expr) : Prop :=
  ∀ {k C Γ R W env h τ}, HasType C Γ R e τ → Holds C → G W Γ env → HeapOK k W h →
    Safe (run k env h e) k W τ R

/-- Well-typed arguments, each safe by the fundamental lemma, run safely. -/
theorem runArgs_sound {C : List Pred} {Γ : Ctx} {R : Option Ty} (hC : Holds C) :
    ∀ (args : List Expr) (τs : List Ty) {k : Nat} {W : World} {env : Env} {h : Heap},
      (∀ a ∈ args, RunSound a) →
      args.length = τs.length → (∀ p ∈ args.zip τs, HasType C Γ R p.1 p.2) → G W Γ env →
      HeapOK k W h → SafeArgs (runArgs k env h args) k W τs R
  | [], [], k, W, env, h, _, _, _, _, hH => by
    simp only [runArgs, SafeArgs]; exact ⟨Nat.le_refl k, W, List.prefix_refl W, hH, by simp⟩
  | [], _ :: _, _, _, _, _, _, hlen, _, _, _ | _ :: _, [], _, _, _, _, _, hlen, _, _, _ => by
    simp at hlen
  | a :: as, τ :: τs, k, W, env, h, ih, hlen, ht, hG, hH => by
    have ha := ih a (by simp) (ht (a, τ) (by simp)) hC hG hH
    have hc₁ := run_clock_le k env h a
    generalize hp : run k env h a = p at ha hc₁
    obtain ⟨r, c₁, h₁⟩ := p
    obtain ⟨_, hr⟩ := ha
    simp only at hc₁
    rcases hr with hr | ⟨W₁, hW₁, hH₁, ⟨v, hr, hv⟩ | ⟨v, hr⟩ | ⟨v, hr, hv⟩⟩ <;>
      simp only at hr <;> subst hr
    · simp only [runArgs, hp]
      exact ⟨hc₁, .inl rfl⟩
    · have has := runArgs_sound hC as τs (fun a' ha' => ih a' (by simp [ha']))
        (by simpa using hlen) (fun q hq => ht q (by simp [hq])) (G.mono hW₁ hG) hH₁
      have hc₂ := runArgs_clock_le c₁ env h₁ as
      rw [← Nat.min_eq_left hc₁] at has hc₂
      simp only [runArgs, hp]
      generalize runArgs (min c₁ k) env h₁ as = q at has hc₂
      obtain ⟨r', c₂, h₂⟩ := q
      rw [Nat.min_eq_left hc₁] at hc₂
      obtain ⟨_, hq⟩ := has
      simp only at hc₂
      cases r' with
      | ok vs =>
        obtain ⟨W₂, hW₂, hH₂, hvs⟩ := hq
        exact ⟨by simp only; omega, W₂, hW₁.trans hW₂, hH₂,
          (VList_cons).mpr ⟨V.mono hc₂ hW₂ hv, hvs⟩⟩
      | error r' =>
        rcases hq with hq | ⟨W₂, hW₂, hH₂, hq⟩
        · exact ⟨by simp only; omega, .inl hq⟩
        · exact ⟨by simp only; omega, .inr ⟨W₂, hW₁.trans hW₂, hH₂, hq⟩⟩
    · simp only [runArgs, hp]
      exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inl ⟨v, rfl⟩⟩⟩
    · simp only [runArgs, hp]
      exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inr ⟨v, rfl, hv⟩⟩⟩

/-! ## The fundamental lemma -/

/-- A call's cells: the arguments, the function and `this`, after the
caller's. -/
theorem G.call {W : World} {Γ : Ctx} {env : Env} {h : Heap} {θ ρ : Ty} {τs : List Ty}
    (hG : G W Γ env) (hlen : h.length = W.length) :
    G (W ++ τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ])
      (τs.map Scheme.mono ++ Scheme.mono (.fn θ τs ρ) :: Scheme.mono θ :: Γ)
      (callEnv h τs.length env) := by
  have e₁ : τs.map Scheme.mono ++ Scheme.mono (.fn θ τs ρ) :: Scheme.mono θ :: Γ =
      (τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ]) ++ Γ := by simp
  have e₂ : callEnv h τs.length env =
      List.range' h.length
        (τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ]).length ++ env := by
    simp [callEnv]
  rw [e₁, e₂, List.append_assoc W]
  refine G.block _ _ (fun i hi => ?_) (G.mono (List.prefix_append _ _) hG)
  rw [hlen, List.getElem?_append_right (by omega)]
  simp

theorem run_sound (e : Expr) : RunSound e := by
  induction e using Expr.ind with
  | lit l =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | lit hl =>
      simp only [run]; exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH (Lit.eval_sound hl)
  | var i =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | var hi hlen hc =>
      obtain ⟨ℓ, hℓ, hs⟩ := G.lookup hG hi
      obtain ⟨v, hv, hsv⟩ := hH.2 ℓ _ hs
      simp only [run, hℓ, hv]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH
        (hsv _ hlen (fun c h => (hc c h).holds hC))
  | func n body ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | @func _ _ _ ρ _ _ θ τs hlen hb =>
      subst hlen
      -- The closure is good for `j` calls in any world its environment is
      -- typed in, by induction on `j`: a call with `i + 1` to spare runs the
      -- body with `i`, where the closure itself (the function's own name)
      -- need only be good for `i`.
      have hclo : ∀ j W, G W Γ env → V j W (.fn θ τs ρ) (.closure env τs.length body) := by
        intro j
        induction j with
        | zero =>
          intro W _
          rw [V_fn]
          intro i hi W' _ h' thisv args _ _ hargs
          obtain rfl : i = 0 := by omega
          simp only [call, hargs.length]
          exact ⟨Nat.le_refl 0, .inl rfl⟩
        | succ j ihj =>
          intro W hGW
          rw [V_fn]
          intro i hi W' hW' h' thisv args hh hthis hargs
          simp only [call, hargs.length]
          cases i with
          | zero => exact ⟨Nat.le_refl 0, .inl rfl⟩
          | succ i =>
            have hH' : HeapOK i W' h' := hh i (by omega)
            have hW₁ : W' <+: W' ++ τs.map .mono := List.prefix_append _ _
            have hW₂ : W' <+: W' ++ τs.map .mono ++ [.mono (.fn θ τs ρ), .mono θ] :=
              hW₁.trans (List.prefix_append _ _)
            have hcells : HeapOK i (W' ++ τs.map .mono ++ [.mono (.fn θ τs ρ), .mono θ])
                (h' ++ args ++ [.closure env τs.length body, thisv]) := by
              refine (hH'.allocList (hargs.mono (j := i) (by omega) hW₁)).alloc (by simp)
                (fun idx s v hs hv => ?_)
              match idx, hs, hv with
              | 0, hs, hv =>
                simp at hs hv; subst hs hv
                exact SchemeV.mono_iff.mpr
                  ((ihj _ (G.mono (hW'.trans hW₂) hGW)).mono (by omega) (List.prefix_refl _))
              | 1, hs, hv =>
                simp at hs hv; subst hs hv
                exact SchemeV.mono_iff.mpr (hthis.mono (by omega) hW₂)
              | _ + 2, hs, _ => simp at hs
            have hGb := G.call (θ := θ) (ρ := ρ) (τs := τs) (G.mono hW' hGW) hH'.1
            exact (ih hb hC hGb hcells).catchReturn (j := i + 1) (by omega) hW₂
      simp only [run]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH (hclo k W hG)
  | app f args ihf iha =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | app hf hlen hargs =>
      rw [run_app]
      refine Safe.bindC (ihf hf hC hG hH) fun vf W₁ _ hW₁ hH₁ hvf => ?_
      have hc₁ := run_clock_le k env h f
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindArgs (runArgs_sound hC args _ iha hlen hargs (G.mono hW₁ hG) hH₁)
        fun vs W₂ _ hW₂ hH₂ hvs => ?_
      have hc₂ := runArgs_clock_le (run k env h f).2.1 env (run k env h f).2.2 args
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      exact Lands.safe (V_fn.mp (V.mono hc₂ hW₂ hvf) _ (Nat.le_refl _) W₂ (List.prefix_refl _)
        _ .undefined vs (fun i hi => hH₂.mono (by omega)) (by simp) hvs)
  | let_ mb e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | let_ s L hgen hval _ h₂ =>
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (L ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Pred.ftv ++
        (R.map Ty.ftv).getD [])
      have hm : ∀ a, a ∈ L ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Pred.ftv ∨
          a ∈ (R.map Ty.ftv).getD [] → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasType (C ++ s.instPreds τs) Γ R e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst (Subst.block m τs)
        have hfresh : ∀ a, a < m → (Subst.block m τs).find a = none := fun a ha =>
          Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
        have hCσ : C.map (·.subst (Subst.block m τs)) = C := by
          conv => rhs; rw [← List.map_id C]
          exact List.map_congr_left (fun c hc => Pred.subst_id (fun a ha =>
            hfresh a (hm a (.inr (.inr (.inr (.inl (List.mem_flatMap.mpr ⟨c, hc, ha⟩))))))))
        have hRσ : R.map (·.subst (Subst.block m τs)) = R := by
          cases R with
          | none => rfl
          | some τr =>
            simp only [Option.map_some, Option.some.injEq]
            exact Ty.subst_id (fun a ha =>
              hfresh a (hm a (.inr (.inr (.inr (.inr (by simpa using ha)))))))
        rwa [List.map_append, hCσ, hRσ,
          Scheme.openPreds_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen,
          ctx_subst_id (fun a ha => hfresh a (hm a (.inr (.inl ha)))),
          Scheme.open_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen] at h
      have hsafe : ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) →
          Safe (run k env h e₁) k W (s.inst τs) R := fun τs hlen hp =>
        ih₁ (hinst τs hlen) (hC.append hp) hG hH
      -- What follows the initialiser: its value in a new cell.
      have hK : ∀ v c₁ h₁ W₁, c₁ ≤ k → W <+: W₁ → HeapOK c₁ W₁ h₁ → SchemeV c₁ W₁ s v →
          Safe (run (min c₁ k) (h₁.length :: env) (h₁ ++ [v]) e₂) c₁ W₁ τ R := by
        intro v c₁ h₁ W₁ hc hW₁ hH₁ hv
        rw [Nat.min_eq_left hc]
        have hW₂ : W₁ <+: W₁ ++ [s] := List.prefix_append _ _
        have hcell : HeapOK c₁ (W₁ ++ [s]) (h₁ ++ [v]) :=
          hH₁.alloc (by simp) (fun i s' v' hs hv' => by
            match i, hs, hv' with
            | 0, hs, hv' =>
              simp at hs hv'; subst hs hv'; exact hv.mono (Nat.le_refl _) hW₂
            | _ + 1, hs, _ => simp at hs)
        have hG₂ : G (W₁ ++ [s]) (s :: Γ) (h₁.length :: env) :=
          ⟨by rw [hH₁.1]; simp, G.mono (hW₁.trans hW₂) hG⟩
        exact (ih₂ h₂ hC hG₂ hcell).weaken (Nat.le_refl _) hW₂
      simp only [run]
      rcases hval with ⟨ha, hp⟩ | ⟨hv, _⟩
      · -- One instance: no quantified variables, no constraints.
        refine Safe.bindC (hsafe [] (by simp [ha]) (by simp [Holds, Scheme.instPreds, hp]))
          fun v W₁ _ hW₁ hH₁ hv => ?_
        exact hK v _ _ W₁ (run_clock_le k env h e₁) hW₁ hH₁ (SchemeV.of_arity_zero ha hv)
      · -- A syntactic value: it allocates nothing, so each instance's world
        -- is `W` itself.
        obtain ⟨v, hrun⟩ := IsValue.run_value hv (hgen m (fun a ha => hm a (.inl ha))) hG hH
        rw [hrun, ok_bindC]
        refine hK v k h W (Nat.le_refl k) (List.prefix_refl W) hH fun τs hl hp => ?_
        have hs := hsafe τs hl hp
        rw [hrun] at hs
        obtain ⟨_, hs⟩ := hs
        rcases hs with hs | ⟨W', hW', hH', ⟨v', hv', hvv⟩ | ⟨_, hv'⟩ | ⟨_, hv', _⟩⟩
        · simp at hs
        · simp at hv'; subst hv'
          obtain rfl := hW'.eq_of_length (by rw [← hH'.1, hH.1])
          exact hvv
        · simp at hv'
        · simp at hv'
  | assign i e ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | assign hi ha _ he =>
      obtain ⟨ℓ, hℓ, hs⟩ := G.lookup hG hi
      simp only [run]
      refine Safe.bindC (ih he hC hG hH) fun v W₁ _ hW₁ hH₁ hv => ?_
      have hs₁ := prefix_getElem? hW₁ hs
      have hlt : ℓ < (run k env h e).2.2.length := by
        rw [hH₁.1]; exact (List.getElem?_eq_some_iff.mp hs₁).1
      simp only [hℓ, hlt, ite_true]
      exact Safe.ok (Nat.le_refl _) (List.prefix_refl _)
        (hH₁.set hs₁ (SchemeV.of_arity_zero ha hv)) hv
  | cond c t e ihc iht ihe =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | cond hc htt hte =>
      simp only [run]
      refine Safe.bindC (ihc hc hC hG hH) fun v W₁ _ hW₁ hH₁ _ => ?_
      have hc₁ := run_clock_le k env h c
      rw [Nat.min_eq_left hc₁]
      split
      · exact iht htt hC (G.mono hW₁ hG) hH₁
      · exact ihe hte hC (G.mono hW₁ hG) hH₁
  | unop op e ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | unop hop he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv =>
        UnOp.eval_sound hop hv (Nat.le_refl _) (List.prefix_refl W₁) hH₁
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | binop hop h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC hG hH) fun v₁ W₁ _ hW₁ hH₁ hv₁ => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ih₂ h₂ hC (G.mono hW₁ hG) hH₁) fun v₂ W₂ _ hW₂ hH₂ hv₂ => ?_
      exact BinOp.eval_sound hC hop (V.mono (run_clock_le _ env _ e₂) hW₂ hv₁) hv₂
        (Nat.le_refl _) (List.prefix_refl W₂) hH₂
  | ret e ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | ret he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv =>
        ⟨Nat.le_refl _, .inr ⟨W₁, List.prefix_refl W₁, hH₁, .inr (.inr ⟨v, rfl, _, rfl, hv⟩)⟩⟩
  | throw_ e ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | throw_ he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ _ =>
        ⟨Nat.le_refl _, .inr ⟨W₁, List.prefix_refl W₁, hH₁, .inr (.inl ⟨v, rfl⟩)⟩⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | seq h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC hG hH) fun _ W₁ _ hW₁ hH₁ _ => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      exact ih₂ h₂ hC (G.mono hW₁ hG) hH₁

/-- Type soundness, for `eval`: a value of the type, a `return` of a value
of the return type, a `throw`, or out of clock; never stuck. -/
theorem eval_sound (clock : Nat) (ht : HasType C Γ R e τ) (hC : Holds C)
    (hG : G W Γ env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  run_sound e ht hC hG hH

/-- A closed program, well typed with no assumptions and outside any
function, never gets stuck, whatever the clock. -/
theorem never_stuck (ht : HasType [] [] none e τ) (clock : Nat) (s : Stuck) :
    eval clock [] [] e ≠ .stuck s :=
  Safe.not_stuck (run_sound e ht (W := []) (fun _ h => by cases h) (by simp [G])
    ⟨rfl, fun _ _ h => by simp at h⟩)

end Inty
