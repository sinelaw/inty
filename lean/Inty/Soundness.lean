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

/-- What the world says of a cell: a variable's, holding a value of a
scheme; an object's, holding fields of a record type; an array's, holding
elements of a type. -/
inductive Cell where
  | scheme (s : Scheme)
  | obj (τ : Ty)
  | arr (τ : Ty)

/-- A variable's cell, of a monotype. -/
abbrev Cell.mono (τ : Ty) : Cell := .scheme (.mono τ)

/-- A world: what each cell allocated so far holds. -/
abbrev World := List Cell

/-- The heap `h` has a cell for each of `W`'s, holding a value that `P`
relates to what `W` says of it. -/
def HeapInv (P : Cell → Value → Prop) (W : World) (h : Heap) : Prop :=
  h.length = W.length ∧ ∀ (ℓ : Nat) c, W[ℓ]? = some c → ∃ v, h[ℓ]? = some v ∧ P c v

/-- What a cell holds, given which values `P` gives each type: a variable's
value has every instance of its scheme whose constraints hold; an object's
fields are the record's present ones, each of its type, and none of its
absent ones (a slot whose presence isn't known, a variable, has no
contents, as a type variable has no values); an array's elements each have
the element type. -/
def CellP (P : Ty → Value → Prop) : Cell → Value → Prop
  | .scheme s, v => ∀ τs, τs.length = s.arity → HoldsOrVar (s.instPreds τs) → P (s.inst τs) v
  | .obj (.record ls slots), v => ∃ fs, v = .fields fs ∧ (∀ l σ,
      Ty.field l ls slots = some (.slot .pre σ) → ∃ v', fs.lookup l = some v' ∧ P σ v') ∧
      ∀ l s, Ty.field l ls slots = some s →
        (∃ σ, s = .slot .pre σ) ∨ ∃ σ, s = .slot .abs σ ∧ fs.lookup l = none
  | .obj _, _ => False
  | .arr τ, v => ∃ vs, v = .items vs ∧ ∀ w ∈ vs, P τ w

theorem CellP.mono {P Q : Ty → Value → Prop} (hPQ : ∀ τ v, P τ v → Q τ v) {c : Cell}
    {v : Value} (h : CellP P c v) : CellP Q c v := by
  cases c with
  | scheme s => exact fun τs hl hp => hPQ _ _ (h τs hl hp)
  | arr τ =>
    obtain ⟨vs, rfl, hvs⟩ := h
    exact ⟨vs, rfl, fun w hw => hPQ _ _ (hvs w hw)⟩
  | obj τ =>
    cases τ with
    | var => simp [CellP] at h
    | mu => simp [CellP] at h
    | app c args =>
      cases c
      case record ls =>
        obtain ⟨fs, rfl, hf, ha⟩ := h
        exact ⟨fs, rfl, fun l σ hl => (hf l σ hl).imp fun _ h => ⟨h.1, hPQ _ _ h.2⟩, ha⟩
      all_goals simp [CellP] at h

/-- An abrupt completion that runs on past a call: a `throw` of any value,
a `break` or `continue`, which a well-scoped program keeps inside its loop
(`Expr.jumpsInLoop`), or a documented fault, at which the program stops. -/
def Result.Abrupt : Result → Prop
  | .thrown _ | .broke | .continued | .fault _ => True
  | _ => False

theorem Result.Abrupt.bindC {p : Ran} {K : Value → Nat → Heap → Ran} (h : p.1.Abrupt) :
    Inty.bindC p K = p := by
  obtain ⟨r, c, hp⟩ := p
  cases r <;> simp_all [Result.Abrupt, Inty.bindC]

theorem Result.Abrupt.catchReturn {r : Result} (h : r.Abrupt) : r.catchReturn = r := by
  cases r <;> simp_all [Result.Abrupt, Result.catchReturn]

theorem Result.Abrupt.ne_stuck {r : Result} (h : r.Abrupt) : r ≠ .stuck s := by
  cases r <;> simp_all [Result.Abrupt]

/-- What a call does, from a clock of `j` in the world `W`: it runs out of
clock, or it takes a tick and ends in a larger world, with a heap `Hp`
accepts, giving back a value `Q` accepts or completing abruptly. -/
def Lands (p : Ran) (j : Nat) (W : World) (Hp : Nat → World → Heap → Prop)
    (Q : Nat → World → Value → Prop) : Prop :=
  p.2.1 ≤ j ∧ (p.1 = .timeout ∨ (p.2.1 < j ∧ ∃ W', W <+: W' ∧ Hp p.2.1 W' p.2.2 ∧
    ((∃ v, p.1 = .ok v ∧ Q p.2.1 W' v) ∨ p.1.Abrupt)))

private theorem lex_le {c c' s s' : Nat} (hc : c' ≤ c) (hs : s' < s) :
    Prod.Lex (· < ·) (· < ·) (c', s') (c, s) := by
  rcases Nat.lt_or_eq_of_le hc with h | rfl
  · exact .left _ _ h
  · exact .right _ hs

mutual
/-- `V k W τ v`: the value `v` has type `τ` for `k` more calls, in the world
`W`. A base type has its values, and `unknown` (what a `catch` binds) has
every value. A type variable has none: a closed program can't make a value
of a type it knows nothing about. A function type is what
calling the function does (see the module docs); the call's `this` and
arguments need only be good below the clock it is given, since the body
runs a tick down. A record is an object whose cell the world says holds
fields of the record type, and an array one whose cell holds elements of
its element type (`CellP`). A slot, a presence, or a constructor applied
to the wrong number of types has no values. -/
def V (k : Nat) (W : World) : Ty → Value → Prop
  | .number, v => ∃ n, v = .number n
  | .string, v => ∃ s, v = .string s
  | .boolean, v => ∃ b, v = .boolean b
  | .undefined, v => v = .undefined
  | .null, v => v = .null
  | .unknown, _ => True
  | .fn θ τs ρ, f => ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args, args.length = τs.length →
      (∀ i, i < j → HeapInv (CellP (fun τ v => V i W' τ v)) W' h) →
      (∀ i, i < j → V i W' θ thisv) → (∀ i, i < j → VList i W' τs args) →
      Lands (call j h f thisv args) j W'
        (fun c W'' h'' => c < j → HeapInv (CellP (fun τ v => V c W'' τ v)) W'' h'')
        (fun c W'' v => c < j → V c W'' ρ v)
  | .record ls slots, v => ∃ ℓ, v = .obj ℓ ∧ W[ℓ]? = some (.obj (.record ls slots))
  | .array τ, v => ∃ ℓ, v = .arr ℓ ∧ W[ℓ]? = some (.arr τ)
  | _, _ => False
termination_by τ => (k, sizeOf τ)
decreasing_by
  all_goals exact .left _ _ (by omega)
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

/-- What a cell holds, at index `k` in `W`. -/
abbrev CellV (k : Nat) (W : World) : Cell → Value → Prop := CellP (V k W)

/-- A value has every instance of the scheme whose constraints hold. -/
def SchemeV (k : Nat) (W : World) (s : Scheme) (v : Value) : Prop :=
  ∀ τs, τs.length = s.arity → HoldsOrVar (s.instPreds τs) → V k W (s.inst τs) v

theorem CellV_scheme : CellV k W (.scheme s) v ↔ SchemeV k W s v := Iff.rfl

theorem CellV_obj : CellV k W (.obj (.record ls slots)) v ↔ ∃ fs, v = .fields fs ∧
      (∀ l σ, Ty.field l ls slots = some (.slot .pre σ) →
        ∃ v', fs.lookup l = some v' ∧ V k W σ v') ∧
      ∀ l s, Ty.field l ls slots = some s →
        (∃ σ, s = .slot .pre σ) ∨ ∃ σ, s = .slot .abs σ ∧ fs.lookup l = none := Iff.rfl

theorem CellV_arr : CellV k W (.arr τ) v ↔ ∃ vs, v = .items vs ∧ ∀ w ∈ vs, V k W τ w := Iff.rfl

/-- The heap is described by the world, at index `k`. -/
def HeapOK (k : Nat) (W : World) (h : Heap) : Prop := HeapInv (CellV k W) W h

/-- The function clause of `V`, in terms of `HeapOK`. -/
theorem V_fn {k : Nat} {W : World} {θ ρ : Ty} {τs : List Ty} {f : Value} :
    V k W (.fn θ τs ρ) f ↔ ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args,
      args.length = τs.length → (∀ i, i < j → HeapOK i W' h) →
      (∀ i, i < j → V i W' θ thisv) → (∀ i, i < j → VList i W' τs args) →
      Lands (call j h f thisv args) j W' (fun c W'' h'' => c < j → HeapOK c W'' h'')
        (fun c W'' v => c < j → V c W'' ρ v) := by
  rw [V]; rfl

@[simp] theorem V_number : V k W .number v ↔ ∃ n, v = .number n := by rw [V.eq_def]
@[simp] theorem V_string : V k W .string v ↔ ∃ s, v = .string s := by rw [V.eq_def]
@[simp] theorem V_boolean : V k W .boolean v ↔ ∃ b, v = .boolean b := by rw [V.eq_def]
@[simp] theorem V_undefined : V k W .undefined v ↔ v = .undefined := by rw [V.eq_def]
@[simp] theorem V_null : V k W .null v ↔ v = .null := by rw [V.eq_def]
@[simp] theorem V_unknown : V k W .unknown v ↔ True := by rw [V.eq_def]
@[simp] theorem V_var : V k W (.var a) v ↔ False := by rw [V.eq_def]

theorem V_record : V k W (.record ls slots) v ↔ ∃ ℓ, v = .obj ℓ ∧
      W[ℓ]? = some (.obj (.record ls slots)) := by
  rw [V.eq_def]

theorem V_array : V k W (.array τ) v ↔ ∃ ℓ, v = .arr ℓ ∧ W[ℓ]? = some (.arr τ) := by
  rw [V.eq_def]

/-- Apart from functions, records and arrays, a type's values don't depend
on the index or the world. -/
theorem V.base {k k' : Nat} {W W' : World} {τ : Ty} {v : Value}
    (hfn : ∀ θ τs ρ, τ ≠ .fn θ τs ρ) (hrec : ∀ ls slots, τ ≠ .record ls slots)
    (harr : ∀ σ, τ ≠ .array σ) :
    V k W τ v ↔ V k' W' τ v := by
  rw [V.eq_def, V.eq_def]
  split <;> simp_all

@[simp] theorem VList_nil : VList k W [] [] := by rw [VList]; trivial
@[simp] theorem VList_cons : VList k W (τ :: τs) (v :: vs) ↔ V k W τ v ∧ VList k W τs vs := by
  rw [VList]
@[simp] theorem VList_nil_cons : ¬ VList k W [] (v :: vs) := by simp [VList]
@[simp] theorem VList_cons_nil : ¬ VList k W (τ :: τs) [] := by simp [VList]

theorem prefix_getElem? {α : Type} {W W' : List α} (hW : W <+: W') {ℓ : Nat} {s : α}
    (hs : W[ℓ]? = some s) : W'[ℓ]? = some s := by
  obtain ⟨t, rfl⟩ := hW
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1, hs]

/-- A value good for `k` calls in `W` is good for fewer, in a larger world. -/
theorem V.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {τ : Ty} {v : Value}
    (hv : V k W τ v) : V j W' τ v := by
  by_cases hfn : ∃ θ τs ρ, τ = .fn θ τs ρ
  · obtain ⟨θ, τs, ρ, rfl⟩ := hfn
    rw [V_fn] at hv ⊢
    intro i hi W'' hW'' h thisv args hl hh ht ha
    exact hv i (Nat.le_trans hi hjk) W'' (hW.trans hW'') h thisv args hl hh ht ha
  · by_cases hrec : ∃ ls slots, τ = .record ls slots
    · obtain ⟨ls, slots, rfl⟩ := hrec
      rw [V_record] at hv ⊢
      obtain ⟨ℓ, rfl, hℓ⟩ := hv
      exact ⟨ℓ, rfl, prefix_getElem? hW hℓ⟩
    · by_cases harr : ∃ σ, τ = .array σ
      · obtain ⟨σ, rfl⟩ := harr
        rw [V_array] at hv ⊢
        obtain ⟨ℓ, rfl, hℓ⟩ := hv
        exact ⟨ℓ, rfl, prefix_getElem? hW hℓ⟩
      · exact (V.base (fun θ τs ρ e => hfn ⟨θ, τs, ρ, e⟩)
          (fun ls slots e => hrec ⟨ls, slots, e⟩) (fun σ e => harr ⟨σ, e⟩)).mp hv

theorem CellV.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {c : Cell}
    {v : Value} (h : CellV k W c v) : CellV j W' c v :=
  CellP.mono (fun _ _ h => V.mono hjk hW h) h

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
  ⟨fun h => by simpa using h [] rfl (by simp [HoldsOrVar, Scheme.instPreds, Scheme.mono]),
    fun h τs _ _ => by simpa using h⟩

/-- A scheme with no quantified variables has one instance. -/
theorem SchemeV.of_arity_zero {k : Nat} {s : Scheme} (ha : s.arity = 0)
    (h : V k W (s.inst []) v) : SchemeV k W s v := fun τs hl _ => by
  rw [ha] at hl; rw [List.eq_nil_of_length_eq_zero hl]; exact h

theorem HeapOK.mono {j k : Nat} {W : World} {h : Heap} (hjk : j ≤ k) (hH : HeapOK k W h) :
    HeapOK j W h :=
  ⟨hH.1, fun ℓ s hs => by
    obtain ⟨v, hv, hsv⟩ := hH.2 ℓ s hs
    exact ⟨v, hv, hsv.mono hjk (List.prefix_refl W)⟩⟩

/-- New cells at the end of the heap, holding values of their schemes. -/
theorem HeapOK.alloc {k : Nat} {W : World} {h : Heap} {ss : World} {vs : List Value}
    (hH : HeapOK k W h) (hlen : vs.length = ss.length)
    (hnew : ∀ (i : Nat) s v, ss[i]? = some s → vs[i]? = some v → CellV k (W ++ ss) s v) :
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
theorem HeapOK.set {k : Nat} {W : World} {h : Heap} {ℓ : Nat} {s : Cell} {v : Value}
    (hH : HeapOK k W h) (hs : W[ℓ]? = some s) (hv : CellV k W s v) :
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
  | s :: Γ, ℓ :: env => W[ℓ]? = some (.scheme s) ∧ G W Γ env
  | _, _ => False

theorem G.mono {W W' : World} (hW : W <+: W') : ∀ {Γ : Ctx} {env : Env}, G W Γ env → G W' Γ env
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hs, hG⟩ => ⟨prefix_getElem? hW hs, G.mono hW hG⟩

theorem G.lookup : ∀ {i : Nat} {Γ : Ctx} {env : Env} {s : Scheme}, G W Γ env →
    Γ[i]? = some s → ∃ ℓ, env[i]? = some ℓ ∧ W[ℓ]? = some (.scheme s)
  | _, [], _, _, _, hi => by simp at hi
  | 0, _ :: _, _ :: _, _, ⟨hs, _⟩, hi => by simp at hi; subst hi; exact ⟨_, rfl, hs⟩
  | i + 1, _ :: _, _ :: _, _, ⟨_, hG⟩, hi => by simpa using G.lookup hG (by simpa using hi)

/-- Variables for a block of cells. -/
theorem G.block {W : World} {Γ : Ctx} {env : Env} :
    ∀ (ss : List Scheme) (base : Nat),
      (∀ (i : Nat) (hi : i < ss.length), W[base + i]? = some (.scheme ss[i])) →
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
    (hH : HeapOK k W h) (hvs : VList k (W ++ τs.map Cell.mono) τs vs) :
    HeapOK k (W ++ τs.map Cell.mono) (h ++ vs) :=
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
after, with a value of `τ`, an abrupt completion (a `throw` of any value,
a `break`, a `continue`), or a `return` of a value of the return type. -/
def Safe (p : Ran) (k : Nat) (W : World) (τ : Ty) (R : Option Ty) : Prop :=
  p.2.1 ≤ k ∧ (p.1 = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧
    ((∃ v, p.1 = .ok v ∧ V p.2.1 W' τ v) ∨ p.1.Abrupt ∨
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
  rcases h.2 with h | ⟨_, _, _, ⟨_, h, _⟩ | h | ⟨_, h, _⟩⟩
  · rw [h]; simp
  · rw [h]; simp
  · exact h.ne_stuck
  · rw [h]; simp

/-- An outcome other than a value is safe at any type. -/
theorem Safe.retype (h : Safe p k W τ R) (hok : ∀ v, p.1 ≠ .ok v) : Safe p k W τ' R := by
  obtain ⟨hc, h | ⟨W', hW, hH, ⟨v, hv, _⟩ | habr | hret⟩⟩ := h
  · exact ⟨hc, .inl h⟩
  · exact absurd hv (hok v)
  · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl habr)⟩⟩
  · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr hret)⟩⟩

/-- What `Safe` says of an outcome that isn't out of clock holds with less
clock and in a larger world. -/
theorem outcome_mono {r : Result} {c c' : Nat} {W W' : World}
    (h : (∃ v, r = .ok v ∧ V c W τ v) ∨ r.Abrupt ∨
      (∃ v, r = .returned v ∧ ∃ τr, R = some τr ∧ V c W τr v))
    (hc : c' ≤ c) (hW : W <+: W') :
    (∃ v, r = .ok v ∧ V c' W' τ v) ∨ r.Abrupt ∨
      (∃ v, r = .returned v ∧ ∃ τr, R = some τr ∧ V c' W' τr v) := by
  rcases h with ⟨v, e, hv⟩ | h | ⟨v, e, τr, hR, hv⟩
  · exact .inl ⟨v, e, hv.mono hc hW⟩
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨v, e, τr, hR, hv.mono hc hW⟩)

/-- Continuing a safe outcome with a safe continuation is safe. -/
theorem Safe.bindC {K : Value → Nat → Heap → Ran} (h : Safe p k W τ₁ R)
    (hK : ∀ v W', p.1 = .ok v → W <+: W' → HeapOK p.2.1 W' p.2.2 → V p.2.1 W' τ₁ v →
      Safe (K v p.2.1 p.2.2) p.2.1 W' τ R) : Safe (Inty.bindC p K) k W τ R := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  rcases h with h | ⟨W', hW, hH, ⟨v, h, hv⟩ | habr | ⟨v, h, hv⟩⟩
  · simp only at h; subst h; exact ⟨hc, .inl rfl⟩
  · simp only at h; subst h; exact (hK v W' rfl hW hH hv).weaken hc hW
  · rw [habr.bindC]; exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl habr)⟩⟩
  · simp only at h; subst h; exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr ⟨v, rfl, hv⟩)⟩⟩

/-- A call's outcome is safe at its result type, in any function. -/
theorem Lands.safe (h : Lands p j W (fun c W' h' => c < j → HeapOK c W' h')
    (fun c W' v => c < j → V c W' τ v)) : Safe p j W τ R := by
  obtain ⟨hc, h | ⟨hlt, W', hW, hH, ⟨v, hr, hv⟩ | habr⟩⟩ := h
  · exact ⟨hc, .inl h⟩
  · exact ⟨hc, .inr ⟨W', hW, hH hlt, .inl ⟨v, hr, hv hlt⟩⟩⟩
  · exact ⟨hc, .inr ⟨W', hW, hH hlt, .inr (.inl habr)⟩⟩

/-- A call's body, run with a tick less than the call was given, returns
its function's result type, by `return` or as its value. -/
theorem Safe.catchReturn {W₁ : World} (h : Safe p i W₁ ρ (some ρ)) (hij : i < j)
    (hW : W <+: W₁) :
    Lands (p.1.catchReturn, p.2) j W (fun c W' h' => c < j → HeapOK c W' h')
      (fun c W' v => c < j → V c W' ρ v) := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  simp only at hc
  rcases h with h | ⟨W', hW', hH, ⟨v, h, hv⟩ | habr | ⟨v, h, τr, hR, hv⟩⟩
  · simp only at h; subst h; exact ⟨by simp only; omega, .inl rfl⟩
  · simp only at h; subst h
    exact ⟨by simp only; omega, .inr ⟨by simp only; omega, W', hW.trans hW', fun _ => hH,
      .inl ⟨v, rfl, fun _ => hv⟩⟩⟩
  · simp only at habr
    exact ⟨by simp only; omega, .inr ⟨by simp only; omega, W', hW.trans hW', fun _ => hH,
      .inr (by simp only [habr.catchReturn]; exact habr)⟩⟩
  · simp only at h; subst h
    cases hR
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

theorem BinOp.eval_sound {W' : World} (hC : HoldsOrVar C) (hop : BinOpTy C op τ₁ τ₂ τ)
    (hv₁ : V c W' τ₁ v₁) (hv₂ : V c W' τ₂ v₂) (hc : c ≤ k) (hW : W <+: W')
    (hH : HeapOK c W' h) : Safe (op.eval v₁ v₂, c, h) k W τ R := by
  cases hop with
  | plus hp =>
    rcases hp.holdsOrVar hC with hi | ⟨a, _, he⟩
    · cases hi with
      | plusNumber =>
        simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
        exact Safe.ok hc hW hH (by simp)
      | plusString =>
        simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
        exact Safe.ok hc hW hH (by simp)
    · simp only [List.cons.injEq] at he; rw [he.1] at hv₁; simp at hv₁
  | minus =>
    simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
    exact Safe.ok hc hW hH (by simp)

/-- Running a syntactic value gives a value, and takes no clock and no
cell. -/
theorem IsValue.run_value (hv : e.IsValue) (ht : HasType L C Γ R e τ) (hG : G W Γ env)
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

/-! ## Objects -/

/-- The value of a field a record type has present, in fields of the
record's types: the first one, as `lookup` finds. -/
theorem field_lookup {k : Nat} {W : World} {l : String} {σ : Ty} :
    ∀ {ls : List String} {τs : List Ty} {vs : List Value},
    VList k W τs vs → Ty.field l ls τs = some σ →
    ∃ v, (ls.zip vs).lookup l = some v ∧ V k W σ v
  | [], _, _, _, h => by simp [Ty.field] at h
  | _ :: _, [], _, _, h => by simp [Ty.field] at h
  | _ :: _, _ :: _, [], hvs, _ => by simp at hvs
  | l' :: ls, τ :: τs, v :: vs, hvs, h => by
    rw [VList_cons] at hvs
    simp only [Ty.field] at h
    simp only [List.zip_cons_cons, List.lookup_cons]
    by_cases e : l' = l
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h
      exact ⟨v, by simp, hvs.1⟩
    · simp only [e, ite_false] at h
      have hne : (l == l') = false := by simpa using Ne.symm e
      obtain ⟨v', h₁, h₂⟩ := field_lookup hvs.2 h
      exact ⟨v', by simp [hne, h₁], h₂⟩

theorem VList.append_single {k : Nat} {W : World} {τ : Ty} {v : Value} :
    ∀ {τs : List Ty} {vs : List Value}, VList k W τs vs → V k W τ v →
      VList k W (τs ++ [τ]) (vs ++ [v])
  | [], [], _, hv => by simpa using hv
  | _ :: _, _ :: _, h, hv => by
    rw [VList_cons] at h
    simp only [List.cons_append, VList_cons]
    exact ⟨h.1, VList.append_single h.2 hv⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h

theorem lookup_filter_ne {l l' : String} (e : l' ≠ l) :
    ∀ fs : List (String × Value), (fs.filter (·.1 != l)).lookup l' = fs.lookup l'
  | [] => rfl
  | (a, v) :: fs => by
    by_cases ha : a = l
    · subst ha
      have : (l' == a) = false := by simpa using e
      simp [List.lookup_cons, this, lookup_filter_ne e fs]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, ha, not_false_eq_true,
        ite_true, List.lookup_cons]
      split <;> simp_all [lookup_filter_ne e fs]

theorem VList.reverse {k : Nat} {W : World} : ∀ {τs : List Ty} {vs : List Value},
    VList k W τs vs → VList k W τs.reverse vs.reverse
  | [], [], _ => by simp
  | τ :: τs, v :: vs, h => by
    rw [VList_cons] at h
    simp only [List.reverse_cons]
    exact VList.append_single (VList.reverse h.2) h.1
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- A field an object literal's type has present is the last of its
occurrences in the literal. -/
theorem objSlots_field {l : String} {σ : Ty} {ls : List String} {τs : List Ty} :
    ∀ {L : List String} {absent : List Ty},
      Ty.field l L (objSlots L ls τs absent) = some (.slot .pre σ) →
      Ty.field l ls.reverse τs.reverse = some σ
  | [], _, h => by simp [Ty.field] at h
  | _ :: _, [], h => by simp [objSlots, Ty.field] at h
  | l' :: L, a :: absent, h => by
    simp only [objSlots, List.zip_cons_cons, List.map_cons, Ty.field] at h
    by_cases e : l' = l
    · subst e
      simp only [ite_true, Option.some.injEq] at h
      revert h
      cases Ty.field l' ls.reverse τs.reverse <;> simp
    · simp only [e, ite_false] at h
      exact objSlots_field (L := L) (absent := absent) h

/-- Each slot of an object literal's type is present, at the type of the
field's last occurrence, or absent, the literal having no such field. -/
theorem objSlots_field_cases {l : String} {s : Ty} {ls : List String} {τs : List Ty} :
    ∀ {L : List String} {absent : List Ty},
      Ty.field l L (objSlots L ls τs absent) = some s →
      (∃ σ, s = .slot .pre σ) ∨ ∃ σ, s = .slot .abs σ ∧ Ty.field l ls.reverse τs.reverse = none
  | [], _, h => by simp [Ty.field] at h
  | _ :: _, [], h => by simp [objSlots, Ty.field] at h
  | l' :: L, a :: absent, h => by
    simp only [objSlots, List.zip_cons_cons, List.map_cons, Ty.field] at h
    by_cases e : l' = l
    · subst e
      simp only [ite_true, Option.some.injEq] at h
      revert h
      cases hf : Ty.field l' ls.reverse τs.reverse with
      | none => intro h; exact .inr ⟨a, h.symm, rfl⟩
      | some σ => intro h; exact .inl ⟨σ, h.symm⟩
    · simp only [e, ite_false] at h
      exact objSlots_field_cases (L := L) (absent := absent) h

/-- A label with no field has no value. -/
theorem field_none_lookup {l : String} : ∀ {ls : List String} {τs : List Ty} {vs : List Value},
    vs.length = τs.length → Ty.field l ls τs = none → (ls.zip vs).lookup l = none
  | [], _, _, _, _ => rfl
  | _ :: _, [], vs, hl, _ => by
    rw [List.eq_nil_of_length_eq_zero (l := vs) (by simpa using hl)]; rfl
  | _ :: _, _ :: _, [], hl, _ => by simp at hl
  | l' :: ls, τ :: τs, v :: vs, hl, h => by
    simp only [Ty.field] at h
    split at h
    · cases h
    · rename_i e
      have hne : (l == l') = false := by simpa using Ne.symm e
      simp only [List.zip_cons_cons, List.lookup_cons, hne]
      exact field_none_lookup (by simpa using hl) h

/-- An object literal's cell holds the contents of its record type. -/
theorem objFields_sound {k : Nat} {W : World} {L ls : List String} {τs absent : List Ty}
    {vs : List Value} (hlen : τs.length = ls.length) (hvs : VList k W τs vs) :
    CellV k W (.obj (.record L (objSlots L ls τs absent))) (objFields ls vs) := by
  rw [CellV_obj]
  have hzip : (ls.zip vs).reverse = ls.reverse.zip vs.reverse := by
    simp only [List.zip_eq_zipWith]
    exact List.reverse_zipWith (by simp [hvs.length, hlen])
  refine ⟨_, rfl, fun l σ hl => ?_, fun l s hl => ?_⟩
  · rw [hzip]
    exact field_lookup hvs.reverse (objSlots_field hl)
  · rcases objSlots_field_cases hl with h | ⟨σ, rfl, hf⟩
    · exact .inl h
    · refine .inr ⟨σ, rfl, ?_⟩
      rw [hzip]
      exact field_none_lookup (by simp [hvs.length]) hf

/-- Reading a field: an instance of `HasProp` says the object's contents
have it, and a type variable has no values. -/
theorem getProp_sound {C : List Pred} {l : String} {τ σ : Ty} {v : Value} {c : Nat}
    {W : World} {h : Heap} {R : Option Ty}
    (hp : Entails C ⟨.hasProp l, [τ, σ]⟩) (hC : HoldsOrVar C) (hv : V c W τ v)
    (hH : HeapOK c W h) : Safe (v.getProp h l, c, h) c W σ R := by
  rcases hp.holdsOrVar hC with hi | ⟨a, _, he⟩
  · cases hi with
    | hasProp hf =>
      rw [V_record] at hv
      obtain ⟨ℓ, rfl, hℓ⟩ := hv
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨fs, rfl, hfs, -⟩ := CellV_obj.mp hsv
      obtain ⟨v', h₁, h₂⟩ := hfs l σ hf
      simp only [Value.getProp, hcv, h₁]
      exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH h₂
    | lengthArray =>
      rw [V_array] at hv
      obtain ⟨ℓ, rfl, hℓ⟩ := hv
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, -⟩ := CellV_arr.mp hsv
      simp only [Value.getProp, hcv, ite_true]
      exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (by simp)
    | lengthString =>
      obtain ⟨s, rfl⟩ := V_string.mp hv
      simp only [Value.getProp, ite_true]
      exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (by simp)
  · simp only [List.cons.injEq] at he; rw [he.1] at hv; simp at hv

/-- Writing a field: the object's contents keep their type. -/
theorem setProp_sound {C : List Pred} {l : String} {τ σ : Ty} {vo vv : Value} {c : Nat}
    {W : World} {h : Heap} {R : Option Ty}
    (hp : Entails C ⟨.hasProp l, [τ, σ]⟩) (hw : Entails C ⟨.fieldWrite, [τ]⟩) (hC : HoldsOrVar C)
    (hvo : V c W τ vo) (hvv : V c W σ vv) (hH : HeapOK c W h) :
    Safe ((vo.setProp h l vv).1, c, (vo.setProp h l vv).2) c W σ R := by
  rcases hp.holdsOrVar hC with hi | ⟨a, _, he⟩
  · cases hi with
    | lengthArray | lengthString =>
      exfalso
      rcases hw.holdsOrVar hC with hi | ⟨a, _, he⟩
      · cases hi
      · simp at he
    | hasProp hf =>
      rename_i ls slots
      rw [V_record] at hvo
      obtain ⟨ℓ, rfl, hℓ⟩ := hvo
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨fs, rfl, hfs, habs⟩ := CellV_obj.mp hsv
      simp only [Value.setProp, hcv]
      refine Safe.ok (Nat.le_refl c) (List.prefix_refl W) (hH.set hℓ ?_) hvv
      rw [CellV_obj]
      refine ⟨_, rfl, fun l' σ' hl' => ?_, fun l' s' hl' => ?_⟩
      rotate_left
      · rcases habs l' s' hl' with h | ⟨σ', rfl, hn⟩
        · exact .inl h
        · refine .inr ⟨σ', rfl, ?_⟩
          have e : l' ≠ l := by rintro rfl; rw [hf] at hl'; cases hl'
          have hne : (l' == l) = false := by simpa using e
          simp only [List.lookup_cons, hne]
          rw [lookup_filter_ne e]
          exact hn
      by_cases e : l' = l
      · subst e
        rw [hf] at hl'
        cases hl'
        exact ⟨vv, by simp, hvv⟩
      · obtain ⟨v', h₁, h₂⟩ := hfs l' σ' hl'
        refine ⟨v', ?_, h₂⟩
        have hne : (l' == l) = false := by simpa using e
        simp only [List.lookup_cons, hne]
        rw [lookup_filter_ne e]
        exact h₁
  · simp only [List.cons.injEq] at he; rw [he.1] at hvo; simp at hvo

/-- A fault is safe: the program stops there. -/
theorem Safe.fault {f : Fault} {c : Nat} {W : World} {h : Heap} {τ : Ty} {R : Option Ty}
    (hH : HeapOK c W h) : Safe (.fault f, c, h) c W τ R :=
  ⟨Nat.le_refl c, .inr ⟨W, List.prefix_refl W, hH, .inr (.inl trivial)⟩⟩

theorem VList.replicate {k : Nat} {W : World} {τ : Ty} :
    ∀ {n : Nat} {vs : List Value}, VList k W (List.replicate n τ) vs → ∀ w ∈ vs, V k W τ w
  | 0, [], _, w, hw => by cases hw
  | _ + 1, v :: vs, h, w, hw => by
    rw [List.replicate_succ, VList_cons] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact VList.replicate h.2 w hw
  | 0, _ :: _, h, _, _ => by simp at h
  | _ + 1, [], h, _, _ => by rw [List.replicate_succ] at h; simp at h

/-- Reading an element: an instance of `Indexable` says the container has
elements of the type, and an index it hasn't is a fault. -/
theorem index_sound {C : List Pred} {τ ι σ : Ty} {vo vi : Value} {c : Nat} {W : World}
    {h : Heap} {R : Option Ty} (hp : Entails C ⟨.indexable, [τ, ι, σ]⟩) (hC : HoldsOrVar C)
    (hvo : V c W τ vo) (hvi : V c W ι vi) (hH : HeapOK c W h) :
    Safe (vo.index h vi, c, h) c W σ R := by
  rcases hp.holdsOrVar hC with hi | ⟨a, _, he⟩
  · cases hi with
    | indexArray =>
      rw [V_array] at hvo
      obtain ⟨ℓ, rfl, hℓ⟩ := hvo
      obtain ⟨n, rfl⟩ := V_number.mp hvi
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, hvs⟩ := CellV_arr.mp hsv
      simp only [Value.index, hcv]
      split
      · rename_i v hv
        obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp hv
        exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (hvs v (List.mem_of_getElem? hk))
      · exact Safe.fault hH
    | indexString =>
      obtain ⟨s, rfl⟩ := V_string.mp hvo
      obtain ⟨n, rfl⟩ := V_number.mp hvi
      simp only [Value.index]
      split
      · exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (by simp)
      · exact Safe.fault hH
  · simp only [List.cons.injEq] at he; rw [he.1] at hvo; simp at hvo

/-- Storing an element: an array's cell keeps its type, and an index past
its end is a fault. -/
theorem setIndex_sound {C : List Pred} {τ ι σ : Ty} {vo vi vv : Value} {c : Nat} {W : World}
    {h : Heap} {R : Option Ty} (hp : Entails C ⟨.indexable, [τ, ι, σ]⟩)
    (hw : Entails C ⟨.indexWrite, [τ]⟩) (hC : HoldsOrVar C) (hvo : V c W τ vo)
    (hvi : V c W ι vi) (hvv : V c W σ vv) (hH : HeapOK c W h) :
    Safe ((vo.setIndex h vi vv).1, c, (vo.setIndex h vi vv).2) c W σ R := by
  rcases hw.holdsOrVar hC with hi | ⟨a, _, he⟩
  · cases hi with
    | writeArray =>
      rename_i ε
      -- The element type is the array's.
      have hσ : σ = ε ∧ ι = .number := by
        rcases hp.holdsOrVar hC with hi | ⟨a, _, he⟩
        · cases hi with
          | indexArray => exact ⟨rfl, rfl⟩
        · simp at he
      obtain ⟨rfl, rfl⟩ := hσ
      rw [V_array] at hvo
      obtain ⟨ℓ, rfl, hℓ⟩ := hvo
      obtain ⟨n, rfl⟩ := V_number.mp hvi
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, hvs⟩ := CellV_arr.mp hsv
      simp only [Value.setIndex, hcv]
      split
      · rename_i k _
        split
        · refine Safe.ok (Nat.le_refl c) (List.prefix_refl W)
            (hH.set hℓ (CellV_arr.mpr ⟨_, rfl, fun w hw => ?_⟩)) hvv
          rcases List.mem_or_eq_of_mem_set hw with hw | rfl
          · exact hvs w hw
          · exact hvv
        · split
          · refine Safe.ok (Nat.le_refl c) (List.prefix_refl W)
              (hH.set hℓ (CellV_arr.mpr ⟨_, rfl, fun w hw => ?_⟩)) hvv
            rcases List.mem_append.mp hw with hw | hw
            · exact hvs w hw
            · simp only [List.mem_singleton] at hw; subst hw; exact hvv
          · exact Safe.fault hH
      · exact Safe.fault hH
  · simp only [List.cons.injEq] at he; rw [he.1] at hvo; simp at hvo

/-- A slot of a spread's result, with the operand's slot and the slot it is
written over for the same label, and the `Merge` relating them. -/
theorem field_merge {l : String} {r : Ty} : ∀ {L : List String} {ps τs ss rs : List Ty},
    ps.length = L.length → τs.length = L.length → ss.length = L.length →
    rs.length = L.length → Ty.field l L rs = some r →
    ∃ p τ s, Ty.field l L (List.zipWith Ty.slot ps τs) = some (.slot p τ) ∧
      Ty.field l L ss = some s ∧ (⟨.merge, [p, τ, s, r]⟩ : Pred) ∈ mergePreds ps τs ss rs
  | [], _, _, _, _, _, _, _, _, h => by simp [Ty.field] at h
  | l' :: L, p :: ps, τ :: τs, s :: ss, r' :: rs, h₁, h₂, h₃, h₄, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂ h₃ h₄
    simp only [List.zipWith_cons_cons, Ty.field, mergePreds] at h ⊢
    by_cases e : l' = l
    · simp only [e, ite_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨p, τ, s, rfl, rfl, List.mem_cons_self⟩
    · simp only [e, ite_false] at h ⊢
      obtain ⟨p', τ', s', hp, hs, hm⟩ := field_merge h₁ h₂ h₃ h₄ h
      exact ⟨p', τ', s', hp, hs, List.mem_cons_of_mem _ hm⟩
  | _ :: _, [], _, _, _, h₁, _, _, _, _ | _ :: _, _ :: _, [], _, _, _, h₂, _, _, _
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h₃, _, _
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, h₄, _ => by simp at *

theorem lookup_append_none {l : String} {fs₁ fs₂ : List (String × Value)}
    (h : fs₂.lookup l = none) : (fs₂ ++ fs₁).lookup l = fs₁.lookup l := by
  induction fs₂ with
  | nil => rfl
  | cons a fs₂ ih =>
    obtain ⟨l', v⟩ := a
    by_cases e : (l == l') = true
    · simp [List.lookup_cons, e] at h
    · simp only [Bool.not_eq_true] at e
      simp only [List.lookup_cons, e] at h
      simp only [List.cons_append, List.lookup_cons, e]
      exact ih h

theorem lookup_append_some {l : String} {v : Value} {fs₁ fs₂ : List (String × Value)}
    (h : fs₂.lookup l = some v) : (fs₂ ++ fs₁).lookup l = some v := by
  induction fs₂ with
  | nil => cases h
  | cons a fs₂ ih =>
    obtain ⟨l', v'⟩ := a
    by_cases e : (l == l') = true
    · simp only [List.lookup_cons, e] at h
      simp only [List.cons_append, List.lookup_cons, e]
      exact h
    · simp only [Bool.not_eq_true] at e
      simp only [List.lookup_cons, e] at h
      simp only [List.cons_append, List.lookup_cons, e]
      exact ih h

/-- A record's value is an object, whose fields have the record's
contents. -/
theorem fieldsOf_sound {L : List String} {ss : List Ty} {v : Value} {c : Nat} {W : World}
    {h : Heap} (hv : V c W (.record L ss) v) (hH : HeapOK c W h) :
    ∃ fs, v.fieldsOf h = some fs ∧ CellV c W (.obj (.record L ss)) (.fields fs) := by
  rw [V_record] at hv
  obtain ⟨ℓ, rfl, hℓ⟩ := hv
  obtain ⟨cv, hcv, hV⟩ := hH.2 ℓ _ hℓ
  obtain ⟨fs, rfl, -⟩ := CellV_obj.mp hV
  exact ⟨fs, by simp [Value.fieldsOf, hcv], hV⟩

/-- A spread of two objects' fields: each `Merge` is an instance, since an
object's contents have no slot of unknown presence, so the merged fields
have the result's type. -/
theorem spread_contents_sound {C : List Pred} {L : List String} {ps τs ss rs : List Ty}
    {fs₁ fs₂ : List (String × Value)} {c : Nat} {W : World} (hC : HoldsOrVar C)
    (hps : ps.length = L.length) (hτs : τs.length = L.length) (hss : ss.length = L.length)
    (hrs : rs.length = L.length) (hm : ∀ p ∈ mergePreds ps τs ss rs, Entails C p)
    (hv₁ : CellV c W (.obj (.record L ss)) (.fields fs₁))
    (hv₂ : CellV c W (.obj (.record L (List.zipWith Ty.slot ps τs))) (.fields fs₂)) :
    CellV c W (.obj (.record L rs)) (.fields (fs₂ ++ fs₁)) := by
  obtain ⟨_, he₁, hpre₁, habs₁⟩ := CellV_obj.mp hv₁
  obtain ⟨_, he₂, hpre₂, habs₂⟩ := CellV_obj.mp hv₂
  cases he₁; cases he₂
  -- Each label: the operand has its field (`pre`) or hasn't (`abs`).
  have key : ∀ l r, Ty.field l L rs = some r →
      (∃ τ, r = .slot .pre τ ∧ ∃ v', fs₂.lookup l = some v' ∧ V c W τ v') ∨
      (Ty.field l L ss = some r ∧ fs₂.lookup l = none) := by
    intro l r hr
    obtain ⟨p, τ, s, hp, hs, hpm⟩ := field_merge hps hτs hss hrs hr
    rcases (hm _ hpm).holdsOrVar hC with hi | ⟨a, _, he⟩
    · cases hi with
      | mergePre => exact .inl ⟨τ, rfl, hpre₂ l τ hp⟩
      | mergeAbs =>
        rcases habs₂ l _ hp with ⟨σ, hσ⟩ | ⟨σ, -, hn⟩
        · cases hσ
        · exact .inr ⟨hs, hn⟩
    · simp only [List.cons.injEq] at he
      rw [he.1] at hp
      rcases habs₂ l _ hp with ⟨σ, hσ⟩ | ⟨σ, hσ, -⟩ <;> cases hσ
  rw [CellV_obj]
  refine ⟨_, rfl, fun l σ hl => ?_, fun l r hl => ?_⟩
  · rcases key l _ hl with ⟨τ, hτ, v', h₁, h₂⟩ | ⟨hs, hn⟩
    · cases hτ; exact ⟨v', lookup_append_some h₁, h₂⟩
    · rw [lookup_append_none hn]; exact hpre₁ l σ hs
  · rcases key l r hl with ⟨τ, rfl, -⟩ | ⟨hs, hn⟩
    · exact .inl ⟨τ, rfl⟩
    · rcases habs₁ l r hs with h' | ⟨σ, rfl, hn₁⟩
      · exact .inl h'
      · exact .inr ⟨σ, rfl, by rw [lookup_append_none hn]; exact hn₁⟩

/-! ## Arguments -/

/-- A safe outcome of running arguments of the types `τs`: their values,
or an outcome other than a value that is safe. -/
def SafeArgs (p : RanArgs) (k : Nat) (W : World) (τs : List Ty) (R : Option Ty) : Prop :=
  p.2.1 ≤ k ∧ match p.1 with
    | .ok vs => ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧ VList p.2.1 W' τs vs
    | .error r => r = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧
        (r.Abrupt ∨ (∃ v, r = .returned v ∧ ∃ τr, R = some τr ∧ V p.2.1 W' τr v))

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
    rcases h with rfl | ⟨W', hW, hH, habr | ⟨v, rfl, hv⟩⟩
    · exact ⟨hc, .inl rfl⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl habr)⟩⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr ⟨v, rfl, hv⟩)⟩⟩

/-- What the fundamental lemma says of one expression. -/
def RunSound (L : List String) (e : Expr) : Prop :=
  ∀ {k C Γ R W env h τ}, HasType L C Γ R e τ → HoldsOrVar C → G W Γ env → HeapOK k W h →
    Safe (run k env h e) k W τ R

/-- Well-typed arguments, each safe by the fundamental lemma, run safely. -/
theorem runArgs_sound {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty}
    (hC : HoldsOrVar C) :
    ∀ (args : List Expr) (τs : List Ty) {k : Nat} {W : World} {env : Env} {h : Heap},
      (∀ a ∈ args, RunSound L a) →
      args.length = τs.length → (∀ p ∈ args.zip τs, HasType L C Γ R p.1 p.2) → G W Γ env →
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
    rcases hr with hr | ⟨W₁, hW₁, hH₁, ⟨v, hr, hv⟩ | habr | ⟨v, hr, hv⟩⟩
    · simp only at hr; subst hr
      simp only [runArgs, hp]
      exact ⟨hc₁, .inl rfl⟩
    · simp only at hr; subst hr
      have has := runArgs_sound hC as τs (fun a' ha' => ih a' (by simp [ha']))
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
    · simp only at habr
      cases r <;> simp only [Result.Abrupt] at habr <;> simp only [runArgs, hp] <;>
        exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inl trivial⟩⟩
    · simp only at hr; subst hr
      simp only [runArgs, hp]
      exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inr ⟨v, rfl, hv⟩⟩⟩

/-! ## The fundamental lemma -/

/-- A call's cells: the arguments, the function and `this`, after the
caller's. -/
theorem G.call {W : World} {Γ : Ctx} {env : Env} {h : Heap} {θ ρ : Ty} {τs : List Ty}
    (hG : G W Γ env) (hlen : h.length = W.length) :
    G (W ++ τs.map Cell.mono ++ [Cell.mono (.fn θ τs ρ), Cell.mono θ])
      (τs.map Scheme.mono ++ Scheme.mono (.fn θ τs ρ) :: Scheme.mono θ :: Γ)
      (callEnv h τs.length env) := by
  have e₁ : τs.map Scheme.mono ++ Scheme.mono (.fn θ τs ρ) :: Scheme.mono θ :: Γ =
      (τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ]) ++ Γ := by simp
  have e₂ : callEnv h τs.length env =
      List.range' h.length
        (τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ]).length ++ env := by
    simp [callEnv]
  have e₃ : W ++ τs.map Cell.mono ++ [Cell.mono (.fn θ τs ρ), Cell.mono θ] =
      W ++ (τs.map Scheme.mono ++ [Scheme.mono (.fn θ τs ρ), Scheme.mono θ]).map Cell.scheme := by
    simp [Cell.mono, Function.comp_def]
  rw [e₁, e₂, e₃]
  refine G.block _ _ (fun i hi => ?_) (G.mono (List.prefix_append _ _) hG)
  rw [hlen, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem run_sound (L : List String) (e : Expr) : RunSound L e := by
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
        (hsv _ hlen (fun c h => (hc c h).holdsOrVar hC))
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
          intro i hi W' _ h' thisv args hl _ _ _
          obtain rfl : i = 0 := by omega
          simp only [call, hl, Nat.le_refl, ↓reduceIte]
          exact ⟨Nat.le_refl 0, .inl rfl⟩
        | succ j ihj =>
          intro W hGW
          rw [V_fn]
          intro i hi W' hW' h' thisv args hl hh hthis hargs
          simp only [call, hl, Nat.le_refl, ↓reduceIte,
            List.take_of_length_le (Nat.le_of_eq hl)]
          cases i with
          | zero => exact ⟨Nat.le_refl 0, .inl rfl⟩
          | succ i =>
            have hH' : HeapOK i W' h' := hh i (by omega)
            have hW₁ : W' <+: W' ++ τs.map Cell.mono := List.prefix_append _ _
            have hW₂ : W' <+: W' ++ τs.map Cell.mono ++ [Cell.mono (.fn θ τs ρ), Cell.mono θ] :=
              hW₁.trans (List.prefix_append _ _)
            have hcells : HeapOK i (W' ++ τs.map Cell.mono ++ [Cell.mono (.fn θ τs ρ), Cell.mono θ])
                (h' ++ args ++ [.closure env τs.length body, thisv]) := by
              refine (hH'.allocList ((hargs i (by omega)).mono (Nat.le_refl i) hW₁)).alloc
                (by simp) (fun idx s v hs hv => ?_)
              match idx, hs, hv with
              | 0, hs, hv =>
                simp at hs hv; subst hs hv
                exact SchemeV.mono_iff.mpr
                  ((ihj _ (G.mono (hW'.trans hW₂) hGW)).mono (by omega) (List.prefix_refl _))
              | 1, hs, hv =>
                simp at hs hv; subst hs hv
                exact SchemeV.mono_iff.mpr ((hthis i (by omega)).mono (Nat.le_refl i) hW₂)
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
        _ .undefined vs hvs.length (fun i hi => hH₂.mono (by omega)) (by simp)
        (fun i hi => hvs.mono (by omega) (List.prefix_refl _)))
  | let_ mb e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | let_ s F hgen hval _ h₂ =>
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (F ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Pred.ftv ++
        (R.map Ty.ftv).getD [])
      have hm : ∀ a, a ∈ F ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Pred.ftv ∨
          a ∈ (R.map Ty.ftv).getD [] → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasType L (C ++ s.instPreds τs) Γ R e₁ (s.inst τs) := by
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
      have hsafe : ∀ τs, τs.length = s.arity → HoldsOrVar (s.instPreds τs) →
          Safe (run k env h e₁) k W (s.inst τs) R := fun τs hlen hp =>
        ih₁ (hinst τs hlen) (hC.append hp) hG hH
      -- What follows the initialiser: its value in a new cell.
      have hK : ∀ v c₁ h₁ W₁, c₁ ≤ k → W <+: W₁ → HeapOK c₁ W₁ h₁ → SchemeV c₁ W₁ s v →
          Safe (run (min c₁ k) (h₁.length :: env) (h₁ ++ [v]) e₂) c₁ W₁ τ R := by
        intro v c₁ h₁ W₁ hc hW₁ hH₁ hv
        rw [Nat.min_eq_left hc]
        have hW₂ : W₁ <+: W₁ ++ [.scheme s] := List.prefix_append _ _
        have hcell : HeapOK c₁ (W₁ ++ [.scheme s]) (h₁ ++ [v]) :=
          hH₁.alloc (by simp) (fun i s' v' hs hv' => by
            match i, hs, hv' with
            | 0, hs, hv' =>
              simp at hs hv'; subst hs hv'; exact hv.mono (Nat.le_refl _) hW₂
            | _ + 1, hs, _ => simp at hs)
        have hG₂ : G (W₁ ++ [.scheme s]) (s :: Γ) (h₁.length :: env) :=
          ⟨by rw [hH₁.1]; simp, G.mono (hW₁.trans hW₂) hG⟩
        exact (ih₂ h₂ hC hG₂ hcell).weaken (Nat.le_refl _) hW₂
      simp only [run]
      rcases hval with ⟨ha, hp⟩ | ⟨hv, _⟩
      · -- One instance: no quantified variables, no constraints.
        refine Safe.bindC (hsafe [] (by simp [ha]) (by simp [HoldsOrVar, Scheme.instPreds, hp]))
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
        rcases hs with hs | ⟨W', hW', hH', ⟨v', hv', hvv⟩ | hv' | ⟨_, hv', _⟩⟩
        · simp at hs
        · simp at hv'; subst hv'
          obtain rfl := hW'.eq_of_length (by rw [← hH'.1, hH.1])
          exact hvv
        · simp [Result.Abrupt] at hv'
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
        ⟨Nat.le_refl _, .inr ⟨W₁, List.prefix_refl W₁, hH₁, .inr (.inl trivial)⟩⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | seq h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC hG hH) fun _ W₁ _ hW₁ hH₁ _ => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      exact ih₂ h₂ hC (G.mono hW₁ hG) hH₁

  | while_ c body ihc ihb =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | while_ hc hb =>
      -- By induction on the clock: each iteration takes a tick.
      induction k using Nat.strongRecOn generalizing W h with
      | _ k ihk =>
        rw [run_while]
        refine Safe.bindC (ihc hc hC hG hH) fun v W₁ _ hW₁ hH₁ _ => ?_
        have hc₁ := run_clock_le k env h c
        rw [Nat.min_eq_left hc₁]
        split
        · have hsb := ihb hb hC (G.mono hW₁ hG) hH₁
          have hc₂ := run_clock_le (run k env h c).2.1 env (run k env h c).2.2 body
          generalize run (run k env h c).2.1 env (run k env h c).2.2 body = p at hsb hc₂ ⊢
          obtain ⟨r, c₂, h₂⟩ := p
          obtain ⟨-, hs⟩ := hsb
          simp only at hc₂
          -- The loop again, from where the body left it.
          have again : ∀ W₂, W₁ <+: W₂ → HeapOK c₂ W₂ h₂ →
              Safe (match min c₂ k with
                | 0 => (.timeout, 0, h₂)
                | c' + 1 => run c' env h₂ (.while_ c body))
                (run k env h c).2.1 W₁ .undefined R := by
            intro W₂ hW₂ hH₂
            rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
            cases c₂ with
            | zero => exact ⟨Nat.zero_le _, .inl rfl⟩
            | succ c' =>
              exact (ihk c' (by omega) (G.mono (hW₁.trans hW₂) hG)
                (hH₂.mono (by omega))).weaken (by omega) hW₂
          rcases hs with hs | ⟨W₂, hW₂, hH₂, ⟨v', hv', _⟩ | habr | ⟨v', hv', hret⟩⟩
          · simp only at hs; subst hs; exact ⟨hc₂, .inl rfl⟩
          · simp only at hv'; subst hv'; exact again W₂ hW₂ hH₂
          · simp only at habr
            cases r
            case broke => exact Safe.ok hc₂ hW₂ hH₂ (by simp)
            case continued => exact again W₂ hW₂ hH₂
            all_goals
              first
                | exact ⟨hc₂, .inr ⟨W₂, hW₂, hH₂, .inr (.inl habr)⟩⟩
                | simp [Result.Abrupt] at habr
          · simp only at hv'; subst hv'
            exact ⟨hc₂, .inr ⟨W₂, hW₂, hH₂, .inr (.inr ⟨v', rfl, hret⟩)⟩⟩
        · exact Safe.ok (Nat.le_refl _) (List.prefix_refl _) hH₁ (by simp)
  | break_ =>
    intro k C Γ R W env h τ _ _ _ hH
    simp only [run]
    exact ⟨Nat.le_refl _, .inr ⟨W, List.prefix_refl W, hH, .inr (.inl trivial)⟩⟩
  | continue_ =>
    intro k C Γ R W env h τ _ _ _ hH
    simp only [run]
    exact ⟨Nat.le_refl _, .inr ⟨W, List.prefix_refl W, hH, .inr (.inl trivial)⟩⟩
  | tryCatch body handler ihb ihh =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | tryCatch hb hh =>
      have hsb := ihb hb hC hG hH
      have hc₁ := run_clock_le k env h body
      simp only [run]
      generalize run k env h body = p at hsb hc₁ ⊢
      obtain ⟨r, c₁, h₁⟩ := p
      obtain ⟨-, hs⟩ := hsb
      simp only at hc₁
      cases r
      case thrown v =>
        simp only
        rcases hs with hs | ⟨W₁, hW₁, hH₁, _⟩
        · cases hs
        · -- The caught value, in a new cell of the opaque type.
          have hW₂ : W₁ <+: W₁ ++ [.mono .unknown] := List.prefix_append _ _
          have hcell : HeapOK c₁ (W₁ ++ [.mono .unknown]) (h₁ ++ [v]) :=
            hH₁.alloc (by simp) (fun i s' v' hs' hv' => by
              match i, hs', hv' with
              | 0, hs', hv' =>
                simp at hs' hv'; subst hs' hv'; exact SchemeV.mono_iff.mpr (by simp)
              | _ + 1, hs', _ => simp at hs')
          have hG₂ : G (W₁ ++ [.mono .unknown]) (.mono .unknown :: Γ) (h₁.length :: env) :=
            ⟨by rw [hH₁.1]; simp, G.mono (hW₁.trans hW₂) hG⟩
          rw [Nat.min_eq_left hc₁]
          exact (ihh hh hC hG₂ hcell).weaken hc₁ (hW₁.trans hW₂)
      all_goals exact ⟨hc₁, hs⟩
  | tryFinally body fin ihb ihf =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | tryFinally hb hf =>
      have hsb := ihb hb hC hG hH
      have hc₁ := run_clock_le k env h body
      simp only [run]
      generalize run k env h body = p at hsb hc₁ ⊢
      obtain ⟨r, c₁, h₁⟩ := p
      obtain ⟨-, hs⟩ := hsb
      simp only at hc₁
      rcases hs with hs | ⟨W₁, hW₁, hH₁, hs⟩
      · simp only at hs; subst hs; exact ⟨hc₁, .inl rfl⟩
      · have hne : r ≠ .timeout := by
          rintro rfl
          rcases hs with ⟨_, e, _⟩ | e | ⟨_, e, _⟩ <;> simp [Result.Abrupt] at e
        have hsf := ihf hf hC (G.mono hW₁ hG) hH₁
        have hc₂ := run_clock_le c₁ env h₁ fin
        cases r
        case timeout => exact absurd rfl hne
        case stuck s =>
          exfalso
          rcases hs with ⟨_, e, _⟩ | e | ⟨_, e, _⟩ <;> simp [Result.Abrupt] at e
        case fault f => exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, hs⟩⟩
        all_goals
          simp only
          rw [Nat.min_eq_left hc₁]
          generalize run c₁ env h₁ fin = q at hsf hc₂ ⊢
          obtain ⟨r', c₂, h₂⟩ := q
          obtain ⟨-, hq⟩ := hsf
          simp only at hc₂
          cases r'
          case ok v' =>
            simp only
            rcases hq with hq | ⟨W₂, hW₂, hH₂, _⟩
            · cases hq
            · exact ⟨by simp only; omega, .inr ⟨W₂, hW₁.trans hW₂, hH₂, outcome_mono hs hc₂ hW₂⟩⟩
          all_goals exact (Safe.retype ⟨hc₂, hq⟩ (by simp)).weaken hc₁ hW₁

  | obj ls es ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | @obj _ _ _ _ _ τs absent hτs habs hL hes hargs =>
      simp only [run]
      refine Safe.bindArgs (runArgs_sound hC es _ ih (by omega) hargs hG hH)
        fun vs W₁ _ hW₁ hH₁ hvs => ?_
      have hb : (runArgs k env h es).2.2.length = W₁.length := hH₁.1
      have hW₂ := List.prefix_append W₁ [Cell.obj (.record L (objSlots L ls τs absent))]
      refine Safe.ok (Nat.le_refl _) hW₂ ?_ ?_
      · exact hH₁.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact (objFields_sound hτs hvs).mono (Nat.le_refl _) hW₂
          | _ + 1, hs, _ => simp at hs)
      · rw [V_record, hb]
        exact ⟨_, rfl, by simp⟩
  | get e l ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | get he hp =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv => getProp_sound hp hC hv hH₁
  | set e l v ihe ihv =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | set he hp hw hv =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ihv hv hC (G.mono hW₁ hG) hH₁) fun vv W₂ _ hW₂ hH₂ hvv => ?_
      exact setProp_sound hp hw hC (hvo.mono (run_clock_le _ _ _ _) hW₂) hvv hH₂
  | spread e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | spread hps hτs hss hrs he₁ he₂ hm =>
      rename_i ss ps τs rs
      simp only [run]
      refine Safe.bindC (ih₁ he₁ hC hG hH) fun v₁ W₁ _ hW₁ hH₁ hv₁ => ?_
      obtain ⟨fs₁, hf₁, hV₁⟩ := fieldsOf_sound hv₁ hH₁
      simp only [hf₁]
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ih₂ he₂ hC (G.mono hW₁ hG) hH₁) fun v₂ W₂ _ hW₂ hH₂ hv₂ => ?_
      obtain ⟨fs₂, hf₂, hV₂⟩ := fieldsOf_sound hv₂ hH₂
      have hV := spread_contents_sound hC hps hτs hss hrs hm
        (hV₁.mono (run_clock_le _ _ _ _) hW₂) hV₂
      generalize run (run k env h e₁).2.1 env (run k env h e₁).2.2 e₂ = p at hf₂ hH₂ hV ⊢
      obtain ⟨r₂, c₂, h₂⟩ := p
      simp only at hf₂ hH₂ hV ⊢
      rw [hf₂]
      have hW₃ := List.prefix_append W₂ [Cell.obj (.record L rs)]
      refine Safe.ok (Nat.le_refl _) hW₃ ?_ ?_
      · exact hH₂.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact hV.mono (Nat.le_refl _) hW₃
          | _ + 1, hs, _ => simp at hs)
      · rw [V_record, hH₂.1]
        exact ⟨_, rfl, by simp⟩

  | arr es ih =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | @arr _ _ _ _ σ hes =>
      simp only [run]
      have hargs : ∀ p ∈ es.zip (List.replicate es.length σ), HasType L C Γ R p.1 p.2 :=
        fun p hp => by
          obtain ⟨h₁, h₂⟩ := List.of_mem_zip hp
          rw [List.eq_of_mem_replicate h₂]; exact hes _ h₁
      refine Safe.bindArgs (runArgs_sound hC es _ ih (by simp) hargs hG hH)
        fun vs W₁ _ hW₁ hH₁ hvs => ?_
      have hb : (runArgs k env h es).2.2.length = W₁.length := hH₁.1
      have hW₂ := List.prefix_append W₁ [Cell.arr σ]
      refine Safe.ok (Nat.le_refl _) hW₂ ?_ ?_
      · exact hH₁.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact CellV_arr.mpr ⟨_, rfl, fun w hw =>
              (VList.replicate hvs w hw).mono (Nat.le_refl _) hW₂⟩
          | _ + 1, hs, _ => simp at hs)
      · rw [V_array, hb]
        exact ⟨_, rfl, by simp⟩
  | index e i ihe ihi =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | index he hi hp =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ihi hi hC (G.mono hW₁ hG) hH₁) fun vi W₂ _ hW₂ hH₂ hvi => ?_
      exact index_sound hp hC (hvo.mono (run_clock_le _ _ _ _) hW₂) hvi hH₂
  | setIndex e i v ihe ihi ihv =>
    intro k C Γ R W env h τ ht hC hG hH
    cases ht with
    | setIndex he hi hp hw hv =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ihi hi hC (G.mono hW₁ hG) hH₁) fun vi W₂ _ hW₂ hH₂ hvi => ?_
      have hc₂ := run_clock_le (run k env h e).2.1 env (run k env h e).2.2 i
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      refine Safe.bindC (ihv hv hC (G.mono (hW₁.trans hW₂) hG) hH₂) fun vv W₃ _ hW₃ hH₃ hvv => ?_
      exact setIndex_sound hp hw hC ((hvo.mono (run_clock_le _ _ _ _) hW₂).mono
        (run_clock_le _ _ _ _) hW₃) (hvi.mono (run_clock_le _ _ _ _) hW₃) hvv hH₃

/-- Type soundness, for `eval`: a value of the type, a `return` of a value
of the return type, a `throw`, or out of clock; never stuck. -/
theorem eval_sound (clock : Nat) (ht : HasType L C Γ R e τ) (hC : HoldsOrVar C)
    (hG : G W Γ env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  run_sound L e ht hC hG hH

/-- A closed program, well typed outside any function, assuming constraints
each an instance or on a type variable, never gets stuck, whatever the
clock. -/
theorem never_stuck (ht : HasType L C [] none e τ) (hC : HoldsOrVar C) (clock : Nat)
    (s : Stuck) : eval clock [] [] e ≠ .stuck s :=
  Safe.not_stuck (run_sound L e ht (W := []) hC (by simp [G])
    ⟨rfl, fun _ _ h => by simp at h⟩)

end Inty
