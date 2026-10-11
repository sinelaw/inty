import Inty.Wide
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

/-- How an object with the properties `fs` holds its field `l`, of the
slot `s` in the record type `T`, given which values `P` gives each type: a
field that holds a value, a value of its type; an own getter, a function
from `T` to its type; a prototype member, a method of its type or such a
getter; an absent field, no own property. (A slot whose presence or kind
isn't known, a variable, has no contents, as a type variable has no
values.) Slots are compared up to equal types. -/
def MemberP (P : Ty → Value → Prop) (T : Ty) (fs : List (String × MemberKind × Value))
    (l : String) (s : Ty) : Prop :=
  (∃ σ, TyEq s (.slot .pre .data σ) ∧ ∃ v, fs.lookup l = some (.data, v) ∧ P σ v) ∨
  (∃ σ, TyEq s (.slot .pre .getter σ) ∧ ∃ g, fs.lookup l = some (.getter, g) ∧
    P (.fn T [] σ) g) ∨
  (∃ σ, TyEq s (.slot .pre .proto σ) ∧
    ((∃ v, fs.lookup l = some (.method, v) ∧ P σ v) ∨
     (∃ g, fs.lookup l = some (.protoGetter, g) ∧ P (.fn T [] σ) g))) ∨
  (∃ k σ, TyEq s (.slot .abs k σ) ∧ fs.lookup l = none)

theorem MemberP.mono {P Q : Ty → Value → Prop} (hPQ : ∀ τ v, P τ v → Q τ v) {T : Ty}
    {fs : List (String × MemberKind × Value)} {l : String} {s : Ty} (h : MemberP P T fs l s) :
    MemberP Q T fs l s := by
  rcases h with ⟨σ, h₁, v, h₂, h₃⟩ | ⟨σ, h₁, g, h₂, h₃⟩ | ⟨σ, h₁, ⟨v, h₂, h₃⟩ | ⟨g, h₂, h₃⟩⟩ |
    ⟨k, σ, h₁, h₂⟩
  · exact .inl ⟨σ, h₁, v, h₂, hPQ _ _ h₃⟩
  · exact .inr (.inl ⟨σ, h₁, g, h₂, hPQ _ _ h₃⟩)
  · exact .inr (.inr (.inl ⟨σ, h₁, .inl ⟨v, h₂, hPQ _ _ h₃⟩⟩))
  · exact .inr (.inr (.inl ⟨σ, h₁, .inr ⟨g, h₂, hPQ _ _ h₃⟩⟩))
  · exact .inr (.inr (.inr ⟨k, σ, h₁, h₂⟩))

/-- What a cell holds, given which values `P` gives each type: a variable's
value has every instance of its scheme whose constraints hold; an object's
properties hold its record type's fields (`MemberP`); an array's elements
each have the element type. -/
def CellP (P : Ty → Value → Prop) : Cell → Value → Prop
  | .scheme s, v => ∀ τs, τs.length = s.arity → HoldsOrVarW (s.instPreds τs) → P (s.inst τs) v
  | .obj (.record ls slots), v => ∃ fs, v = .fields fs ∧ (∀ l s, Ty.field l ls slots = some s →
      MemberP P (.record ls slots) fs l s) ∧ ∀ l, Ty.field l ls slots = none → fs.lookup l = none
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
        obtain ⟨fs, rfl, hf, hn⟩ := h
        exact ⟨fs, rfl, fun l s hl => (hf l s hl).mono hPQ, hn⟩
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

/-- The measure of `V`'s recursion: a recursive type unfolds, at the same
index, to a constructor application, and a sum `Ty.maybe` goes, at the
same index, to the head under its layers, which is neither. -/
def Ty.rank : Ty → Nat
  | .mu _ _ => 2
  | .app (.maybe _) _ => 1
  | _ => 0

/-- The layers of sums `Ty.maybe` on top of a type, unfolding recursive
types, with fuel `n`: the values the first `n` layers add, and the head
under them if there are fewer (`μt. Nullable t` has as many layers as one
likes, each adding `null`). -/
def Ty.strip : Nat → Ty → List Nothing × Option Ty
  | 0, _ => ([], none)
  | n + 1, τ => match τ.whnf with
    | .app (.maybe z) [σ] => ((z :: (Ty.strip n σ).1), (Ty.strip n σ).2)
    | t => ([], some t)

theorem Ty.rank_app_lt_mu (c : Con) (args : List Ty) (i : Nat) (sys : List RTy) :
    (Ty.app c args).rank < (Ty.mu i sys).rank := by
  cases c <;> simp [Ty.rank]

theorem Ty.rank_lt_maybe {t : Ty} (h : t.rank = 0) (z : Nothing) (τ : Ty) :
    t.rank < (Ty.maybe z τ).rank := by
  rw [h]; simp [Ty.rank]

theorem Ty.rank_le (τ : Ty) : τ.rank ≤ 2 := by
  unfold Ty.rank; split <;> omega

mutual
/-- `V k W τ v`: the value `v` has type `τ` for `k` more calls, in the world
`W`. A base type has its values, and `unknown` (what a `catch` binds) has
every value. A type variable has none: a closed program can't make a value
of a type it knows nothing about. A function type is what
calling the function does (see the module docs); the call's `this` and
arguments need only be good below the clock it is given, since the body
runs a tick down. A record is an object whose cell the world says holds
fields of a record type equal to it, and an array one whose cell holds
elements of a type equal to its element type (`CellP`). A recursive type
has the values of its unfolding, if that is a constructor application. A
slot, a presence, or a constructor applied to the wrong number of types has
no values. -/
def V (k : Nat) (W : World) : Ty → Value → Prop
  | .number, v => ∃ n, v = .number n
  | .string, v => ∃ s, v = .string s
  | .boolean, v => ∃ b, v = .boolean b
  | .undefined, v => v = .undefined
  | .null, v => v = .null
  | .unknown, _ => True
  | .newTarget, _ => True
  | .fn θ τs ρ, f => (TyEq θ .newTarget → f.isCtor = true) ∧
      ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args, args.length = τs.length →
      (∀ i, i < j → HeapInv (CellP (fun τ v => V i W' τ v)) W' h) →
      (∀ i, i < j → V i W' θ thisv) → (∀ i, i < j → VList i W' τs args) →
      Lands (call j h f thisv args) j W'
        (fun c W'' h'' => c < j → HeapInv (CellP (fun τ v => V c W'' τ v)) W'' h'')
        (fun c W'' v => c < j → V c W'' ρ v)
  | .record ls slots, v => ∃ ℓ τc, v = .obj ℓ ∧ W[ℓ]? = some (.obj τc) ∧
      TyEq (.record ls slots) τc
  | .array τ, v => ∃ ℓ τc, v = .arr ℓ ∧ W[ℓ]? = some (.arr τc) ∧ TyEq τ τc
  | .mu i sys, v =>
    match (Ty.mu i sys).view with
    | some (.app c args) => V k W (.app c args) v
    | _ => False
  | .maybe z τ, v => v = z.value ∨ ∃ n, v ∈ (Ty.strip n τ).1.map Nothing.value ∨
      match (Ty.strip n τ).2 with
      | some t => if _ : t.rank = 0 then V k W t v else False
      | none => False
  | _, _ => False
termination_by τ => (k, τ.rank)
decreasing_by
  all_goals first
    | exact .left _ _ (by omega)
    | exact .right _ (Ty.rank_app_lt_mu _ _ _ _)
    | exact .right _ (Ty.rank_lt_maybe ‹_› _ _)
/-- `VList k W τs vs`: one value of each type. -/
def VList (k : Nat) (W : World) : List Ty → List Value → Prop
  | [], [] => True
  | τ :: τs, v :: vs => V k W τ v ∧ VList k W τs vs
  | _, _ => False
termination_by τs => (k, 3 + τs.length)
decreasing_by
  all_goals first
    | exact .left _ _ (by omega)
    | exact .right _ (by have := Ty.rank_le τ; omega)
    | exact .right _ (by simp)
end

/-- What a cell holds, at index `k` in `W`. -/
abbrev CellV (k : Nat) (W : World) : Cell → Value → Prop := CellP (V k W)

/-- A value has every instance of the scheme whose constraints hold. -/
def SchemeV (k : Nat) (W : World) (s : Scheme) (v : Value) : Prop :=
  ∀ τs, τs.length = s.arity → HoldsOrVarW (s.instPreds τs) → V k W (s.inst τs) v

theorem CellV_scheme : CellV k W (.scheme s) v ↔ SchemeV k W s v := Iff.rfl

theorem CellV_obj : CellV k W (.obj (.record ls slots)) v ↔ ∃ fs, v = .fields fs ∧
      (∀ l s, Ty.field l ls slots = some s → MemberP (V k W) (.record ls slots) fs l s) ∧
      ∀ l, Ty.field l ls slots = none → fs.lookup l = none := Iff.rfl

theorem CellV_arr : CellV k W (.arr τ) v ↔ ∃ vs, v = .items vs ∧ ∀ w ∈ vs, V k W τ w := Iff.rfl

/-- The heap is described by the world, at index `k`. -/
def HeapOK (k : Nat) (W : World) (h : Heap) : Prop := HeapInv (CellV k W) W h

/-- The function clause of `V`, in terms of `HeapOK`. -/
theorem V_fn {k : Nat} {W : World} {θ ρ : Ty} {τs : List Ty} {f : Value} :
    V k W (.fn θ τs ρ) f ↔ (TyEq θ .newTarget → f.isCtor = true) ∧ ∀ j, j ≤ k → ∀ W', W <+: W' → ∀ h thisv args,
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
@[simp] theorem V_newTarget : V k W .newTarget v ↔ True := by rw [V.eq_def]
@[simp] theorem V_var : V k W (.var a) v ↔ False := by rw [V.eq_def]

theorem V_record : V k W (.record ls slots) v ↔ ∃ ℓ τc, v = .obj ℓ ∧
      W[ℓ]? = some (.obj τc) ∧ TyEq (.record ls slots) τc := by
  rw [V.eq_def]

theorem V_array : V k W (.array τ) v ↔ ∃ ℓ τc, v = .arr ℓ ∧ W[ℓ]? = some (.arr τc) ∧
      TyEq τ τc := by
  rw [V.eq_def]

theorem V_mu : V k W (.mu i sys) v ↔
    ∃ c args, (Ty.mu i sys).view = some (.app c args) ∧ V k W (.app c args) v := by
  rw [V.eq_def]
  simp only
  split
  · rename_i c args h; exact ⟨fun hv => ⟨c, args, h, hv⟩, fun ⟨c', args', h', hv⟩ => by
      rw [h] at h'; cases h'; exact hv⟩
  · rename_i h; exact ⟨False.elim, fun ⟨c', args', h', _⟩ => h c' args' h'⟩

/-- A type has the values of its unfolding, which is a constructor
application if it has any. -/
theorem V_view : V k W τ v ↔ ∃ c args, τ.view = some (.app c args) ∧ V k W (.app c args) v := by
  cases τ with
  | var a => simp [Ty.view]
  | app c args =>
    exact ⟨fun hv => ⟨c, args, rfl, hv⟩, fun ⟨_, _, h, hv⟩ => by
      simp only [Ty.view, Option.some.injEq, Ty.app.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hv⟩
  | mu i sys => exact V_mu

/-- Apart from functions, records, arrays, recursive types and sums, a
type's values don't depend on the index or the world. -/
theorem V.base {k k' : Nat} {W W' : World} {τ : Ty} {v : Value}
    (hfn : ∀ θ τs ρ, τ ≠ .fn θ τs ρ) (hrec : ∀ ls slots, τ ≠ .record ls slots)
    (harr : ∀ σ, τ ≠ .array σ) (hmu : ∀ i sys, τ ≠ .mu i sys)
    (hmay : ∀ z σ, τ ≠ .maybe z σ) :
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

/-- `V.mono` for a constructor application other than a sum's. -/
theorem V.mono_app_base {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {c : Con}
    {args : List Ty} {v : Value} (hc : ∀ z, c ≠ .maybe z) (hv : V k W (.app c args) v) :
    V j W' (.app c args) v := by
  by_cases hfn : ∃ θ τs ρ, Ty.app c args = .fn θ τs ρ
  · obtain ⟨θ, τs, ρ, e⟩ := hfn
    rw [e] at hv ⊢
    rw [V_fn] at hv ⊢
    refine ⟨hv.1, ?_⟩
    intro i hi W'' hW'' h thisv args hl hh ht ha
    exact hv.2 i (Nat.le_trans hi hjk) W'' (hW.trans hW'') h thisv args hl hh ht ha
  · by_cases hrec : ∃ ls slots, Ty.app c args = .record ls slots
    · obtain ⟨ls, slots, e⟩ := hrec
      rw [e] at hv ⊢
      rw [V_record] at hv ⊢
      obtain ⟨ℓ, τc, rfl, hℓ, hτ⟩ := hv
      exact ⟨ℓ, τc, rfl, prefix_getElem? hW hℓ, hτ⟩
    · by_cases harr : ∃ σ, Ty.app c args = .array σ
      · obtain ⟨σ, e⟩ := harr
        rw [e] at hv ⊢
        rw [V_array] at hv ⊢
        obtain ⟨ℓ, τc, rfl, hℓ, hτ⟩ := hv
        exact ⟨ℓ, τc, rfl, prefix_getElem? hW hℓ, hτ⟩
      · exact (V.base (fun θ τs ρ e => hfn ⟨θ, τs, ρ, e⟩)
          (fun ls slots e => hrec ⟨ls, slots, e⟩) (fun σ e => harr ⟨σ, e⟩)
          (fun i sys e => by cases e) (fun z σ e => by cases e; exact hc z rfl)).mp hv

/-! ### Sums -/

/-- What `V` says of a sum's layers, with fuel `n`. -/
def StripV (k : Nat) (W : World) (τ : Ty) (n : Nat) (v : Value) : Prop :=
  v ∈ (Ty.strip n τ).1.map Nothing.value ∨
    ∃ t, (Ty.strip n τ).2 = some t ∧ t.rank = 0 ∧ V k W t v

theorem V_maybe_def : V k W (.maybe z τ) v ↔ v = z.value ∨ ∃ n, StripV k W τ n v := by
  rw [V.eq_def]
  simp only [StripV]
  refine or_congr Iff.rfl (exists_congr fun n => or_congr Iff.rfl ?_)
  cases (Ty.strip n τ).2 <;> simp

@[simp] theorem Ty.strip_zero (τ : Ty) : Ty.strip 0 τ = ([], none) := rfl

theorem Ty.strip_succ_maybe {τ σ : Ty} {z : Nothing} (h : τ.whnf = .maybe z σ) (n : Nat) :
    Ty.strip (n + 1) τ = (z :: (Ty.strip n σ).1, (Ty.strip n σ).2) := by
  rw [Ty.strip, h]

theorem Ty.strip_succ_other {τ : Ty} (h : ∀ z σ, τ.whnf ≠ .maybe z σ) (n : Nat) :
    Ty.strip (n + 1) τ = ([], some τ.whnf) := by
  rw [Ty.strip]
  split
  · rename_i z σ e; exact absurd e (h z σ)
  · rfl

/-- A type has the values of its head. -/
theorem V_whnf : V k W τ v ↔ V k W τ.whnf v := by
  cases hv : τ.view with
  | none => simp [Ty.whnf, hv]
  | some t =>
    rw [Ty.whnf_of_view hv, V_view (τ := τ)]
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
    · simp [hv]
    · exact ⟨fun ⟨c', a', h, h'⟩ => by rw [hv] at h; cases h; exact h',
        fun h => ⟨c, args, hv, h⟩⟩

theorem Ty.rank_zero {t : Ty} (h : t.rank = 0) :
    (∃ a, t = .var a) ∨ ∃ c args, t = .app c args ∧ ∀ z, c ≠ .maybe z := by
  cases t with
  | var a => exact .inl ⟨a, rfl⟩
  | app c args =>
    refine .inr ⟨c, args, rfl, fun z e => ?_⟩
    subst e; simp [Ty.rank] at h
  | mu i sys => simp [Ty.rank] at h

/-- A sum `Nullable σ` or `Optional σ` has its value `z` and the values of
`σ`. -/
theorem V_maybe : V k W (.maybe z σ) v ↔ v = z.value ∨ V k W σ v := by
  rw [V_maybe_def]
  refine or_congr Iff.rfl ⟨fun ⟨n, h⟩ => ?_, fun h => ?_⟩
  · cases n with
    | zero => simp [StripV, Ty.strip_zero] at h
    | succ n =>
      rw [V_whnf]
      by_cases hm : ∃ z' σ', σ.whnf = .maybe z' σ'
      · obtain ⟨z', σ', hw⟩ := hm
        rw [hw, V_maybe_def]
        simp only [StripV, Ty.strip_succ_maybe hw, List.map_cons, List.mem_cons] at h
        rcases h with (h | h) | h
        · exact .inl h
        · exact .inr ⟨n, .inl h⟩
        · exact .inr ⟨n, .inr h⟩
      · simp only [StripV, Ty.strip_succ_other (fun z' σ' e => hm ⟨z', σ', e⟩),
          List.map_nil, List.not_mem_nil, false_or, Option.some.injEq] at h
        obtain ⟨t, rfl, -, ht⟩ := h
        exact ht
  · rw [V_whnf] at h
    by_cases hm : ∃ z' σ', σ.whnf = .maybe z' σ'
    · obtain ⟨z', σ', hw⟩ := hm
      rw [hw, V_maybe_def] at h
      rcases h with h | ⟨n, h⟩
      · exact ⟨1, .inl (by simp [Ty.strip_succ_maybe hw, h])⟩
      · refine ⟨n + 1, ?_⟩
        simp only [StripV, Ty.strip_succ_maybe hw, List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inl (.inr h)
        · exact .inr h
    · have hs := Ty.strip_succ_other (fun z' σ' e => hm ⟨z', σ', e⟩) 0
      refine ⟨1, .inr ⟨σ.whnf, by rw [hs], ?_, h⟩⟩
      cases hw : σ.whnf with
      | var a => simp [Ty.rank]
      | mu i sys =>
        exfalso
        have hv0 : (Ty.mu i sys).view = none := by
          rw [← hw, Ty.view_whnf]
          cases h' : σ.view with
          | none => rfl
          | some t =>
            rcases Ty.view_shape h' with ⟨a, rfl⟩ | ⟨c, a, rfl⟩ <;>
              simp [Ty.whnf_of_view h'] at hw
        rw [hw, V_mu] at h
        obtain ⟨_, _, h', -⟩ := h
        rw [hv0] at h'; cases h'
      | app c args =>
        cases c with
        | maybe z' =>
          rw [hw] at h
          match args, h, hw with
          | [σ'], _, hw => exact absurd ⟨z', σ', hw⟩ hm
          | [], h, _ => rw [V.eq_def] at h; simp at h
          | _ :: _ :: _, h, _ => rw [V.eq_def] at h; simp at h
        | _ => simp [Ty.rank]

/-- A sum's layers, with fuel, in a larger world and for fewer calls. -/
theorem StripV.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {τ : Ty} {n : Nat}
    {v : Value} (h : StripV k W τ n v) : StripV j W' τ n v := by
  rcases h with h | ⟨t, ht, hr, hv⟩
  · exact .inl h
  · refine .inr ⟨t, ht, hr, ?_⟩
    rcases Ty.rank_zero hr with ⟨a, rfl⟩ | ⟨c, args, rfl, hc⟩
    · simp at hv
    · exact V.mono_app_base hjk hW hc hv

/-- `V.mono` for a constructor application. -/
theorem V.mono_app {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {c : Con}
    {args : List Ty} {v : Value} (hv : V k W (.app c args) v) : V j W' (.app c args) v := by
  by_cases hm : ∃ z σ, Ty.app c args = .maybe z σ
  · obtain ⟨z, σ, e⟩ := hm
    rw [e, V_maybe_def] at hv ⊢
    exact hv.imp id (fun ⟨n, h⟩ => ⟨n, h.mono hjk hW⟩)
  · refine V.mono_app_base hjk hW (fun z e => ?_) hv
    subst e
    match args with
    | [σ] => exact hm ⟨z, σ, rfl⟩
    | [] => rw [V.eq_def] at hv; simp at hv
    | _ :: _ :: _ => rw [V.eq_def] at hv; simp at hv

/-- A value good for `k` calls in `W` is good for fewer, in a larger world. -/
theorem V.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {τ : Ty} {v : Value}
    (hv : V k W τ v) : V j W' τ v := by
  obtain ⟨c, args, hτ, hv⟩ := V_view.mp hv
  exact V_view.mpr ⟨c, args, hτ, V.mono_app hjk hW hv⟩

theorem CellV.mono {j k : Nat} {W W' : World} (hjk : j ≤ k) (hW : W <+: W') {c : Cell}
    {v : Value} (h : CellV k W c v) : CellV j W' c v :=
  CellP.mono (fun _ _ h => V.mono hjk hW h) h

/-! ## Equal types have the same values -/

/-- A constructor other than a function's, a record's, an array's or a
sum's has the same values whatever its arguments, given as many. -/
theorem V.app_congr_base {k : Nat} {W : World} {c : Con} {args args' : List Ty} {v : Value}
    (hl : args.length = args'.length) (hfn : c ≠ .fn) (hrec : ∀ ls, c ≠ .record ls)
    (harr : c ≠ .array) (hmay : ∀ z, c ≠ .maybe z) :
    V k W (.app c args) v ↔ V k W (.app c args') v := by
  cases c
  case fn => exact absurd rfl hfn
  case record ls => exact absurd rfl (hrec ls)
  case array => exact absurd rfl harr
  case maybe z => exact absurd rfl (hmay z)
  all_goals
    rw [V.eq_def, V.eq_def]
    try (cases args <;> cases args' <;> simp_all)

/-- One value of each type, for types pairwise equal and with values
invariant under equality. -/
theorem VList.tyEq {k : Nat} {W : World}
    (h : ∀ {τ τ' : Ty} {v : Value}, TyEq τ τ' → V k W τ v → V k W τ' v) :
    ∀ {τs τs' : List Ty} {vs : List Value}, τs.length = τs'.length →
      (∀ x ∈ τs.zip τs', TyEq x.1 x.2) → VList k W τs vs → VList k W τs' vs
  | [], [], _, _, _, hv => hv
  | τ :: τs, τ' :: τs', v :: vs, hl, hz, hv => by
    rw [VList_cons] at hv ⊢
    exact ⟨h (hz (τ, τ') (by simp)) hv.1,
      VList.tyEq h (by simpa using hl) (fun x hx => hz x (by simp [hx])) hv.2⟩
  | [], _ :: _, _, hl, _, _ | _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hv => by simp at hv

theorem zip_tyEq_symm {xs ys : List Ty} (h : ∀ x ∈ xs.zip ys, TyEq x.1 x.2) :
    ∀ x ∈ ys.zip xs, TyEq x.1 x.2 := by
  intro x hx
  obtain ⟨a, b⟩ := x
  have : (b, a) ∈ xs.zip ys := by
    rw [List.mem_iff_getElem] at hx ⊢
    obtain ⟨i, hi, e⟩ := hx
    simp only [List.getElem_zip, Prod.mk.injEq, List.length_zip] at e hi ⊢
    exact ⟨i, by omega, e.2, e.1⟩
  exact (h _ this).symm

/-- `strip` respects equal types: the same layers, and equal heads. -/
theorem Ty.strip_tyEq : ∀ (n : Nat) {τ τ' : Ty}, TyEq τ τ' →
    (Ty.strip n τ).1 = (Ty.strip n τ').1 ∧
    ∀ t, (Ty.strip n τ).2 = some t → ∃ ρ ρ', t = ρ.whnf ∧ (Ty.strip n τ').2 = some ρ'.whnf ∧
      TyEq ρ ρ'
  | 0, _, _, _ => by simp
  | n + 1, τ, τ', h => by
    by_cases hm : ∃ z σ, τ.whnf = .maybe z σ
    · obtain ⟨z, σ, hw⟩ := hm
      obtain ⟨ys, hw', he⟩ := TyEq.whnf_app h hw
      obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp he
      match ys, hl, hz, hw' with
      | [σ'], _, hz, hw' =>
        have hσ : TyEq σ σ' := hz (σ, σ') (by simp)
        obtain ⟨h1, h2⟩ := Ty.strip_tyEq n hσ
        rw [Ty.strip_succ_maybe hw, Ty.strip_succ_maybe hw']
        exact ⟨by simp [h1], h2⟩
      | [], hl, _, _ | _ :: _ :: _, hl, _, _ => simp at hl
    · have hm' : ∀ z σ', τ'.whnf ≠ .maybe z σ' := fun z σ' hw' => by
        obtain ⟨ys, hw, he⟩ := TyEq.whnf_app h.symm hw'
        obtain ⟨-, hl, -⟩ := TyEq.app_iff.mp he
        match ys, hl, hw with
        | [σ], _, hw => exact hm ⟨z, σ, hw⟩
        | [], hl, _ | _ :: _ :: _, hl, _ => simp at hl
      rw [Ty.strip_succ_other (fun z σ e => hm ⟨z, σ, e⟩), Ty.strip_succ_other hm']
      refine ⟨rfl, fun t ht => ⟨τ, τ', ?_, rfl, h⟩⟩
      simp only [Option.some.injEq] at ht
      exact ht.symm

/-- Equal types have the same values: a recursive type and its unfolding
in particular. -/
theorem V.tyEq : ∀ (k : Nat) {W : World} {τ τ' : Ty} {v : Value},
    TyEq τ τ' → V k W τ v → V k W τ' v := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  -- A constructor application other than a sum's, at this index.
  have happ : ∀ {W : World} {c : Con} {args args' : List Ty} {v : Value},
      (∀ z, c ≠ .maybe z) → TyEq (.app c args') (.app c args) → V k W (.app c args) v →
      V k W (.app c args') v := by
    intro W c args args' v hc h₂ hv
    obtain ⟨-, hl, hz⟩ := TyEq.app_iff.mp h₂
    -- `hz` relates `args'` to `args`.
    by_cases hfn : c = .fn
    · subst hfn
      match args, args', hl, hz, hv with
      | θ :: ρ :: τs, θ' :: ρ' :: τs', hl, hz, hv =>
        have hθ : TyEq θ' θ := hz (θ', θ) (by simp)
        have hρ : TyEq ρ ρ' := (hz (ρ', ρ) (by simp)).symm
        have hτs : ∀ x ∈ τs.zip τs', TyEq x.1 x.2 :=
          zip_tyEq_symm (fun x hx => hz x (by simp [hx]))
        have hl' : τs.length = τs'.length := by simp at hl; omega
        change V k W (.fn θ' τs' ρ') v
        change V k W (.fn θ τs ρ) v at hv
        rw [V_fn] at hv ⊢
        refine ⟨fun h' => hv.1 (hθ.symm.trans h'), ?_⟩
        intro j hj W' hW h thisv xs hxs hh hthis hargs
        have H := hv.2 j hj W' hW h thisv xs (by rw [hxs]; exact hl'.symm) hh
          (fun i hi => ihk i (by omega) hθ (hthis i hi))
          (fun i hi => VList.tyEq (fun e hv' => ihk i (by omega) e hv') hl'.symm
            (zip_tyEq_symm hτs) (hargs i hi))
        obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H
        · exact ⟨hc, .inl H⟩
        · refine ⟨hc, .inr ⟨hlt, W'', hW'', hH, ?_⟩⟩
          rcases hr with ⟨v', e, hv'⟩ | habr
          · exact .inl ⟨v', e, fun h' => ihk _ (by omega) hρ (hv' h')⟩
          · exact .inr habr
      | [], _, _, _, hv | [_], _, _, _, hv => rw [V.eq_def] at hv; simp at hv
      | _ :: _ :: _, [], hl, _, _ | _ :: _ :: _, [_], hl, _, _ => simp at hl
    · by_cases hrec : ∃ ls, c = .record ls
      · obtain ⟨ls, rfl⟩ := hrec
        change V k W (.record ls args') v
        change V k W (.record ls args) v at hv
        rw [V_record] at hv ⊢
        obtain ⟨ℓ, τc, rfl, hℓ, hτc⟩ := hv
        exact ⟨ℓ, τc, rfl, hℓ, h₂.trans hτc⟩
      · by_cases harr : c = .array
        · subst harr
          match args, args', hl, hz, hv with
          | [σ], [σ'], _, hz, hv =>
            change V k W (.array σ') v
            change V k W (.array σ) v at hv
            rw [V_array] at hv ⊢
            obtain ⟨ℓ, τc, rfl, hℓ, hτc⟩ := hv
            exact ⟨ℓ, τc, rfl, hℓ, (hz (σ', σ) (by simp)).trans hτc⟩
          | [], _, _, _, hv | _ :: _ :: _, _, _, _, hv => rw [V.eq_def] at hv; simp at hv
          | [_], [], hl, _, _ | [_], _ :: _ :: _, hl, _, _ => simp at hl
        · exact (V.app_congr_base hl.symm hfn (fun ls e => hrec ⟨ls, e⟩) harr hc).mp hv
  intro W τ τ' v he hv
  obtain ⟨c, args, hτ, hv⟩ := V_view.mp hv
  have h₁ : TyEq τ' (.app c args) := by
    have := TyEq.whnf τ
    simp only [Ty.whnf, hτ, Option.getD_some] at this
    exact he.symm.trans this.symm
  obtain ⟨args', hτ', h₂⟩ := TyEq.view_app h₁
  refine V_view.mpr ⟨c, args', hτ', ?_⟩
  by_cases hm : ∃ z, c = .maybe z
  · obtain ⟨z, rfl⟩ := hm
    match args, args', TyEq.app_iff.mp h₂, hv with
    | [σ], [σ'], ⟨_, _, hz⟩, hv =>
      have hσ : TyEq σ σ' := (hz (σ', σ) (by simp)).symm
      change V k W (.maybe z σ) v at hv
      change V k W (.maybe z σ') v
      rw [V_maybe_def] at hv ⊢
      refine hv.imp id (fun ⟨n, h⟩ => ⟨n, ?_⟩)
      obtain ⟨h1, h2⟩ := Ty.strip_tyEq n hσ
      rcases h with h | ⟨t, ht, hr, hvt⟩
      · exact .inl (h1 ▸ h)
      · obtain ⟨ρ, ρ', rfl, ht', hρ⟩ := h2 _ ht
        rcases Ty.rank_zero hr with ⟨a, ha⟩ | ⟨c', a', ha, hc'⟩
        · rw [ha] at hvt; simp at hvt
        · obtain ⟨ys, hw', he'⟩ := TyEq.whnf_app hρ ha
          refine .inr ⟨ρ'.whnf, ht', ?_, ?_⟩
          · rw [hw']
            cases c' with
            | maybe z' => exact absurd rfl (hc' z')
            | _ => simp [Ty.rank]
          · rw [hw']; rw [ha] at hvt
            exact happ hc' he'.symm hvt
    | [], _, _, hv | _ :: _ :: _, _, _, hv => rw [V.eq_def] at hv; simp at hv
    | [_], [], ⟨_, hl, _⟩, _ | [_], _ :: _ :: _, ⟨_, hl, _⟩, _ => simp at hl
  · exact happ (fun z e => hm ⟨z, e⟩) h₂ hv

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
  ⟨fun h => by simpa using h [] rfl (by simp [HoldsOrVarS, Scheme.instPreds, Scheme.mono]),
    fun h τs _ _ => by simpa using h⟩


/-- A type that unfolds to a type variable has no values. -/
theorem V_whnf_var {k : Nat} {W : World} {τ : Ty} {v : Value} {a : Nat} (h : τ.whnf = .var a)
    (hv : V k W τ v) : False := by
  have he : TyEq τ (.var a) := h ▸ (TyEq.whnf τ).symm
  have := V.tyEq k he hv
  simp at this

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

/-- A safe outcome at a type is safe at an equal type. -/
theorem Safe.tyEq {p : Ran} {k : Nat} {W : World} {τ τ' : Ty} {R : Option Ty}
    (h : Safe p k W τ R) (he : TyEq τ τ') : Safe p k W τ' R := by
  obtain ⟨hc, h | ⟨W', hW, hH, ⟨v, hv, hV⟩ | habr | hret⟩⟩ := h
  · exact ⟨hc, .inl h⟩
  · exact ⟨hc, .inr ⟨W', hW, hH, .inl ⟨v, hv, V.tyEq _ he hV⟩⟩⟩
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

theorem BinOp.eval_sound {W' : World} (hC : HoldsOrVarW C) (hop : BinOpTyS Sys.wide C op τ₁ τ₂ τ)
    (hv₁ : V c W' τ₁ v₁) (hv₂ : V c W' τ₂ v₂) (hc : c ≤ k) (hW : W <+: W')
    (hH : HeapOK c W' h) : Safe (op.eval v₁ v₂, c, h) k W τ R := by
  cases hop with
  | plus hp =>
    rcases hp.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩
    · cases hi
      case plusNumber =>
        have he := (PredEq.one hq).2
        have h₁ := V.tyEq _ he hv₁; have h₂ := V.tyEq _ he hv₂
        simp at h₁ h₂; obtain ⟨_, rfl⟩ := h₁; obtain ⟨_, rfl⟩ := h₂
        exact Safe.ok hc hW hH (V.tyEq _ he.symm (by simp))
      case plusString =>
        have he := (PredEq.one hq).2
        have h₁ := V.tyEq _ he hv₁; have h₂ := V.tyEq _ he hv₂
        simp at h₁ h₂; obtain ⟨_, rfl⟩ := h₁; obtain ⟨_, rfl⟩ := h₂
        exact Safe.ok hc hW hH (V.tyEq _ he.symm (by simp))
      all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
    · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hv₁).elim
  | minus =>
    simp at hv₁ hv₂; obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂
    exact Safe.ok hc hW hH (by simp)

/-- Running a syntactic value gives a value, and takes no clock and no
cell. -/
theorem IsValue.run_value (hv : e.IsValue) (ht : HasTypeS Sys.wide L C Γ R rm md e τ) (hG : G W Γ env)
    (hH : HeapOK k W h) : ∃ v, run k env h e = (.ok v, k, h) := by
  induction ht
  case lit => exact ⟨_, by simp [run]; rfl⟩
  case func => exact ⟨_, by simp [run]; rfl⟩
  case funcCheck => exact ⟨_, by simp [run]; rfl⟩
  case ctor => exact ⟨_, by simp [run]; rfl⟩
  case var hi _ _ =>
    obtain ⟨ℓ, hℓ, hs⟩ := G.lookup hG hi
    obtain ⟨v, hv, _⟩ := hH.2 ℓ _ hs
    exact ⟨v, by simp [run, hℓ, hv]⟩
  case conv ih => exact ih hv hG
  case inj ih => exact ih hv hG
  all_goals cases hv

/-! ## Objects -/

theorem lookup_map_snd {α β : Type} (g : α → β) (l : String) :
    ∀ xs : List (String × α), (xs.map (Prod.map id g)).lookup l = (xs.lookup l).map g
  | [] => rfl
  | (l', a) :: xs => by
    simp only [List.map_cons, Prod.map, id, List.lookup_cons]
    split <;> simp_all [lookup_map_snd g l xs]

theorem lookup_mem {α : Type} {l : String} {a : α} :
    ∀ {xs : List (String × α)}, xs.lookup l = some a → (l, a) ∈ xs
  | [], h => by cases h
  | (l', a') :: xs, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i e; cases h; simp only [beq_iff_eq] at e; subst e; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_eq_none {α : Type} {l : String} :
    ∀ {xs : List (String × α)}, (∀ x ∈ xs, x.1 ≠ l) → xs.lookup l = none
  | [], _ => rfl
  | (a, v) :: xs, h => by
    have ha : (l == a) = false :=
      beq_eq_false_iff_ne.mpr (fun e => h (a, v) List.mem_cons_self e.symm)
    simp only [List.lookup_cons, ha]
    exact lookup_eq_none (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem lookup_ne_none {α : Type} {l : String} :
    ∀ {xs : List (String × α)}, l ∈ xs.map (·.1) → xs.lookup l ≠ none
  | [], h => by simp at h
  | (a, v) :: xs, h => by
    cases e : l == a
    · have hne : l ≠ a := by simpa using e
      simp only [List.lookup_cons, e]
      simp only [List.map_cons, List.mem_cons] at h
      exact lookup_ne_none (h.resolve_left hne)
    · simp [List.lookup_cons, e]

theorem lookup_append {α : Type} {l : String} :
    ∀ (xs ys : List (String × α)), (xs ++ ys).lookup l = (xs.lookup l).or (ys.lookup l)
  | [], ys => by simp
  | (a, v) :: xs, ys => by
    cases e : l == a <;> simp [List.lookup_cons, e, lookup_append xs ys]

theorem lookup_reverse {α : Type} {l : String} :
    ∀ {xs : List (String × α)}, (xs.map (·.1)).Nodup → xs.reverse.lookup l = xs.lookup l
  | [], _ => rfl
  | (a, v) :: xs, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    rw [List.reverse_cons, lookup_append, lookup_reverse h.2]
    cases e : l == a
    · simp [List.lookup_cons, e]
    · have : l = a := by simpa using e
      subst this
      have hn : xs.lookup l = none :=
        lookup_eq_none (fun x hx hx' => h.1 (List.mem_map.mpr ⟨x, hx, hx'⟩))
      simp [hn]

theorem lookup_of_mem {α : Type} {l : String} {a : α} :
    ∀ {xs : List (String × α)}, (xs.map (·.1)).Nodup → (l, a) ∈ xs → xs.lookup l = some a
  | [], _, h => by cases h
  | (l', a') :: xs, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with e | h
    · cases e; simp
    · have hne : l ≠ l' := fun e => hn.1 (List.mem_map.mpr ⟨_, h, e⟩)
      have : (l == l') = false := by simpa using hne
      simp only [List.lookup_cons, this]
      exact lookup_of_mem hn.2 h

theorem Ty.field_eq_lookup (l : String) :
    ∀ (ls : List String) (fs : List Ty), Ty.field l ls fs = (ls.zip fs).lookup l
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, f :: fs => by
    simp only [Ty.field, List.zip_cons_cons, List.lookup_cons, Ty.field_eq_lookup l ls fs]
    by_cases e : l' = l
    · subst e; simp
    · have : (l == l') = false := by simpa using Ne.symm e
      simp [e, this]

theorem zip_reverse {α β : Type} {xs : List α} {ys : List β} (h : xs.length = ys.length) :
    (xs.zip ys).reverse = xs.reverse.zip ys.reverse := by
  simp only [List.zip_eq_zipWith]
  exact List.reverse_zipWith h

theorem field_map_eq {l : String} {f : String → Ty} {s : Ty} :
    ∀ {L : List String}, Ty.field l L (L.map f) = some s → s = f l
  | [], h => by simp [Ty.field] at h
  | l' :: L, h => by
    simp only [List.map_cons, Ty.field] at h
    split at h
    · rename_i e; cases h; subst e; rfl
    · exact field_map_eq h

theorem Ty.field_map_none {l : String} {f : String → Ty} :
    ∀ {L : List String}, Ty.field l L (L.map f) = none → l ∉ L
  | [], _ => by simp
  | l' :: L, h => by
    simp only [List.map_cons, Ty.field] at h
    split at h
    · cases h
    · rename_i hne
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => hne e.symm, Ty.field_map_none h⟩

theorem Ty.field_none_length {l : String} : ∀ {ls : List String} {fs fs' : List Ty},
    fs.length = fs'.length → Ty.field l ls fs = none → Ty.field l ls fs' = none
  | [], _, _, _, _ => rfl
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, hl, _ => by simp at hl
  | _ :: _, _ :: _, [], hl, _ => by simp at hl
  | l' :: ls, f :: fs, f' :: fs', hl, h => by
    simp only [Ty.field] at h ⊢
    split
    · simp_all
    · simp only [*, ite_false] at h
      exact Ty.field_none_length (by simpa using hl) h

/-- A slot of an object literal's or a class instance's type: its last
field's for the label, or absent. -/
theorem objSlots_field {l : String} {s : Ty} {L ls : List String} {ss : List Ty}
    (h : Ty.field l L (objSlots L ls ss) = some s) (hlen : ls.length = ss.length) :
    s = (((ls.zip ss).reverse).lookup l).getD .absSlot := by
  rw [field_map_eq h, Ty.field_eq_lookup, zip_reverse hlen]

theorem VList.mem_zip {k : Nat} {W : World} : ∀ {τs : List Ty} {vs : List Value} {τ : Ty}
    {v : Value}, VList k W τs vs → (τ, v) ∈ τs.zip vs → V k W τ v
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | τ' :: τs, v' :: vs, τ, v, hvs, h => by
    rw [VList_cons] at hvs
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hvs.1
    · exact VList.mem_zip hvs.2 h

theorem VList.of_mem_zip {k : Nat} {W : World} : ∀ {τs : List Ty} {vs : List Value},
    τs.length = vs.length → (∀ x ∈ τs.zip vs, V k W x.1 x.2) → VList k W τs vs
  | [], [], _, _ => by simp
  | τ :: τs, v :: vs, hl, h => by
    rw [VList_cons]
    exact ⟨h (τ, v) (by simp), VList.of_mem_zip (by simpa using hl)
      (fun x hx => h x (by simp [hx]))⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem zip_zip_mem {α β γ : Type} : ∀ {xs : List α} {ys : List β} {zs : List γ} {x : α} {y : β}
    {z : γ}, (x, y, z) ∈ xs.zip (ys.zip zs) → (x, y) ∈ xs.zip ys ∧ (y, z) ∈ ys.zip zs ∧
      (x, z) ∈ xs.zip zs
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp at h
  | a :: xs, b :: ys, c :: zs, x, y, z, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · simp
    · obtain ⟨h₁, h₂, h₃⟩ := zip_zip_mem h
      exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂, List.mem_cons_of_mem _ h₃⟩

theorem zip_member_eq : ∀ (ks : List FieldKind) (τs ss : List Ty) (vs : List Value),
    ks.length = τs.length → τs.length = ss.length → ss.length = vs.length →
    (ks.map FieldKind.member).zip vs = (ks.zip (τs.zip (ss.zip vs))).map
      (fun w => (w.1.member, w.2.2.2))
  | [], _, _, _, _, _, _ => by simp
  | k :: ks, τ :: τs, s :: ss, v :: vs, h₁, h₂, h₃ => by
    simp [zip_member_eq ks τs ss vs (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)]
  | _ :: _, [], _, _, h₁, _, _ | _ :: _, _ :: _, [], _, _, h₂, _
  | _ :: _, _ :: _, _ :: _, [], _, _, h₃ => by simp at *

theorem zip_slot_eq : ∀ (ks : List FieldKind) (τs ss : List Ty) (vs : List Value),
    ks.length = τs.length → τs.length = ss.length → ss.length = vs.length →
    ss = (ks.zip (τs.zip (ss.zip vs))).map (fun w => w.2.2.1)
  | [], τs, ss, _, h₁, h₂, _ => by
    have : ss.length = 0 := by simp at h₁; omega
    rw [List.eq_nil_of_length_eq_zero this]; rfl
  | k :: ks, τ :: τs, s :: ss, v :: vs, h₁, h₂, h₃ => by
    simp [← zip_slot_eq ks τs ss vs (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)]
  | _ :: _, [], _, _, h₁, _, _ | _ :: _, _ :: _, [], _, _, h₂, _
  | _ :: _, _ :: _, _ :: _, [], _, _, h₃ => by simp at *

theorem zip4_mem {α β γ δ : Type} : ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}
    {a : α} {b : β} {c : γ} {d : δ}, (a, b, c, d) ∈ as.zip (bs.zip (cs.zip ds)) →
      (a, b, c) ∈ as.zip (bs.zip cs) ∧ (b, d) ∈ bs.zip ds
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp at h
  | a' :: as, b' :: bs, c' :: cs, d' :: ds, a, b, c, d, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ | h
    · simp
    · obtain ⟨h₁, h₂⟩ := zip4_mem h
      exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩

/-- Functions of equal `this` types are equal. -/
theorem TyEq.fn_this {θ θ' : Ty} {τs : List Ty} {ρ : Ty} (h : TyEq θ θ') :
    TyEq (.fn θ τs ρ) (.fn θ' τs ρ) :=
  TyEq.app rfl (fun x hx => by
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact h
    · exact TyEq.refl _
    · obtain ⟨a, b⟩ := x
      have : a = b := by
        clear h
        induction τs with
        | nil => cases hx
        | cons t ts ih =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hx
          rcases hx with ⟨rfl, rfl⟩ | hx
          · rfl
          · exact ih hx
      subst this; exact TyEq.refl _)

/-- A property of a zip of four lists, without the second. -/
theorem zip_drop_snd {α β γ δ : Type} {P : α → β → γ → δ → Prop} :
    ∀ {ks : List α} {es : List β} {ts : List γ} {ss : List δ}, es.length = ks.length →
      (∀ x ∈ ks.zip (es.zip (ts.zip ss)), P x.1 x.2.1 x.2.2.1 x.2.2.2) →
      ∀ x ∈ ks.zip (ts.zip ss), ∃ e, P x.1 e x.2.1 x.2.2
  | [], _, _, _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, x, hx => by simp at hx
  | _ :: _, _ :: _, _ :: _, [], _, _, x, hx => by simp at hx
  | k :: ks, e :: es, t :: ts, s :: ss, hl, h, x, hx => by
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨e, h (k, e, t, s) (by simp)⟩
    · exact zip_drop_snd (by simpa using hl) (fun y hy => h y (by simp [hy])) x hx

theorem lookup_filter_ne {α : Type} {l l' : String} (e : l' ≠ l) :
    ∀ fs : List (String × α), (fs.filter (·.1 != l)).lookup l' = fs.lookup l'
  | [] => rfl
  | (a, v) :: fs => by
    by_cases ha : a = l
    · subst ha
      have : (l' == a) = false := by simpa using e
      simp [List.lookup_cons, this, lookup_filter_ne e fs]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, ha, not_false_eq_true,
        ite_true, List.lookup_cons]
      split <;> simp_all [lookup_filter_ne e fs]

/-- A lookup of the last occurrence of a label, in a merged list. -/
theorem mergeLabels_lookup {α : Type} (l : String) :
    ∀ xs : List (String × α), (mergeLabels xs).lookup l = xs.reverse.lookup l
  | [] => by simp [mergeLabels]
  | (l', a) :: xs => by
    have ih := mergeLabels_lookup l xs
    simp only [mergeLabels, List.reverse_cons, lookup_append, List.lookup_cons, List.lookup_nil]
    by_cases e : l = l'
    · subst e
      simp only [beq_self_eq_true, ih]
      cases xs.reverse.lookup l <;> rfl
    · have hne : (l == l') = false := by simpa using e
      simp only [hne, Option.or_none, lookup_filter_ne e, ih]

/-- A merged list's labels are among the list's. -/
theorem mergeLabels_keys {α : Type} {l : String} :
    ∀ {xs : List (String × α)}, l ∈ (mergeLabels xs).map (·.1) → l ∈ xs.map (·.1)
  | [], h => by simp [mergeLabels] at h
  | (l', a) :: xs, h => by
    simp only [mergeLabels, List.map_cons, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact .inl h
    · simp only [List.mem_map, List.mem_filter] at h
      obtain ⟨x, ⟨hx, -⟩, rfl⟩ := h
      exact .inr (mergeLabels_keys (List.mem_map_of_mem hx))

/-- A merged list has each label once. -/
theorem mergeLabels_nodup {α : Type} :
    ∀ xs : List (String × α), ((mergeLabels xs).map (·.1)).Nodup
  | [] => by simp [mergeLabels]
  | (l, a) :: xs => by
    simp only [mergeLabels, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at h
      obtain ⟨x, ⟨-, hx⟩, e⟩ := h
      exact hx e
    · exact ((mergeLabels_nodup xs).sublist (List.Sublist.map _ List.filter_sublist))

/-- An object literal's fields, looked up: the last of each label. -/
theorem mergeLabels_reverse_lookup {α : Type} (l : String) (xs : List (String × α)) :
    (mergeLabels xs).reverse.lookup l = xs.reverse.lookup l := by
  rw [lookup_reverse (mergeLabels_nodup xs), mergeLabels_lookup]

/-- An object literal's cell holds the contents of its record type: each
field the last of its label, as its kind says. -/
theorem objFields_sound {k : Nat} {W : World} {L ls : List String} {ks : List FieldKind}
    {τs ss : List Ty} {vs : List Value} (hks : ks.length = ls.length)
    (hτs : τs.length = ls.length) (hss : ss.length = ls.length) (hL : ∀ l ∈ ls, l ∈ L)
    (hvs : VList k W τs vs)
    (hfs : ∀ x ∈ ks.zip (τs.zip ss), ∃ e, FieldSlot (.record L (objSlots L ls ss)) x.1 e x.2.1 x.2.2) :
    CellV k W (.obj (.record L (objSlots L ls ss))) (objFields ls ks vs) := by
  have hvl := hvs.length
  -- One list of each field's kind, type, slot and value.
  let ws := ks.zip (τs.zip (ss.zip vs))
  have hws : ws.length = ls.length := by simp [ws, hks, hτs, hss, hvl]
  have hw1 : (ks.map FieldKind.member).zip vs = ws.map (fun w => (w.1.member, w.2.2.2)) :=
    zip_member_eq ks τs ss vs (by omega) (by omega) (by omega)
  have hw2 : ss = ws.map (fun w => w.2.2.1) :=
    zip_slot_eq ks τs ss vs (by omega) (by omega) (by omega)
  have hcell : ls.zip ((ks.map FieldKind.member).zip vs) =
      (ls.zip ws).map (Prod.map id (fun w => (w.1.member, w.2.2.2))) := by
    rw [hw1, List.zip_map_right]
  have hslots : ls.zip ss = (ls.zip ws).map (Prod.map id (fun w => w.2.2.1)) := by
    conv => lhs; rw [hw2]
    rw [List.zip_map_right]
  rw [CellV_obj]
  refine ⟨_, rfl, fun l s hl => ?_, fun l hl => ?_⟩
  rotate_left
  · have hlL := Ty.field_map_none hl
    rw [mergeLabels_reverse_lookup]
    refine lookup_eq_none (fun x hx e => hlL (hL _ ?_))
    rw [← e]; exact (List.of_mem_zip (List.mem_reverse.mp hx)).1
  have hs := objSlots_field hl (by rw [hss])
  rw [hslots, ← List.map_reverse,
    lookup_map_snd (fun w : FieldKind × Ty × Ty × Value => w.2.2.1)] at hs
  have hrt : ((mergeLabels (ls.zip ((ks.map FieldKind.member).zip vs))).reverse).lookup l =
      (((ls.zip ws).reverse).lookup l).map (fun w => (w.1.member, w.2.2.2)) := by
    rw [mergeLabels_reverse_lookup, hcell, ← List.map_reverse,
      lookup_map_snd (fun w : FieldKind × Ty × Ty × Value => (w.1.member, w.2.2.2))]
  cases hw : ((ls.zip ws).reverse).lookup l with
  | none =>
    rw [hw] at hs hrt; simp only [Option.map_none, Option.getD_none] at hs
    subst hs
    exact .inr (.inr (.inr ⟨_, _, TyEq.refl _, hrt⟩))
  | some w =>
    rw [hw] at hs hrt; simp only [Option.map_some, Option.getD_some] at hs hrt
    subst hs
    obtain ⟨kf, τ, sl, v⟩ := w
    have hmem : (kf, τ, sl, v) ∈ ws := (List.of_mem_zip (List.mem_reverse.mp (lookup_mem hw))).2
    obtain ⟨hm₁, hm₂⟩ := zip4_mem hmem
    have hv := hvs.mem_zip hm₂
    obtain ⟨e, hfsl⟩ := hfs _ hm₁
    simp only at hfsl
    cases hfsl with
    | data => exact .inl ⟨τ, TyEq.refl _, v, hrt, hv⟩
    | method he => exact .inl ⟨_, TyEq.refl _, v, hrt, hv⟩
    | getter he =>
      exact .inr (.inl ⟨_, TyEq.refl _, v, hrt, V.tyEq _ (TyEq.fn_this he) hv⟩)

/-- The cell of an object of a record type: its world gives it a record
type over the same labels with pairwise equal slots. -/
theorem obj_cell {k : Nat} {W : World} {h : Heap} {ls : List String} {fs : List Ty} {v : Value}
    (hv : V k W (.record ls fs) v) (hH : HeapOK k W h) :
    ∃ ℓ fs' cv, v = .obj ℓ ∧ W[ℓ]? = some (.obj (.record ls fs')) ∧ h[ℓ]? = some cv ∧
      CellV k W (.obj (.record ls fs')) cv ∧ fs.length = fs'.length ∧
      ∀ x ∈ fs.zip fs', TyEq x.1 x.2 := by
  rw [V_record] at hv
  obtain ⟨ℓ, τc, rfl, hℓ, hτc⟩ := hv
  obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
  cases τc with
  | var a => simp [CellP] at hsv
  | mu i sys => simp [CellP] at hsv
  | app c args =>
    obtain ⟨rfl, hl, hz⟩ := TyEq.app_iff.mp hτc
    exact ⟨ℓ, args, cv, rfl, hℓ, hcv, hsv, hl, hz⟩

/-- Functions of equal result types are equal. -/
theorem TyEq.fn_ret {θ : Ty} {τs : List Ty} {ρ ρ' : Ty} (h : TyEq ρ ρ') :
    TyEq (.fn θ τs ρ) (.fn θ τs ρ') :=
  TyEq.app rfl (fun x hx => by
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact TyEq.refl _
    · exact h
    · obtain ⟨a, b⟩ := x
      have : a = b := by
        clear h
        induction τs with
        | nil => cases hx
        | cons t ts ih =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hx
          rcases hx with ⟨rfl, rfl⟩ | hx
          · rfl
          · exact ih hx
      subst this; exact TyEq.refl _)

/-- An object, as a value of its cell's type. -/
theorem V_obj_cell {k : Nat} {W : World} {ℓ : Nat} {ls : List String} {fs : List Ty}
    (hℓ : W[ℓ]? = some (.obj (.record ls fs))) : V k W (.record ls fs) (.obj ℓ) :=
  V_record.mpr ⟨ℓ, _, rfl, hℓ, TyEq.refl _⟩

/-- Calling a getter of an object, a function from the object's type, is
safe. -/
theorem getter_call_sound {k : Nat} {W : World} {h : Heap} {T σ : Ty} {g vo : Value}
    {R : Option Ty} (hg : V k W (.fn T [] σ) g) (hvo : V k W T vo) (hH : HeapOK k W h) :
    Safe (call k h g vo []) k W σ R :=
  Lands.safe ((V_fn.mp hg).2 _ (Nat.le_refl k) W (List.prefix_refl W) h vo [] rfl
    (fun _ hi => hH.mono (by omega)) (fun _ hi => hvo.mono (by omega) (List.prefix_refl W))
    (fun _ _ => by simp))

/-- Reading a field that is present, of any kind, from an object of a
record type: a getter called gives a value of its type. -/
theorem readSlot_sound {l : String} {ls : List String} {fs : List Ty} {s k σ : Ty} {v : Value}
    {c : Nat} {W : World} {h : Heap} {R : Option Ty}
    (hf : Ty.field l ls fs = some s) (hs : TyEq s (.slot .pre k σ))
    (hv : V c W (.record ls fs) v) (hH : HeapOK c W h) :
    Safe (getter c h v (v.read h l)) c W σ R := by
  obtain ⟨ℓ, fs', cv, rfl, hℓ, hcv, hsv, hl, hz⟩ := obj_cell hv hH
  obtain ⟨s', hs', hss'⟩ := Ty.field_tyEq hl hz hf
  obtain ⟨fsv, rfl, hfs, -⟩ := CellV_obj.mp hsv
  have hself := V_obj_cell (k := c) hℓ
  have hss := hs.symm.trans hss'
  rcases hfs l s' hs' with ⟨σ'', h₁, v', h₂, h₃⟩ | ⟨σ'', h₁, g, h₂, h₃⟩ |
      ⟨σ'', h₁, ⟨v', h₂, h₃⟩ | ⟨g, h₂, h₃⟩⟩ | ⟨k', σ'', h₁, -⟩
  · have hσσ := (TyEq.slot (hss.trans h₁)).2.2
    simp only [Value.read, hcv, readMember, h₂, Option.getD_some, getter]
    exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (V.tyEq _ hσσ.symm h₃)
  · have hσσ := (TyEq.slot (hss.trans h₁)).2.2
    simp only [Value.read, hcv, readMember, h₂, Option.getD_some, getter]
    exact getter_call_sound (V.tyEq _ (TyEq.fn_ret hσσ.symm) h₃) hself hH
  · have hσσ := (TyEq.slot (hss.trans h₁)).2.2
    simp only [Value.read, hcv, readMember, h₂, Option.getD_some, getter]
    exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (V.tyEq _ hσσ.symm h₃)
  · have hσσ := (TyEq.slot (hss.trans h₁)).2.2
    simp only [Value.read, hcv, readMember, h₂, Option.getD_some, getter]
    exact getter_call_sound (V.tyEq _ (TyEq.fn_ret hσσ.symm) h₃) hself hH
  · exact absurd (TyEq.slot (hss.trans h₁)).1 TyEq.pre_abs

/-- Reading a property: an instance of `HasProp` says the object's contents
have it, a getter called gives a value of its type, and a type variable has
no values. -/
theorem read_sound {C : List Pred} {l : String} {τ κ σ : Ty} {v : Value} {c : Nat}
    {W : World} {h : Heap} {R : Option Ty}
    (hp : EntailsS Sys.wide C ⟨.hasProp l, [τ, κ, σ]⟩) (hC : HoldsOrVarW C) (hv : V c W τ v)
    (hH : HeapOK c W h) : Safe (getter c h v (v.read h l)) c W σ R := by
  rcases hp.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩
  · cases hi
    case hasProp l' ls fs k σ' hf =>
      obtain ⟨hcls, hτ, -, hσ⟩ := PredEq.three hq
      cases hcls
      exact (readSlot_sound hf (TyEq.refl _) (V.tyEq _ hτ hv) hH).tyEq hσ.symm
    case lengthArray τq =>
      obtain ⟨hcls, hτ, -, hσ⟩ := PredEq.three hq
      cases hcls
      have hv' := V.tyEq _ hτ hv
      rw [V_array] at hv'
      obtain ⟨ℓ, τc, rfl, hℓ, -⟩ := hv'
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, -⟩ := CellV_arr.mp hsv
      simp only [Value.read, hcv, ite_true, getter]
      exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (V.tyEq _ hσ.symm (by simp))
    case lengthString =>
      obtain ⟨hcls, hτ, -, hσ⟩ := PredEq.three hq
      cases hcls
      obtain ⟨s, rfl⟩ := V_string.mp (V.tyEq _ hτ hv)
      simp only [Value.read, ite_true, getter]
      exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (V.tyEq _ hσ.symm (by simp))
    all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
  · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hv).elim

/-- A record and an array type are never equal. -/
theorem TyEq.record_array {ls : List String} {fs : List Ty} {σ : Ty} :
    ¬ TyEq (.record ls fs) (.array σ) := fun h => by cases TyEq.con h

theorem lookup_replaceField_ne {l l' : String} (e : l' ≠ l) (v : Value) :
    ∀ fs : List (String × MemberKind × Value), (replaceField fs l v).lookup l' = fs.lookup l'
  | [] => rfl
  | (a, w) :: fs => by
    have ih := lookup_replaceField_ne e v fs
    simp only [replaceField] at ih ⊢
    by_cases ha : a = l
    · subst ha
      have h₁ : (l' == a) = false := by simpa using e
      simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.lookup_cons, h₁]
      exact ih
    · have h₁ : (a == l) = false := by simpa using ha
      simp only [List.map_cons, h₁, Bool.false_eq_true, ↓reduceIte, List.lookup_cons]
      split <;> simp_all

theorem lookup_replaceField_self {l : String} {v : Value} :
    ∀ {fs : List (String × MemberKind × Value)}, (fs.lookup l).isSome →
      (replaceField fs l v).lookup l = some (.data, v)
  | [], h => by simp at h
  | (a, w) :: fs, h => by
    simp only [replaceField, List.map_cons]
    by_cases ha : a = l
    · subst ha; simp
    · have h₁ : (a == l) = false := by simpa using ha
      have h₂ : (l == a) = false := by simpa using Ne.symm ha
      simp only [h₁, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, h₂] at h ⊢
      exact lookup_replaceField_self h

/-- Writing a field that holds a value: the object's contents keep their
type. -/
theorem setProp_sound {C : List Pred} {l : String} {τ σ : Ty} {vo vv : Value} {c : Nat}
    {W : World} {h : Heap} {R : Option Ty}
    (hp : EntailsS Sys.wide C ⟨.hasProp l, [τ, .data, σ]⟩)
    (hC : HoldsOrVarW C) (hvo : V c W τ vo) (hvv : V c W σ vv) (hH : HeapOK c W h) :
    Safe ((vo.setProp h l vv).1, c, (vo.setProp h l vv).2) c W σ R := by
  -- The receiver is a record whose field holds a value of the stored type.
  obtain ⟨ls, fs, sw, σw, hτr, hfw, hsw, hσw⟩ : ∃ ls fs sw σw, TyEq τ (.record ls fs) ∧
      Ty.field l ls fs = some sw ∧ TyEq sw (.slot .pre .data σw) ∧ TyEq σ σw := by
    rcases hp.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩
    · cases hi
      case hasProp l' ls fs k σ' hf =>
        obtain ⟨hcls, hτ', hk, hσ⟩ := PredEq.three hq
        cases hcls
        exact ⟨ls, fs, _, σ', hτ', hf, TyEq.slot_mk (TyEq.refl _) hk.symm (TyEq.refl _), hσ⟩
      case lengthArray => exact absurd (PredEq.three hq).2.2.1 (TyEq.con_ne (by decide))
      case lengthString => exact absurd (PredEq.three hq).2.2.1 (TyEq.con_ne (by decide))
      all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
    · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hvo).elim
  obtain ⟨ℓ, fs', cv, rfl, hℓ, hcv, hsv, hl, hz⟩ := obj_cell (V.tyEq _ hτr hvo) hH
  obtain ⟨s', hs', hss₀⟩ := Ty.field_tyEq hl hz hfw
  have hss' := hsw.symm.trans hss₀
  obtain ⟨fsv, rfl, hfs, hfn⟩ := CellV_obj.mp hsv
  -- The object holds the field as a value.
  obtain ⟨σ'', h₁, v', h₂, -⟩ : ∃ σ'', TyEq s' (.slot .pre .data σ'') ∧ ∃ v',
      fsv.lookup l = some (.data, v') ∧ V c W σ'' v' := by
    rcases hfs l s' hs' with h | ⟨σ'', h₁, -⟩ | ⟨σ'', h₁, -⟩ | ⟨k', σ'', h₁, -⟩
    · exact h
    · exact absurd (TyEq.slot (hss'.trans h₁)).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot (hss'.trans h₁)).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot (hss'.trans h₁)).1 TyEq.pre_abs
  simp only [Value.setProp, hcv, h₂]
  refine Safe.ok (Nat.le_refl c) (List.prefix_refl W) (hH.set hℓ ?_) hvv
  rw [CellV_obj]
  refine ⟨_, rfl, fun l'' s'' hl'' => ?_, fun l'' hl'' => ?_⟩
  rotate_left
  · have e : l'' ≠ l := fun e => by rw [e, hs'] at hl''; cases hl''
    rw [lookup_replaceField_ne e]; exact hfn l'' hl''
  by_cases e : l'' = l
  · subst e
    rw [hs'] at hl''
    cases hl''
    refine .inl ⟨σ'', h₁, vv, lookup_replaceField_self (by simp [h₂]), ?_⟩
    exact V.tyEq _ (hσw.trans (TyEq.slot (hss'.trans h₁)).2.2) hvv
  · unfold MemberP; rw [lookup_replaceField_ne e]; exact hfs l'' s'' hl''

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
    {h : Heap} {R : Option Ty} (hp : EntailsS Sys.wide C ⟨.indexable, [τ, ι, σ]⟩) (hC : HoldsOrVarW C)
    (hvo : V c W τ vo) (hvi : V c W ι vi) (hH : HeapOK c W h) :
    Safe (getter c h vo (vo.index h vi)) c W σ R := by
  rcases hp.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩
  · cases hi
    case indexArray τq =>
      obtain ⟨-, hτ, hι, hσ⟩ := PredEq.three hq
      have hvo' := V.tyEq _ hτ hvo
      rw [V_array] at hvo'
      obtain ⟨ℓ, τc, rfl, hℓ, hτc⟩ := hvo'
      obtain ⟨n, rfl⟩ := V_number.mp (V.tyEq _ hι hvi)
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, hvs⟩ := CellV_arr.mp hsv
      simp only [Value.index, hcv]
      split
      · rename_i v hv
        simp only [getter]
        obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp hv
        exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH
          (V.tyEq _ (hσ.trans hτc).symm (hvs v (List.mem_of_getElem? hk)))
      · simp only [getter]; exact Safe.fault hH
    case indexString =>
      obtain ⟨-, hτ, hι, hσ⟩ := PredEq.three hq
      obtain ⟨s, rfl⟩ := V_string.mp (V.tyEq _ hτ hvo)
      obtain ⟨n, rfl⟩ := V_number.mp (V.tyEq _ hι hvi)
      simp only [Value.index]
      split
      · simp only [getter]
        exact Safe.ok (Nat.le_refl c) (List.prefix_refl W) hH (V.tyEq _ hσ.symm (by simp))
      · simp only [getter]; exact Safe.fault hH
    all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
  · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hvo).elim

/-- Storing an element: an array's cell keeps its type, and an index past
its end is a fault. -/
theorem setIndex_sound {C : List Pred} {τ ι σ : Ty} {vo vi vv : Value} {c : Nat} {W : World}
    {h : Heap} {R : Option Ty} (hp : EntailsS Sys.wide C ⟨.indexable, [τ, ι, σ]⟩)
    (hw : EntailsS Sys.wide C ⟨.indexWrite, [τ]⟩) (hC : HoldsOrVarW C) (hvo : V c W τ vo)
    (hvi : V c W ι vi) (hvv : V c W σ vv) (hH : HeapOK c W h) :
    Safe ((vo.setIndex h vi vv).1, c, (vo.setIndex h vi vv).2) c W σ R := by
  rcases hw.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩
  · cases hi
    case writeArray ε =>
      have hτε := (PredEq.one hq).2
      -- The element type is the array's.
      have hσ : TyEq σ ε ∧ TyEq ι .number := by
        rcases hp.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q', hq', hi'⟩ | ⟨_, a, _, he, hw⟩
        · cases hi'
          case indexArray τq =>
            obtain ⟨-, hτ, hι, hσ⟩ := PredEq.three hq'
            exact ⟨hσ.trans (TyEq.array_inj (hτ.symm.trans hτε)), hι⟩
          case indexString =>
            exact absurd ((PredEq.three hq').2.1.symm.trans hτε) (fun h => by cases TyEq.con h)
          all_goals (obtain ⟨hcls, -, -⟩ := hq'; cases hcls)
        · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hvo).elim
      obtain ⟨hσε, hι⟩ := hσ
      have hvo' := V.tyEq _ hτε hvo
      rw [V_array] at hvo'
      obtain ⟨ℓ, τc, rfl, hℓ, hτc⟩ := hvo'
      obtain ⟨n, rfl⟩ := V_number.mp (V.tyEq _ hι hvi)
      obtain ⟨cv, hcv, hsv⟩ := hH.2 ℓ _ hℓ
      obtain ⟨vs, rfl, hvs⟩ := CellV_arr.mp hsv
      have hvv' : V c W τc vv := V.tyEq _ (hσε.trans hτc) hvv
      simp only [Value.setIndex, hcv]
      split
      · rename_i k _
        split
        · refine Safe.ok (Nat.le_refl c) (List.prefix_refl W)
            (hH.set hℓ (CellV_arr.mpr ⟨_, rfl, fun w hw => ?_⟩)) hvv
          rcases List.mem_or_eq_of_mem_set hw with hw | rfl
          · exact hvs w hw
          · exact hvv'
        · split
          · refine Safe.ok (Nat.le_refl c) (List.prefix_refl W)
              (hH.set hℓ (CellV_arr.mpr ⟨_, rfl, fun w hw => ?_⟩)) hvv
            rcases List.mem_append.mp hw with hw | hw
            · exact hvs w hw
            · simp only [List.mem_singleton] at hw; subst hw; exact hvv'
          · exact Safe.fault hH
      · exact Safe.fault hH
    all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
  · simp only [List.cons.injEq] at he; exact (V_whnf_var (by rw [he.1]; exact hw) hvo).elim

/-! ### Spread -/

theorem lookup_dedup {α : Type} {l : String} :
    ∀ xs : List (String × α), (dedupLabels xs).lookup l = xs.lookup l
  | [] => rfl
  | (a, v) :: xs => by
    simp only [dedupLabels]
    cases e : l == a
    · have hne : l ≠ a := by simpa using e
      simp only [List.lookup_cons, e]
      rw [lookup_filter_ne hne, lookup_dedup xs]
    · simp [List.lookup_cons, e]

theorem dedup_nodup {α : Type} : ∀ xs : List (String × α), ((dedupLabels xs).map (·.1)).Nodup
  | [] => List.nodup_nil
  | (a, v) :: xs => by
    simp only [dedupLabels, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, List.Nodup.sublist ((List.filter_sublist ..).map _) (dedup_nodup xs)⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
    have := (List.mem_filter.mp hx).2
    simp [e] at this

/-- What a spread copies of an object's property `l`, of the slot `s` in
its type: a field that holds a value, or a getter, gives a field holding a
value of its type; a prototype member or an absent field, nothing. -/
def CopyP (k : Nat) (W : World) (cs : List (String × MemberKind × Value)) (l : String)
    (s : Ty) : Prop :=
  (∃ σ, (TyEq s (.slot .pre .data σ) ∨ TyEq s (.slot .pre .getter σ)) ∧
    ∃ v, cs.lookup l = some (.data, v) ∧ V k W σ v) ∨
  (((∃ σ, TyEq s (.slot .pre .proto σ)) ∨ ∃ k' σ, TyEq s (.slot .abs k' σ)) ∧ cs.lookup l = none)

theorem CopyP.tyEq {k : Nat} {W : World} {cs : List (String × MemberKind × Value)} {l : String}
    {s s' : Ty} (h : CopyP k W cs l s) (e : TyEq s s') : CopyP k W cs l s' := by
  rcases h with ⟨σ, h₁ | h₁, v, h₂, h₃⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, h₂⟩
  · exact .inl ⟨σ, .inl (e.symm.trans h₁), v, h₂, h₃⟩
  · exact .inl ⟨σ, .inr (e.symm.trans h₁), v, h₂, h₃⟩
  · exact .inr ⟨.inl ⟨σ, e.symm.trans h₁⟩, h₂⟩
  · exact .inr ⟨.inr ⟨k', σ, e.symm.trans h₁⟩, h₂⟩

theorem CopyP.mono {j k : Nat} {W W' : World} {cs : List (String × MemberKind × Value)}
    {l : String} {s : Ty} (hjk : j ≤ k) (hW : W <+: W') (h : CopyP k W cs l s) :
    CopyP j W' cs l s := by
  rcases h with ⟨σ, h₁, v, h₂, h₃⟩ | h
  · exact .inl ⟨σ, h₁, v, h₂, h₃.mono hjk hW⟩
  · exact .inr h

/-- A safe outcome of copying an object's properties: the copies, which
`Q` accepts, or an outcome other than a value that is safe. -/
def SafeFields (p : RanFields) (k : Nat) (W : World)
    (Q : Nat → World → List (String × MemberKind × Value) → Prop) : Prop :=
  p.2.1 ≤ k ∧ match p.1 with
    | .ok cs => ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧ Q p.2.1 W' cs
    | .error r => r = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧ r.Abrupt

theorem SafeFields.imp {p : RanFields} {k : Nat} {W : World}
    {Q Q' : Nat → World → List (String × MemberKind × Value) → Prop}
    (h : SafeFields p k W Q) (hQ : ∀ c W cs, Q c W cs → Q' c W cs) : SafeFields p k W Q' := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  cases r with
  | ok cs => obtain ⟨W', hW, hH, hq⟩ := h; exact ⟨hc, W', hW, hH, hQ _ _ _ hq⟩
  | error r => exact ⟨hc, h⟩

theorem SafeFields.weaken {p : RanFields} {c k : Nat} {W W' : World}
    {Q : Nat → World → List (String × MemberKind × Value) → Prop}
    (h : SafeFields p c W' Q) (hc : c ≤ k) (hW : W <+: W') : SafeFields p k W Q := by
  obtain ⟨r, c', hp⟩ := p
  obtain ⟨hc', h⟩ := h
  refine ⟨Nat.le_trans hc' hc, ?_⟩
  cases r with
  | ok cs => obtain ⟨W'', hW', hH, hq⟩ := h; exact ⟨W'', hW.trans hW', hH, hq⟩
  | error r =>
    rcases h with h | ⟨W'', hW', hH, ha⟩
    · exact .inl h
    · exact .inr ⟨W'', hW.trans hW', hH, ha⟩

theorem SafeFields.of_error {r : Result} {c k : Nat} {h : Heap} {W : World}
    {Q Q' : Nat → World → List (String × MemberKind × Value) → Prop}
    (hs : SafeFields (.error r, c, h) k W Q) : SafeFields (.error r, c, h) k W Q' := hs

/-- Continuing safe copies with a safe continuation is safe. -/
theorem Safe.bindFields {p : RanFields} {k : Nat} {W : World} {τ : Ty} {R : Option Ty}
    {Q : Nat → World → List (String × MemberKind × Value) → Prop}
    {K : List (String × MemberKind × Value) → Nat → Heap → Ran} (h : SafeFields p k W Q)
    (hK : ∀ cs W', p.1 = .ok cs → W <+: W' → HeapOK p.2.1 W' p.2.2 → Q p.2.1 W' cs →
      Safe (K cs p.2.1 p.2.2) p.2.1 W' τ R) :
    Safe (Inty.bindFields p K) k W τ R := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  cases r with
  | ok cs =>
    obtain ⟨W', hW, hH, hq⟩ := h
    exact (hK cs W' rfl hW hH hq).weaken hc hW
  | error r =>
    simp only [Inty.bindFields]
    rcases h with rfl | ⟨W', hW, hH, habr⟩
    · exact ⟨hc, .inl rfl⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl habr)⟩⟩

/-- What copying the properties `xs` of an object, of the record type
`record ls ss`, gives: for each label, nothing if `xs` has no own property
of it, and otherwise a field holding a value of the type of the object's
field, which holds a value or is a getter. -/
def CopiedP (ls : List String) (ss : List Ty) (xs : List (String × MemberKind × Value))
    (c : Nat) (W : World) (cs : List (String × MemberKind × Value)) : Prop :=
  (cs.map (·.1)).Nodup ∧ ∀ l,
    (cs.lookup l = none ∧ ∀ x ∈ xs, x.1 = l → x.2.1.isOwn = false) ∨
    ((∃ x ∈ xs, x.1 = l ∧ x.2.1.isOwn = true) ∧ ∃ s σ v, Ty.field l ls ss = some s ∧
      (TyEq s (.slot .pre .data σ) ∨ TyEq s (.slot .pre .getter σ)) ∧
      cs.lookup l = some (.data, v) ∧ V c W σ v)

/-- Copying an object's properties, each read from the heap as it is
reached: a getter is called with the object as `this`. -/
theorem copyOwn_sound {ℓ : Nat} {ls : List String} {ss : List Ty} :
    ∀ {c : Nat} {W : World} {h : Heap} (xs : List (String × MemberKind × Value)),
    W[ℓ]? = some (.obj (.record ls ss)) → (xs.map (·.1)).Nodup →
    (∀ x ∈ xs, x.2.1.isOwn = true → ∃ s σ, Ty.field x.1 ls ss = some s ∧
      (TyEq s (.slot .pre .data σ) ∨ TyEq s (.slot .pre .getter σ))) →
    HeapOK c W h → SafeFields (copyOwn c h (.obj ℓ) xs) c W (CopiedP ls ss xs)
  | c, W, h, [], _, _, _, hH => by
    simp only [copyOwn]
    exact ⟨Nat.le_refl c, W, List.prefix_refl W, hH, List.nodup_nil,
      fun l => .inl ⟨rfl, by simp⟩⟩
  | c, W, h, (l, m, w) :: xs, hℓ, hnd, hxs, hH => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hxs' : ∀ x ∈ xs, x.2.1.isOwn = true → ∃ s σ, Ty.field x.1 ls ss = some s ∧
        (TyEq s (.slot .pre .data σ) ∨ TyEq s (.slot .pre .getter σ)) :=
      fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    simp only [copyOwn]
    by_cases hm : m.isOwn = true
    · simp only [hm, ite_true]
      obtain ⟨s, σ, hf, hs⟩ := hxs _ List.mem_cons_self hm
      have hsafe : Safe (getter c h (.obj ℓ) ((Value.obj ℓ).read h l)) c W σ none := by
        rcases hs with hs | hs
        · exact readSlot_sound hf hs (V_obj_cell hℓ) hH
        · exact readSlot_sound hf hs (V_obj_cell hℓ) hH
      generalize getter c h (.obj ℓ) ((Value.obj ℓ).read h l) = q at hsafe ⊢
      obtain ⟨r, c₁, h₁⟩ := q
      obtain ⟨hc₁, hto | ⟨W₁, hW₁, hH₁, ⟨v, hr, hv⟩ | habr | ⟨v, -, τr, hR, -⟩⟩⟩ := hsafe
      · simp only at hto; subst hto
        exact ⟨hc₁, .inl rfl⟩
      · simp only at hr hc₁ hH₁ hv; subst hr
        simp only [Nat.min_eq_left hc₁]
        have ih := copyOwn_sound xs (prefix_getElem? hW₁ hℓ) hnd.2 hxs' hH₁
        generalize copyOwn c₁ h₁ (.obj ℓ) xs = q at ih ⊢
        obtain ⟨r', c', h'⟩ := q
        cases r' with
        | ok cs =>
          obtain ⟨hc', W', hW', hH', hcnd, hcs⟩ := ih
          simp only at hc' hH' hcnd hcs ⊢
          refine ⟨Nat.le_trans hc' hc₁, W', hW₁.trans hW', hH', ?_, fun l' => ?_⟩
          · simp only [List.map_cons, List.nodup_cons]
            refine ⟨fun hl => ?_, hcnd⟩
            rcases hcs l with ⟨hn, -⟩ | ⟨⟨x, hx, hxl, -⟩, -⟩
            · exact lookup_ne_none hl hn
            · exact hnd.1 (List.mem_map.mpr ⟨x, hx, hxl⟩)
          · by_cases e : l' = l
            · subst e
              refine .inr ⟨⟨_, List.mem_cons_self, rfl, hm⟩, s, σ, v, hf, hs, by simp, ?_⟩
              exact hv.mono hc' hW'
            · have hne : (l' == l) = false := by simpa using e
              rcases hcs l' with ⟨hn, hown⟩ | ⟨⟨x, hx, hxl, hxo⟩, hrest⟩
              · refine .inl ⟨by simp only [List.lookup_cons, hne]; exact hn, fun x hx hxl => ?_⟩
                rcases List.mem_cons.mp hx with rfl | hx
                · exact absurd hxl.symm e
                · exact hown x hx hxl
              · refine .inr ⟨⟨x, List.mem_cons_of_mem _ hx, hxl, hxo⟩, ?_⟩
                simp only [List.lookup_cons, hne]; exact hrest
        | error r' =>
          exact SafeFields.of_error (ih.weaken hc₁ hW₁)
      · cases r <;> simp only [Result.Abrupt] at habr <;>
          exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, trivial⟩⟩
      · cases hR
    · simp only [hm, Bool.false_eq_true, ite_false]
      refine (copyOwn_sound xs hℓ hnd.2 hxs' hH).imp fun c' W' cs ⟨hcnd, hcs⟩ => ⟨hcnd, fun l' => ?_⟩
      rcases hcs l' with ⟨hn, hown⟩ | ⟨⟨x, hx, hxl, hxo⟩, hrest⟩
      · refine .inl ⟨hn, fun x hx hxl => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa using hm
        · exact hown x hx hxl
      · exact .inr ⟨⟨x, List.mem_cons_of_mem _ hx, hxl, hxo⟩, hrest⟩

/-- What a spread copies of an operand of a record type: each field's
copy (`CopyP`), and nothing of a label the type hasn't. -/
def OwnP (L : List String) (ss : List Ty) (c : Nat) (W : World)
    (cs : List (String × MemberKind × Value)) : Prop :=
  (∀ l s, Ty.field l L ss = some s → CopyP c W cs l s) ∧
  ∀ l, Ty.field l L ss = none → cs.lookup l = none

theorem OwnP.mono {j k : Nat} {W W' : World} {L : List String} {ss : List Ty}
    {cs : List (String × MemberKind × Value)} (hjk : j ≤ k) (hW : W <+: W')
    (h : OwnP L ss k W cs) : OwnP L ss j W' cs :=
  ⟨fun l s hs => (h.1 l s hs).mono hjk hW, h.2⟩

/-- Copying the own properties of an object of a record type. -/
theorem own_sound {L : List String} {ss : List Ty} {v : Value} {c : Nat} {W : World} {h : Heap}
    (hv : V c W (.record L ss) v) (hH : HeapOK c W h) :
    SafeFields (own c h v) c W (OwnP L ss) := by
  obtain ⟨ℓ, ss', cv, rfl, hℓ, hcv, hsv, hl, hz⟩ := obj_cell hv hH
  obtain ⟨fsv, rfl, hfs, hnone⟩ := CellV_obj.mp hsv
  have hnd := dedup_nodup fsv
  have hnd' : (((dedupLabels fsv).reverse).map (·.1)).Nodup := by
    rw [List.map_reverse]; exact List.pairwise_reverse.mpr (hnd.imp fun h e => h e.symm)
  have hlk : ∀ l, ((dedupLabels fsv).reverse).lookup l = fsv.lookup l := fun l => by
    rw [lookup_reverse hnd, lookup_dedup]
  have hmem : ∀ x ∈ (dedupLabels fsv).reverse, fsv.lookup x.1 = some x.2 := fun x hx => by
    rw [← hlk]; exact lookup_of_mem hnd' hx
  have hxs : ∀ x ∈ (dedupLabels fsv).reverse, x.2.1.isOwn = true → ∃ s σ,
      Ty.field x.1 L ss' = some s ∧
        (TyEq s (.slot .pre .data σ) ∨ TyEq s (.slot .pre .getter σ)) := by
    intro ⟨l, m, w⟩ hx hm
    have hlx := hmem _ hx
    cases hf : Ty.field l L ss' with
    | none => rw [hnone l hf] at hlx; cases hlx
    | some s =>
      rcases hfs l s hf with ⟨σ, h₁, v, h₂, -⟩ | ⟨σ, h₁, v, h₂, -⟩ |
          ⟨σ, h₁, ⟨v, h₂, -⟩ | ⟨v, h₂, -⟩⟩ | ⟨k', σ, -, h₂⟩
      · exact ⟨s, σ, rfl, .inl h₁⟩
      · exact ⟨s, σ, rfl, .inr h₁⟩
      · rw [h₂] at hlx; cases hlx; cases hm
      · rw [h₂] at hlx; cases hlx; cases hm
      · rw [h₂] at hlx; cases hlx
  have hcp := copyOwn_sound (c := c) _ hℓ hnd' hxs hH
  simp only [own, hcv]
  generalize copyOwn c h (.obj ℓ) (dedupLabels fsv).reverse = q at hcp ⊢
  obtain ⟨r, c', h'⟩ := q
  cases r with
  | error r => exact SafeFields.of_error hcp
  | ok cs =>
    obtain ⟨hc', W', hW', hH', hcnd, hcs⟩ := hcp
    simp only at hc' hH' hcnd hcs ⊢
    refine ⟨hc', W', hW', hH', fun l s hs => ?_, fun l hn => ?_⟩
    · obtain ⟨s', hs', hss'⟩ := Ty.field_tyEq hl hz hs
      rcases hcs l with ⟨hn, hown⟩ | ⟨-, s'', σ, v, hs'', h₁, h₂, h₃⟩
      · have hn' : cs.reverse.lookup l = none := by rw [lookup_reverse hcnd]; exact hn
        rcases hfs l s' hs' with ⟨σ, h₁, v, h₂, -⟩ | ⟨σ, h₁, g, h₂, -⟩ |
            ⟨σ, h₁, -⟩ | ⟨k', σ, h₁, -⟩
        · rw [← hlk] at h₂
          exact absurd (hown _ (lookup_mem h₂) rfl) (by simp [MemberKind.isOwn])
        · rw [← hlk] at h₂
          exact absurd (hown _ (lookup_mem h₂) rfl) (by simp [MemberKind.isOwn])
        · exact .inr ⟨.inl ⟨σ, hss'.trans h₁⟩, hn'⟩
        · exact .inr ⟨.inr ⟨k', σ, hss'.trans h₁⟩, hn'⟩
      · rw [hs'] at hs''; cases hs''
        refine .inl ⟨σ, ?_, v, by rw [lookup_reverse hcnd]; exact h₂, h₃⟩
        rcases h₁ with h₁ | h₁
        · exact .inl (hss'.trans h₁)
        · exact .inr (hss'.trans h₁)
    · have hn' := Ty.field_none_length hl hn
      rw [lookup_reverse hcnd]
      rcases hcs l with ⟨hn, -⟩ | ⟨-, s'', -, -, hs'', -⟩
      · exact hn
      · rw [hn'] at hs''; cases hs''

/-- A slot of a spread's result, with the operand's slot and the slot it is
written over for the same label, and the `Merge` relating them. -/
theorem field_merge {l : String} {r : Ty} : ∀ {L : List String} {ps ks τs ss rs : List Ty},
    ps.length = L.length → ks.length = L.length → τs.length = L.length →
    ss.length = L.length → rs.length = L.length → Ty.field l L rs = some r →
    ∃ p k τ s, Ty.field l L (slots3 ps ks τs) = some (.slot p k τ) ∧
      Ty.field l L ss = some s ∧ (⟨.merge, [p, k, τ, s, r]⟩ : Pred) ∈ mergePreds ps ks τs ss rs
  | [], _, _, _, _, _, _, _, _, _, _, h => by simp [Ty.field] at h
  | l' :: L, p :: ps, k :: ks, τ :: τs, s :: ss, r' :: rs, h₁, h₂, h₃, h₄, h₅, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂ h₃ h₄ h₅
    simp only [slots3, Ty.field, mergePreds] at h ⊢
    by_cases e : l' = l
    · simp only [e, ite_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨p, k, τ, s, rfl, rfl, List.mem_cons_self⟩
    · simp only [e, ite_false] at h ⊢
      obtain ⟨p', k', τ', s', hp, hs, hm⟩ := field_merge h₁ h₂ h₃ h₄ h₅ h
      exact ⟨p', k', τ', s', hp, hs, List.mem_cons_of_mem _ hm⟩
  | _ :: _, [], _, _, _, _, h₁, _, _, _, _, _ | _ :: _, _ :: _, [], _, _, _, _, h₂, _, _, _, _
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h₃, _, _, _
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h₄, _, _
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h₅, _ => by simp at *

theorem Pred.MergeOnVar.cases {p k τ s r : Ty} (h : Pred.MergeOnVar ⟨.merge, [p, k, τ, s, r]⟩) :
    (p.whnf = .pre ∧ ∃ a, k.whnf = .var a) ∨
      (((p.whnf = .pre ∧ k.whnf = .proto) ∨ p.whnf = .abs) ∧ s.SlotOnVar) := h

theorem Ty.not_tyEq_app_of_whnf_var {t : Ty} {a : Nat} {c : Con} {xs : List Ty}
    (h : t.whnf = .var a) : ¬ TyEq t (.app c xs) := fun he => by
  have := TyEq.whnf_var he h
  simp [Ty.whnf, Ty.view] at this

/-- A copied slot is never one whose presence or kind is a type
variable. -/
theorem CopyP.not_slotOnVar {k : Nat} {W : World} {cs : List (String × MemberKind × Value)}
    {l : String} {s : Ty} (h : CopyP k W cs l s) (hs : s.SlotOnVar) : False := by
  rcases h with ⟨σ, h₁ | h₁, -⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩ <;>
    · have := hs.tyEq h₁
      simp [Ty.SlotOnVar, Ty.whnf, Ty.view] at this

/-- A slot the operand doesn't write over: what is copied of it
(`SlotCopy`) is what was copied of the object written over. -/
theorem copy_member {k : Nat} {W : World} {T : Ty} {cs : List (String × MemberKind × Value)}
    {l : String} {s sq rq r : Ty} (h : CopyP k W cs l s) (hs : TyEq s sq) (hc : SlotCopy sq rq)
    (hr : TyEq r rq) : MemberP (V k W) T cs l r := by
  have h' := h.tyEq hs
  cases hc with
  | data =>
    rcases h' with ⟨σ, h₁ | h₁, v, h₂, h₃⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩
    · exact .inl ⟨σ, hr.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _)
        (TyEq.slot h₁).2.2), v, h₂, h₃⟩
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot h₁).1 TyEq.pre_abs
  | getter =>
    rcases h' with ⟨σ, h₁ | h₁, v, h₂, h₃⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact .inl ⟨σ, hr.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _)
        (TyEq.slot h₁).2.2), v, h₂, h₃⟩
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot h₁).1 TyEq.pre_abs
  | proto =>
    rcases h' with ⟨σ, h₁ | h₁, -⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, h₂⟩
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact absurd (TyEq.slot h₁).2.1 (TyEq.con_ne (by decide))
    · exact .inr (.inr (.inr ⟨_, _, hr, h₂⟩))
    · exact absurd (TyEq.slot h₁).1 TyEq.pre_abs
  | abs =>
    rcases h' with ⟨σ, h₁ | h₁, -⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, h₂⟩
    · exact absurd (TyEq.slot h₁).1.symm TyEq.pre_abs
    · exact absurd (TyEq.slot h₁).1.symm TyEq.pre_abs
    · exact absurd (TyEq.slot h₁).1.symm TyEq.pre_abs
    · exact .inr (.inr (.inr ⟨_, _, hr, h₂⟩))

/-- A spread of two objects' copied properties: each `Merge` is an
instance, since an object's type has no slot of unknown presence or kind,
so the merged fields have the result's type. -/
theorem spread_contents_sound {C : List Pred} {L : List String} {ps ks τs ss rs : List Ty}
    {cs₁ cs₂ : List (String × MemberKind × Value)} {c : Nat} {W : World} (hC : HoldsOrVarW C)
    (hps : ps.length = L.length) (hks : ks.length = L.length) (hτs : τs.length = L.length)
    (hss : ss.length = L.length) (hrs : rs.length = L.length)
    (hm : ∀ p ∈ mergePreds ps ks τs ss rs, EntailsS Sys.wide C p)
    (h₁ : OwnP L ss c W cs₁) (h₂ : OwnP L (slots3 ps ks τs) c W cs₂) :
    CellV c W (.obj (.record L rs)) (.fields (cs₂ ++ cs₁)) := by
  rw [CellV_obj]
  refine ⟨_, rfl, fun l r hr => ?_, fun l hn => ?_⟩
  rotate_left
  · have hl3 : (slots3 ps ks τs).length = L.length := by
      rw [slots3_length ps ks τs (by omega) (by omega)]; exact hps
    rw [lookup_append, h₂.2 l (Ty.field_none_length (by omega) hn),
      h₁.2 l (Ty.field_none_length (by omega) hn)]
    rfl
  obtain ⟨p, k, τ, s, hp, hs, hpm⟩ := field_merge hps hks hτs hss hrs hr
  have hc₂ := h₂.1 l _ hp
  have hc₁ := h₁.1 l s hs
  rcases (hm _ hpm).holdsOrVarN hC (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨_, a, _, he, hw⟩ | hmv
  · cases hi
    case mergeData τq sq =>
      obtain ⟨-, hpre, hk, hτ, -, hr'⟩ := PredEq.five hq
      rcases hc₂ with ⟨σ, h₁ | h₁, v, h₂, h₃⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩
      · refine .inl ⟨σ, ?_, v, by rw [lookup_append, h₂]; rfl, h₃⟩
        exact hr'.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _)
          (hτ.symm.trans (TyEq.slot h₁).2.2))
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · exact absurd (hpre.symm.trans (TyEq.slot h₁).1) TyEq.pre_abs
    case mergeGetter τq sq =>
      obtain ⟨-, hpre, hk, hτ, -, hr'⟩ := PredEq.five hq
      rcases hc₂ with ⟨σ, h₁ | h₁, v, h₂, h₃⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · refine .inl ⟨σ, ?_, v, by rw [lookup_append, h₂]; rfl, h₃⟩
        exact hr'.trans (TyEq.slot_mk (TyEq.refl _) (TyEq.refl _)
          (hτ.symm.trans (TyEq.slot h₁).2.2))
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · exact absurd (hpre.symm.trans (TyEq.slot h₁).1) TyEq.pre_abs
    case mergeAbs sq rq kq τq hcp =>
      obtain ⟨-, habs, -, -, hs', hr'⟩ := PredEq.five hq
      rcases hc₂ with ⟨σ, h₁ | h₁, -⟩ | ⟨-, hn⟩
      · exact absurd ((TyEq.slot h₁).1.symm.trans habs) TyEq.pre_abs
      · exact absurd ((TyEq.slot h₁).1.symm.trans habs) TyEq.pre_abs
      · have := copy_member (T := .record L rs) hc₁ hs' hcp hr'
        unfold MemberP; rw [lookup_append, hn]; exact this
    case mergeProto sq rq τq hcp =>
      obtain ⟨-, hpre, hk, -, hs', hr'⟩ := PredEq.five hq
      rcases hc₂ with ⟨σ, h₁ | h₁, -⟩ | ⟨-, hn⟩
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · exact absurd (hk.symm.trans (TyEq.slot h₁).2.1) (TyEq.con_ne (by decide))
      · have := copy_member (T := .record L rs) hc₁ hs' hcp hr'
        unfold MemberP; rw [lookup_append, hn]; exact this
    all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
  · simp only [List.cons.injEq] at he
    rw [← he.1] at hw
    rcases hc₂ with ⟨σ, h₁ | h₁, -⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩ <;>
      exact absurd (TyEq.slot h₁).1 (Ty.not_tyEq_app_of_whnf_var hw)
  · rcases Pred.MergeOnVar.cases hmv with ⟨hpre, a, hka⟩ | ⟨-, hs⟩
    · rcases hc₂ with ⟨σ, h₁ | h₁, -⟩ | ⟨⟨σ, h₁⟩ | ⟨k', σ, h₁⟩, -⟩
      · exact absurd (TyEq.slot h₁).2.1 (Ty.not_tyEq_app_of_whnf_var hka)
      · exact absurd (TyEq.slot h₁).2.1 (Ty.not_tyEq_app_of_whnf_var hka)
      · exact absurd (TyEq.slot h₁).2.1 (Ty.not_tyEq_app_of_whnf_var hka)
      · have := TyEq.whnf_const (TyEq.slot h₁).1 hpre
        simp [Ty.whnf, Ty.view] at this
    · exact (hc₁.not_slotOnVar hs).elim

/-! ## Arguments -/

/-- A safe outcome of running arguments of the types `τs`: their values,
or an outcome other than a value that is safe. -/
def SafeArgs (p : RanArgs) (k : Nat) (W : World) (τs : List Ty) (R : Option Ty) : Prop :=
  p.2.1 ≤ k ∧ match p.1 with
    | .ok vs => ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧ VList p.2.1 W' τs vs
    | .error r => r = .timeout ∨ ∃ W', W <+: W' ∧ HeapOK p.2.1 W' p.2.2 ∧
        (r.Abrupt ∨ (∃ v, r = .returned v ∧ ∃ τr, R = some τr ∧ V p.2.1 W' τr v))

/-- Safe arguments outside any function (no `return` leaves them) are
safe inside one. -/
theorem SafeArgs.of_none {p : RanArgs} (h : SafeArgs p k W τs none) : SafeArgs p k W τs R := by
  obtain ⟨r, c, hp⟩ := p
  obtain ⟨hc, h⟩ := h
  refine ⟨hc, ?_⟩
  cases r with
  | ok vs => exact h
  | error r =>
    rcases h with h | ⟨W', hW, hH, habr | ⟨v, -, τr, hτr, -⟩⟩
    · exact .inl h
    · exact .inr ⟨W', hW, hH, .inl habr⟩
    · cases hτr

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
  ∀ {k C Γ R rm md W env h τ}, HasTypeS Sys.wide L C Γ R rm md e τ → HoldsOrVarW C → G W Γ env →
    HeapOK k W h → Safe (run k env h e) k W τ R

/-- Well-typed arguments, each safe by the fundamental lemma, run safely. -/
theorem runArgs_sound {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode}
    (hC : HoldsOrVarW C) :
    ∀ (args : List Expr) (τs : List Ty) {k : Nat} {W : World} {env : Env} {h : Heap},
      (∀ a ∈ args, RunSound L a) →
      args.length = τs.length → (∀ p ∈ args.zip τs, HasTypeS Sys.wide L C Γ R rm md p.1 p.2) → G W Γ env →
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

/-- A closure whose body is well typed is good for any number of calls, in
any world its environment is typed in, by induction on the number: a call
with `i + 1` to spare runs the body with `i`, where the closure itself
(the function's own name) need only be good for `i`. -/
theorem closure_sound {L : List String} {C : List Pred} {Γ : Ctx} {θ ρ : Ty} {τs : List Ty}
    {body : Expr} {env : Env} (ih : RunSound L body)
    {rm md : Mode}
    (hb : HasTypeS Sys.wide L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) rm md body ρ)
    (hC : HoldsOrVarW C) : ∀ j W, G W Γ env → V j W (.fn θ τs ρ) (.closure env τs.length body) := by
  intro j
  induction j with
  | zero =>
    intro W _
    rw [V_fn]
    refine ⟨fun _ => rfl, ?_⟩
    intro i hi W' _ h' thisv args hl _ _ _
    obtain rfl : i = 0 := by omega
    simp only [call, callClosure, hl, Nat.le_refl, ↓reduceIte]
    exact ⟨Nat.le_refl 0, .inl rfl⟩
  | succ j ihj =>
    intro W hGW
    rw [V_fn]
    refine ⟨fun _ => rfl, ?_⟩
    intro i hi W' hW' h' thisv args hl hh hthis hargs
    cases i with
    | zero =>
      simp only [call, callClosure, hl, Nat.le_refl, ↓reduceIte]
      exact ⟨Nat.le_refl 0, .inl rfl⟩
    | succ i =>
      simp only [call, callClosure, hl, Nat.le_refl, ↓reduceIte,
        List.take_of_length_le (Nat.le_of_eq hl)]
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

/-- A function expression's value, of its type. -/
theorem func_value {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {τ : Ty}
    {n : Nat} {b : Expr} {k : Nat} {W : World} {env : Env} {h : Heap}
    {rm md : Mode}
    (ih : RunSound L (.func n b)) (ht : HasTypeS Sys.wide L C Γ R rm md (.func n b) τ) (hC : HoldsOrVarW C)
    (hG : G W Γ env) (hH : HeapOK k W h) : V k W τ (.closure env n b) := by
  have hs := ih ht hC hG hH
  simp only [run] at hs
  obtain ⟨-, hs | ⟨W', hW', hH', ⟨v, hv, hV⟩ | habr | ⟨v, hv, -⟩⟩⟩ := hs
  · cases hs
  · simp only [Result.ok.injEq] at hv; subst hv
    obtain rfl := hW'.eq_of_length (by rw [← hH'.1, hH.1])
    exact hV
  · simp [Result.Abrupt] at habr
  · cases hv

/-- A closure bound to `self`: calling it calls the closure on `self`,
whatever it is called on. It isn't a constructor, so its `this` type isn't
`newTarget`. -/
theorem V_bound {k : Nat} {W : World} {θ θ' ρ : Ty} {τs : List Ty} {cenv : Env} {n : Nat}
    {b : Expr} {self : Value} (hf : V k W (.fn θ τs ρ) (.closure cenv n b))
    (hs : ∀ i, i ≤ k → V i W θ self) (hθ' : ¬ TyEq θ' .newTarget) :
    V k W (.fn θ' τs ρ) (.bound (.closure cenv n b) self) := by
  rw [V_fn] at hf ⊢
  refine ⟨fun h' => absurd h' hθ', ?_⟩
  intro j hj W' hW' h thisv args hl hh _ ha
  have e : call j h (.bound (.closure cenv n b) self) thisv args =
      call j h (.closure cenv n b) self args := by simp only [call]
  rw [e]
  exact hf.2 j hj W' hW' h self args hl hh
    (fun i hi => (hs i (by omega)).mono (Nat.le_refl i) hW') ha

/-- An entailed `InjectW τ T`, under constraints each an instance or on a
type variable: a value of `τ` is one of `T` (a type variable has none). -/
theorem EntailsS.inject {C : List Pred} {T τ : Ty} (hC : HoldsOrVarW C)
    (h : EntailsS Sys.wide C ⟨.injectW, [τ, T]⟩) {k : Nat} {W : World} {v : Value}
    (hv : V k W τ v) : V k W T v := by
  rcases h.instOrVar hC (by simp) with ⟨q, hq, hi⟩ | ⟨t, a, rest, ht, hw⟩
  · obtain ⟨c, args⟩ := q
    match args, hq.2.1 with
    | [τ', T'], _ =>
      obtain ⟨hc, hτ, hT⟩ := PredEq.two hq
      subst hc
      have hv' := V.tyEq k hτ hv
      cases hi with
      | narrow hi => cases hi
      | injectSelf => exact V.tyEq k hT.symm hv'
      | @injectNothing z σ =>
        refine V.tyEq k hT.symm (V_maybe.mpr (.inl ?_))
        cases z <;> simpa [Nothing.ty, Nothing.con, Nothing.value] using hv'
      | injectSome => exact V.tyEq k hT.symm (V_maybe.mpr (.inr hv'))
  · simp only [List.cons.injEq] at ht
    obtain ⟨rfl, -⟩ := ht
    exact (V_whnf_var hw hv).elim

/-- What a derivation's last rule makes safe at its type is safe at the
derivation's: an equal type, or an annotation's type the value is
injected into. -/
theorem Safe.lift {p : Ran} {k : Nat} {W : World} {τ₀ τ : Ty} {R : Option Ty} {C : List Pred}
    {md md₀ : Mode} (hC : HoldsOrVarW C) (hl : LiftS Sys.wide C md md₀ τ₀ τ) (h : Safe p k W τ₀ R) :
    Safe p k W τ R := by
  rcases hl with ⟨-, he, -⟩ | ⟨-, -, -, hi⟩
  · exact h.tyEq he
  · obtain ⟨hc, h | ⟨W', hW, hH, ⟨v, hv, hV⟩ | habr | hret⟩⟩ := h
    · exact ⟨hc, .inl h⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inl ⟨v, hv, EntailsS.inject hC hi hV⟩⟩⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inl habr)⟩⟩
    · exact ⟨hc, .inr ⟨W', hW, hH, .inr (.inr hret)⟩⟩

/-- An entailed `Strip τ σ`, under constraints each an instance or on a
type variable: a value of `τ` that isn't nothing is one of `σ`. -/
theorem EntailsS.strip {C : List Pred} {τ σ : Ty} (hC : HoldsOrVarW C)
    (h : EntailsS Sys.wide C ⟨.strip, [τ, σ]⟩) {k : Nat} {W : World} {v : Value} (hv : V k W τ v)
    (hn : v.isNothing = false) : V k W σ v := by
  rcases h.instOrVar hC (by simp) with ⟨q, hq, hi⟩ | ⟨t, a, rest, ht, hw⟩
  · obtain ⟨c, args⟩ := q
    match args, hq.2.1 with
    | [τ', σ'], _ =>
      obtain ⟨hc, hτ, hσ⟩ := PredEq.two hq
      subst hc
      have hv' := V.tyEq k hτ hv
      cases hi with
      | narrow hi =>
        cases hi with
        | @stripSome z _ =>
          rcases V_maybe.mp hv' with h | h
          · subst h; cases z <;> simp [Nothing.value, Value.isNothing] at hn
          · exact V.tyEq k hσ.symm h
        | stripSelf _ _ _ => exact V.tyEq k hσ.symm hv'
      | stripSelf => exact V.tyEq k hσ.symm hv'
  · simp only [List.cons.injEq] at ht
    obtain ⟨rfl, -⟩ := ht
    exact (V_whnf_var hw hv).elim

/-- An entailed `NotNew θ`, under constraints each an instance or on a type
variable: `θ` isn't `newTarget`. -/
theorem EntailsS.notNew {C : List Pred} {θ : Ty} (hC : HoldsOrVarW C)
    (h : EntailsS Sys.wide C ⟨.notNew, [θ]⟩) : ¬ TyEq θ .newTarget := by
  intro hθ
  rcases h.instOrVarN hC (by simp) (by simp) (by simp) with ⟨q, hq, hi⟩ | ⟨t, a, rest, ht, hv⟩
  · cases hi with
    | notNew hc => exact hc (TyEq.app_iff.mp ((PredEq.one hq).2.symm.trans hθ)).1
    | _ => cases hq.1
  · simp only [List.cons.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    simpa using TyEq.whnf_var hθ hv

/-- The types of a class's fields that hold values, in order. -/
def dataTys : List ClassKind → List Ty → List Ty
  | k :: ks, τ :: τs =>
    match k with
    | .data => τ :: dataTys ks τs
    | _ => dataTys ks τs
  | _, _ => []

theorem memberCtx_zero (Γ : Ctx) (ks : List ClassKind) (τs : List Ty) :
    memberCtx Γ ks τs 0 .data = Γ := by
  simp [memberCtx]

theorem memberCtx_data (Γ : Ctx) (ks : List ClassKind) (τ : Ty) (τs : List Ty) (i : Nat) :
    memberCtx Γ (.data :: ks) (τ :: τs) (i + 1) .data = memberCtx (.mono τ :: Γ) ks τs i .data := by
  simp [memberCtx]

theorem memberCtx_other (Γ : Ctx) {k : ClassKind} (hk : k ≠ .data) (ks : List ClassKind) (τ : Ty)
    (τs : List Ty) (i : Nat) :
    memberCtx Γ (k :: ks) (τ :: τs) (i + 1) .data = memberCtx Γ ks τs i .data := by
  cases k <;> simp_all [memberCtx]

/-- A class's field initialisers, each typed in its context, run safely:
each sees the fields before it, in new cells. -/
theorem runInits_sound {L : List String} {C : List Pred} {R : Option Ty} {rm md : Mode}
    (hC : HoldsOrVarW C) :
    ∀ (es : List Expr) (ks : List ClassKind) (τs : List Ty) {Γ : Ctx} {k : Nat} {W : World}
      {env : Env} {h : Heap},
      (∀ e ∈ es, RunSound L e) → es.length = ks.length → τs.length = ks.length →
      (∀ i e τ, es[i]? = some e → ks[i]? = some .data → τs[i]? = some τ →
        HasTypeS Sys.wide L C (memberCtx Γ ks τs i .data) R rm md e τ) →
      G W Γ env → HeapOK k W h → SafeArgs (runInits k env h es ks) k W (dataTys ks τs) R
  | [], [], [], Γ, k, W, env, h, _, _, _, _, _, hH => by
    simp only [runInits, dataTys, SafeArgs]
    exact ⟨Nat.le_refl k, W, List.prefix_refl W, hH, by simp⟩
  | [], _ :: _, _, _, _, _, _, _, _, hl, _, _, _, _
  | _ :: _, [], _, _, _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hl, _, _, _
  | [], [], _ :: _, _, _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | e :: es, kd :: ks, τ :: τs, Γ, k, W, env, h, ih, hl₁, hl₂, ht, hG, hH => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl₁ hl₂
    have ih' : ∀ e ∈ es, RunSound L e := fun e he => ih e (List.mem_cons_of_mem _ he)
    cases kd
    case data =>
      have he := ih e List.mem_cons_self (ht 0 e τ rfl rfl rfl) hC
        (by rw [memberCtx_zero]; exact hG) hH
      have hc₁ := run_clock_le k env h e
      simp only [runInits, dataTys]
      generalize hp : run k env h e = p at he hc₁
      obtain ⟨r, c₁, h₁⟩ := p
      obtain ⟨_, hr⟩ := he
      simp only at hc₁
      rcases hr with hr | ⟨W₁, hW₁, hH₁, ⟨v, hr, hv⟩ | habr | ⟨v, hr, hv⟩⟩
      · simp only at hr; subst hr
        exact ⟨hc₁, .inl rfl⟩
      · simp only at hr; subst hr
        have hW₂ : W₁ <+: W₁ ++ [.mono τ] := List.prefix_append _ _
        have hcell : HeapOK c₁ (W₁ ++ [.mono τ]) (h₁ ++ [v]) :=
          hH₁.alloc (by simp) (fun i s' v' hs' hv' => by
            match i, hs', hv' with
            | 0, hs', hv' =>
              simp at hs' hv'; subst hs' hv'; exact SchemeV.mono_iff.mpr (hv.mono (Nat.le_refl _) hW₂)
            | _ + 1, hs', _ => simp at hs')
        have hG₂ : G (W₁ ++ [.mono τ]) (.mono τ :: Γ) (h₁.length :: env) :=
          ⟨by rw [hH₁.1]; simp, G.mono (hW₁.trans hW₂) hG⟩
        have has := runInits_sound hC es ks τs ih' hl₁ hl₂
          (fun i e' τ' h₁ h₂ h₃ => by
            have := ht (i + 1) e' τ' (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
            rwa [memberCtx_data] at this) hG₂ hcell
        have hc₂ := runInits_clock_le c₁ (h₁.length :: env) (h₁ ++ [v]) es ks
        dsimp only
        rw [Nat.min_eq_left hc₁]
        generalize runInits c₁ (h₁.length :: env) (h₁ ++ [v]) es ks = q at has hc₂
        obtain ⟨r', c₂, h₂⟩ := q
        obtain ⟨_, hq⟩ := has
        simp only at hc₂
        cases r' with
        | ok vs =>
          obtain ⟨W₃, hW₃, hH₃, hvs⟩ := hq
          exact ⟨by simp only; omega, W₃, hW₁.trans (hW₂.trans hW₃), hH₃,
            (VList_cons).mpr ⟨V.mono hc₂ (hW₂.trans hW₃) hv, hvs⟩⟩
        | error r' =>
          rcases hq with hq | ⟨W₃, hW₃, hH₃, hq⟩
          · exact ⟨by simp only; omega, .inl hq⟩
          · exact ⟨by simp only; omega, .inr ⟨W₃, hW₁.trans (hW₂.trans hW₃), hH₃, hq⟩⟩
      · simp only at habr
        cases r <;> simp only [Result.Abrupt] at habr <;>
          exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inl trivial⟩⟩
      · simp only at hr; subst hr
        exact ⟨hc₁, .inr ⟨W₁, hW₁, hH₁, .inr ⟨v, rfl, hv⟩⟩⟩
    all_goals
      simp only [runInits, dataTys]
      exact runInits_sound hC es ks τs ih' hl₁ hl₂
        (fun i e' τ' h₁ h₂ h₃ => by
          have := ht (i + 1) e' τ' (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
          rwa [memberCtx_other _ (by decide)] at this) hG hH

theorem MemberP.congr {P : Ty → Value → Prop} {T : Ty} {fs fs' : List (String × MemberKind × Value)}
    {l : String} {s : Ty} (e : fs.lookup l = fs'.lookup l) (h : MemberP P T fs l s) :
    MemberP P T fs' l s := by
  unfold MemberP at h ⊢; rw [← e]; exact h

/-- A class's members: each holds what its slot says, the instance's
type being `T`. -/
theorem clsMembers_sound {c : Nat} {W : World} {env : Env} {self : Value} {T : Ty}
    {C : List Pred} (hself : ∀ i, i ≤ c → V i W T self) (hC : HoldsOrVarW C) :
    ∀ (ls : List String) (es : List Expr) (ks : List ClassKind) (τs ss : List Ty)
      (vs : List Value),
      es.length = ls.length → ks.length = ls.length → τs.length = ls.length →
      ss.length = ls.length →
      (∀ x ∈ ks.zip (es.zip (τs.zip ss)), MemberSlotS Sys.wide C T x.1 x.2.1 x.2.2.1 x.2.2.2) →
      (∀ (i : Nat) (kd : ClassKind) (n : Nat) (b : Expr) (τ : Ty), ks[i]? = some kd →
        es[i]? = some (Expr.func n b) → τs[i]? = some τ →
        kd ≠ .data → V c W τ (.closure env n b)) →
      VList c W (dataTys ks τs) vs →
      ∃ fs, clsMembers env self ls es ks vs = some fs ∧ fs.map (·.1) = ls ∧
        ∀ p ∈ fs.zip ss, MemberP (V c W) T [p.1] p.1.1 p.2
  | [], [], [], [], [], [], _, _, _, _, _, _, _ => ⟨[], by simp [clsMembers], rfl, by simp⟩
  | [], [], [], [], [], _ :: _, _, _, _, _, _, _, hvs => by simp [dataTys] at hvs
  | [], _ :: _, _, _, _, _, hl, _, _, _, _, _, _ | [], _, _ :: _, _, _, _, _, hl, _, _, _, _, _
  | [], _, _, _ :: _, _, _, _, _, hl, _, _, _, _ | [], _, _, _, _ :: _, _, _, _, _, hl, _, _, _ => by
    simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _, _, _, _, _ | _ :: _, _, [], _, _, _, _, hl, _, _, _, _, _
  | _ :: _, _, _, [], _, _, _, _, hl, _, _, _, _ | _ :: _, _, _, _, [], _, _, _, _, hl, _, _, _ => by
    simp at hl
  | l :: ls, e :: es, kd :: ks, τ :: τs, s :: ss, vs, h₁, h₂, h₃, h₄, hm, hf, hvs => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂ h₃ h₄
    have hm' : ∀ x ∈ ks.zip (es.zip (τs.zip ss)), MemberSlotS Sys.wide C T x.1 x.2.1 x.2.2.1 x.2.2.2 :=
      fun x hx => hm x (List.mem_cons_of_mem _ hx)
    have hf' : ∀ (i : Nat) (kd : ClassKind) (n : Nat) (b : Expr) (τ : Ty), ks[i]? = some kd →
        es[i]? = some (Expr.func n b) →
        τs[i]? = some τ → kd ≠ .data → V c W τ (.closure env n b) :=
      fun i kd n b τ a₁ a₂ a₃ a₄ => hf (i + 1) kd n b τ (by simpa using a₁) (by simpa using a₂)
        (by simpa using a₃) a₄
    have hms : MemberSlotS Sys.wide C T kd e τ s := hm _ List.mem_cons_self
    cases hms with
    | data =>
      cases vs with
      | nil => simp [dataTys] at hvs
      | cons v vs =>
        simp only [dataTys, VList_cons] at hvs
        obtain ⟨fs, hfs, hl, hp⟩ := clsMembers_sound hself hC ls es ks τs ss vs h₁ h₂ h₃ h₄ hm' hf'
          hvs.2
        refine ⟨(l, .data, v) :: fs, by simp [clsMembers, hfs], by simp [hl], fun p hp' => ?_⟩
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact .inl ⟨τ, TyEq.refl _, v, by simp, hvs.1⟩
        · exact hp p hp'
    | @arrow θ θ' n b τs' ρ hθ hn =>
      simp only [dataTys] at hvs
      obtain ⟨fs, hfs, hl, hp⟩ := clsMembers_sound hself hC ls es ks τs ss vs h₁ h₂ h₃ h₄ hm' hf' hvs
      refine ⟨(l, .data, .bound (.closure env n b) self) :: fs, by simp [clsMembers, hfs],
        by simp [hl], fun p hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hp'
      · have hclo := hf 0 .arrow n b _ rfl rfl rfl (by decide)
        refine .inl ⟨_, TyEq.refl _, .bound (.closure env n b) self, by simp,
          V_bound hclo (fun i hi => ?_) (EntailsS.notNew hC hn)⟩
        exact V.tyEq _ hθ.symm ((hself i hi).mono (Nat.le_refl i) (List.prefix_refl W))
      · exact hp p hp'
    | @method θ n b τs' ρ hθ =>
      simp only [dataTys] at hvs
      obtain ⟨fs, hfs, hl, hp⟩ := clsMembers_sound hself hC ls es ks τs ss vs h₁ h₂ h₃ h₄ hm' hf' hvs
      refine ⟨(l, .method, .closure env n b) :: fs, by simp [clsMembers, hfs], by simp [hl],
        fun p hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hp'
      · have hclo := hf 0 .method n b _ rfl rfl rfl (by decide)
        exact .inr (.inr (.inl ⟨_, TyEq.refl _, .inl ⟨_, by simp, hclo⟩⟩))
      · exact hp p hp'
    | @getter θ b σ hθ =>
      simp only [dataTys] at hvs
      obtain ⟨fs, hfs, hl, hp⟩ := clsMembers_sound hself hC ls es ks τs ss vs h₁ h₂ h₃ h₄ hm' hf' hvs
      refine ⟨(l, .protoGetter, .closure env 0 b) :: fs, by simp [clsMembers, hfs],
        by simp [hl], fun p hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hp'
      · have hclo := hf 0 .getter 0 b _ rfl rfl rfl (by decide)
        exact .inr (.inr (.inl ⟨_, TyEq.refl _, .inr ⟨_, by simp, V.tyEq _ (TyEq.fn_this hθ) hclo⟩⟩))
      · exact hp p hp'

theorem zip_fst_mem {α β : Type} {l : String} {s : β} :
    ∀ {fs : List (String × α)} {ls : List String} {ss : List β}, fs.map (·.1) = ls →
      (l, s) ∈ ls.zip ss → ∃ p, p.1 = l ∧ (p, s) ∈ fs.zip ss
  | [], [], _, _, h => by simp at h
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => by simp at hl
  | _ :: _, _ :: _, [], _, h => by simp at h
  | p :: fs, l' :: ls, s' :: ss, hl, h => by
    simp only [List.map_cons, List.cons.injEq] at hl
    rcases List.mem_cons.mp h with e | h
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨p, hl.1, List.mem_cons_self⟩
    · obtain ⟨q, hq, hm⟩ := zip_fst_mem hl.2 h
      exact ⟨q, hq, List.mem_cons_of_mem _ hm⟩

/-- A class instance's cell holds its members, as its type says. -/
theorem cls_cell {c : Nat} {W : World} {L ls : List String} {ss : List Ty}
    {fs : List (String × MemberKind × Value)} (hss : ss.length = ls.length) (hnd : ls.Nodup)
    (hL : ∀ l ∈ ls, l ∈ L) (hl : fs.map (·.1) = ls)
    (hp : ∀ p ∈ fs.zip ss, MemberP (V c W) (.record L (objSlots L ls ss)) [p.1] p.1.1 p.2) :
    CellV c W (.obj (.record L (objSlots L ls ss))) (.fields fs.reverse) := by
  have hnd' : (fs.map (·.1)).Nodup := by rw [hl]; exact hnd
  rw [CellV_obj]
  refine ⟨_, rfl, fun l s hs => ?_, fun l hn => ?_⟩
  · have hs' := objSlots_field hs (by rw [hss])
    cases hlk : ((ls.zip ss).reverse).lookup l with
    | none =>
      rw [hlk] at hs'; simp only [Option.getD_none] at hs'; subst hs'
      refine .inr (.inr (.inr ⟨_, _, TyEq.refl _, ?_⟩))
      rw [lookup_reverse hnd']
      refine lookup_eq_none (fun x hx e => ?_)
      have hxl : l ∈ ls := by rw [← hl, ← e]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxl
      have : ((ls.zip ss).reverse).lookup ls[i] ≠ none := by
        refine lookup_ne_none ?_
        simp only [List.map_reverse, List.mem_reverse]
        rw [List.map_fst_zip (by omega)]
        exact List.getElem_mem hi
      exact this hlk
    | some s' =>
      rw [hlk] at hs'; simp only [Option.getD_some] at hs'; subst hs'
      have hmem := List.mem_reverse.mp (lookup_mem hlk)
      obtain ⟨p, rfl, hpm⟩ := zip_fst_mem hl hmem
      refine (hp _ hpm).congr ?_
      rw [lookup_reverse hnd', lookup_of_mem hnd' (List.of_mem_zip hpm).1]
      obtain ⟨a, b⟩ := p
      simp
  · rw [lookup_reverse hnd']
    have hlL : l ∉ L := by
      unfold objSlots at hn; exact Ty.field_map_none hn
    refine lookup_eq_none (fun x hx e => hlL (hL _ ?_))
    rw [← hl, ← e]; exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem run_sound (L : List String) (e : Expr) : RunSound L e := by
  induction e using Expr.ind with
  | lit l =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | lit hl =>
      simp only [run]; exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH (Lit.eval_sound hl)
  | var i =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | var hi hlen hc =>
      obtain ⟨ℓ, hℓ, hs⟩ := G.lookup hG hi
      obtain ⟨v, hv, hsv⟩ := hH.2 ℓ _ hs
      simp only [run, hℓ, hv]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH
        (hsv _ hlen (fun c h => (hc c h).holdsOrVar hC))
  | func n body ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | @func _ _ _ ρ _ _ _ θ τs hlen hb =>
      subst hlen
      simp only [run]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH (closure_sound ih hb hC k W hG)
    | @funcCheck T _ _ _ θ τs ρ _ _ _ hT _ hlen hb =>
      subst hlen
      simp only [run]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH
        (V_whnf.mpr (hT ▸ closure_sound ih hb hC k W hG))
  | app f args ihf iha =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | app hf hlen hargs =>
      rw [run]
      refine Safe.bindC (ihf hf hC hG hH) fun vf W₁ _ hW₁ hH₁ hvf => ?_
      have hc₁ := run_clock_le k env h f
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindArgs (runArgs_sound hC args _ iha hlen hargs (G.mono hW₁ hG) hH₁)
        fun vs W₂ _ hW₂ hH₂ hvs => ?_
      have hc₂ := runArgs_clock_le (run k env h f).2.1 env (run k env h f).2.2 args
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      exact Lands.safe ((V_fn.mp (V.mono hc₂ hW₂ hvf)).2 _ (Nat.le_refl _) W₂ (List.prefix_refl _)
        _ .undefined vs hvs.length (fun i hi => hH₂.mono (by omega)) (by simp)
        (fun i hi => hvs.mono (by omega) (List.prefix_refl _)))
  | let_ mb ann e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | let_ s F hgen hval _ _ h₂ =>
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (F ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Pred.ftv ++
        (R.map Ty.ftv).getD [])
      have hm : ∀ a, a ∈ F ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Pred.ftv ∨
          a ∈ (R.map Ty.ftv).getD [] → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasTypeS Sys.wide L (C ++ s.instPreds τs) Γ R rm (annMode ann) e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst Sys.wide_substable (Subst.block m τs)
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
      have hsafe : ∀ τs, τs.length = s.arity → HoldsOrVarW (s.instPreds τs) →
          Safe (run k env h e₁) k W (s.inst τs) R := fun τs hlen hp =>
        ih₁ (hinst τs hlen) (hC.append hp) hG hH
      -- What follows the initialiser: its value in a new cell.
      have hK : ∀ v c₁ h₁ W₁, c₁ ≤ k → W <+: W₁ → HeapOK c₁ W₁ h₁ → SchemeV c₁ W₁ s v →
          Safe (run (min c₁ k) (h₁.length :: env) (h₁ ++ [v]) e₂) c₁ W₁ τ₀ R := by
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
        refine Safe.bindC (hsafe [] (by simp [ha]) (by simp [HoldsOrVarS, Scheme.instPreds, hp]))
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
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | unop hop he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv =>
        UnOp.eval_sound hop hv (Nat.le_refl _) (List.prefix_refl W₁) hH₁
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | ret he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv =>
        ⟨Nat.le_refl _, .inr ⟨W₁, List.prefix_refl W₁, hH₁, .inr (.inr ⟨v, rfl, _, rfl, hv⟩)⟩⟩
  | throw_ e ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | throw_ he =>
      simp only [run]
      exact Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ _ =>
        ⟨Nat.le_refl _, .inr ⟨W₁, List.prefix_refl W₁, hH₁, .inr (.inl trivial)⟩⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | seq h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC hG hH) fun _ W₁ _ hW₁ hH₁ _ => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      exact ih₂ h₂ hC (G.mono hW₁ hG) hH₁

  | while_ c body ihc ihb =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
    intro k C Γ R rm md W env h τ _ _ _ hH
    simp only [run]
    exact ⟨Nat.le_refl _, .inr ⟨W, List.prefix_refl W, hH, .inr (.inl trivial)⟩⟩
  | continue_ =>
    intro k C Γ R rm md W env h τ _ _ _ hH
    simp only [run]
    exact ⟨Nat.le_refl _, .inr ⟨W, List.prefix_refl W, hH, .inr (.inl trivial)⟩⟩
  | tryCatch body handler ihb ihh =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
  | unwrap e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | @unwrap _ _ _ _ _ _ σ _ _ _ _ h₁ hs h₂ h₃ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC hG hH) fun v W₁ _ hW₁ hH₁ hv => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      split
      · exact ih₂ h₂ hC (G.mono hW₁ hG) hH₁
      · -- What isn't nothing, in a new cell of the type `Strip` leaves.
        rename_i hn
        have hv' := EntailsS.strip hC hs hv (by simpa using hn)
        have hW₂ : W₁ <+: W₁ ++ [.mono σ] := List.prefix_append _ _
        have hcell : HeapOK (run k env h e₁).2.1 (W₁ ++ [.mono σ]) ((run k env h e₁).2.2 ++ [v]) :=
          hH₁.alloc (by simp) (fun i s' v' hs' hv'' => by
            match i, hs', hv'' with
            | 0, hs', hv'' =>
              simp at hs' hv''; subst hs' hv''
              exact SchemeV.mono_iff.mpr (hv'.mono (Nat.le_refl _) hW₂)
            | _ + 1, hs', _ => simp at hs')
        have hG₂ : G (W₁ ++ [.mono σ]) (.mono σ :: Γ) ((run k env h e₁).2.2.length :: env) :=
          ⟨by rw [hH₁.1]; simp, G.mono (hW₁.trans hW₂) hG⟩
        exact (ih₃ h₃ hC hG₂ hcell).weaken (Nat.le_refl _) hW₂
  | tryFinally body fin ihb ihf =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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

  | obj ls es ms ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | obj hes hks hτs hss hL hargs hfs =>
      rename_i ss τs
      simp only [run]
      refine Safe.bindArgs (runArgs_sound hC es τs ih (by omega) hargs hG hH)
        fun vs W₁ _ hW₁ hH₁ hvs => ?_
      have hb : (runArgs k env h es).2.2.length = W₁.length := hH₁.1
      have hW₂ := List.prefix_append W₁ [Cell.obj (.record L (objSlots L ls ss))]
      refine Safe.ok (Nat.le_refl _) hW₂ ?_ ?_
      · exact hH₁.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact (objFields_sound hks hτs hss hL hvs (zip_drop_snd (by omega) hfs)).mono
              (Nat.le_refl _) hW₂
          | _ + 1, hs, _ => simp at hs)
      · rw [V_record, hb]
        exact ⟨_, _, rfl, by simp, TyEq.refl _⟩
  | get e l ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | get he hp =>
      simp only [run]
      refine Safe.bindC (ih he hC hG hH) fun v W₁ _ _ hH₁ hv => ?_
      rw [Nat.min_eq_left (run_clock_le k env h e)]
      exact read_sound hp hC hv hH₁
  | set e l v ihe ihv =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | set he hp hv =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ihv hv hC (G.mono hW₁ hG) hH₁) fun vv W₂ _ hW₂ hH₂ hvv => ?_
      exact setProp_sound hp hC (hvo.mono (run_clock_le _ _ _ _) hW₂) hvv hH₂
  | spread e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | spread hps hks hτs hss hrs he₁ he₂ hm =>
      rename_i ss ps ks τs rs
      simp only [run]
      refine Safe.bindC (ih₁ he₁ hC hG hH) fun v₁ W₁ _ hW₁ hH₁ hv₁ => ?_
      have hc₁ := run_clock_le k env h e₁
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindFields (own_sound hv₁ hH₁) fun cs₁ W₂ _ hW₂ hH₂ hcs₁ => ?_
      have hc₂ := own_clock_le (run k env h e₁).2.1 (run k env h e₁).2.2 v₁
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      refine Safe.bindC (ih₂ he₂ hC (G.mono (hW₁.trans hW₂) hG) hH₂)
        fun v₂ W₃ _ hW₃ hH₃ hv₂ => ?_
      rw [Nat.min_eq_left (Nat.le_trans (run_clock_le _ _ _ _) (Nat.le_trans hc₂ hc₁))]
      refine Safe.bindFields (own_sound hv₂ hH₃) fun cs₂ W₄ _ hW₄ hH₄ hcs₂ => ?_
      have hV := spread_contents_sound hC hps hks hτs hss hrs hm
        ((hcs₁.mono (run_clock_le _ _ _ _) hW₃).mono (own_clock_le _ _ _) hW₄) hcs₂
      have hW₅ := List.prefix_append W₄ [Cell.obj (.record L rs)]
      refine Safe.ok (Nat.le_refl _) hW₅ ?_ ?_
      · exact hH₄.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact hV.mono (Nat.le_refl _) hW₅
          | _ + 1, hs, _ => simp at hs)
      · rw [V_record, hH₄.1]
        exact ⟨_, _, rfl, by simp, TyEq.refl _⟩

  | arr es ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | @arr _ _ _ _ _ σ hes =>
      simp only [run]
      have hargs : ∀ p ∈ es.zip (List.replicate es.length σ), HasTypeS Sys.wide L C Γ R _ _ p.1 p.2 :=
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
        exact ⟨_, _, rfl, by simp, TyEq.refl _⟩
    | @arrCheck T _ _ _ _ _ σ hT _ hes =>
      simp only [run]
      have hargs : ∀ p ∈ es.zip (List.replicate es.length σ), HasTypeS Sys.wide L C Γ R _ _ p.1 p.2 :=
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
      · rw [V_whnf, hT, V_array, hb]
        exact ⟨_, _, rfl, by simp, TyEq.refl _⟩
  | index e i ihe ihi =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | index he hi hp =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ihi hi hC (G.mono hW₁ hG) hH₁) fun vi W₂ _ hW₂ hH₂ hvi => ?_
      rw [Nat.min_eq_left (Nat.le_trans (run_clock_le _ _ _ _) hc₁)]
      exact index_sound hp hC (hvo.mono (run_clock_le _ _ _ _) hW₂) hvi hH₂
  | setIndex e i v ihe ihi ihv =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
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
  | mcall e l args ihe iha =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | mcall he hp hlen hargs =>
      simp only [run]
      refine Safe.bindC (ihe he hC hG hH) fun vo W₁ _ hW₁ hH₁ hvo => ?_
      have hc₁ := run_clock_le k env h e
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (read_sound (R := R) hp hC hvo hH₁) fun vf W₂ _ hW₂ hH₂ hvf => ?_
      have hc₂ := getter_clock_le (run k env h e).2.1 (run k env h e).2.2 vo
        (vo.read (run k env h e).2.2 l)
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      refine Safe.bindArgs (runArgs_sound hC args _ iha hlen hargs (G.mono (hW₁.trans hW₂) hG) hH₂)
        fun vs W₃ _ hW₃ hH₃ hvs => ?_
      have hc₃ := runArgs_clock_le
        (getter (run k env h e).2.1 (run k env h e).2.2 vo (vo.read (run k env h e).2.2 l)).2.1
        env (getter (run k env h e).2.1 (run k env h e).2.2 vo (vo.read (run k env h e).2.2 l)).2.2
        args
      rw [Nat.min_eq_left (Nat.le_trans hc₃ (Nat.le_trans hc₂ hc₁))]
      exact Lands.safe ((V_fn.mp (V.mono hc₃ hW₃ hvf)).2 _ (Nat.le_refl _) W₃ (List.prefix_refl _)
        _ vo vs hvs.length (fun i hi => hH₃.mono (by omega))
        (fun i hi => hvo.mono (by omega) (hW₂.trans hW₃))
        (fun i hi => hvs.mono (by omega) (List.prefix_refl _)))
  | cls ls es ks ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | cls hes hks hτs hss hnd hL hty hms =>
      rename_i τs ss
      simp only [run]
      -- The members that are functions: closures over the class's
      -- environment.
      have hfun : ∀ (i : Nat) (kd : ClassKind) (n : Nat) (b : Expr) (τ : Ty), ks[i]? = some kd →
          es[i]? = some (Expr.func n b) → τs[i]? = some τ → kd ≠ .data →
            V k W τ (.closure env n b) := by
        intro i kd n b τ h₁ h₂ h₃ h₄
        have := hty i _ kd τ h₂ h₁ h₃
        rw [show memberCtx Γ ks τs i kd = Γ by cases kd <;> simp_all [memberCtx]] at this
        exact func_value (ih _ (List.mem_of_getElem? h₂)) this hC hG hH
      refine Safe.bindArgs (runInits_sound hC es ks τs ih (by omega) (by omega)
        (fun i e τ h₁ h₂ h₃ => hty i e .data τ h₁ h₂ h₃) hG hH).of_none
        fun vs W₁ _ hW₁ hH₁ hvs => ?_
      have hc₁ := runInits_clock_le k env h es ks
      generalize runInits k env h es ks = p at hc₁ hH₁ hvs ⊢
      obtain ⟨r, c₁, h₁⟩ := p
      simp only at hc₁ hH₁ hvs ⊢
      have hW₂ := List.prefix_append W₁ [Cell.obj (.record L (objSlots L ls ss))]
      have hself : ∀ i, i ≤ c₁ → V i (W₁ ++ [Cell.obj (.record L (objSlots L ls ss))])
          (.record L (objSlots L ls ss)) (.obj h₁.length) := fun i _ =>
        V_obj_cell (by rw [hH₁.1]; simp)
      obtain ⟨fs, hfs, hl, hp⟩ := clsMembers_sound hself hC ls es ks τs ss vs (by omega) (by omega)
        (by omega) (by omega) hms
        (fun i kd n b τ h₁ h₂ h₃ h₄ => (hfun i kd n b τ h₁ h₂ h₃ h₄).mono hc₁ (hW₁.trans hW₂))
        (hvs.mono (Nat.le_refl _) hW₂)
      rw [hfs]
      refine Safe.ok (Nat.le_refl _) hW₂ ?_ ?_
      · exact hH₁.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact cls_cell hss hnd hL hl hp
          | _ + 1, hs, _ => simp at hs)
      · rw [V_record, hH₁.1]
        exact ⟨_, _, rfl, by simp, TyEq.refl _⟩
  | ctor n body ih =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | ctor hlen hb =>
      subst hlen
      simp only [run]
      exact Safe.ok (Nat.le_refl k) (List.prefix_refl W) hH (closure_sound ih hb hC k W hG)
  | new_ f args ihf iha =>
    intro k C Γ R rm md W env h τ ht hC hG hH
    obtain ⟨_, τ₀, ht, hτ₀⟩ := ht.top
    refine Safe.lift hC hτ₀ ?_
    cases ht with
    | new_ hf hlen hargs hρ _ =>
      simp only [run]
      refine Safe.bindC (ihf hf hC hG hH) fun vf W₁ _ hW₁ hH₁ hvf => ?_
      have hc₁ := run_clock_le k env h f
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindArgs (runArgs_sound hC args _ iha hlen hargs (G.mono hW₁ hG) hH₁)
        fun vs W₂ _ hW₂ hH₂ hvs => ?_
      have hc₂ := runArgs_clock_le (run k env h f).2.1 env (run k env h f).2.2 args
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      generalize runArgs (run k env h f).2.1 env (run k env h f).2.2 args = pa at hc₂ hH₂ hvs ⊢
      obtain ⟨ra, c₂, h₂⟩ := pa
      simp only at hc₂ hH₂ hvs ⊢
      -- `this`: a new object, of no fields.
      have hW₃ := List.prefix_append W₂ [Cell.obj (.record [] [])]
      have hH₃ : HeapOK c₂ (W₂ ++ [Cell.obj (.record [] [])]) (h₂ ++ [.fields []]) :=
        hH₂.alloc (by simp) (fun i s' v' hs hv' => by
          match i, hs, hv' with
          | 0, hs, hv' =>
            simp at hs hv'; subst hs hv'
            exact CellV_obj.mpr ⟨[], rfl, fun l s hs => by simp [Ty.field] at hs, fun l _ => rfl⟩
          | _ + 1, hs, _ => simp at hs)
      have hvf' := (hvf.mono hc₂ hW₂).mono (Nat.le_refl _) hW₃
      -- A constructor: `new` calls it.
      have hctor : vf.asCtor = vf := by
        simp [Value.asCtor, (V_fn.mp hvf').1 (TyEq.refl _)]
      rw [hctor]
      have hcall := (V_fn.mp hvf').2 c₂ (Nat.le_refl _) _
        (List.prefix_refl _) (h₂ ++ [.fields []]) (.obj h₂.length) vs hvs.length
        (fun i hi => hH₃.mono (by omega)) (by simp)
        (fun i hi => hvs.mono (by omega) hW₃)
      generalize call c₂ (h₂ ++ [.fields []]) vf (.obj h₂.length) vs = pc at hcall ⊢
      obtain ⟨rc, c₃, h₃⟩ := pc
      obtain ⟨hc₃, hto | ⟨hlt, W₄, hW₄, hH₄, ⟨v, hv, hV⟩ | habr⟩⟩ := hcall
      · simp only at hto; subst hto; exact ⟨hc₃, .inl rfl⟩
      · simp only at hv hlt hH₄ hV hc₃; subst hv
        have hv' := V.tyEq _ hρ (hV hlt)
        obtain ⟨ℓ, τc, rfl, -⟩ := V_record.mp hv'
        simp only [Value.isObject]
        exact Safe.ok hc₃ (hW₃.trans hW₄) (hH₄ hlt) (hV hlt)
      · simp only at habr hlt hH₄ hc₃
        cases rc <;> simp only [Result.Abrupt] at habr <;>
          exact ⟨hc₃, .inr ⟨W₄, hW₃.trans hW₄, hH₄ hlt, .inr (.inl trivial)⟩⟩

/-- Type soundness, for `eval`: a value of the type, a `return` of a value
of the return type, a `throw`, or out of clock; never stuck. -/
theorem eval_soundW (clock : Nat) (ht : HasTypeS Sys.wide L C Γ R rm md e τ) (hC : HoldsOrVarW C)
    (hG : G W Γ env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  run_sound L e ht hC hG hH

/-- A closed program, well typed outside any function, assuming constraints
each an instance or on a type variable, never gets stuck, whatever the
clock. -/
theorem never_stuckW (ht : HasTypeS Sys.wide L C [] none rm md e τ) (hC : HoldsOrVarW C)
    (clock : Nat) (s : Stuck) : eval clock [] [] e ≠ .stuck s :=
  Safe.not_stuck (run_sound L e ht (W := []) hC (by simp [G])
    ⟨rfl, fun _ _ h => by simp at h⟩)

/-- Soundness of the narrow system, the one inference implements: its
derivations are wide ones (`HasTypeS.toWide`), whose schemes carry their
injections in the wide form (`Scheme.toW`, the identity on a scheme without
any). -/
theorem eval_sound (clock : Nat) (ht : HasType L C Γ R rm md e τ) (hC : HoldsOrVar C)
    (hG : G W (Γ.map Scheme.toW) env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  eval_soundW clock ht.toWide hC.toW hG hH

theorem never_stuck (ht : HasType L C [] none rm md e τ) (hC : HoldsOrVar C) (clock : Nat)
    (s : Stuck) : eval clock [] [] e ≠ .stuck s :=
  never_stuckW ht.toWide hC.toW clock s

end Inty
