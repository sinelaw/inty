import Inty.InferSound

/-!
# Builtins

Native functions have types because of what they do, which is what the
semantic typing of `Inty.Soundness` is for: no typing derivation describes
`Math.abs`, but `V` relates it to `number → number` all the same, by its
definition (`Prim.apply`). Programs then run with the builtins in scope:
those inference accepts in the builtins' context never get stuck in their
environment. This is the shape `src/builtins` will take in the model, one
native function at a time, each with its proof.
-/

namespace Inty

/-- `Math.abs : (number) => number`, called with any `this`. A native call
takes a tick and leaves the heap alone. -/
theorem Prim.abs_sound (k : Nat) (W : World) (θ : Ty) :
    V k W (.fn θ [.number] .number) (.prim .abs) := by
  rw [V_fn]
  intro j _ W' _ h _ args _ hh _ hargs
  cases j with
  | zero => exact ⟨Nat.le_refl 0, .inl rfl⟩
  | succ j =>
    have hargs := hargs j (by omega)
    match args, hargs with
    | [_], hargs =>
      simp only [VList_cons, V_number, VList_nil, and_true] at hargs
      obtain ⟨n, rfl⟩ := hargs
      exact ⟨by simp [call], .inr ⟨by simp [call], W', List.prefix_refl _,
        fun _ => hh j (by omega), .inl ⟨_, rfl, fun _ => by simp⟩⟩⟩
    | [], hargs | _ :: _ :: _, hargs => simp at hargs

/-- `Boolean : <a>(a) => boolean`: it takes any value. -/
theorem Prim.truthy_sound (k : Nat) (W : World) (θ τ : Ty) :
    V k W (.fn θ [τ] .boolean) (.prim .truthy) := by
  rw [V_fn]
  intro j _ W' _ h _ args _ hh _ hargs
  cases j with
  | zero => exact ⟨Nat.le_refl 0, .inl rfl⟩
  | succ j =>
    have hargs := hargs j (by omega)
    match args, hargs with
    | [_], _ =>
      exact ⟨by simp [call], .inr ⟨by simp [call], W', List.prefix_refl _,
        fun _ => hh j (by omega), .inl ⟨_, rfl, fun _ => by simp⟩⟩⟩
    | [], hargs | _ :: _ :: _, hargs => simp at hargs

/-- The builtins' types, innermost first: `Boolean` is variable 0 and
`Math.abs` variable 1 of a program run with them. Called outside a
receiver, their `this` is `undefined`. -/
def builtinCtx : Ctx :=
  [⟨1, .fn .undefined [.bound 0] .boolean, []⟩, .mono (.fn .undefined [.number] .number)]

/-- The builtins' cells, and the variables bound to them. -/
def builtinHeap : Heap := [.prim .truthy, .prim .abs]
def builtinEnv : Env := [0, 1]

/-- The builtins have their types, in the world of their schemes. -/
theorem builtins_sound (k : Nat) :
    G (builtinCtx.map .scheme) builtinCtx builtinEnv ∧
      HeapOK k (builtinCtx.map .scheme) builtinHeap := by
  refine ⟨by simp [G, builtinCtx, builtinEnv], rfl, fun ℓ s hs => ?_⟩
  match ℓ, hs with
  | 0, hs =>
    simp [builtinCtx] at hs; subst hs
    exact ⟨_, rfl, fun τs _ _ => by
      simpa [Scheme.inst, PTy.inst] using Prim.truthy_sound k _ _ _⟩
  | 1, hs =>
    simp [builtinCtx] at hs; subst hs
    exact ⟨_, rfl, SchemeV.mono_iff.mpr (Prim.abs_sound k _ _)⟩
  | _ + 2, hs => simp [builtinCtx] at hs

/-- A program well typed in the builtins' context never gets stuck in their
environment, whatever the clock. -/
theorem never_stuck_with_builtins (h : HasType L C builtinCtx none e τ) (hC : HoldsOrVar C)
    (clock : Nat) (s : Stuck) : eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  Safe.not_stuck (run_sound L e h hC (builtins_sound clock).1 (builtins_sound clock).2)

/-- A program inference accepts with the builtins never gets stuck with them. -/
theorem inferIn_builtins_never_stuck {L : List String} {e : Expr} {τ : Ty}
    (h : inferIn L builtinCtx e = some τ) (clock : Nat) (s : Stuck) :
    eval clock builtinEnv builtinHeap e ≠ .stuck s := by
  obtain ⟨C, hC, ht⟩ := inferIn_sound rfl h
  exact never_stuck_with_builtins ht hC clock s

end Inty
