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

/-- `Math.abs : (number) => number`, called with any `this`. -/
theorem Prim.abs_sound (k : Nat) (θ : Ty) : V k (.fn θ [.number] .number) (.prim .abs) := by
  intro j _ _ args _ hargs
  match args, hargs with
  | [_], ⟨⟨n, rfl⟩, _⟩ => exact ⟨Nat.le_refl j, .inr (.inl ⟨_, rfl, ⟨_, rfl⟩⟩)⟩

/-- `Boolean : <a>(a) => boolean`: it takes any value. -/
theorem Prim.truthy_sound (k : Nat) (θ τ : Ty) :
    V k (.fn θ [τ] .boolean) (.prim .truthy) := by
  intro j _ _ args _ hargs
  match args, hargs with
  | [_], _ => exact ⟨Nat.le_refl j, .inr (.inl ⟨_, rfl, ⟨_, rfl⟩⟩)⟩

/-- The builtins' types, innermost first: `Boolean` is variable 0 and
`Math.abs` variable 1 of a program run with them. Called outside a
receiver, their `this` is `undefined`. -/
def builtinCtx : Ctx :=
  [⟨1, .fn .undefined [.bound 0] .boolean, []⟩, .mono (.fn .undefined [.number] .number)]

/-- The builtins themselves. -/
def builtinEnv : Env := [.prim .truthy, .prim .abs]

/-- The builtins have their types. -/
theorem builtins_sound (k : Nat) : G k builtinCtx builtinEnv :=
  ⟨fun τs _ _ => by simpa [Scheme.inst, PTy.inst] using Prim.truthy_sound k _ _,
    SchemeV.mono_iff.mpr (Prim.abs_sound k _), trivial⟩

/-- A program well typed in the builtins' context never gets stuck in their
environment, whatever the clock. -/
theorem never_stuck_with_builtins (h : HasType [] builtinCtx none e τ) (clock : Nat)
    (s : Stuck) : eval clock builtinEnv e ≠ .stuck s :=
  Safe.not_stuck (run_sound e h (fun _ h => by cases h) (builtins_sound clock))

/-- A program inference accepts with the builtins never gets stuck with them. -/
theorem inferIn_builtins_never_stuck {e : Expr} {τ : Ty} (h : inferIn builtinCtx e = some τ)
    (clock : Nat) (s : Stuck) : eval clock builtinEnv e ≠ .stuck s :=
  never_stuck_with_builtins (inferIn_sound rfl h) clock s

end Inty
