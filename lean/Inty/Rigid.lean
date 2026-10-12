import Inty.Wide

/-!
# Instantiating rigid type variables

A polymorphic annotation's quantified variables are rigid in the
initialiser it is checked against (`Con.rigid`): constants there, which
unification never binds. The annotated binding has every instance of the
annotation, which the soundness proof gets by substituting types for the
rigid variables throughout the initialiser's derivation (`Ty.rsub`), as it
substitutes types for a generalised binding's variables (`Ty.subst`). A
rigid variable is a leaf of the trees types unfold to, so the substitution
grafts its image there (`Ty.approx_rsub`), and equal types stay equal.
-/

namespace Inty

/-- Types for some rigid type variables. -/
abbrev RSubst := Nat → Nat → Option Ty

/-- A rigid type variable's image, if it has one. -/
def Con.rimg (ρ : RSubst) : Con → Option Ty
  | .rigid s i => ρ s i
  | _ => none

/-- The image of a constructor applied to `args`: a rigid type variable's,
which takes no arguments. -/
def Con.rimgA {α : Type} (ρ : RSubst) (c : Con) (args : List α) : Option Ty :=
  if args.isEmpty then c.rimg ρ else none

@[simp] theorem Con.rimgA_none {α : Type} {ρ : RSubst} {c : Con} (h : c.rimg ρ = none) (args : List α) :
    c.rimgA ρ args = none := by
  simp [Con.rimgA, h]

theorem Con.rimgA_some {α : Type} {ρ : RSubst} {c : Con} {args : List α} {τ : Ty}
    (h : c.rimgA ρ args = some τ) : c.rimg ρ = some τ ∧ args = [] := by
  unfold Con.rimgA at h
  split at h
  · rename_i he; exact ⟨h, List.isEmpty_iff.mp he⟩
  · cases h

theorem Con.rimgA_map {α β : Type} (ρ : RSubst) (c : Con) (args : List α) (f : α → β) :
    c.rimgA ρ (args.map f) = c.rimgA ρ args := by
  simp [Con.rimgA]

mutual
def RTy.rsub (ρ : RSubst) : RTy → RTy
  | .free a => .free a
  | .self j => .self j
  | .app c args =>
    match c.rimgA ρ args with
    | some τ => τ.toRTy
    | none => .app c (RTy.rsubs ρ args)
  | .mu i sys => .mu i (RTy.rsubs ρ sys)
def RTy.rsubs (ρ : RSubst) : List RTy → List RTy
  | [] => []
  | r :: rs => r.rsub ρ :: RTy.rsubs ρ rs
end

@[simp] theorem RTy.rsubs_eq (ρ : RSubst) (rs : List RTy) : RTy.rsubs ρ rs = rs.map (RTy.rsub ρ) := by
  induction rs <;> simp_all [RTy.rsubs]

theorem RTy.rsub_app (ρ : RSubst) (c : Con) (args : List RTy) :
    (RTy.app c args).rsub ρ = match c.rimgA ρ args with
      | some τ => τ.toRTy
      | none => .app c (args.map (·.rsub ρ)) := by
  simp only [RTy.rsub, RTy.rsubs_eq]

@[simp] theorem RTy.rsub_app_none {ρ : RSubst} {c : Con} {args : List RTy} (h : c.rimgA ρ args = none) :
    (RTy.app c args).rsub ρ = .app c (args.map (·.rsub ρ)) := by
  rw [RTy.rsub_app, h]

@[simp] theorem RTy.rsub_mu (ρ : RSubst) (i : Nat) (sys : List RTy) :
    (RTy.mu i sys).rsub ρ = .mu i (sys.map (·.rsub ρ)) := by simp [RTy.rsub]

mutual
def Ty.rsub (ρ : RSubst) : Ty → Ty
  | .var a => .var a
  | .app c args =>
    match c.rimgA ρ args with
    | some τ => τ
    | none => .app c (Ty.rsubs ρ args)
  | .mu i sys => .mu i (RTy.rsubs ρ sys)
def Ty.rsubs (ρ : RSubst) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.rsub ρ :: Ty.rsubs ρ τs
end

@[simp] theorem Ty.rsubs_eq (ρ : RSubst) (τs : List Ty) : Ty.rsubs ρ τs = τs.map (Ty.rsub ρ) := by
  induction τs <;> simp_all [Ty.rsubs]

theorem Ty.rsub_app (ρ : RSubst) (c : Con) (args : List Ty) :
    (Ty.app c args).rsub ρ = match c.rimgA ρ args with
      | some τ => τ
      | none => .app c (args.map (·.rsub ρ)) := by
  simp only [Ty.rsub, Ty.rsubs_eq]

@[simp] theorem Ty.rsub_app_none {ρ : RSubst} {c : Con} {args : List Ty} (h : c.rimgA ρ args = none) :
    (Ty.app c args).rsub ρ = .app c (args.map (·.rsub ρ)) := by
  rw [Ty.rsub_app, h]

@[simp] theorem Ty.rsub_app_some {ρ : RSubst} {c : Con} {τ : Ty} {args : List Ty}
    (h : c.rimgA ρ args = some τ) : (Ty.app c args).rsub ρ = τ := by
  rw [Ty.rsub_app, h]

@[simp] theorem Ty.rsub_var (ρ : RSubst) (a : Nat) : (Ty.var a).rsub ρ = .var a := rfl

@[simp] theorem Ty.rsub_mu (ρ : RSubst) (i : Nat) (sys : List RTy) :
    (Ty.mu i sys).rsub ρ = .mu i (sys.map (·.rsub ρ)) := by simp [Ty.rsub]

/-- The constructors that aren't rigid type variables have no image. -/
theorem Con.rimg_of_not_rigid {ρ : RSubst} {c : Con} (h : c.isRigid = false) : c.rimg ρ = none := by
  cases c <;> simp_all [Con.rimg, Con.isRigid]

@[simp] theorem Con.rimg_maybe (ρ : RSubst) (z : Nothing) : (Con.maybe z).rimg ρ = none := rfl
@[simp] theorem Con.rimg_record (ρ : RSubst) (ls : List String) : (Con.record ls).rimg ρ = none := rfl

theorem Ty.toRTy_rsub (ρ : RSubst) (τ : Ty) : τ.toRTy.rsub ρ = (τ.rsub ρ).toRTy := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.rsub_app, Ty.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => rfl
    | none =>
      simp only [Ty.toRTy_app, List.map_map, RTy.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys => simp [Ty.toRTy]

/-! ## Unfolding -/

theorem RTy.open_rsub (ρ : RSubst) (env : Nat → Ty) (r : RTy) :
    (r.rsub ρ).open (fun j => (env j).rsub ρ) = (r.open env).rsub ρ := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    rw [RTy.rsub_app, RTy.open_app, Ty.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => simp
    | none =>
      simp only [RTy.open_app, List.map_map, Ty.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys _ => simp [RTy.open]

theorem muEnv_rsub (ρ : RSubst) (sys : List RTy) :
    muEnv (sys.map (·.rsub ρ)) = fun j => (muEnv sys j).rsub ρ := by
  funext j; simp [muEnv]

theorem RTy.head_rsub (ρ : RSubst) (r : RTy) (env : Nat → Ty) :
    (r.rsub ρ).head (fun j => (env j).rsub ρ) = (r.head env).bind (fun t => (t.rsub ρ).view) := by
  induction r using RTy.ind generalizing env with
  | free a => simp [RTy.rsub, RTy.head, Ty.view]
  | self j => simp [RTy.rsub, RTy.head]
  | app c args _ =>
    rw [RTy.rsub_app]
    cases hc : c.rimgA ρ args with
    | some τ =>
      rw [RTy.head_toRTy, RTy.head]
      have hc' : c.rimgA ρ (args.map (RTy.open env)) = some τ := by rw [Con.rimgA_map]; exact hc
      simp [Ty.rsub_app_some hc']
    | none =>
      rw [RTy.head, RTy.head]
      have hc' : c.rimgA ρ (args.map (RTy.open env)) = none := by rw [Con.rimgA_map]; exact hc
      simp [Ty.view, List.map_map, Function.comp_def, RTy.open_rsub, Ty.rsub_app_none hc']
  | mu i sys ih =>
    simp only [RTy.rsub_mu, RTy.head_mu, List.getElem?_map]
    cases hr : sys[i]? with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [muEnv_rsub]
      exact ih r (List.mem_of_getElem? hr) (muEnv sys)

theorem Ty.view_rsub (ρ : RSubst) (τ : Ty) :
    (τ.rsub ρ).view = τ.view.bind (fun t => (t.rsub ρ).view) := by
  have := RTy.head_rsub ρ τ.toRTy (fun _ => .undefined)
  rw [Ty.toRTy_rsub, RTy.head_toRTy, RTy.head_toRTy] at this
  exact this

/-- `t` with the images of its rigid type variables grafted at them, at
the depth that remains. -/
def Tree.graftR (ρ : RSubst) : Nat → Tree → Tree
  | 0, _ => .bot
  | _ + 1, .bot => .bot
  | _ + 1, .var a => .var a
  | n + 1, .node c ts =>
    match c.rimgA ρ ts with
    | some τ => τ.approx (n + 1)
    | none => .node c (ts.map (Tree.graftR ρ n))

theorem Ty.approx_rsub (ρ : RSubst) :
    ∀ (n : Nat) (τ : Ty), (τ.rsub ρ).approx n = (τ.approx n).graftR ρ n
  | 0, _ => rfl
  | n + 1, τ => by
    rw [Ty.approx_succ, Ty.approx_succ, Ty.view_rsub]
    cases hv : τ.view with
    | none => rfl
    | some t =>
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · simp [Tree.graftR, Ty.view]
      · simp only [Option.bind_some]
        cases hc : c.rimgA ρ args with
        | some τ' =>
          have hc' : c.rimgA ρ (args.map (Ty.approx n)) = some τ' := by rw [Con.rimgA_map]; exact hc
          simp only [Ty.rsub_app_some hc, Tree.graftR, hc']
          rw [Ty.approx_succ]
        | none =>
          have hc' : c.rimgA ρ (args.map (Ty.approx n)) = none := by rw [Con.rimgA_map]; exact hc
          simp only [Ty.rsub_app_none hc, Ty.view, Tree.graftR, hc', List.map_map]
          congr 1
          exact List.map_congr_left (fun a _ => Ty.approx_rsub ρ n a)

/-- Equal types stay equal when their rigid type variables are instantiated. -/
theorem TyEq.rsub (ρ : RSubst) {s t : Ty} (h : TyEq s t) : TyEq (s.rsub ρ) (t.rsub ρ) :=
  fun n => by rw [Ty.approx_rsub, Ty.approx_rsub, h n]

/-- A constructor application's head survives the instantiation, unless it
is a rigid type variable instantiated. -/
theorem Ty.whnf_rsub_of_app {ρ : RSubst} {T : Ty} {c : Con} {xs : List Ty} (h : T.whnf = .app c xs)
    (hc : c.rimgA ρ xs = none) : (T.rsub ρ).whnf = .app c (xs.map (·.rsub ρ)) := by
  rcases Ty.whnf_cases T with ⟨a, ha⟩ | ⟨c', xs', hw, hv⟩ | hv
  · rw [ha] at h; cases h
  · rw [hw] at h
    simp only [Ty.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply Ty.whnf_of_view
    rw [Ty.view_rsub, hv]
    simp [Ty.rsub_app_none hc, Ty.view]
  · rw [Ty.whnf_headless hv] at h
    subst h
    simp [Ty.view] at hv

theorem Ty.view_of_whnf_var {t : Ty} {a : Nat} (h : t.whnf = .var a) : t.view = some (.var a) := by
  cases hv : t.view with
  | none => rw [Ty.whnf_headless hv] at h; subst h; simp [Ty.view] at hv
  | some u => rw [Ty.whnf_of_view hv] at h; rw [h]

theorem Ty.whnf_rsub_var {ρ : RSubst} {t : Ty} {a : Nat} (h : t.whnf = .var a) :
    (t.rsub ρ).whnf = .var a := by
  apply Ty.whnf_of_view
  rw [Ty.view_rsub, Ty.view_of_whnf_var h]
  rfl

/-! ## Scheme bodies, schemes and constraints -/

mutual
def PTy.rsub (ρ : RSubst) : PTy → PTy
  | .free a => .free a
  | .bound i => .bound i
  | .self j => .self j
  | .app c args =>
    match c.rimgA ρ args with
    | some τ => τ.toPTy
    | none => .app c (PTy.rsubs ρ args)
  | .mu i sys => .mu i (PTy.rsubs ρ sys)
def PTy.rsubs (ρ : RSubst) : List PTy → List PTy
  | [] => []
  | p :: ps => p.rsub ρ :: PTy.rsubs ρ ps
end

@[simp] theorem PTy.rsubs_eq (ρ : RSubst) (ps : List PTy) : PTy.rsubs ρ ps = ps.map (PTy.rsub ρ) := by
  induction ps <;> simp_all [PTy.rsubs]

theorem PTy.rsub_app (ρ : RSubst) (c : Con) (args : List PTy) :
    (PTy.app c args).rsub ρ = match c.rimgA ρ args with
      | some τ => τ.toPTy
      | none => .app c (args.map (·.rsub ρ)) := by
  simp only [PTy.rsub, PTy.rsubs_eq]

@[simp] theorem PTy.rsub_mu (ρ : RSubst) (i : Nat) (sys : List PTy) :
    (PTy.mu i sys).rsub ρ = .mu i (sys.map (·.rsub ρ)) := by simp [PTy.rsub]

@[simp] theorem Ty.undefined_rsub (ρ : RSubst) : Ty.undefined.rsub ρ = .undefined := rfl

theorem List.getD_map_rsub (ρ : RSubst) (τs : List Ty) (i : Nat) :
    (τs.map (·.rsub ρ)).getD i .undefined = (τs.getD i .undefined).rsub ρ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases τs[i]? <;> rfl

theorem PTy.instR_rsub (ρ : RSubst) (τs : List Ty) (p : PTy) :
    (p.rsub ρ).instR (τs.map (·.rsub ρ)) = (p.instR τs).rsub ρ := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => simp only [PTy.rsub, PTy.instR, List.getD_map_rsub, Ty.toRTy_rsub]
  | self j => rfl
  | app c args ih =>
    rw [PTy.rsub_app, PTy.instR_app, RTy.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => simp
    | none =>
      simp only [PTy.instR_app, List.map_map, RTy.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [PTy.rsub_mu, PTy.instR_mu, RTy.rsub_mu, List.map_map, RTy.mu.injEq, true_and]
    exact List.map_congr_left ih

theorem PTy.inst_rsub (ρ : RSubst) (τs : List Ty) (p : PTy) :
    (p.rsub ρ).inst (τs.map (·.rsub ρ)) = (p.inst τs).rsub ρ := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => simp only [PTy.rsub, PTy.inst, List.getD_map_rsub]
  | self j => rfl
  | app c args ih =>
    rw [PTy.rsub_app, PTy.inst_app, Ty.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => simp
    | none =>
      simp only [PTy.inst_app, List.map_map, Ty.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys _ =>
    simp only [PTy.rsub_mu, PTy.inst_mu, Ty.rsub_mu, List.map_map, Ty.mu.injEq, true_and]
    exact List.map_congr_left (fun p _ => PTy.instR_rsub ρ τs p)

/-- A class with its parameter instantiated. -/
def Cls.rsub (ρ : RSubst) : Cls → Cls
  | .inject T => .inject (T.rsub ρ)
  | c => c

def Pred.rsub (ρ : RSubst) (p : Pred) : Pred := ⟨p.cls.rsub ρ, p.args.map (·.rsub ρ)⟩

def PPred.rsub (ρ : RSubst) (p : PPred) : PPred := ⟨p.cls.rsub ρ, p.args.map (·.rsub ρ)⟩

def Scheme.rsub (ρ : RSubst) (s : Scheme) : Scheme :=
  ⟨s.arity, s.body.rsub ρ, s.preds.map (PPred.rsub ρ)⟩

@[simp] theorem Cls.rsub_of_ne {ρ : RSubst} {c : Cls} (h : ∀ T, c ≠ .inject T) : c.rsub ρ = c := by
  cases c <;> simp_all [Cls.rsub]

theorem PPred.inst_rsub (ρ : RSubst) (τs : List Ty) (p : PPred) :
    (p.rsub ρ).inst (τs.map (·.rsub ρ)) = (p.inst τs).rsub ρ := by
  simp [PPred.rsub, PPred.inst, Pred.rsub, PTy.inst_rsub]

theorem Scheme.inst_rsub (ρ : RSubst) (τs : List Ty) (s : Scheme) :
    (s.rsub ρ).inst (τs.map (·.rsub ρ)) = (s.inst τs).rsub ρ := PTy.inst_rsub ρ τs s.body

theorem Scheme.instPreds_rsub (ρ : RSubst) (τs : List Ty) (s : Scheme) :
    (s.rsub ρ).instPreds (τs.map (·.rsub ρ)) = (s.instPreds τs).map (Pred.rsub ρ) := by
  simp only [Scheme.instPreds, Scheme.rsub, List.map_map]
  exact List.map_congr_left fun p _ => PPred.inst_rsub ρ τs p

@[simp] theorem varBlock_rsub (ρ : RSubst) (m k : Nat) : (varBlock m k).map (·.rsub ρ) = varBlock m k := by
  simp [varBlock, Function.comp_def]

theorem Scheme.open_rsub (ρ : RSubst) (s : Scheme) (m : Nat) :
    (s.rsub ρ).open m = (s.open m).rsub ρ := by
  have := Scheme.inst_rsub ρ (varBlock m s.arity) s
  rwa [varBlock_rsub] at this

theorem Scheme.openPreds_rsub (ρ : RSubst) (s : Scheme) (m : Nat) :
    (s.rsub ρ).openPreds m = (s.openPreds m).map (Pred.rsub ρ) := by
  have := Scheme.instPreds_rsub ρ (varBlock m s.arity) s
  rwa [varBlock_rsub] at this

@[simp] theorem Scheme.rsub_arity (ρ : RSubst) (s : Scheme) : (s.rsub ρ).arity = s.arity := rfl

theorem RTy.toPTy_rsub (ρ : RSubst) (r : RTy) : (r.rsub ρ).toPTy = r.toPTy.rsub ρ := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    rw [RTy.rsub_app, RTy.toPTy_app, PTy.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => simp
    | none =>
      simp only [RTy.toPTy_app, List.map_map, PTy.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.rsub_mu, RTy.toPTy_mu, PTy.rsub_mu, List.map_map, PTy.mu.injEq, true_and]
    exact List.map_congr_left ih

theorem Scheme.mono_rsub (ρ : RSubst) (τ : Ty) : (Scheme.mono τ).rsub ρ = .mono (τ.rsub ρ) := by
  simp only [Scheme.mono, Scheme.rsub, List.map_nil, Scheme.mk.injEq, true_and, and_true]
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    rw [Ty.toPTy_app, PTy.rsub_app, Ty.rsub_app, Con.rimgA_map]
    cases c.rimgA ρ args with
    | some τ => rfl
    | none =>
      simp only [Ty.toPTy_app, List.map_map, PTy.app.injEq, true_and]
      exact List.map_congr_left ih
  | mu i sys =>
    simp only [Ty.toPTy_mu, PTy.rsub_mu, Ty.rsub_mu, List.map_map, PTy.mu.injEq, true_and]
    exact List.map_congr_left fun r _ => (RTy.toPTy_rsub ρ r).symm

/-! ## Tree variables, fields, slots -/

theorem Ty.approx_graftR_hasVar (ρ : RSubst) {a : Nat} :
    ∀ (n : Nat) (τ : Ty), (τ.approx n).HasVar a → ((τ.approx n).graftR ρ n).HasVar a
  | 0, _, h => absurd h Ty.approx_zero_hasVar
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h ⊢
    cases hv : τ.view with
    | none => rw [hv] at h; cases h
    | some t =>
      rw [hv] at h
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · simpa [Tree.graftR] using h
      · dsimp only at h ⊢
        cases h with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          unfold Tree.graftR
          cases hc : c.rimgA ρ (args.map (Ty.approx n)) with
          | some τ' =>
            have := (Con.rimgA_some hc).2
            rw [List.map_eq_nil_iff] at this; subst this; cases hx
          | none =>
            simp only [List.map_map]
            exact .node (List.mem_map_of_mem (f := (Tree.graftR ρ n) ∘ Ty.approx n) hx)
              (Ty.approx_graftR_hasVar ρ n x ht)

/-- Instantiating rigid type variables keeps the tree variables. -/
theorem Ty.TV.rsub (ρ : RSubst) {τ : Ty} {a : Nat} (h : τ.TV a) : (τ.rsub ρ).TV a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [Ty.approx_rsub]; exact Ty.approx_graftR_hasVar ρ n τ hn⟩

attribute [simp] Con.isRigid

@[simp] theorem Ty.rsub_app_nr {ρ : RSubst} {c : Con} (h : c.isRigid = false) (args : List Ty) :
    (Ty.app c args).rsub ρ = .app c (args.map (·.rsub ρ)) :=
  Ty.rsub_app_none (Con.rimgA_none (Con.rimg_of_not_rigid h) args)


@[simp] theorem Ty.rsub_number (ρ : RSubst) : Ty.number.rsub ρ = .number := rfl
@[simp] theorem Ty.rsub_string (ρ : RSubst) : Ty.string.rsub ρ = .string := rfl
@[simp] theorem Ty.rsub_boolean (ρ : RSubst) : Ty.boolean.rsub ρ = .boolean := rfl
@[simp] theorem Ty.rsub_null (ρ : RSubst) : Ty.null.rsub ρ = .null := rfl
@[simp] theorem Ty.rsub_unknown (ρ : RSubst) : Ty.unknown.rsub ρ = .unknown := rfl
@[simp] theorem Ty.rsub_pre (ρ : RSubst) : Ty.pre.rsub ρ = .pre := rfl
@[simp] theorem Ty.rsub_abs (ρ : RSubst) : Ty.abs.rsub ρ = .abs := rfl
@[simp] theorem Ty.rsub_data (ρ : RSubst) : Ty.data.rsub ρ = .data := rfl
@[simp] theorem Ty.rsub_getter (ρ : RSubst) : Ty.getter.rsub ρ = .getter := rfl
@[simp] theorem Ty.rsub_proto (ρ : RSubst) : Ty.proto.rsub ρ = .proto := rfl
@[simp] theorem Ty.rsub_newTarget (ρ : RSubst) : Ty.newTarget.rsub ρ = .newTarget := rfl
@[simp] theorem Ty.rsub_absSlot (ρ : RSubst) : Ty.absSlot.rsub ρ = .absSlot := rfl
@[simp] theorem Ty.rsub_slot (ρ : RSubst) (p k τ : Ty) :
    (Ty.slot p k τ).rsub ρ = .slot (p.rsub ρ) (k.rsub ρ) (τ.rsub ρ) := rfl
@[simp] theorem Ty.rsub_fn (ρ : RSubst) (θ : Ty) (τs : List Ty) (r : Ty) :
    (Ty.fn θ τs r).rsub ρ = .fn (θ.rsub ρ) (τs.map (·.rsub ρ)) (r.rsub ρ) := by
  simp [Ty.fn, Ty.rsub, Con.rimgA]
@[simp] theorem Ty.rsub_record (ρ : RSubst) (ls : List String) (ss : List Ty) :
    (Ty.record ls ss).rsub ρ = .record ls (ss.map (·.rsub ρ)) := by
  simp [Ty.record, Ty.rsub, Con.rimgA, Con.rimg]
@[simp] theorem Ty.rsub_array (ρ : RSubst) (τ : Ty) : (Ty.array τ).rsub ρ = .array (τ.rsub ρ) := rfl
@[simp] theorem Ty.rsub_tuple (ρ : RSubst) (τs : List Ty) :
    (Ty.tuple τs).rsub ρ = .tuple (τs.map (·.rsub ρ)) := by
  simp [Ty.tuple, Ty.rsub, Con.rimgA, Con.rimg]
@[simp] theorem Ty.rsub_maybe (ρ : RSubst) (z : Nothing) (τ : Ty) :
    (Ty.maybe z τ).rsub ρ = .maybe z (τ.rsub ρ) := rfl
@[simp] theorem Nothing.ty_rsub (ρ : RSubst) (z : Nothing) : z.ty.rsub ρ = z.ty := by
  cases z <;> rfl
@[simp] theorem Pred.rsub_mk_nr (ρ : RSubst) {c : Cls} (h : ∀ T, c ≠ .inject T) (args : List Ty) :
    Pred.rsub ρ ⟨c, args⟩ = ⟨c, args.map (·.rsub ρ)⟩ := by
  simp [Pred.rsub, Cls.rsub_of_ne h]

theorem PTy.TreeBound.rsub {k : Nat} {p : PTy} {i : Nat} (hi : i < k) (h : p.TreeBound k i)
    (ρ : RSubst) : (p.rsub ρ).TreeBound k i := by
  have hN := lt_maxPlusOne (l := p.ftv ++ (p.rsub ρ).ftv)
  generalize maxPlusOne (p.ftv ++ (p.rsub ρ).ftv) = N at hN
  rw [PTy.treeBound_iff hi (fun a ha => hN a (by simp [ha]))] at h
  rw [PTy.treeBound_iff hi (fun a ha => hN a (by simp [ha]))]
  rw [← varBlock_rsub ρ N k, PTy.inst_rsub]
  exact h.rsub ρ

theorem Scheme.Simple.rsub {s : Scheme} (hs : s.Simple) (ρ : RSubst) : (s.rsub ρ).Simple := by
  intro p hp
  simp only [Scheme.rsub, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rcases hs q hq with ⟨hcls, hlen, i, hi, rest, h⟩ | ⟨q', k, τ, t, r, h, hb⟩
  · refine .inl ⟨?_, ?_, i, hi, rest.map (·.rsub ρ), ?_⟩
    · obtain ⟨c, args⟩ := q
      cases c <;> simp_all [PPred.rsub, Cls.rsub]
    · obtain ⟨c, args⟩ := q
      cases c <;> simp_all [PPred.rsub, Cls.rsub, Cls.arity]
    · simp [PPred.rsub, h, PTy.rsub]
  · subst h
    obtain ⟨i, hi, x, hx, hb⟩ := hb
    refine .inr ⟨q'.rsub ρ, k.rsub ρ, τ.rsub ρ, t.rsub ρ, r.rsub ρ, by simp [PPred.rsub, Cls.rsub],
      i, by simpa [Scheme.rsub] using hi, x.rsub ρ, ?_, by simpa using hb.rsub hi ρ⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem Ty.field_rsub (ρ : RSubst) (l : String) :
    ∀ (ls : List String) (fs : List Ty),
      Ty.field l ls (fs.map (·.rsub ρ)) = (Ty.field l ls fs).map (·.rsub ρ)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, τ :: τs => by
    simp only [List.map_cons, Ty.field]
    split
    · rfl
    · exact Ty.field_rsub ρ l ls τs

theorem objSlots_rsub (ρ : RSubst) (L ls : List String) (ss : List Ty) :
    (objSlots L ls ss).map (·.rsub ρ) = objSlots L ls (ss.map (·.rsub ρ)) := by
  simp only [objSlots, List.map_map, ← List.map_reverse, Ty.field_rsub]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  generalize Ty.field l ls.reverse ss.reverse = o
  cases o <;> simp

theorem mergePreds_rsub (ρ : RSubst) : ∀ (ps ks τs ss rs : List Ty),
    (mergePreds ps ks τs ss rs).map (Pred.rsub ρ) =
      mergePreds (ps.map (·.rsub ρ)) (ks.map (·.rsub ρ)) (τs.map (·.rsub ρ))
        (ss.map (·.rsub ρ)) (rs.map (·.rsub ρ))
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs => by
    simp only [mergePreds, List.map_cons, ← mergePreds_rsub ρ ps ks τs ss rs]; rfl
  | [], _, _, _, _ | _ :: _, [], _, _, _ | _ :: _, _ :: _, [], _, _
  | _ :: _, _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, _ :: _, [] => by
    simp [mergePreds]

theorem slots3_rsub (ρ : RSubst) : ∀ (ps ks τs : List Ty),
    (slots3 ps ks τs).map (·.rsub ρ) =
      slots3 (ps.map (·.rsub ρ)) (ks.map (·.rsub ρ)) (τs.map (·.rsub ρ))
  | p :: ps, k :: ks, τ :: τs => by
    simp only [slots3, List.map_cons, slots3_rsub ρ ps ks τs]
    simp
  | [], _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] => by simp [slots3]

theorem PredEq.rsub (ρ : RSubst) {p q : Pred} (h : PredEq p q) : PredEq (p.rsub ρ) (q.rsub ρ) := by
  obtain ⟨hc, hl, hz⟩ := h
  refine ⟨by simp [Pred.rsub, hc], by simp [Pred.rsub, hl], fun x hx => ?_⟩
  simp only [Pred.rsub] at hx
  rw [List.zip_map] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact TyEq.rsub ρ (hz y hy)

theorem SlotCopy.rsub (ρ : RSubst) (h : SlotCopy s r) : SlotCopy (s.rsub ρ) (r.rsub ρ) := by
  cases h <;> simp <;> constructor

/-- A non-rigid constructor's head survives instantiating rigid type
variables. -/
theorem Ty.whnf_rsub_nr {ρ : RSubst} {T : Ty} {c : Con} {xs : List Ty} (h : T.whnf = .app c xs)
    (hc : c.isRigid = false) : (T.rsub ρ).whnf = .app c (xs.map (·.rsub ρ)) :=
  Ty.whnf_rsub_of_app h (Con.rimgA_none (Con.rimg_of_not_rigid hc) xs)

theorem Ty.tagOf_rsub (ρ : RSubst) {l : String} {R : Ty} {t : String} (h : R.tagOf l = some t) :
    (R.rsub ρ).tagOf l = some t := by
  unfold Ty.tagOf at h ⊢
  split at h
  · rename_i ls slots hR
    rw [Ty.whnf_rsub_nr hR rfl]
    simp only
    rw [Ty.field_rsub]
    split at h
    · rename_i s hs
      rw [hs]
      simp only [Option.map_some]
      split at h
      · rename_i p k τ hsw
        rw [Ty.whnf_rsub_nr hsw rfl]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_rsub_nr hp rfl, Ty.whnf_rsub_nr hk rfl]
          simp only [List.map_nil, and_self, ↓reduceIte]
          split at h
          · rename_i t' hτ
            rw [Ty.whnf_rsub_nr hτ rfl]
            simpa using h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem variantRest_rsub (ρ : RSubst) (d : Disc) (ts : List String) (Rs : List Ty) :
    (variantRest d ts Rs).rsub ρ = variantRest d ts (Rs.map (·.rsub ρ)) := by
  match Rs with
  | [] => simp [variantRest, Con.rimgA, Con.rimg]
  | [_] => rfl
  | _ :: _ :: _ => simp [variantRest, Con.rimgA]

theorem Ty.dataField_rsub (ρ : RSubst) {T : Ty} {l : String} {τ : Ty} (h : T.dataField l = some τ) :
    (T.rsub ρ).dataField l = some (τ.rsub ρ) := by
  unfold Ty.dataField at h ⊢
  split at h
  · rename_i ls slots hT
    rw [Ty.whnf_rsub_nr hT rfl]
    simp only
    rw [Ty.field_rsub]
    split at h
    · rename_i s hs
      rw [hs]
      simp only [Option.map_some]
      split at h
      · rename_i p k τ' hsw
        rw [Ty.whnf_rsub_nr hsw rfl]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_rsub_nr hp rfl, Ty.whnf_rsub_nr hk rfl]
          simp only [List.map_nil, and_self, ↓reduceIte]
          simp only [Option.some.injEq] at h ⊢
          rw [h]
        · cases h
      · cases h
    · cases h
  · cases h

theorem Ty.dataFields_rsub (ρ : RSubst) {T : Ty} : ∀ {ls : List String} {τs : List Ty},
    T.dataFields ls = some τs → (T.rsub ρ).dataFields ls = some (τs.map (·.rsub ρ))
  | [], τs, h => by
    simp only [Ty.dataFields, Option.some.injEq] at h ⊢
    subst h; rfl
  | l :: ls, τs, h => by
    simp only [Ty.dataFields] at h ⊢
    split at h
    · rename_i τ τs' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rw [Ty.dataField_rsub ρ h1, Ty.dataFields_rsub ρ h2]
      rfl
    · cases h

/-- The wide instances survive instantiating rigid type variables. -/
theorem ObjCase.rsub (ρ : RSubst) {ls : List String} {es : List Expr} {T P : Ty}
    (h : ObjCase ls es T P) : ObjCase ls es (T.rsub ρ) (P.rsub ρ) := by
  cases h with
  | self => exact .self
  | variant hw hl hi hP ht =>
    exact .variant (Ty.whnf_rsub_nr hw rfl) hl hi (by simp [hP]) (Ty.tagOf_rsub ρ ht)

theorem InstW.rsub (ρ : RSubst) {p : Pred} (h : InstW p) : InstW (p.rsub ρ) := by
  cases h with
  | narrow h hc =>
    cases h with
    | plusNumber => exact .narrow .plusNumber (by simp)
    | plusString => exact .narrow .plusString (by simp)
    | @hasProp l ls fs k σ hf =>
      have : Ty.field l ls (fs.map (·.rsub ρ)) = some (.slot .pre (k.rsub ρ) (σ.rsub ρ)) := by
        simp [Ty.field_rsub, hf]
      simpa [Pred.rsub] using InstW.narrow (Inst.hasProp this) (by simp)
    | mergeData => simpa [Pred.rsub] using InstW.narrow Inst.mergeData (by simp)
    | mergeGetter => simpa [Pred.rsub] using InstW.narrow Inst.mergeGetter (by simp)
    | mergeAbs hs => simpa [Pred.rsub] using InstW.narrow (Inst.mergeAbs (hs.rsub ρ)) (by simp)
    | mergeProto hs => simpa [Pred.rsub] using InstW.narrow (Inst.mergeProto (hs.rsub ρ)) (by simp)
    | lengthArray => simpa [Pred.rsub] using InstW.narrow Inst.lengthArray (by simp)
    | lengthString => simpa [Pred.rsub] using InstW.narrow Inst.lengthString (by simp)
    | indexArray => simpa [Pred.rsub] using InstW.narrow Inst.indexArray (by simp)
    | indexString => simpa [Pred.rsub] using InstW.narrow Inst.indexString (by simp)
    | writeArray => simpa [Pred.rsub] using InstW.narrow Inst.writeArray (by simp)
    | @notNew c args hn =>
      have hr : c.isRigid = false := by
        cases hc' : c.isRigid
        · rfl
        · exact absurd (.inr hc') hn
      simpa [Pred.rsub, Ty.rsub_app_nr hr] using
        InstW.narrow (Inst.notNew (c := c) (args := args.map (·.rsub ρ)) hn) (by simp)
    | injectSelf _ => exact absurd rfl (hc _)
    | injectNothing _ _ => exact absurd rfl (hc _)
    | injectSome _ _ _ _ _ => exact absurd rfl (hc _)
    | injectArm _ _ _ _ _ _ _ _ => exact absurd rfl (hc _)
    | stripSome => simpa [Pred.rsub] using InstW.narrow Inst.stripSome (by simp)
    | @stripSelf c args _ _ _ => simpa [Pred.rsub] using InstW.stripSelf (τ := (Ty.app c args).rsub ρ)
    | @caseHit ts i t Rs R d hn hi hR =>
      refine InstW.narrow ?_ (by simp [Pred.rsub, Cls.rsub])
      simpa [Pred.rsub, Cls.rsub, variantRest_rsub, ← eraseIdx_map, Ty.rsub_app, Con.rimgA,
        Con.rimg] using Inst.caseHit (d := d) (ts := ts) hn hi (by simp [hR])
  | injectSelf => simpa [Pred.rsub] using InstW.injectSelf
  | @injectNothing z σ =>
    have : z.ty.rsub ρ = z.ty := Nothing.ty_rsub ρ z
    simpa [Pred.rsub, this] using InstW.injectNothing (z := z) (σ := σ.rsub ρ)
  | injectSome => simpa [Pred.rsub] using InstW.injectSome
  | @injectArm Rs i R c xs t ts hR hw hc hi =>
    simpa [Pred.rsub, Ty.rsub_app, Con.rimgA, Con.rimg] using
      InstW.injectArm (Rs := Rs.map (·.rsub ρ)) (by simp [hR])
        (Ty.whnf_rsub_nr (ρ := ρ) hw (Con.isRigid_of_typeTag hc)) hc hi
  | stripSelf => simpa [Pred.rsub] using InstW.stripSelf

theorem InstEqW.rsub (ρ : RSubst) {p : Pred} (h : InstEqW p) : InstEqW (p.rsub ρ) := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.rsub ρ, hpq.rsub ρ, hq.rsub ρ⟩

theorem EntailsS.rsub (ρ : RSubst) {C : List Pred} {p : Pred} (h : EntailsS Sys.wide C p) :
    EntailsS Sys.wide (C.map (Pred.rsub ρ)) (p.rsub ρ) :=
  h.elim (fun h => .inl (InstEqW.rsub ρ h))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.rsub ρ, List.mem_map_of_mem hq, hpq.rsub ρ⟩)

/-- A system whose instances, expected types and injections survive
instantiating rigid type variables as `ρ` does. -/
structure Sys.RSubstable (S : Sys) (ρ : RSubst) : Prop where
  inst : ∀ {p : Pred}, S.inst p → S.inst (p.rsub ρ)
  closed : ∀ {T : Ty}, S.closed T → S.closed (T.rsub ρ)
  injPred : ∀ τ T, (S.injPred τ T).rsub ρ = S.injPred (τ.rsub ρ) (T.rsub ρ)

/-- The wide system holds whatever types the rigid type variables are. -/
theorem Sys.wide_rsubstable (ρ : RSubst) : Sys.wide.RSubstable ρ where
  inst := InstEqW.rsub ρ
  closed := fun _ => trivial
  injPred _ _ := by simp [Sys.wide, Pred.rsub, Cls.rsub]

theorem EntailsS.rsubS {S : Sys} {ρ : RSubst} (hS : S.RSubstable ρ) {C : List Pred} {p : Pred}
    (h : EntailsS S C p) : EntailsS S (C.map (Pred.rsub ρ)) (p.rsub ρ) :=
  h.elim (fun h => .inl (hS.inst h))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.rsub ρ, List.mem_map_of_mem hq, hpq.rsub ρ⟩)

theorem Ty.whnf_rsub_con {ρ : RSubst} {t : Ty} {c : Con} (h : t.whnf = .app c [])
    (hc : c.isRigid = false) : (t.rsub ρ).whnf = .app c [] := by
  simpa using Ty.whnf_rsub_of_app h (Con.rimgA_none (Con.rimg_of_not_rigid hc) [])

theorem Ty.SlotOnVar.rsub (ρ : RSubst) {s : Ty} (h : s.SlotOnVar) : (s.rsub ρ).SlotOnVar := by
  unfold Ty.SlotOnVar at h ⊢
  generalize hw : s.whnf = w at h
  match w, h with
  | .var a, _ => rw [Ty.whnf_rsub_var hw]; trivial
  | .slot p k τ, h =>
    rw [Ty.whnf_rsub_of_app hw (Con.rimgA_none rfl _)]
    simp only [List.map_cons, List.map_nil]
    rcases h with ⟨a, ha⟩ | ⟨hpre, a, ha⟩
    · exact .inl ⟨a, Ty.whnf_rsub_var ha⟩
    · exact .inr ⟨Ty.whnf_rsub_con hpre rfl, a, Ty.whnf_rsub_var ha⟩

theorem Pred.OnVar.rsub (ρ : RSubst) {p : Pred} (h : p.OnVar) : (p.rsub ρ).OnVar := by
  rcases h with ⟨t, a, rest, he, hw⟩ | hm
  · exact .inl ⟨t.rsub ρ, a, rest.map (·.rsub ρ), by simp [Pred.rsub, he], Ty.whnf_rsub_var hw⟩
  · right
    obtain ⟨c, args⟩ := p
    unfold Pred.MergeOnVar at hm
    split at hm
    · rename_i q k τ s r heq
      simp only [Pred.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Pred.rsub_mk_nr ρ (c := .merge) (by simp), List.map_cons, List.map_nil]
      unfold Pred.MergeOnVar
      rcases hm with ⟨hpre, a, ha⟩ | ⟨hqk, hsv⟩
      · exact .inl ⟨Ty.whnf_rsub_con hpre rfl, a, Ty.whnf_rsub_var ha⟩
      · refine .inr ⟨?_, hsv.rsub ρ⟩
        rcases hqk with ⟨hpre, hpro⟩ | habs
        · exact .inl ⟨Ty.whnf_rsub_con hpre rfl, Ty.whnf_rsub_con hpro rfl⟩
        · exact .inr (Ty.whnf_rsub_con habs rfl)
    · exact hm.elim

theorem HoldsOrVarW.rsub (ρ : RSubst) {C : List Pred} (h : HoldsOrVarW C) :
    HoldsOrVarW (C.map (Pred.rsub ρ)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).imp (InstEqW.rsub ρ) (Pred.OnVar.rsub ρ)

theorem FieldSlot.rsub (ρ : RSubst) (h : FieldSlot T k e τ s) :
    FieldSlot (T.rsub ρ) k e (τ.rsub ρ) (s.rsub ρ) := by
  cases h with
  | data => simpa using FieldSlot.data (T := T.rsub ρ) (e := e) (τ := τ.rsub ρ)
  | method he => simpa using FieldSlot.method (τs := _) (ρ := _) (he.rsub ρ)
  | getter he => simpa using FieldSlot.getter (σ := _) (he.rsub ρ)

theorem MemberSlotS.rsub {S : Sys} {ρ : RSubst} (hS : S.RSubstable ρ) (h : MemberSlotS S C T k e τ s) :
    MemberSlotS S (C.map (Pred.rsub ρ)) (T.rsub ρ) k e (τ.rsub ρ) (s.rsub ρ) := by
  cases h with
  | data =>
    simpa using MemberSlotS.data (S := S) (C := C.map (Pred.rsub ρ)) (T := T.rsub ρ) (e := e)
      (τ := τ.rsub ρ)
  | arrow he hn =>
    simpa using MemberSlotS.arrow (τs := _) (ρ := _) (he.rsub ρ)
      (by simpa using hn.rsubS hS)
  | method he => simpa using MemberSlotS.method (τs := _) (ρ := _) (he.rsub ρ)
  | getter he => simpa using MemberSlotS.getter (σ := _) (he.rsub ρ)

theorem memberCtx_rsub (ρ : RSubst) (Γ : Ctx) (ks : List ClassKind) (τs : List Ty)
    (i : Nat) (k : ClassKind) :
    (memberCtx Γ ks τs i k).map (Scheme.rsub ρ) =
      memberCtx (Γ.map (Scheme.rsub ρ)) ks (τs.map (·.rsub ρ)) i k := by
  cases k with
  | data =>
    simp only [memberCtx, List.map_append]
    congr 1
    rw [List.zip_map_right, ← List.map_take]
    generalize (ks.zip τs).take i = xs
    induction xs with
    | nil => rfl
    | cons p ps ih =>
      obtain ⟨k, τ⟩ := p
      cases k <;> simp_all [Scheme.mono_rsub]
  | _ => rfl


/-! ## Away from a type's rigid type variables -/

theorem RTy.rkeysL_eq (rs : List RTy) : RTy.rkeysL rs = rs.flatMap RTy.rkeys := by
  induction rs <;> simp_all [RTy.rkeysL]

theorem Ty.rkeysL_eq (τs : List Ty) : Ty.rkeysL τs = τs.flatMap Ty.rkeys := by
  induction τs <;> simp_all [Ty.rkeysL]

theorem PTy.rkeysL_eq (ps : List PTy) : PTy.rkeysL ps = ps.flatMap PTy.rkeys := by
  induction ps <;> simp_all [PTy.rkeysL]

/-- `ρ` has no image for the rigid type variables named in `ks`. -/
def RSubst.Off (ρ : RSubst) (ks : List Nat) : Prop := ∀ s ∈ ks, ∀ i, ρ s i = none

theorem RSubst.Off.mono {ρ : RSubst} {ks ks' : List Nat} (h : ρ.Off ks') (hk : ∀ s ∈ ks, s ∈ ks') :
    ρ.Off ks := fun s hs => h s (hk s hs)

theorem Con.rimg_off {ρ : RSubst} {c : Con} (h : ρ.Off c.rkeys) : c.rimg ρ = none := by
  cases c <;> simp_all [Con.rimg, Con.rkeys, RSubst.Off]

theorem RTy.rsub_off {ρ : RSubst} {r : RTy} (h : ρ.Off r.rkeys) : r.rsub ρ = r := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RSubst.Off, RTy.rkeys, RTy.rkeysL_eq, List.mem_append, List.mem_flatMap] at h
    rw [RTy.rsub_app_none (Con.rimgA_none (Con.rimg_off fun s hs => h s (.inl hs)) _)]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp fun s hs => h s (.inr ⟨p, hp, hs⟩)).trans
      (List.map_id _)
  | mu i sys ih =>
    simp only [RSubst.Off, RTy.rkeys, RTy.rkeysL_eq, List.mem_flatMap] at h
    rw [RTy.rsub_mu]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp fun s hs => h s ⟨p, hp, hs⟩).trans
      (List.map_id _)

theorem Ty.rsub_off {ρ : RSubst} {τ : Ty} (h : ρ.Off τ.rkeys) : τ.rsub ρ = τ := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [RSubst.Off, Ty.rkeys, Ty.rkeysL_eq, List.mem_append, List.mem_flatMap] at h
    rw [Ty.rsub_app_none (Con.rimgA_none (Con.rimg_off fun s hs => h s (.inl hs)) _)]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp fun s hs => h s (.inr ⟨p, hp, hs⟩)).trans
      (List.map_id _)
  | mu i sys =>
    simp only [RSubst.Off, Ty.rkeys, RTy.rkeysL_eq, List.mem_flatMap] at h
    rw [Ty.rsub_mu]
    congr 1
    exact (List.map_congr_left fun p hp => RTy.rsub_off fun s hs => h s ⟨p, hp, hs⟩).trans
      (List.map_id _)

theorem PTy.rsub_off {ρ : RSubst} {p : PTy} (h : ρ.Off p.rkeys) : p.rsub ρ = p := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RSubst.Off, PTy.rkeys, PTy.rkeysL_eq, List.mem_append, List.mem_flatMap] at h
    rw [PTy.rsub_app, Con.rimgA_none (Con.rimg_off fun s hs => h s (.inl hs))]
    dsimp only
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp fun s hs => h s (.inr ⟨p, hp, hs⟩)).trans
      (List.map_id _)
  | mu i sys ih =>
    simp only [RSubst.Off, PTy.rkeys, PTy.rkeysL_eq, List.mem_flatMap] at h
    rw [PTy.rsub_mu]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp fun s hs => h s ⟨p, hp, hs⟩).trans
      (List.map_id _)

theorem Cls.rsub_off {ρ : RSubst} {c : Cls} (h : ρ.Off c.rkeys) : c.rsub ρ = c := by
  cases c <;> simp_all [Cls.rsub, Cls.rkeys, Ty.rsub_off]

theorem Pred.rsub_off {ρ : RSubst} {p : Pred} (h : ρ.Off p.rkeys) : p.rsub ρ = p := by
  obtain ⟨c, args⟩ := p
  simp only [RSubst.Off, Pred.rkeys, Ty.rkeysL_eq, List.mem_append, List.mem_flatMap] at h
  simp only [Pred.rsub, Pred.mk.injEq]
  exact ⟨Cls.rsub_off fun s hs => h s (.inl hs),
    (List.map_congr_left fun τ hτ => Ty.rsub_off fun s hs => h s (.inr ⟨τ, hτ, hs⟩)).trans
      (List.map_id _)⟩

theorem PPred.rsub_off {ρ : RSubst} {p : PPred} (h : ρ.Off p.rkeys) : p.rsub ρ = p := by
  obtain ⟨c, args⟩ := p
  simp only [RSubst.Off, PPred.rkeys, PTy.rkeysL_eq, List.mem_append, List.mem_flatMap] at h
  simp only [PPred.rsub, PPred.mk.injEq]
  exact ⟨Cls.rsub_off fun s hs => h s (.inl hs),
    (List.map_congr_left fun τ hτ => PTy.rsub_off fun s hs => h s (.inr ⟨τ, hτ, hs⟩)).trans
      (List.map_id _)⟩

theorem Scheme.rsub_off {ρ : RSubst} {s : Scheme} (h : ρ.Off s.rkeys) : s.rsub ρ = s := by
  obtain ⟨n, b, ps⟩ := s
  simp only [RSubst.Off, Scheme.rkeys, List.mem_append, List.mem_flatMap] at h
  simp only [Scheme.rsub, Scheme.mk.injEq, true_and]
  exact ⟨PTy.rsub_off fun s hs => h s (.inl hs),
    (List.map_congr_left fun p hp => PPred.rsub_off fun s hs => h s (.inr ⟨p, hp, hs⟩)).trans
      (List.map_id _)⟩

theorem Scheme.rsub_of_rkeys_nil (ρ : RSubst) {s : Scheme} (h : s.rkeys = []) : s.rsub ρ = s :=
  Scheme.rsub_off (by simp [RSubst.Off, h])

theorem ctx_rsub_off {ρ : RSubst} {Γ : Ctx} (h : ρ.Off (ctxRkeys Γ)) : Γ.map (Scheme.rsub ρ) = Γ :=
  (List.map_congr_left fun s hs => Scheme.rsub_off fun k hk =>
    h k (List.mem_flatMap.mpr ⟨s, hs, hk⟩)).trans (List.map_id _)

theorem preds_rsub_off {ρ : RSubst} {C : List Pred} (h : ρ.Off (C.flatMap Pred.rkeys)) :
    C.map (Pred.rsub ρ) = C :=
  (List.map_congr_left fun p hp => Pred.rsub_off fun k hk =>
    h k (List.mem_flatMap.mpr ⟨p, hp, hk⟩)).trans (List.map_id _)

theorem ret_rsub_off {ρ : RSubst} {R : Option Ty} (h : ρ.Off (Ret.rkeys R)) :
    R.map (·.rsub ρ) = R := by
  cases R with
  | none => rfl
  | some τ => simpa using Ty.rsub_off (by simpa [Ret.rkeys] using h)

/-- Rigid type variables without an image stay. -/
theorem rigids_rsub {ρ : RSubst} {k : Nat} (h : ∀ i, ρ k i = none) (n : Nat) :
    (rigids k n).map (·.rsub ρ) = rigids k n := by
  simp [rigids, Con.rimgA, Con.rimg, h]

/-- The instantiation of the rigid type variables named `k` at `τs`. -/
def RSubst.at (k : Nat) (τs : List Ty) : RSubst := fun s i => if s = k then τs[i]? else none

theorem rigids_rsub_at (k : Nat) (τs : List Ty) :
    (rigids k τs.length).map (·.rsub (RSubst.at k τs)) = τs := by
  apply List.ext_getElem (by simp [rigids])
  intro i h₁ h₂
  simp [rigids, Con.rimgA, Con.rimg, RSubst.at, List.getElem?_eq_getElem h₂]

theorem RSubst.at_off {k : Nat} {τs : List Ty} {ks : List Nat} (h : k ∉ ks) : (RSubst.at k τs).Off ks :=
  fun s hs i => by
    have : s ≠ k := fun e => h (e ▸ hs)
    simp [RSubst.at, this]

/-- Instantiating rigid type variables in a derivation, in a system that
survives it (`Sys.RSubstable`): the wide system holds whatever types they
are. A polymorphic binding's initialiser is typed at fresh rigid type
variables (`letPoly`), whose names `ρ` leaves (it has images only for names
in `D`). -/
theorem HasTypeS.rsub {S : Sys} {ρ : RSubst} (hS : S.RSubstable ρ) (D : List Nat)
    (hD : ∀ s i τ, ρ s i = some τ → s ∈ D) (h : HasTypeS S L C Γ R rm md e τ) :
    HasTypeS S L (C.map (Pred.rsub ρ)) (Γ.map (Scheme.rsub ρ)) (R.map (·.rsub ρ)) rm md e
      (τ.rsub ρ) := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen hc =>
    rw [← Scheme.inst_rsub]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa using hlen) ?_
    intro c hc'
    rw [Scheme.instPreds_rsub] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).rsubS hS
  | func hlen _ ih =>
    refine .func (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_rsub] using ih
  | @funcCheck T n C Γ θ τs ρ' body R rm hT hT₀ hlen _ ih =>
    refine .funcCheck (Ty.whnf_rsub_of_app hT (by simp [Con.rimgA])) (hS.closed hT₀) (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_rsub] using ih
  | app _ hlen _ ihf iha =>
    refine .app (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    refine .let_ (s.rsub ρ) F (fun m hm => ?_) ?_ (hs.rsub ρ) ?_ (by simpa using ih₂)
    · rw [Scheme.open_rsub, Scheme.openPreds_rsub, ← List.map_append]
      exact ih₁ m hm
    · simpa [Scheme.rsub] using hv
    · intro a h
      obtain ⟨rfl, h'⟩ := ha a h
      rw [Scheme.rsub_of_rkeys_nil ρ h'.2.2.2]
      exact ⟨rfl, h'⟩
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ =>
    have ha : a.rsub ρ = a := Scheme.rsub_of_rkeys_nil ρ hr
    refine .letPoly a (K ++ D) h0 hp hf hr (fun k hk => ?_) hv hw (by simpa [ha] using ih₂)
    have hk' : ∀ i, ρ k i = none := fun i => by
      cases hρ : ρ k i with
      | none => rfl
      | some τ => exact absurd (List.mem_append.mpr (.inr (hD k i τ hρ))) hk
    have := ih₁ k (fun h => hk (List.mem_append.mpr (.inl h)))
    rwa [← Scheme.inst_rsub, ha, rigids_rsub hk'] at this
  | assign hi ha hp _ ih =>
    rw [← Scheme.inst_rsub]
    refine .assign (by simp [List.getElem?_map, hi]) (by simpa using ha)
      (by simp [Scheme.rsub, hp]) ?_
    simpa [← Scheme.inst_rsub] using ih
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih =>
    cases hop with
    | not => exact .unop .not ih
    | typeof => exact .unop .typeof ih
    | neg => exact .unop .neg ih
  | binop hop _ _ ih₁ ih₂ =>
    cases hop with
    | plus hc => exact .binop (.plus (by simpa [Pred.rsub] using hc.rsubS hS)) ih₁ ih₂
    | num h =>
      rw [show ∀ o : BinOp, o.resTy.rsub ρ = o.resTy from fun o => by cases o <;> rfl]
      exact .binop (.num h) ih₁ ih₂
    | strictEq => exact .binop .strictEq ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb (by simpa [Scheme.mono_rsub] using ihh)
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ =>
    exact .unwrap ih₁ (by simpa [Pred.rsub] using hs.rsubS hS) ih₂
      (by simpa [Scheme.mono_rsub] using ih₃)
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf
  | @obj _ _ _ _ _ _ _ _ τs hes hks hτs hss hL _ hm ih =>
    simp only [Ty.rsub_record, objSlots_rsub]
    refine .obj (τs := τs.map (·.rsub ρ)) hes hks (by simpa using hτs) (by simpa using hss) hL
      (fun p hp => ?_) (fun x hx => ?_)
    · rw [List.zip_map_right] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
    · rw [zip4_map] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).rsub ρ
      simpa [Ty.rsub_record, objSlots_rsub] using this
  | @cls _ _ _ τs _ _ _ _ _ hes hks hτs hss hnd hL _ hm ih =>
    simp only [Ty.rsub_record, objSlots_rsub]
    refine .cls (τs := τs.map (·.rsub ρ)) hes hks (by simpa using hτs) (by simpa using hss) hnd hL
      (fun i e k τ he hk hτ => ?_) (fun x hx => ?_)
    · rw [List.getElem?_map] at hτ
      obtain ⟨τ₀, hτ₀, rfl⟩ := Option.map_eq_some_iff.mp hτ
      have := ih i e k τ₀ he hk hτ₀
      rw [memberCtx_rsub] at this
      simpa using this
    · rw [zip4_map] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).rsub hS
      simpa [Ty.rsub_record, objSlots_rsub] using this
  | ctor hlen _ ih =>
    refine .ctor (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_rsub] using ih
  | new_ _ hlen _ hρ hss ihf iha =>
    refine .new_ (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_)
      (by simpa using hρ.rsub ρ) (by simpa using hss)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | get _ hp ih => exact .get ih (by simpa [Pred.rsub] using hp.rsubS hS)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa [Pred.rsub] using hp.rsubS hS) ihv
  | @spread _ _ _ _ _ _ _ ps ks τs _ hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    simp only [Ty.rsub_record] at ih₁ ih₂ ⊢
    refine .spread (ps := ps.map (·.rsub ρ)) (ks := ks.map (·.rsub ρ)) (τs := τs.map (·.rsub ρ))
      (by simpa using hps) (by simpa using hks) (by simpa using hτs) (by simpa using hss)
      (by simpa using hrs) ih₁ ?_ (fun p hp => ?_)
    · simpa [slots3_rsub] using ih₂
    · rw [← mergePreds_rsub] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hm q hq).rsubS hS
  | arr _ ih => exact .arr ih
  | arrCheck hT hT₀ _ ih =>
    exact .arrCheck (Ty.whnf_rsub_of_app hT (by simp [Con.rimgA])) (hS.closed hT₀)
      (fun e he => by simpa using ih e he)
  | index _ _ hp ihe ihi => exact .index ihe ihi (by simpa [Pred.rsub] using hp.rsubS hS)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    exact .setIndex ihe ihi (by simpa [Pred.rsub] using hp.rsubS hS)
      (by simpa [Pred.rsub] using hw.rsubS hS) ihv
  | mcall _ hp hlen _ ihe iha =>
    refine .mcall ihe (by simpa [Pred.rsub] using hp.rsubS hS) (by simpa using hlen)
      (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | conv _ he ih => exact .conv ih (he.rsub ρ)
  | inj _ hT hi ih => exact .inj ih (hS.closed hT) (by rw [← hS.injPred]; exact hi.rsubS hS)
  | drop _ ih => exact .drop ih
  | litStr hw => exact .litStr (Ty.whnf_rsub_nr hw rfl)
  | objCheck hc hn hk hl hL hd he _ ih =>
    refine .objCheck (hc.rsub ρ) hn hk hl hL (Ty.dataFields_rsub ρ hd) ?_ (fun p hp => ?_)
    · simpa [objSlots_rsub, List.map_map, Function.comp_def] using he.rsub ρ
    · rw [List.zip_map_right] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ =>
    exact .caseTag ih₁ (by simpa [Pred.rsub, Cls.rsub] using hc.rsubS hS)
      (by simpa [Scheme.mono_rsub] using ih₂) (by simpa [Scheme.mono_rsub] using ih₃)

end Inty
