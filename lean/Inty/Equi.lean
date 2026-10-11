import Inty.Subst

/-!
# Equi-recursive type equality

A recursive type `mu i sys` is the type its equation's right-hand side
gives, with each `self j` read as `mu j sys`: unfolding it yields an equal
type, as in inty, where unification unrolls a `Type::Named` against a
structural type (`InferState::unroll_named`). Two types are equal
(`TyEq`) when they unfold to the same infinite tree. That tree is given by
its finite approximations (`Ty.approx n`, the tree cut at depth `n`), which
makes the equality an equivalence closed under substitution and taken apart
by constructors (`TyEq.app_iff`), with no coinduction (Amadio and
Cardelli, TOPLAS 1993; Brandt and Henglein, Fundamenta Informaticae 1998,
treat it coinductively).

An equation whose right-hand side is a bare `self` (`t = t`) has no head
(`Ty.view` is `none`): such a type equals only other such types, and has
no values.
-/

namespace Inty

mutual
/-- A right-hand side as a type, with `self j` read as `env j`. -/
def RTy.open (env : Nat → Ty) : RTy → Ty
  | .free a => .var a
  | .self j => env j
  | .app c args => .app c (RTy.opens env args)
  | .mu i sys => .mu i sys
def RTy.opens (env : Nat → Ty) : List RTy → List Ty
  | [] => []
  | r :: rs => r.open env :: RTy.opens env rs
end

@[simp] theorem RTy.opens_eq (env : Nat → Ty) (rs : List RTy) :
    RTy.opens env rs = rs.map (RTy.open env) := by
  induction rs <;> simp_all [RTy.opens]

@[simp] theorem RTy.open_app (env : Nat → Ty) (c : Con) (args : List RTy) :
    (RTy.app c args).open env = .app c (args.map (RTy.open env)) := by simp [RTy.open]

/-- What a system's `self j` stand for: its own types. -/
def muEnv (sys : List RTy) (j : Nat) : Ty := .mu j sys

/-- The head of a right-hand side whose `self j` stand for `env j`: a type
variable, or a constructor applied to types; none for a bare `self`. A
nested system's is its own type's. -/
def RTy.head (env : Nat → Ty) : RTy → Option Ty
  | .free a => some (.var a)
  | .self _ => none
  | .app c args => some (.app c (args.map (RTy.open env)))
  | .mu i sys =>
    match _h : sys[i]? with
    | some r => RTy.head (muEnv sys) r
    | none => none
termination_by r => sizeOf r
decreasing_by
  have := List.sizeOf_lt_of_mem (List.mem_of_getElem? _h); simp; omega

theorem RTy.head_mu (env : Nat → Ty) (i : Nat) (sys : List RTy) :
    (RTy.mu i sys).head env = sys[i]?.bind (RTy.head (muEnv sys)) := by
  rw [RTy.head]
  split <;> simp_all

/-- A type's head, unfolding recursive types: a type variable or a
constructor applied to types, or none for a recursive type with no head. -/
def Ty.view : Ty → Option Ty
  | .var a => some (.var a)
  | .app c args => some (.app c args)
  | .mu i sys => sys[i]?.bind (RTy.head (muEnv sys))

/-- A type with its head unfolded, if it has one. -/
def Ty.whnf (τ : Ty) : Ty := τ.view.getD τ

/-- Finite trees: the approximations of the infinite tree a type unfolds
to. -/
inductive Tree where
  | bot
  | var (a : Nat)
  | node (c : Con) (ts : List Tree)

/-- The tree a type unfolds to, cut at depth `n`. -/
def Ty.approx : Nat → Ty → Tree
  | 0, _ => .bot
  | n + 1, τ =>
    match τ.view with
    | some (.var a) => .var a
    | some (.app c args) => .node c (args.map (Ty.approx n))
    | _ => .bot

/-- Equi-recursive type equality: the two types unfold to the same tree. -/
def TyEq (s t : Ty) : Prop := ∀ n, s.approx n = t.approx n

theorem TyEq.refl (τ : Ty) : TyEq τ τ := fun _ => rfl
theorem TyEq.symm {s t : Ty} (h : TyEq s t) : TyEq t s := fun n => (h n).symm
theorem TyEq.trans {s t u : Ty} (h₁ : TyEq s t) (h₂ : TyEq t u) : TyEq s u :=
  fun n => (h₁ n).trans (h₂ n)
theorem TyEq.of_eq {s t : Ty} (h : s = t) : TyEq s t := h ▸ TyEq.refl s

/-! ## Heads -/

@[simp] theorem RTy.open_toRTy (env : Nat → Ty) (τ : Ty) : τ.toRTy.open env = τ := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.open_app, List.map_map, Ty.app.injEq, true_and]
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left ih
  | mu i sys => rfl

/-- A type's head is that of its right-hand side. -/
theorem RTy.head_toRTy (env : Nat → Ty) (τ : Ty) : τ.toRTy.head env = τ.view := by
  cases τ with
  | var a => simp [Ty.toRTy, RTy.head, Ty.view]
  | app c args =>
    simp only [Ty.toRTy_app, Ty.view]
    rw [RTy.head]
    simp [Function.comp_def]
  | mu i sys => simp [Ty.toRTy, RTy.head_mu, Ty.view]

/-- A head is a variable or a constructor applied to types. -/
theorem RTy.head_shape {env : Nat → Ty} {r : RTy} {t : Ty} (h : r.head env = some t) :
    (∃ a, t = .var a) ∨ ∃ c args, t = .app c args := by
  induction r using RTy.ind generalizing env t with
  | free a => simp [RTy.head] at h; exact .inl ⟨a, h.symm⟩
  | self j => simp [RTy.head] at h
  | app c args _ => rw [RTy.head] at h; cases h; exact .inr ⟨_, _, rfl⟩
  | mu i sys ih =>
    rw [RTy.head_mu, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    exact ih r (List.mem_of_getElem? hr) h

theorem Ty.view_shape {τ t : Ty} (h : τ.view = some t) :
    (∃ a, t = .var a) ∨ ∃ c args, t = .app c args := by
  cases τ with
  | var a => simp [Ty.view] at h; exact .inl ⟨a, h.symm⟩
  | app c args => simp [Ty.view] at h; exact .inr ⟨c, args, h.symm⟩
  | mu i sys =>
    simp only [Ty.view, Option.bind_eq_some_iff] at h
    obtain ⟨r, -, h⟩ := h
    exact RTy.head_shape h

theorem Ty.view_of_shape {t : Ty}
    (h : (∃ a, t = .var a) ∨ ∃ c args, t = .app c args) : t.view = some t := by
  rcases h with ⟨a, rfl⟩ | ⟨c, args, rfl⟩ <;> rfl

theorem Ty.view_whnf (τ : Ty) : τ.whnf.view = τ.view := by
  unfold Ty.whnf
  cases h : τ.view with
  | none => simp [h]
  | some t => simpa using Ty.view_of_shape (Ty.view_shape h)

/-- The approximation one level down depends only on the head. -/
theorem Ty.approx_succ (n : Nat) (τ : Ty) : τ.approx (n + 1) =
    match τ.view with
    | some (.var a) => .var a
    | some (.app c args) => .node c (args.map (Ty.approx n))
    | _ => .bot := by
  rw [Ty.approx]

theorem Ty.approx_congr_view {n : Nat} {s t : Ty} (h : s.view = t.view) :
    s.approx n = t.approx n := by
  cases n with
  | zero => rfl
  | succ n => rw [Ty.approx_succ, Ty.approx_succ, h]

/-- Unfolding a type's head gives an equal type. -/
theorem TyEq.whnf (τ : Ty) : TyEq τ.whnf τ := fun _ => Ty.approx_congr_view (Ty.view_whnf τ)

@[simp] theorem Ty.whnf_app (c : Con) (args : List Ty) : (Ty.app c args).whnf = .app c args := rfl
@[simp] theorem Ty.whnf_var (a : Nat) : (Ty.var a).whnf = .var a := rfl

theorem RTy.open_ftv {env : Nat → Ty} {r : RTy} {a : Nat} (h : a ∈ (r.open env).ftv) :
    a ∈ r.ftv ∨ ∃ j, a ∈ (env j).ftv := by
  induction r using RTy.ind with
  | free b => simp [RTy.open] at h; simp [RTy.ftv, h]
  | self j => exact .inr ⟨j, by simpa [RTy.open] using h⟩
  | app c args ih =>
    simp only [RTy.open_app, Ty.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases ih q hq h with h | h
    · exact .inl (by simp only [RTy.ftv_app, List.mem_flatMap]; exact ⟨q, hq, h⟩)
    · exact .inr h
  | mu i sys _ => exact .inl (by simpa [RTy.open] using h)

theorem RTy.head_ftv {env : Nat → Ty} {r : RTy} {t : Ty} {a : Nat} (h : r.head env = some t)
    (ha : a ∈ t.ftv) : a ∈ r.ftv ∨ ∃ j, a ∈ (env j).ftv := by
  induction r using RTy.ind generalizing env t with
  | free b => simp [RTy.head] at h; subst h; simp [RTy.ftv] at ha ⊢; exact .inl ha
  | self j => simp [RTy.head] at h
  | app c args _ =>
    rw [RTy.head] at h; cases h
    simp only [Ty.ftv_app, List.mem_flatMap, List.mem_map] at ha
    obtain ⟨_, ⟨q, hq, rfl⟩, ha⟩ := ha
    rcases RTy.open_ftv ha with h | h
    · exact .inl (by simp only [RTy.ftv_app, List.mem_flatMap]; exact ⟨q, hq, h⟩)
    · exact .inr h
  | mu i sys ih =>
    rw [RTy.head_mu, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hmem := List.mem_of_getElem? hr
    refine .inl ?_
    simp only [RTy.ftv_mu, List.mem_flatMap]
    rcases ih r hmem h ha with h | ⟨j, h⟩
    · exact ⟨r, hmem, h⟩
    · simpa [muEnv] using h

/-- Unfolding brings no new variables. -/
theorem Ty.view_ftv {τ t : Ty} (h : τ.view = some t) : ∀ a ∈ t.ftv, a ∈ τ.ftv := by
  intro a ha
  cases τ with
  | var b => simp [Ty.view] at h; subst h; exact ha
  | app c args => simp [Ty.view] at h; subst h; exact ha
  | mu i sys =>
    simp only [Ty.view, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hmem := List.mem_of_getElem? hr
    simp only [Ty.ftv_mu, List.mem_flatMap]
    rcases RTy.head_ftv h ha with h | ⟨j, h⟩
    · exact ⟨r, hmem, h⟩
    · simpa [muEnv] using h

theorem Ty.whnf_ftv {τ : Ty} {a : Nat} (h : a ∈ τ.whnf.ftv) : a ∈ τ.ftv := by
  unfold Ty.whnf at h
  cases hv : τ.view with
  | none => simpa [hv] using h
  | some t => simp only [hv, Option.getD_some] at h; exact Ty.view_ftv hv a h

/-! ## Constructors -/

theorem forall₂_of_map_eq {f g : Nat → Ty → Tree} :
    ∀ {ts ts' : List Ty}, (∀ n, ts.map (f n) = ts'.map (g n)) →
      ts.length = ts'.length ∧ ∀ p ∈ ts.zip ts', ∀ n, f n p.1 = g n p.2
  | [], [], _ => ⟨rfl, by simp⟩
  | [], _ :: _, h => by simpa using h 0
  | _ :: _, [], h => by simpa using h 0
  | t :: ts, t' :: ts', h => by
    have h' : ∀ n, ts.map (f n) = ts'.map (g n) := fun n => by
      have := h n; simp only [List.map_cons, List.cons.injEq] at this; exact this.2
    obtain ⟨hl, hz⟩ := forall₂_of_map_eq h'
    refine ⟨by simp [hl], fun p hp n => ?_⟩
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have := h n; simp only [List.map_cons, List.cons.injEq] at this; exact this.1
    · exact hz p hp n

theorem map_eq_of_forall₂ {f g : Ty → Tree} :
    ∀ {ts ts' : List Ty}, ts.length = ts'.length → (∀ p ∈ ts.zip ts', f p.1 = g p.2) →
      ts.map f = ts'.map g
  | [], [], _, _ => rfl
  | t :: ts, t' :: ts', hl, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (t, t') (by simp), map_eq_of_forall₂ (by simpa using hl)
      (fun p hp => h p (by simp [hp]))⟩

/-- Two constructor applications are equal when the constructors are and
their arguments pairwise are. -/
theorem TyEq.app_iff {c c' : Con} {ts ts' : List Ty} :
    TyEq (.app c ts) (.app c' ts') ↔
      c = c' ∧ ts.length = ts'.length ∧ ∀ p ∈ ts.zip ts', TyEq p.1 p.2 := by
  constructor
  · intro h
    have h₁ := h (0 + 1)
    simp only [Ty.approx_succ, Ty.view, Tree.node.injEq] at h₁
    refine ⟨h₁.1, ?_⟩
    have := forall₂_of_map_eq (f := fun n => Ty.approx n) (g := fun n => Ty.approx n)
      (ts := ts) (ts' := ts') (fun n => by
        have := h (n + 1)
        simp only [Ty.approx_succ, Ty.view, Tree.node.injEq] at this
        exact this.2)
    exact ⟨this.1, fun p hp n => this.2 p hp n⟩
  · rintro ⟨rfl, hl, h⟩ n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Ty.approx_succ, Ty.view]
      rw [map_eq_of_forall₂ hl (fun p hp => h p hp n)]

theorem TyEq.app {c : Con} {ts ts' : List Ty} (hl : ts.length = ts'.length)
    (h : ∀ p ∈ ts.zip ts', TyEq p.1 p.2) : TyEq (.app c ts) (.app c ts') :=
  TyEq.app_iff.mpr ⟨rfl, hl, h⟩

/-- A type equal to a constructor application unfolds to one. -/
theorem TyEq.view_app {τ : Ty} {c : Con} {ts : List Ty} (h : TyEq τ (.app c ts)) :
    ∃ ts', τ.view = some (.app c ts') ∧ TyEq (.app c ts') (.app c ts) := by
  have h₁ := h (0 + 1)
  rw [Ty.approx_succ, Ty.approx_succ] at h₁
  cases hv : τ.view with
  | none => rw [hv] at h₁; simp [Ty.view] at h₁
  | some t =>
    rw [hv] at h₁
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c', ts', rfl⟩
    · simp [Ty.view] at h₁
    · simp only [Ty.view, Tree.node.injEq] at h₁
      obtain ⟨rfl, -⟩ := h₁
      refine ⟨ts', rfl, ?_⟩
      have := TyEq.whnf τ
      simp only [Ty.whnf, hv, Option.getD_some] at this
      exact this.trans h

/-- A type equal to a variable unfolds to it. -/
theorem TyEq.view_var {τ : Ty} {a : Nat} (h : TyEq τ (.var a)) : τ.view = some (.var a) := by
  have h₁ := h (0 + 1)
  rw [Ty.approx_succ, Ty.approx_succ] at h₁
  cases hv : τ.view with
  | none => rw [hv] at h₁; simp [Ty.view] at h₁
  | some t =>
    rw [hv] at h₁
    rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c', ts', rfl⟩
    · simp only [Ty.view, Tree.var.injEq] at h₁; rw [h₁]
    · simp [Ty.view] at h₁

theorem TyEq.var_app {a : Nat} {c : Con} {ts : List Ty} : ¬ TyEq (.var a) (.app c ts) := by
  intro h
  have := h (0 + 1)
  rw [Ty.approx_succ, Ty.approx_succ] at this
  simp [Ty.view] at this

/-! ## Substitution -/

/-- `t` with `f` grafted at its variables: a variable `a` at remaining depth
`m` becomes `f a m`. -/
def Tree.graft (f : Nat → Nat → Tree) : Nat → Tree → Tree
  | 0, _ => .bot
  | _ + 1, .bot => .bot
  | n + 1, .var a => f a (n + 1)
  | n + 1, .node c ts => .node c (ts.map (Tree.graft f n))

theorem RTy.open_subst (σ : Subst) (env : Nat → Ty) (r : RTy) :
    (r.subst σ).open (fun j => (env j).subst σ) = (r.open env).subst σ := by
  induction r using RTy.ind with
  | free a => simp [RTy.subst, RTy.open, Ty.subst]
  | self j => rfl
  | app c args ih =>
    simp only [RTy.subst_app, RTy.open_app, List.map_map, Ty.subst_app, Ty.app.injEq, true_and]
    exact List.map_congr_left ih
  | mu i sys _ => simp [RTy.open]

theorem muEnv_subst (σ : Subst) (sys : List RTy) :
    muEnv (sys.map (·.subst σ)) = fun j => (muEnv sys j).subst σ := by
  funext j; simp [muEnv]

/-- Substitution and heads: a variable's head becomes its image's. -/
theorem RTy.head_subst (σ : Subst) (r : RTy) (env : Nat → Ty) :
    (r.subst σ).head (fun j => (env j).subst σ) = (r.head env).bind (fun t => (t.subst σ).view) := by
  induction r using RTy.ind generalizing env with
  | free a =>
    simp only [RTy.subst, RTy.head_toRTy]
    simp [RTy.head, Ty.subst]
  | self j => simp [RTy.subst, RTy.head]
  | app c args _ =>
    simp only [RTy.subst_app]
    rw [RTy.head, RTy.head]
    simp [Ty.view, List.map_map, Function.comp_def, RTy.open_subst]
  | mu i sys ih =>
    simp only [RTy.subst_mu, RTy.head_mu, List.getElem?_map]
    cases hr : sys[i]? with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [muEnv_subst]
      exact ih r (List.mem_of_getElem? hr) (muEnv sys)

theorem Ty.view_subst (σ : Subst) (τ : Ty) :
    (τ.subst σ).view = τ.view.bind (fun t => (t.subst σ).view) := by
  have := RTy.head_subst σ τ.toRTy (fun _ => .undefined)
  rw [Ty.toRTy_subst, RTy.head_toRTy, RTy.head_toRTy] at this
  exact this

theorem Ty.approx_subst (σ : Subst) :
    ∀ (n : Nat) (τ : Ty),
      (τ.subst σ).approx n = (τ.approx n).graft (fun a m => ((Ty.var a).subst σ).approx m) n
  | 0, _ => rfl
  | _ + 1, τ => by
    rw [Ty.approx_succ, Ty.approx_succ, Ty.view_subst]
    cases hv : τ.view with
    | none => rfl
    | some t =>
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · simp only [Option.bind_some, Tree.graft]
        rw [← Ty.approx_succ]
      · simp only [Option.bind_some, Ty.subst_app, Ty.view, Tree.graft, List.map_map]
        congr 1
        exact List.map_congr_left (fun a _ => Ty.approx_subst σ _ a)

/-- Equal types stay equal through substitution. -/
theorem TyEq.subst (σ : Subst) {s t : Ty} (h : TyEq s t) : TyEq (s.subst σ) (t.subst σ) :=
  fun n => by rw [Ty.approx_subst, Ty.approx_subst, h n]

/-! ## Constraints -/

/-- Two constraints of one class on pairwise equal types. -/
def PredEq (p q : Pred) : Prop :=
  p.cls = q.cls ∧ p.args.length = q.args.length ∧ ∀ x ∈ p.args.zip q.args, TyEq x.1 x.2

theorem zip_self_tyEq : ∀ (l : List Ty), ∀ x ∈ l.zip l, TyEq x.1 x.2
  | [], _, hx => by cases hx
  | y :: ys, x, hx => by
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact TyEq.refl y
    · exact zip_self_tyEq ys x hx

theorem PredEq.refl (p : Pred) : PredEq p p := ⟨rfl, rfl, zip_self_tyEq p.args⟩

theorem PredEq.subst (σ : Subst) {p q : Pred} (h : PredEq p q) :
    PredEq (p.subst σ) (q.subst σ) := by
  obtain ⟨hc, hl, hz⟩ := h
  refine ⟨hc, by simp [Pred.subst, hl], fun x hx => ?_⟩
  simp only [Pred.subst] at hx
  rw [List.zip_map] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact TyEq.subst σ (hz y hy)

/-- The arguments of equal constraints, two at a time. -/
theorem PredEq.args {c c' : Cls} {xs ys : List Ty} (h : PredEq ⟨c, xs⟩ ⟨c', ys⟩) :
    c = c' ∧ xs.length = ys.length ∧ ∀ x ∈ xs.zip ys, TyEq x.1 x.2 := h

theorem PredEq.symm {p q : Pred} (h : PredEq p q) : PredEq q p := by
  obtain ⟨hc, hl, hz⟩ := h
  refine ⟨hc.symm, hl.symm, fun x hx => ?_⟩
  obtain ⟨a, b⟩ := x
  have : (b, a) ∈ p.args.zip q.args := by
    rw [List.mem_iff_getElem] at hx ⊢
    obtain ⟨i, hi, e⟩ := hx
    simp only [List.getElem_zip, Prod.mk.injEq, List.length_zip] at e hi ⊢
    exact ⟨i, by omega, e.2, e.1⟩
  exact (hz _ this).symm

theorem PredEq.one {c c' : Cls} {a a' : Ty} (h : PredEq ⟨c, [a]⟩ ⟨c', [a']⟩) :
    c = c' ∧ TyEq a a' :=
  ⟨h.1, h.2.2 (a, a') (by simp)⟩

theorem PredEq.two {c c' : Cls} {a b a' b' : Ty} (h : PredEq ⟨c, [a, b]⟩ ⟨c', [a', b']⟩) :
    c = c' ∧ TyEq a a' ∧ TyEq b b' :=
  ⟨h.1, h.2.2 (a, a') (by simp), h.2.2 (b, b') (by simp)⟩

theorem PredEq.three {c c' : Cls} {a b d a' b' d' : Ty}
    (h : PredEq ⟨c, [a, b, d]⟩ ⟨c', [a', b', d']⟩) :
    c = c' ∧ TyEq a a' ∧ TyEq b b' ∧ TyEq d d' :=
  ⟨h.1, h.2.2 (a, a') (by simp), h.2.2 (b, b') (by simp), h.2.2 (d, d') (by simp)⟩

theorem PredEq.four {c c' : Cls} {a b d e a' b' d' e' : Ty}
    (h : PredEq ⟨c, [a, b, d, e]⟩ ⟨c', [a', b', d', e']⟩) :
    c = c' ∧ TyEq a a' ∧ TyEq b b' ∧ TyEq d d' ∧ TyEq e e' :=
  ⟨h.1, h.2.2 (a, a') (by simp), h.2.2 (b, b') (by simp), h.2.2 (d, d') (by simp),
    h.2.2 (e, e') (by simp)⟩

theorem PredEq.five {c c' : Cls} {a b d e f a' b' d' e' f' : Ty}
    (h : PredEq ⟨c, [a, b, d, e, f]⟩ ⟨c', [a', b', d', e', f']⟩) :
    c = c' ∧ TyEq a a' ∧ TyEq b b' ∧ TyEq d d' ∧ TyEq e e' ∧ TyEq f f' :=
  ⟨h.1, h.2.2 (a, a') (by simp), h.2.2 (b, b') (by simp), h.2.2 (d, d') (by simp),
    h.2.2 (e, e') (by simp), h.2.2 (f, f') (by simp)⟩

/-- A constraint equal to one with the shape of an instance has that shape
up to its arguments. -/
theorem PredEq.args_length {c c' : Cls} {xs ys : List Ty} (h : PredEq ⟨c, xs⟩ ⟨c', ys⟩) :
    xs.length = ys.length := h.2.1

/-! ## Constructors of equal types -/

theorem TyEq.con {c c' : Con} {ts ts' : List Ty} (h : TyEq (.app c ts) (.app c' ts')) :
    c = c' := (TyEq.app_iff.mp h).1

theorem TyEq.slot {p k σ p' k' σ' : Ty} (h : TyEq (.slot p k σ) (.slot p' k' σ')) :
    TyEq p p' ∧ TyEq k k' ∧ TyEq σ σ' := by
  obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp h
  exact ⟨hz (p, p') (by simp), hz (k, k') (by simp), hz (σ, σ') (by simp)⟩

theorem TyEq.slot_mk {p k σ p' k' σ' : Ty} (hp : TyEq p p') (hk : TyEq k k') (hσ : TyEq σ σ') :
    TyEq (.slot p k σ) (.slot p' k' σ') :=
  TyEq.app rfl (fun x hx => by
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hk
    · exact hσ)

theorem TyEq.pre_abs : ¬ TyEq .pre .abs := fun h => by cases TyEq.con h

/-- Distinct constants are distinct types. -/
theorem TyEq.con_ne {c c' : Con} (hc : c ≠ c') : ¬ TyEq (.app c []) (.app c' []) :=
  fun h => hc (TyEq.con h)

theorem TyEq.array_inj {σ σ' : Ty} (h : TyEq (.array σ) (.array σ')) : TyEq σ σ' := by
  obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp h
  exact hz (σ, σ') (by simp)

/-! ## Bisimulation

Two types are equal when a relation holding of them is a bisimulation:
related types have the same head, their arguments related. Up to equality:
a related pair may stand for an equal pair of that shape. -/

/-- `s` and `t` have one head, their arguments related by `R`. -/
def Matched (R : Ty → Ty → Prop) (s t : Ty) : Prop :=
  (s.view = none ∧ t.view = none) ∨
  (∃ a, s.view = some (.var a) ∧ t.view = some (.var a)) ∨
  (∃ c xs ys, s.view = some (.app c xs) ∧ t.view = some (.app c ys) ∧
    xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, R p.1 p.2)

/-- A pair `R` relates is equal, or equal to a pair with one head whose
arguments `R` relates. -/
def BisimStep (R : Ty → Ty → Prop) (s t : Ty) : Prop :=
  TyEq s t ∨ ∃ s' t', TyEq s s' ∧ TyEq t t' ∧ Matched R s' t'

theorem map_approx_eq_of_zip {n : Nat} : ∀ {xs ys : List Ty}, xs.length = ys.length →
    (∀ p ∈ xs.zip ys, p.1.approx n = p.2.approx n) → xs.map (Ty.approx n) = ys.map (Ty.approx n)
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (x, y) (by simp), map_approx_eq_of_zip (by simpa using hl)
      (fun p hp => h p (by simp [hp]))⟩

theorem mem_zip_self {α : Type} : ∀ {l : List α} {y z : α}, (y, z) ∈ l.zip l → y = z ∧ y ∈ l
  | [], _, _, h => by cases h
  | w :: ws, y, z, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨rfl, List.mem_cons_self⟩
    · exact (mem_zip_self h).imp id (List.mem_cons_of_mem _)

/-- Bisimulation up to equality: what a bisimulation relates is equal. -/
theorem TyEq.of_bisim (R : Ty → Ty → Prop) (h : ∀ s t, R s t → BisimStep R s t) :
    ∀ s t, R s t → TyEq s t := by
  suffices ∀ n s t, R s t → s.approx n = t.approx n from fun s t hr n => this n s t hr
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro s t hr
    rcases h s t hr with he | ⟨s', t', hs, ht, hm⟩
    · exact he (n + 1)
    rw [hs (n + 1), ht (n + 1), Ty.approx_succ, Ty.approx_succ]
    rcases hm with ⟨h₁, h₂⟩ | ⟨a, h₁, h₂⟩ | ⟨c, xs, ys, h₁, h₂, hl, hz⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂]
    · rw [h₁, h₂]
      simp only [Tree.node.injEq, true_and]
      exact map_approx_eq_of_zip hl (fun p hp => ih p.1 p.2 (hz p hp))

/-- Substitutions that give equal types for a type's variables give it equal
types. -/
theorem Ty.subst_tyEq_congr {σ σ' : Subst} {τ : Ty}
    (h : ∀ a ∈ τ.ftv, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    TyEq (τ.subst σ) (τ.subst σ') := by
  refine TyEq.of_bisim (fun x y => ∃ t : Ty, (∀ a ∈ t.ftv, a ∈ τ.ftv) ∧ x = t.subst σ ∧
    y = t.subst σ') (fun x y hr => ?_) _ _ ⟨τ, fun _ h => h, rfl, rfl⟩
  obtain ⟨t, ht, rfl, rfl⟩ := hr
  cases hv : t.view with
  | none =>
    right
    refine ⟨t.subst σ, t.subst σ', TyEq.refl _, TyEq.refl _, .inl ⟨?_, ?_⟩⟩ <;>
      rw [Ty.view_subst, hv] <;> rfl
  | some v =>
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, xs, rfl⟩
    · left
      have hw : TyEq t (.var a) := by
        have := TyEq.whnf t; simp only [Ty.whnf, hv, Option.getD_some] at this; exact this.symm
      exact (hw.subst σ).trans ((h a (ht a (Ty.view_ftv hv a (by simp)))).trans
        (hw.subst σ').symm)
    · have hw : TyEq t (.app c xs) := by
        have := TyEq.whnf t; simp only [Ty.whnf, hv, Option.getD_some] at this; exact this.symm
      right
      refine ⟨(Ty.app c xs).subst σ, (Ty.app c xs).subst σ', hw.subst σ, hw.subst σ',
        .inr (.inr ⟨c, xs.map (·.subst σ), xs.map (·.subst σ'), by simp [Ty.view],
          by simp [Ty.view], by simp, fun p hp => ?_⟩)⟩
      rw [List.zip_map] at hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y, z⟩ := x
      obtain ⟨rfl, hy⟩ := mem_zip_self hx
      refine ⟨y, fun a ha => ht a (Ty.view_ftv hv a ?_), rfl, rfl⟩
      simp only [Ty.ftv_app, List.mem_flatMap]
      exact ⟨y, hy, ha⟩


end Inty
