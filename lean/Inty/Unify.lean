import Inty.Equi

/-!
# Unification up to unfolding, by congruence closure

Two types are unified as the finite graphs their unfoldings are: every type
has finitely many subterms up to unfolding (`Ty.subs`), so unification is a
congruence closure on them (Huet's algorithm for rational trees). The
subterms of both types are the nodes, labelled by class; classes are merged
for the two types, for each recursive type and its unfolding, and for the
arguments of two constructor applications already in one class. When no
merge is left, each class must have one head. The unifier binds each
variable to its class read as a recursive type: one equation per class, a
constructor class's equation being its constructor applied to its
arguments' classes (`unifySubst`). It is most general up to `TyEq`
(`unify_mgu`), and sound (`unify_sound`).
-/

namespace Inty

@[simp] theorem Ty.toRTy_ftv (τ : Ty) : τ.toRTy.ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.ftv_app, List.flatMap_map, Ty.ftv_app]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih
  | mu i sys => simp [Ty.toRTy]

/-! ## Subterms -/

mutual
/-- The subterms of the right-hand side `r` of an equation of `sys`, each
read as a type (`self j` as `mu j sys`). -/
def RTy.subsIn (sys : List RTy) : RTy → List Ty
  | .free a => [.var a]
  | .self j => [.mu j sys]
  | .app c rs => .app c (rs.map (RTy.open (muEnv sys))) :: RTy.subsInL sys rs
  | .mu i sys' =>
    .mu i sys' :: ((List.range sys'.length).map (Ty.mu · sys') ++ RTy.subsInL sys' sys')
def RTy.subsInL (sys : List RTy) : List RTy → List Ty
  | [] => []
  | r :: rs => RTy.subsIn sys r ++ RTy.subsInL sys rs
end

mutual
/-- A type's subterms, up to unfolding: a recursive type's include its
system's other types and its equations' subterms. -/
def Ty.subs : Ty → List Ty
  | .var a => [.var a]
  | .app c args => .app c args :: Ty.subsL args
  | .mu i sys => .mu i sys :: ((List.range sys.length).map (Ty.mu · sys) ++ RTy.subsInL sys sys)
def Ty.subsL : List Ty → List Ty
  | [] => []
  | t :: ts => t.subs ++ Ty.subsL ts
end

/-- A node's successors in the graph: a constructor's arguments, a recursive
type's unfolding. -/
def Ty.kids (τ : Ty) : List Ty :=
  match τ with
  | .var _ => []
  | .app _ args => args
  | .mu _ _ =>
    match τ.view with
    | some v => [v]
    | none => []

/-! ## The graph -/

/-- The nodes: both types' subterms. -/
def nodes (τ₁ τ₂ : Ty) : List Ty := (τ₁.subs ++ τ₂.subs).eraseDups

/-- A node's index. -/
def nodeIdx (ns : List Ty) (x : Ty) : Nat := ns.idxOf x

/-- The node at index `i`. -/
def node (ns : List Ty) (i : Nat) : Ty := ns.getD i (.var 0)

/-- The class of node `i`. -/
def labOf (lab : List Nat) (i : Nat) : Nat := lab.getD i i

def Ty.isVar : Ty → Bool
  | .var _ => true
  | _ => false

def Ty.isApp : Ty → Bool
  | .app _ _ => true
  | _ => false

/-- A constructor application's constructor and number of arguments. -/
def Ty.headCon : Ty → Option (Con × Nat)
  | .app c args => some (c, args.length)
  | _ => none

/-- A type with no head (`Ty.view` is `none`). -/
def Ty.headless (τ : Ty) : Bool := τ.view.isNone

/-- The first constructor node of class `ℓ`. -/
def firstApp (ns : List Ty) (lab : List Nat) (ℓ : Nat) : Option Nat :=
  (List.range ns.length).find? fun f => labOf lab f == ℓ && (node ns f).isApp

/-- The pairs merged first: the two types, and each recursive type with its
unfolding. -/
def genPairs (ns : List Ty) (i₁ i₂ : Nat) : List (Nat × Nat) :=
  (i₁, i₂) :: (List.range ns.length).filterMap fun i =>
    match node ns i with
    | .mu j sys =>
      match (Ty.mu j sys).view with
      | some v => some (i, nodeIdx ns v)
      | none => none
    | _ => none

/-- The pairs congruence merges: each constructor node's arguments with its
class's first constructor node's, when they have one constructor. -/
def congPairs (ns : List Ty) (lab : List Nat) : List (Nat × Nat) :=
  (List.range ns.length).flatMap fun i =>
    match firstApp ns lab (labOf lab i) with
    | some f =>
      if (node ns f).headCon = (node ns i).headCon then
        ((node ns f).kids.map (nodeIdx ns)).zip ((node ns i).kids.map (nodeIdx ns))
      else []
    | none => []

/-- A pair still to merge. -/
def pending (ns : List Ty) (gens : List (Nat × Nat)) (lab : List Nat) : Option (Nat × Nat) :=
  (gens ++ congPairs ns lab).find? fun p => labOf lab p.1 != labOf lab p.2

/-- Merge the classes of `p` and `q`. -/
def merge (lab : List Nat) (p q : Nat) : List Nat :=
  lab.map fun l => if l = labOf lab q then labOf lab p else l

/-- Merge until nothing is pending, with `fuel` merges. -/
def closeLoop (ns : List Ty) (gens : List (Nat × Nat)) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | k + 1, lab =>
    match pending ns gens lab with
    | none => some lab
    | some (p, q) => closeLoop ns gens k (merge lab p q)

/-- Each class has one head: its constructor nodes one constructor, and no
headless node beside one. -/
def consistent (ns : List Ty) (lab : List Nat) : Bool :=
  (List.range ns.length).all fun i =>
    match firstApp ns lab (labOf lab i) with
    | some f =>
      match node ns i with
      | .app c args => (node ns f).headCon == some (c, args.length)
      | t => !t.headless
    | none => true

/-! ## The substitution -/

/-- Whether class `ℓ` has a headless node. -/
def hasHeadless (ns : List Ty) (lab : List Nat) (ℓ : Nat) : Bool :=
  (List.range ns.length).any fun i => labOf lab i == ℓ && (node ns i).headless

/-- A class of type variables only (and recursive types unfolding to them). -/
def varOnly (ns : List Ty) (lab : List Nat) (ℓ : Nat) : Bool :=
  (firstApp ns lab ℓ).isNone && !hasHeadless ns lab ℓ

/-- The variable a class of variables stands for: its last (the second
type's, which the first's is bound to). -/
def classVar (ns : List Ty) (lab : List Nat) (ℓ : Nat) : Nat :=
  match (List.range ns.length).reverse.find? (fun i => labOf lab i == ℓ && (node ns i).isVar) with
  | some i =>
    match node ns i with
    | .var a => a
    | _ => 0
  | none => 0

/-- A reference to a node's class in the system. -/
def classRef (ns : List Ty) (lab : List Nat) (x : Ty) : RTy :=
  let ℓ := labOf lab (nodeIdx ns x)
  if varOnly ns lab ℓ then .free (classVar ns lab ℓ) else .self ℓ

/-- The equation of node `j`'s class: its first constructor node's
constructor applied to its arguments' classes, or none (a headless class,
or one never used). -/
def classEq (ns : List Ty) (lab : List Nat) (j : Nat) : RTy :=
  match firstApp ns lab (labOf lab j) with
  | some f =>
    match node ns f with
    | .app c args => .app c (args.map (classRef ns lab))
    | _ => .self j
  | none => .self j

/-- The system of the classes' equations, one per node. -/
def classSys (ns : List Ty) (lab : List Nat) : List RTy :=
  (List.range ns.length).map (classEq ns lab)

/-- The type class `ℓ` stands for. -/
def classTy (ns : List Ty) (lab : List Nat) (ℓ : Nat) : Ty :=
  if varOnly ns lab ℓ then .var (classVar ns lab ℓ) else .mu ℓ (classSys ns lab)

/-- A type with its recursive types unfolded, except where one is reached
again inside itself (`seen`): the unifier's types are recursive only
where they must be. -/
def unroll : Nat → List Nat → Ty → Ty
  | 0, _, τ => τ
  | k + 1, seen, .mu ℓ sys =>
    if ℓ ∈ seen then .mu ℓ sys
    else
      match (Ty.mu ℓ sys).view with
      | some (.app c xs) => .app c (xs.map (unroll k (ℓ :: seen)))
      | some (.var a) => .var a
      | _ => .mu ℓ sys
  | k + 1, seen, .app c xs => .app c (xs.map (unroll k seen))
  | _ + 1, _, .var a => .var a

/-- The type `unifySubst` binds a variable node to: its class's. -/
def nodeVal (ns : List Ty) (lab : List Nat) (x : Ty) : Ty :=
  unroll (ns.length + 1) [] (classTy ns lab (labOf lab (nodeIdx ns x)))

/-- Each variable among the nodes bound to its class's type. -/
def unifySubst (ns : List Ty) (lab : List Nat) : Subst :=
  ns.filterMap fun x =>
    match x with
    | .var a => some (a, nodeVal ns lab (.var a))
    | _ => none

/-- Unify two types up to unfolding. -/
def unify (τ₁ τ₂ : Ty) : Option Subst :=
  let ns := nodes τ₁ τ₂
  let gens := genPairs ns (nodeIdx ns τ₁) (nodeIdx ns τ₂)
  match closeLoop ns gens (ns.length + 1) (List.range ns.length) with
  | none => none
  | some lab => if consistent ns lab then some (unifySubst ns lab) else none


/-! ## The subterms are closed -/

@[simp] theorem RTy.subsInL_eq (sys rs : List RTy) :
    RTy.subsInL sys rs = rs.flatMap (RTy.subsIn sys) := by
  induction rs <;> simp_all [RTy.subsInL]

@[simp] theorem Ty.subsL_eq (ts : List Ty) : Ty.subsL ts = ts.flatMap Ty.subs := by
  induction ts <;> simp_all [Ty.subsL]

theorem Ty.mem_subs_self (τ : Ty) : τ ∈ τ.subs := by
  cases τ <;> simp [Ty.subs]

theorem RTy.open_mem_subsIn (sys : List RTy) (r : RTy) : r.open (muEnv sys) ∈ r.subsIn sys := by
  cases r <;> simp [RTy.open, RTy.subsIn, muEnv]

/-- A right-hand side's head, its `self`s read in its system, is among its
subterms. -/
theorem RTy.head_mem_subsIn {r : RTy} : ∀ {sys : List RTy} {v : Ty},
    r.head (muEnv sys) = some v → v ∈ r.subsIn sys := by
  induction r using RTy.ind with
  | free a => intro sys v h; simp [RTy.head] at h; subst h; simp [RTy.subsIn]
  | self j => intro sys v h; simp [RTy.head] at h
  | app c rs _ => intro sys v h; rw [RTy.head] at h; cases h; simp [RTy.subsIn]
  | mu i sys' ih =>
    intro sys v h
    rw [RTy.head_mu, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hm := List.mem_of_getElem? hr
    simp only [RTy.subsIn, RTy.subsInL_eq, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_flatMap]
    exact .inr (.inr ⟨r, hm, ih r hm h⟩)

/-- A recursive type's unfolding is among its system's subterms. -/
theorem Ty.kids_mu_mem {j : Nat} {sys : List RTy} {U : List Ty}
    (hU : ∀ x ∈ RTy.subsInL sys sys, x ∈ U) : ∀ y ∈ (Ty.mu j sys).kids, y ∈ U := by
  intro y hy
  simp only [Ty.kids] at hy
  split at hy
  · rename_i v hv
    simp only [List.mem_singleton] at hy; subst hy
    simp only [Ty.view, Option.bind_eq_some_iff] at hv
    obtain ⟨r, hr, h⟩ := hv
    exact hU _ (by simpa using ⟨r, List.mem_of_getElem? hr, RTy.head_mem_subsIn h⟩)
  · cases hy

theorem RTy.subsIn_closed {r : RTy} : ∀ {sys : List RTy} {U : List Ty},
    (∀ x ∈ RTy.subsInL sys sys, x ∈ U) → (∀ x ∈ r.subsIn sys, x ∈ U) →
      ∀ x ∈ r.subsIn sys, ∀ y ∈ x.kids, y ∈ U := by
  induction r using RTy.ind with
  | free a => intro sys U _ _ x hx y hy; simp [RTy.subsIn] at hx; subst hx; simp [Ty.kids] at hy
  | self j =>
    intro sys U hsys _ x hx
    simp [RTy.subsIn] at hx; subst hx
    exact Ty.kids_mu_mem hsys
  | app c rs ih =>
    intro sys U hsys hsub x hx y hy
    simp only [RTy.subsIn, RTy.subsInL_eq, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with rfl | ⟨r, hr, hx⟩
    · simp only [Ty.kids, List.mem_map] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      exact hsub _ (by
        simp only [RTy.subsIn, RTy.subsInL_eq, List.mem_cons, List.mem_flatMap]
        exact .inr ⟨r, hr, RTy.open_mem_subsIn sys r⟩)
    · exact ih r hr hsys (fun x' hx' => hsub x' (by
        simp only [RTy.subsIn, RTy.subsInL_eq, List.mem_cons, List.mem_flatMap]
        exact .inr ⟨r, hr, hx'⟩)) x hx y hy
  | mu i sys' ih =>
    intro sys U _ hsub x hx y hy
    have hsys' : ∀ x ∈ RTy.subsInL sys' sys', x ∈ U := fun x' hx' => hsub x' (by
      simp only [RTy.subsIn, List.mem_cons, List.mem_append]; exact .inr (.inr hx'))
    simp only [RTy.subsIn, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨j, -, rfl⟩ | hx
    · exact Ty.kids_mu_mem hsys' y hy
    · exact Ty.kids_mu_mem hsys' y hy
    · simp only [RTy.subsInL_eq, List.mem_flatMap] at hx
      obtain ⟨r, hr, hx⟩ := hx
      exact ih r hr hsys' (fun x' hx' => hsys' x' (by simpa using ⟨r, hr, hx'⟩)) x hx y hy

/-- A subterm's successors are subterms. -/
theorem Ty.subs_closed (τ : Ty) : ∀ x ∈ τ.subs, ∀ y ∈ x.kids, y ∈ τ.subs := by
  induction τ using Ty.ind with
  | var a => intro x hx y hy; simp [Ty.subs] at hx; subst hx; simp [Ty.kids] at hy
  | app c args ih =>
    intro x hx y hy
    simp only [Ty.subs, Ty.subsL_eq, List.mem_cons, List.mem_flatMap] at hx ⊢
    rcases hx with rfl | ⟨t, ht, hx⟩
    · exact .inr ⟨y, by simpa [Ty.kids] using hy, Ty.mem_subs_self y⟩
    · exact .inr ⟨t, ht, ih t ht x hx y hy⟩
  | mu i sys =>
    intro x hx y hy
    have hsys : ∀ x ∈ RTy.subsInL sys sys, x ∈ (Ty.mu i sys).subs := fun x' hx' => by
      simp only [Ty.subs, List.mem_cons, List.mem_append]; exact .inr (.inr hx')
    simp only [Ty.subs, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨j, -, rfl⟩ | hx
    · exact Ty.kids_mu_mem hsys y hy
    · exact Ty.kids_mu_mem hsys y hy
    · simp only [RTy.subsInL_eq, List.mem_flatMap] at hx
      obtain ⟨r, hr, hx⟩ := hx
      exact RTy.subsIn_closed hsys (fun x' hx' => hsys x' (by simpa using ⟨r, hr, hx'⟩)) x hx y hy

/-! ### Variables of subterms -/

theorem RTy.subsIn_ftv {r : RTy} : ∀ {sys : List RTy} {x : Ty}, x ∈ r.subsIn sys →
    ∀ a ∈ x.ftv, a ∈ r.ftv ∨ a ∈ sys.flatMap RTy.ftv := by
  induction r using RTy.ind with
  | free b => intro sys x hx a ha; simp [RTy.subsIn] at hx; subst hx; simp_all [RTy.ftv]
  | self j =>
    intro sys x hx a ha; simp [RTy.subsIn] at hx; subst hx; exact .inr (by simpa using ha)
  | app c rs ih =>
    intro sys x hx a ha
    simp only [RTy.subsIn, RTy.subsInL_eq, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with rfl | ⟨r, hr, hx⟩
    · rcases RTy.open_ftv (env := muEnv sys) (r := .app c rs) (by simpa using ha) with h | ⟨j, h⟩
      · exact .inl h
      · exact .inr (by simpa [muEnv] using h)
    · rcases ih r hr hx a ha with h | h
      · exact .inl (by simp only [RTy.ftv_app, List.mem_flatMap]; exact ⟨r, hr, h⟩)
      · exact .inr h
  | mu i sys' ih =>
    intro sys x hx a ha
    left
    simp only [RTy.ftv_mu, List.mem_flatMap]
    simp only [RTy.subsIn, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨j, -, rfl⟩ | hx
    · simpa using ha
    · simpa using ha
    · simp only [RTy.subsInL_eq, List.mem_flatMap] at hx
      obtain ⟨r, hr, hx⟩ := hx
      rcases ih r hr hx a ha with h | h
      · exact ⟨r, hr, h⟩
      · simpa using h

/-- A subterm's variables are the type's. -/
theorem Ty.subs_ftv {τ : Ty} : ∀ {x : Ty}, x ∈ τ.subs → ∀ a ∈ x.ftv, a ∈ τ.ftv := by
  induction τ using Ty.ind with
  | var b => intro x hx a ha; simp [Ty.subs] at hx; subst hx; exact ha
  | app c args ih =>
    intro x hx a ha
    simp only [Ty.subs, Ty.subsL_eq, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with rfl | ⟨t, ht, hx⟩
    · exact ha
    · simp only [Ty.ftv_app, List.mem_flatMap]; exact ⟨t, ht, ih t ht hx a ha⟩
  | mu i sys =>
    intro x hx a ha
    simp only [Ty.subs, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨j, -, rfl⟩ | hx
    · exact ha
    · simpa using ha
    · simp only [RTy.subsInL_eq, List.mem_flatMap] at hx
      obtain ⟨r, hr, hx⟩ := hx
      simp only [Ty.ftv_mu, List.mem_flatMap]
      rcases RTy.subsIn_ftv hx a ha with h | h
      · exact ⟨r, hr, h⟩
      · simpa using h

/-! ## Labels -/

theorem labOf_lt_len {lab : List Nat} {i : Nat} (h : i < lab.length) : labOf lab i = lab[i] := by
  simp [labOf, List.getD, List.getElem?_eq_getElem h]

theorem labOf_merge {lab : List Nat} {p q i : Nat} (h : i < lab.length) :
    labOf (merge lab p q) i =
      if labOf lab i = labOf lab q then labOf lab p else labOf lab i := by
  have h' : i < (merge lab p q).length := by simpa [merge] using h
  rw [labOf_lt_len h', labOf_lt_len h]
  simp [merge]

@[simp] theorem merge_length (lab : List Nat) (p q : Nat) : (merge lab p q).length = lab.length := by
  simp [merge]

/-- Labels name a node of their class: each node's label is below `n`, and
labelled by itself. -/
def Canon (n : Nat) (lab : List Nat) : Prop :=
  lab.length = n ∧ ∀ i < n, labOf lab i < n ∧ labOf lab (labOf lab i) = labOf lab i

theorem Canon.range (n : Nat) : Canon n (List.range n) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have : labOf (List.range n) i = i := by simp [labOf, List.getD, hi]
  rw [this, this]; exact ⟨hi, rfl⟩

theorem Canon.merge {n : Nat} {lab : List Nat} {p q : Nat} (h : Canon n lab) (hp : p < n)
    (hq : q < n) : Canon n (merge lab p q) := by
  obtain ⟨hl, hc⟩ := h
  refine ⟨by simp [hl], fun i hi => ?_⟩
  have hi' : i < lab.length := hl ▸ hi
  rw [labOf_merge hi']
  obtain ⟨hpl, hpc⟩ := hc p hp
  obtain ⟨hql, hqc⟩ := hc q hq
  obtain ⟨hil, hic⟩ := hc i hi
  split
  · rename_i hiq
    refine ⟨hpl, ?_⟩
    rw [labOf_merge (hl ▸ hpl), hpc]
    split <;> rfl
  · rename_i hiq
    refine ⟨hil, ?_⟩
    rw [labOf_merge (hl ▸ hil), hic, ite_eq_right_iff.mpr (fun h => absurd h hiq)]

/-- The number of nodes labelled by themselves: one per class. -/
def roots (n : Nat) (lab : List Nat) : Nat := (List.range n).countP fun i => labOf lab i == i

theorem countP_one_less {P Q : Nat → Bool} : ∀ {l : List Nat} {b : Nat}, l.Nodup → b ∈ l →
    P b = true → Q b = false → (∀ x ∈ l, x ≠ b → P x = Q x) → l.countP P = l.countP Q + 1
  | [], _, _, hb, _, _, _ => by cases hb
  | x :: xs, b, hnd, hb, hP, hQ, hPQ => by
    simp only [List.nodup_cons] at hnd
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · have : xs.countP P = xs.countP Q :=
        List.countP_congr (fun y hy => by
          rw [hPQ y (List.mem_cons_of_mem _ hy) (fun e => hnd.1 (e ▸ hy))])
      simp [hP, hQ, this]
    · have hx : x ≠ b := fun e => hnd.1 (e ▸ hb')
      rw [countP_one_less hnd.2 hb' hP hQ (fun y hy hyb => hPQ y (List.mem_cons_of_mem _ hy) hyb),
        hPQ x List.mem_cons_self hx]
      split <;> omega

theorem roots_merge {n : Nat} {lab : List Nat} {p q : Nat} (h : Canon n lab) (hp : p < n)
    (hq : q < n) (hne : labOf lab p ≠ labOf lab q) : roots n (merge lab p q) + 1 = roots n lab := by
  obtain ⟨hl, hc⟩ := h
  obtain ⟨hql, hqc⟩ := hc q hq
  obtain ⟨hpl, hpc⟩ := hc p hp
  unfold roots
  refine (countP_one_less (b := labOf lab q) List.nodup_range (List.mem_range.mpr hql)
    (by simp [hqc]) ?_ (fun x hx hxb => ?_)).symm
  · rw [labOf_merge (hl ▸ hql), hqc]; simp [hne]
  · have hx' := List.mem_range.mp hx
    rw [labOf_merge (hl ▸ hx')]
    split
    · rename_i h
      obtain ⟨-, hxc⟩ := hc x hx'
      have h1 : labOf lab x ≠ x := fun e => hxb (by rw [← e, h])
      have h2 : labOf lab p ≠ x := fun e => hne (by rw [← h, ← e, hpc])
      rw [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2]
    · rfl

/-! ## Nodes -/

theorem node_mem {ns : List Ty} {i : Nat} (h : i < ns.length) : node ns i ∈ ns := by
  simp [node, List.getD, List.getElem?_eq_getElem h]

theorem nodeIdx_lt {ns : List Ty} {x : Ty} (h : x ∈ ns) : nodeIdx ns x < ns.length :=
  List.idxOf_lt_length_iff.mpr h

theorem node_nodeIdx {ns : List Ty} {x : Ty} (h : x ∈ ns) : node ns (nodeIdx ns x) = x := by
  have hl := nodeIdx_lt h
  simp only [node, List.getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.getElem_idxOf hl

theorem firstApp_some {ns : List Ty} {lab : List Nat} {ℓ f : Nat} (h : firstApp ns lab ℓ = some f) :
    f < ns.length ∧ labOf lab f = ℓ ∧ (node ns f).isApp = true := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_range.mp hm, hp.1, hp.2⟩

theorem firstApp_none {ns : List Ty} {lab : List Nat} {ℓ : Nat} (h : firstApp ns lab ℓ = none)
    {f : Nat} (hf : f < ns.length) (hl : labOf lab f = ℓ) : (node ns f).isApp = false := by
  have := List.find?_eq_none.mp h f (List.mem_range.mpr hf)
  simpa [hl] using this

/-- A class with a constructor node has a first one. -/
theorem firstApp_of_app {ns : List Ty} {lab : List Nat} {i : Nat} (hi : i < ns.length)
    (ha : (node ns i).isApp = true) : ∃ f, firstApp ns lab (labOf lab i) = some f := by
  cases h : firstApp ns lab (labOf lab i) with
  | some f => exact ⟨f, rfl⟩
  | none => rw [firstApp_none h hi rfl] at ha; cases ha

/-- The nodes are closed under successors. -/
def KidsClosed (ns : List Ty) : Prop := ∀ x ∈ ns, ∀ y ∈ x.kids, y ∈ ns

theorem nodes_closed (τ₁ τ₂ : Ty) : KidsClosed (nodes τ₁ τ₂) := by
  intro x hx y hy
  simp only [nodes, List.mem_eraseDups, List.mem_append] at hx ⊢
  exact hx.imp (fun h => Ty.subs_closed τ₁ x h y hy) (fun h => Ty.subs_closed τ₂ x h y hy)

theorem mem_nodes_left (τ₁ τ₂ : Ty) : τ₁ ∈ nodes τ₁ τ₂ := by
  simp [nodes, Ty.mem_subs_self]

theorem mem_nodes_right (τ₁ τ₂ : Ty) : τ₂ ∈ nodes τ₁ τ₂ := by
  simp [nodes, Ty.mem_subs_self]

theorem nodes_ftv {τ₁ τ₂ x : Ty} (hx : x ∈ nodes τ₁ τ₂) : ∀ a ∈ x.ftv, a ∈ τ₁.ftv ∨ a ∈ τ₂.ftv := by
  intro a ha
  simp only [nodes, List.mem_eraseDups, List.mem_append] at hx
  exact hx.imp (fun h => Ty.subs_ftv h a ha) (fun h => Ty.subs_ftv h a ha)

/-! ## The merge loop -/

/-- Pairs of nodes. -/
def PairsIn (n : Nat) (ps : List (Nat × Nat)) : Prop := ∀ p ∈ ps, p.1 < n ∧ p.2 < n

theorem congPairs_in {ns : List Ty} (hk : KidsClosed ns) (lab : List Nat) :
    PairsIn ns.length (congPairs ns lab) := by
  intro pq hpq
  simp only [congPairs, List.mem_flatMap, List.mem_range] at hpq
  obtain ⟨i, hi, hpq⟩ := hpq
  split at hpq
  · rename_i f hf
    split at hpq
    · have hfl := (firstApp_some hf).1
      have hz := List.of_mem_zip hpq
      simp only [List.mem_map] at hz
      obtain ⟨⟨y, hy, hy'⟩, ⟨z, hz, hz'⟩⟩ := hz
      rw [← hy', ← hz']
      exact ⟨nodeIdx_lt (hk _ (node_mem hfl) y hy), nodeIdx_lt (hk _ (node_mem hi) z hz)⟩
    · cases hpq
  · cases hpq

theorem genPairs_in {ns : List Ty} (hk : KidsClosed ns) {i₁ i₂ : Nat} (h₁ : i₁ < ns.length)
    (h₂ : i₂ < ns.length) : PairsIn ns.length (genPairs ns i₁ i₂) := by
  intro pq hpq
  simp only [genPairs, List.mem_cons, List.mem_filterMap, List.mem_range] at hpq
  rcases hpq with rfl | ⟨i, hi, hpq⟩
  · exact ⟨h₁, h₂⟩
  · split at hpq
    · rename_i j sys hn
      split at hpq
      · rename_i v hv
        cases hpq
        refine ⟨hi, nodeIdx_lt (hk _ (node_mem hi) v ?_)⟩
        rw [hn]; simp [Ty.kids, hv]
      · cases hpq
    · cases hpq

theorem pending_some {ns : List Ty} {gens : List (Nat × Nat)} {lab : List Nat} {p q : Nat}
    (h : pending ns gens lab = some (p, q)) :
    (p, q) ∈ gens ++ congPairs ns lab ∧ labOf lab p ≠ labOf lab q := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [bne_iff_ne, ne_eq] at hp
  exact ⟨hm, hp⟩

theorem pending_none {ns : List Ty} {gens : List (Nat × Nat)} {lab : List Nat}
    (h : pending ns gens lab = none) : ∀ p ∈ gens ++ congPairs ns lab, labOf lab p.1 = labOf lab p.2 := by
  intro pq hpq
  have := List.find?_eq_none.mp h pq hpq
  simpa using this

/-- What the loop gives satisfies any invariant its merges keep, and has
nothing pending. -/
theorem closeLoop_inv {ns : List Ty} {gens : List (Nat × Nat)} (Inv : List Nat → Prop)
    (hinv : ∀ lab p q, Inv lab → pending ns gens lab = some (p, q) → Inv (merge lab p q)) :
    ∀ k lab lab', Inv lab → closeLoop ns gens k lab = some lab' →
      Inv lab' ∧ pending ns gens lab' = none
  | 0, _, _, _, h => by simp [closeLoop] at h
  | k + 1, lab, lab', hi, h => by
    unfold closeLoop at h
    split at h
    · rename_i hp; cases h; exact ⟨hi, hp⟩
    · rename_i p q hp
      exact closeLoop_inv Inv hinv k _ _ (hinv lab p q hi hp) h

/-- With more fuel than classes, the loop finishes. -/
theorem closeLoop_some {ns : List Ty} {gens : List (Nat × Nat)} (hk : KidsClosed ns)
    (hg : PairsIn ns.length gens) :
    ∀ k lab, Canon ns.length lab → roots ns.length lab < k →
      ∃ lab', closeLoop ns gens k lab = some lab'
  | 0, _, _, h => by omega
  | k + 1, lab, hc, hr => by
    unfold closeLoop
    split
    · exact ⟨lab, rfl⟩
    · rename_i p q hp
      obtain ⟨hm, hne⟩ := pending_some hp
      have hpq : p < ns.length ∧ q < ns.length := by
        rcases List.mem_append.mp hm with h | h
        · exact hg _ h
        · exact congPairs_in hk lab _ h
      have := roots_merge hc hpq.1 hpq.2 hne
      exact closeLoop_some hk hg k _ (hc.merge hpq.1 hpq.2) (by omega)

theorem roots_le (n : Nat) (lab : List Nat) : roots n lab ≤ n := by
  unfold roots
  have := List.countP_le_length (p := fun i => labOf lab i == i) (l := List.range n)
  simpa using this

/-! ## A unifier respects the classes -/

/-- `ψ` gives the nodes of one class equal types. -/
def Resp (ψ : Subst) (ns : List Ty) (lab : List Nat) : Prop :=
  ∀ i j, i < ns.length → j < ns.length → labOf lab i = labOf lab j →
    TyEq ((node ns i).subst ψ) ((node ns j).subst ψ)

theorem Resp.range (ψ : Subst) (ns : List Ty) : Resp ψ ns (List.range ns.length) := by
  intro i j hi hj h
  simp only [labOf, List.getD, List.getElem?_range hi, List.getElem?_range hj,
    Option.getD_some] at h
  subst h; exact TyEq.refl _

theorem Resp.merge {ψ : Subst} {ns : List Ty} {lab : List Nat} {p q : Nat} (h : Resp ψ ns lab)
    (hl : lab.length = ns.length) (hp : p < ns.length) (hq : q < ns.length)
    (he : TyEq ((node ns p).subst ψ) ((node ns q).subst ψ)) : Resp ψ ns (merge lab p q) := by
  intro i j hi hj hij
  rw [labOf_merge (hl ▸ hi), labOf_merge (hl ▸ hj)] at hij
  split at hij <;> split at hij
  · rename_i h₁ h₂; exact h i j hi hj (h₁.trans h₂.symm)
  · rename_i h₁ h₂
    exact (h i q hi hq h₁).trans (he.symm.trans (h p j hp hj hij))
  · rename_i h₁ h₂
    exact (h i p hi hp hij).trans (he.trans (h q j hq hj h₂.symm))
  · exact h i j hi hj hij

theorem TyEq.of_view_none_app {s : Ty} {c : Con} {xs : List Ty} (hs : s.view = none) :
    ¬ TyEq s (.app c xs) := by
  intro h
  have := h 1
  rw [Ty.approx_succ, Ty.approx_succ, hs] at this
  simp [Ty.view] at this

/-- The pairs the loop merges are equated by a unifier of the two types that
respects the classes. -/
theorem pending_resp {ψ : Subst} {ns : List Ty} (hk : KidsClosed ns) {i₁ i₂ : Nat}
    (he : TyEq ((node ns i₁).subst ψ) ((node ns i₂).subst ψ)) {lab : List Nat} (hr : Resp ψ ns lab) :
    ∀ pq ∈ genPairs ns i₁ i₂ ++ congPairs ns lab,
      TyEq ((node ns pq.1).subst ψ) ((node ns pq.2).subst ψ) := by
  intro pq hpq
  rcases List.mem_append.mp hpq with hpq | hpq
  · simp only [genPairs, List.mem_cons, List.mem_filterMap, List.mem_range] at hpq
    rcases hpq with rfl | ⟨i, hi, hpq⟩
    · exact he
    · split at hpq
      · rename_i j sys hn
        split at hpq
        · rename_i v hv
          cases hpq
          have hvk : v ∈ ns := hk _ (node_mem hi) v (by rw [hn]; simp [Ty.kids, hv])
          simp only
          rw [node_nodeIdx hvk, hn]
          have := TyEq.whnf (Ty.mu j sys)
          simp only [Ty.whnf, hv, Option.getD_some] at this
          exact (this.subst ψ).symm
        · cases hpq
      · cases hpq
  · simp only [congPairs, List.mem_flatMap, List.mem_range] at hpq
    obtain ⟨i, hi, hpq⟩ := hpq
    split at hpq
    · rename_i f hf
      split at hpq
      · rename_i hc
        obtain ⟨hfl, hlf, hfa⟩ := firstApp_some hf
        have hfi := hr f i hfl hi hlf
        generalize hnf : node ns f = xf at hc hfi hpq hfa
        generalize hni : node ns i = xi at hc hfi hpq
        cases xf with
        | var _ | mu _ _ => simp [Ty.isApp] at hfa
        | app c xs =>
          cases xi with
          | var _ | mu _ _ => simp [Ty.headCon] at hc
          | app c' ys =>
            simp only [Ty.subst_app] at hfi
            obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp hfi
            simp only [Ty.kids] at hpq
            rw [List.zip_map] at hpq
            obtain ⟨⟨x, y⟩, hxy, rfl⟩ := List.mem_map.mp hpq
            have hx : x ∈ xs := (List.of_mem_zip hxy).1
            have hy : y ∈ ys := (List.of_mem_zip hxy).2
            have hxn : x ∈ ns := hk _ (hnf ▸ node_mem hfl) x (by simp [Ty.kids, hx])
            have hyn : y ∈ ns := hk _ (hni ▸ node_mem hi) y (by simp [Ty.kids, hy])
            simp only [Prod.map]
            rw [node_nodeIdx hxn, node_nodeIdx hyn]
            refine hz (x.subst ψ, y.subst ψ) ?_
            rw [List.zip_map]
            exact List.mem_map_of_mem hxy
      · cases hpq
    · cases hpq

/-- Nodes of one class have one head, under a unifier that respects them. -/
theorem consistent_of_resp {ψ : Subst} {ns : List Ty} {lab : List Nat} (hr : Resp ψ ns lab) :
    consistent ns lab = true := by
  simp only [consistent, List.all_eq_true, List.mem_range]
  intro i hi
  split
  · rename_i f hf
    obtain ⟨hfl, hlf, hfa⟩ := firstApp_some hf
    have hfi := hr f i hfl hi hlf
    generalize hnf : node ns f = xf at hfi hfa
    cases xf with
    | var _ | mu _ _ => simp [Ty.isApp] at hfa
    | app c xs =>
      generalize hni : node ns i = xi at hfi
      cases xi with
      | app c' ys =>
        simp only [Ty.subst_app] at hfi
        obtain ⟨hc, hl, -⟩ := TyEq.app_iff.mp hfi
        simp only [List.length_map] at hl
        simp [Ty.headCon, hc, hl]
      | var a => simp [Ty.headless, Ty.view]
      | mu j sys =>
        simp only [Ty.headless, Bool.not_eq_true', Option.isNone_eq_false_iff]
        cases hv : (Ty.mu j sys).view with
        | some _ => rfl
        | none =>
          exfalso
          refine TyEq.of_view_none_app (s := (Ty.mu j sys).subst ψ) ?_ (hfi.symm)
          rw [Ty.view_subst, hv]; rfl
  · rfl

/-! ## The substitution read off the classes -/

/-- Unfolding gives an equal type. -/
theorem unroll_tyEq : ∀ (k : Nat) (seen : List Nat) (τ : Ty), TyEq (unroll k seen τ) τ
  | 0, _, τ => TyEq.refl τ
  | k + 1, seen, .mu ℓ sys => by
    unfold unroll
    split
    · exact TyEq.refl _
    · have hw := TyEq.whnf (Ty.mu ℓ sys)
      split
      · rename_i c xs hv
        simp only [Ty.whnf, hv, Option.getD_some] at hw
        refine TyEq.trans (TyEq.app (by simp) (fun p hp => ?_)) hw
        rw [List.zip_map_left] at hp
        obtain ⟨⟨x, y⟩, hxy, rfl⟩ := List.mem_map.mp hp
        obtain ⟨rfl, -⟩ := mem_zip_self hxy
        exact unroll_tyEq k _ x
      · rename_i a hv
        simp only [Ty.whnf, hv, Option.getD_some] at hw
        exact hw
      · exact TyEq.refl _
  | k + 1, seen, .app c xs => by
    unfold unroll
    refine TyEq.app (by simp) (fun p hp => ?_)
    rw [List.zip_map_left] at hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := List.mem_map.mp hp
    obtain ⟨rfl, -⟩ := mem_zip_self hxy
    exact unroll_tyEq k seen x
  | _ + 1, _, .var a => by unfold unroll; exact TyEq.refl _

theorem find_filterMap_var (V : Ty → Ty) (a : Nat) : ∀ l : List Ty,
    Subst.find (l.filterMap fun x => match x with
      | .var b => some (b, V (.var b))
      | _ => none) a = if Ty.var a ∈ l then some (V (.var a)) else none
  | [] => by simp [Subst.find]
  | x :: l => by
    have ih := find_filterMap_var V a l
    cases x with
    | var b =>
      simp only [List.filterMap_cons, Subst.find, List.mem_cons, Ty.var.injEq]
      by_cases h : a = b
      · subst h; simp
      · simp [h, ih]
    | app c args => simp [ih]
    | mu i sys => simp [ih]

theorem unifySubst_find (ns : List Ty) (lab : List Nat) (a : Nat) :
    (unifySubst ns lab).find a = if Ty.var a ∈ ns then some (nodeVal ns lab (.var a)) else none := by
  unfold unifySubst
  exact find_filterMap_var (nodeVal ns lab) a ns

theorem classRef_open (ns : List Ty) (lab : List Nat) (x : Ty) :
    (classRef ns lab x).open (muEnv (classSys ns lab)) =
      classTy ns lab (labOf lab (nodeIdx ns x)) := by
  by_cases h : varOnly ns lab (labOf lab (nodeIdx ns x)) <;>
    simp [classRef, classTy, h, RTy.open, muEnv]

theorem classSys_get {ns : List Ty} {lab : List Nat} {ℓ : Nat} (h : ℓ < ns.length) :
    (classSys ns lab)[ℓ]? = some (classEq ns lab ℓ) := by
  simp [classSys, List.getElem?_map, List.getElem?_range h]

/-- A constructor class's type unfolds to its first constructor node's
constructor, applied to its arguments' classes' types. -/
theorem classTy_view_app {ns : List Ty} {lab : List Nat} {ℓ f : Nat} (hℓ : ℓ < ns.length)
    (hc : labOf lab ℓ = ℓ) (hf : firstApp ns lab ℓ = some f) {c : Con} {ys : List Ty}
    (hn : node ns f = .app c ys) :
    classTy ns lab ℓ = .mu ℓ (classSys ns lab) ∧
    (Ty.mu ℓ (classSys ns lab)).view =
      some (.app c (ys.map fun y => classTy ns lab (labOf lab (nodeIdx ns y)))) := by
  refine ⟨by simp [classTy, varOnly, hf], ?_⟩
  simp only [Ty.view, classSys_get hℓ, Option.bind_some, classEq, hc, hf, hn]
  rw [RTy.head]
  simp [classRef_open]

/-- A headless class's type is headless. -/
theorem classTy_view_none {ns : List Ty} {lab : List Nat} {ℓ : Nat} (hℓ : ℓ < ns.length)
    (hc : labOf lab ℓ = ℓ) (hf : firstApp ns lab ℓ = none) (hh : hasHeadless ns lab ℓ = true) :
    classTy ns lab ℓ = .mu ℓ (classSys ns lab) ∧ (Ty.mu ℓ (classSys ns lab)).view = none := by
  refine ⟨by simp [classTy, varOnly, hh], ?_⟩
  simp only [Ty.view, classSys_get hℓ, Option.bind_some, classEq, hc, hf]
  rw [RTy.head]

theorem hasHeadless_of {ns : List Ty} {lab : List Nat} {i : Nat} (hi : i < ns.length)
    (hh : (node ns i).headless = true) : hasHeadless ns lab (labOf lab i) = true := by
  simp only [hasHeadless, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  exact ⟨i, hi, rfl, hh⟩

/-- The closure is stable: nothing is left to merge. -/
def Stable (ns : List Ty) (gens : List (Nat × Nat)) (lab : List Nat) : Prop :=
  ∀ p ∈ gens ++ congPairs ns lab, labOf lab p.1 = labOf lab p.2

/-- In a stable closure, a node and its unfolding are in one class. -/
theorem Stable.mu {ns : List Ty} {i₁ i₂ : Nat} {lab : List Nat} (hs : Stable ns (genPairs ns i₁ i₂) lab)
    {x v : Ty} (hx : x ∈ ns) (hm : ∃ j sys, x = .mu j sys) (hv : x.view = some v) :
    labOf lab (nodeIdx ns x) = labOf lab (nodeIdx ns v) := by
  obtain ⟨j, sys, rfl⟩ := hm
  refine hs (nodeIdx ns (.mu j sys), nodeIdx ns v) (List.mem_append_left _ ?_)
  simp only [genPairs, List.mem_cons, List.mem_filterMap, List.mem_range]
  refine .inr ⟨nodeIdx ns (.mu j sys), nodeIdx_lt hx, ?_⟩
  rw [node_nodeIdx hx]; simp [hv]

/-- In a stable closure, two constructor nodes of one class have their
arguments in one class each. -/
theorem Stable.cong {ns : List Ty} {gens : List (Nat × Nat)} {lab : List Nat}
    (hs : Stable ns gens lab) {f i : Nat} (hi : i < ns.length)
    (hf : firstApp ns lab (labOf lab i) = some f) {c : Con} {xs ys : List Ty}
    (hnf : node ns f = .app c xs) (hni : node ns i = .app c ys) (hl : xs.length = ys.length) :
    ∀ p ∈ xs.zip ys, labOf lab (nodeIdx ns p.1) = labOf lab (nodeIdx ns p.2) := by
  intro p hp
  refine hs (nodeIdx ns p.1, nodeIdx ns p.2) (List.mem_append_right _ ?_)
  simp only [congPairs, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [hf, hnf, hni, Ty.headCon, hl, ite_true, Ty.kids]
  rw [List.zip_map]
  exact List.mem_map_of_mem hp

theorem consistent_at {ns : List Ty} {lab : List Nat} (h : consistent ns lab = true) {i f : Nat}
    (hi : i < ns.length) (hf : firstApp ns lab (labOf lab i) = some f) :
    (∀ c args, node ns i = .app c args → (node ns f).headCon = some (c, args.length)) ∧
    ((node ns i).isApp = false → (node ns i).headless = false) := by
  simp only [consistent, List.all_eq_true, List.mem_range] at h
  have := h i hi
  rw [hf] at this
  constructor
  · intro c args hn
    rw [hn] at this
    simpa using this
  · intro hna
    generalize hn : node ns i = t at this hna
    cases t with
    | app _ _ => simp [Ty.isApp] at hna
    | var a => simp [Ty.headless, Ty.view]
    | mu j sys => simpa using this

theorem Ty.headCon_some {t : Ty} {c : Con} {k : Nat} (h : t.headCon = some (c, k)) :
    ∃ ys, t = .app c ys ∧ ys.length = k := by
  cases t <;> simp [Ty.headCon] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

theorem mem_zip_swap {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α} {b : β},
    (a, b) ∈ l₁.zip l₂ → (b, a) ∈ l₂.zip l₁
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (mem_zip_swap h)

/-- The substitution read off a stable closure with one head per class
gives each node its class's type. -/
theorem extract_sound {ns : List Ty} {i₁ i₂ : Nat} {lab : List Nat} (hk : KidsClosed ns)
    (hc : Canon ns.length lab) (hs : Stable ns (genPairs ns i₁ i₂) lab)
    (hcons : consistent ns lab = true) :
    ∀ x ∈ ns, TyEq (x.subst (unifySubst ns lab)) (classTy ns lab (labOf lab (nodeIdx ns x))) := by
  -- A variable node: what it is bound to.
  have hvar : ∀ a, Ty.var a ∈ ns → TyEq ((Ty.var a).subst (unifySubst ns lab))
      (classTy ns lab (labOf lab (nodeIdx ns (.var a)))) := by
    intro a ha
    simp only [Ty.subst, unifySubst_find, ha, ite_true, Option.getD_some, nodeVal]
    exact unroll_tyEq _ _ _
  let R : Ty → Ty → Prop := fun s t => ∃ x ∈ ns, s = x.subst (unifySubst ns lab) ∧
    t = classTy ns lab (labOf lab (nodeIdx ns x))
  -- A constructor node: one head, its arguments related.
  have happ : ∀ c args, Ty.app c args ∈ ns →
      Matched R ((Ty.app c args).subst (unifySubst ns lab))
        (classTy ns lab (labOf lab (nodeIdx ns (.app c args)))) := by
    intro c args hx
    have hi := nodeIdx_lt hx
    have hni := node_nodeIdx hx
    obtain ⟨f, hf⟩ := firstApp_of_app (lab := lab) hi (by rw [hni]; rfl)
    have hhc := (consistent_at hcons hi hf).1 c args hni
    obtain ⟨ys, hnf, hl⟩ := Ty.headCon_some hhc
    obtain ⟨hℓ, hℓc⟩ := hc.2 _ hi
    obtain ⟨hT, hv⟩ := classTy_view_app hℓ hℓc hf hnf
    rw [hT]
    refine .inr (.inr ⟨c, args.map (·.subst (unifySubst ns lab)), _, by simp [Ty.view], hv,
      by simp [hl], fun p hp => ?_⟩)
    rw [List.zip_map] at hp
    obtain ⟨⟨a, y⟩, hay, rfl⟩ := List.mem_map.mp hp
    have hlab := Stable.cong hs hi hf hnf hni hl (y, a) (mem_zip_swap hay)
    have ha : a ∈ ns := hk _ hx a (by simp [Ty.kids, (List.of_mem_zip hay).1])
    refine ⟨a, ha, rfl, ?_⟩
    simp only [Prod.map]
    rw [hlab]
  refine fun x hx => TyEq.of_bisim R (fun s t hr => ?_) _ _ ⟨x, hx, rfl, rfl⟩
  obtain ⟨x, hx, rfl, rfl⟩ := hr
  cases x with
  | var a => exact .inl (hvar a hx)
  | app c args => exact .inr ⟨_, _, TyEq.refl _, TyEq.refl _, happ c args hx⟩
  | mu j sys =>
    cases hv : (Ty.mu j sys).view with
    | some v =>
      have hvn : v ∈ ns := hk _ hx v (by simp [Ty.kids, hv])
      have hlab := Stable.mu hs hx ⟨j, sys, rfl⟩ hv
      have hw : TyEq ((Ty.mu j sys).subst (unifySubst ns lab)) (v.subst (unifySubst ns lab)) := by
        have := TyEq.whnf (Ty.mu j sys)
        simp only [Ty.whnf, hv, Option.getD_some] at this
        exact this.symm.subst _
      rw [hlab]
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · exact .inl (hw.trans (hvar a hvn))
      · exact .inr ⟨_, _, hw, TyEq.refl _, happ c args hvn⟩
    | none =>
      have hi := nodeIdx_lt hx
      have hni := node_nodeIdx hx
      have hhl : (node ns (nodeIdx ns (.mu j sys))).headless = true := by
        rw [hni]; simp [Ty.headless, hv]
      have hf : firstApp ns lab (labOf lab (nodeIdx ns (.mu j sys))) = none := by
        cases hf : firstApp ns lab (labOf lab (nodeIdx ns (.mu j sys))) with
        | none => rfl
        | some f =>
          have := (consistent_at hcons hi hf).2 (by rw [hni]; rfl)
          rw [hhl] at this; cases this
      obtain ⟨hℓ, hℓc⟩ := hc.2 _ hi
      have hh := hasHeadless_of (lab := lab) hi hhl
      obtain ⟨hT, hvT⟩ := classTy_view_none hℓ hℓc hf hh
      rw [hT]
      refine .inr ⟨_, _, TyEq.refl _, TyEq.refl _, .inl ⟨?_, hvT⟩⟩
      rw [Ty.view_subst, hv]; rfl

/-! ## Most general -/

theorem classVar_spec {ns : List Ty} {lab : List Nat} {ℓ i : Nat} (hi : i < ns.length)
    (hl : labOf lab i = ℓ) (hv : (node ns i).isVar = true) :
    ∃ j, j < ns.length ∧ labOf lab j = ℓ ∧ node ns j = .var (classVar ns lab ℓ) := by
  unfold classVar
  cases h : (List.range ns.length).reverse.find? (fun i => labOf lab i == ℓ && (node ns i).isVar) with
  | none =>
    have := List.find?_eq_none.mp h i (List.mem_reverse.mpr (List.mem_range.mpr hi))
    simp [hl, hv] at this
  | some j =>
    have hm := List.mem_range.mp (List.mem_reverse.mp (List.mem_of_find?_eq_some h))
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨j, hm, hp.1, ?_⟩
    generalize hn : node ns j = t at hp
    cases t <;> simp_all [Ty.isVar]

/-- A class of variables has a variable node, the one it stands for. -/
theorem varOnly_var {ns : List Ty} {i₁ i₂ : Nat} {lab : List Nat} (hk : KidsClosed ns)
    (hs : Stable ns (genPairs ns i₁ i₂) lab) {x : Ty} (hx : x ∈ ns)
    (hvo : varOnly ns lab (labOf lab (nodeIdx ns x)) = true) :
    ∃ j, j < ns.length ∧ labOf lab j = labOf lab (nodeIdx ns x) ∧
      node ns j = .var (classVar ns lab (labOf lab (nodeIdx ns x))) := by
  simp only [varOnly, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hvo
  obtain ⟨hf, hh⟩ := hvo
  have hi := nodeIdx_lt hx
  have hni := node_nodeIdx hx
  cases x with
  | var a => exact classVar_spec hi rfl (by rw [hni]; rfl)
  | app c args =>
    have := firstApp_none hf hi rfl; rw [hni] at this; cases this
  | mu j sys =>
    cases hv : (Ty.mu j sys).view with
    | none =>
      have := hasHeadless_of (lab := lab) hi (by rw [hni]; simp [Ty.headless, hv])
      rw [hh] at this; cases this
    | some v =>
      have hvn : v ∈ ns := hk _ hx v (by simp [Ty.kids, hv])
      have hlab := Stable.mu hs hx ⟨j, sys, rfl⟩ hv
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · rw [hlab]
        exact classVar_spec (nodeIdx_lt hvn) rfl (by rw [node_nodeIdx hvn]; rfl)
      · have := firstApp_none hf (nodeIdx_lt hvn) hlab.symm
        rw [node_nodeIdx hvn] at this; cases this

/-- Under a unifier respecting the classes, a node's class's type is the
node's type. -/
theorem extract_mgu {ψ : Subst} {ns : List Ty} {i₁ i₂ : Nat} {lab : List Nat} (hk : KidsClosed ns)
    (hc : Canon ns.length lab) (hs : Stable ns (genPairs ns i₁ i₂) lab) (hr : Resp ψ ns lab) :
    ∀ x ∈ ns, TyEq ((classTy ns lab (labOf lab (nodeIdx ns x))).subst ψ) (x.subst ψ) := by
  let R : Ty → Ty → Prop := fun s t => ∃ x ∈ ns,
    s = (classTy ns lab (labOf lab (nodeIdx ns x))).subst ψ ∧ t = x.subst ψ
  refine fun x hx => TyEq.of_bisim R (fun s t hR => ?_) _ _ ⟨x, hx, rfl, rfl⟩
  obtain ⟨x, hx, rfl, rfl⟩ := hR
  have hi := nodeIdx_lt hx
  have hni := node_nodeIdx hx
  obtain ⟨hℓ, hℓc⟩ := hc.2 _ hi
  cases hf : firstApp ns lab (labOf lab (nodeIdx ns x)) with
  | some f =>
    obtain ⟨hfl, hlf, hfa⟩ := firstApp_some hf
    generalize hnf : node ns f = xf at hfa
    cases xf with
    | var _ | mu _ _ => simp [Ty.isApp] at hfa
    | app c ys =>
      obtain ⟨hT, hv⟩ := classTy_view_app hℓ hℓc hf hnf
      have hxf := hr (nodeIdx ns x) f hi hfl hlf.symm
      rw [hni, hnf] at hxf
      refine .inr ⟨_, _, TyEq.refl _, hxf, .inr (.inr ⟨c,
        ys.map (fun y => (classTy ns lab (labOf lab (nodeIdx ns y))).subst ψ), ys.map (·.subst ψ), ?_,
        by simp [Ty.view],
        by simp, fun p hp => ?_⟩)⟩
      · rw [hT, Ty.view_subst, hv]; simp [Ty.view]
      · rw [List.zip_map] at hp
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
        obtain ⟨rfl, ha⟩ := mem_zip_self hab
        exact ⟨a, hk _ (hnf ▸ node_mem hfl) a (by simp [Ty.kids, ha]), rfl, rfl⟩
  | none =>
    cases hh : hasHeadless ns lab (labOf lab (nodeIdx ns x)) with
    | true =>
      obtain ⟨hT, hv⟩ := classTy_view_none hℓ hℓc hf hh
      simp only [hasHeadless, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hh
      obtain ⟨h, hhl, hlh, hhh⟩ := hh
      have hxh := hr (nodeIdx ns x) h hi hhl hlh.symm
      rw [hni] at hxh
      refine .inr ⟨_, _, TyEq.refl _, hxh, .inl ⟨?_, ?_⟩⟩
      · rw [hT, Ty.view_subst, hv]; rfl
      · simp only [Ty.headless, Option.isNone_iff_eq_none] at hhh
        rw [Ty.view_subst, hhh]; rfl
    | false =>
      have hvo : varOnly ns lab (labOf lab (nodeIdx ns x)) = true := by
        simp [varOnly, hf, hh]
      obtain ⟨j, hj, hlj, hnj⟩ := varOnly_var hk hs hx hvo
      have hT : classTy ns lab (labOf lab (nodeIdx ns x)) =
          .var (classVar ns lab (labOf lab (nodeIdx ns x))) := by simp [classTy, hvo]
      have hxj := hr j (nodeIdx ns x) hj hi hlj
      rw [hni, hnj] at hxj
      left; rw [hT]; exact hxj

/-! ## The unifier -/

theorem unify_eq {τ₁ τ₂ : Ty} {σ : Subst} (h : unify τ₁ τ₂ = some σ) :
    ∃ lab, closeLoop (nodes τ₁ τ₂) (genPairs (nodes τ₁ τ₂) (nodeIdx (nodes τ₁ τ₂) τ₁)
        (nodeIdx (nodes τ₁ τ₂) τ₂)) ((nodes τ₁ τ₂).length + 1) (List.range (nodes τ₁ τ₂).length) =
        some lab ∧ consistent (nodes τ₁ τ₂) lab = true ∧ σ = unifySubst (nodes τ₁ τ₂) lab := by
  unfold unify at h
  simp only at h
  split at h
  · cases h
  · rename_i lab hl
    split at h
    · cases h; exact ⟨lab, hl, ‹_›, rfl⟩
    · cases h

/-- The loop's result, with the invariants it keeps. -/
theorem closeLoop_canon {τ₁ τ₂ : Ty} {lab : List Nat}
    (h : closeLoop (nodes τ₁ τ₂) (genPairs (nodes τ₁ τ₂) (nodeIdx (nodes τ₁ τ₂) τ₁)
        (nodeIdx (nodes τ₁ τ₂) τ₂)) ((nodes τ₁ τ₂).length + 1) (List.range (nodes τ₁ τ₂).length) =
        some lab) :
    Canon (nodes τ₁ τ₂).length lab ∧
      Stable (nodes τ₁ τ₂) (genPairs (nodes τ₁ τ₂) (nodeIdx (nodes τ₁ τ₂) τ₁)
        (nodeIdx (nodes τ₁ τ₂) τ₂)) lab := by
  have hk := nodes_closed τ₁ τ₂
  have hg := genPairs_in hk (nodeIdx_lt (mem_nodes_left τ₁ τ₂)) (nodeIdx_lt (mem_nodes_right τ₁ τ₂))
  obtain ⟨hc, hp⟩ := closeLoop_inv (Canon (nodes τ₁ τ₂).length) (fun lab p q hc hp => by
      obtain ⟨hm, -⟩ := pending_some hp
      have hpq : p < (nodes τ₁ τ₂).length ∧ q < (nodes τ₁ τ₂).length := by
        rcases List.mem_append.mp hm with h | h
        · exact hg _ h
        · exact congPairs_in hk lab _ h
      exact hc.merge hpq.1 hpq.2) _ _ _ (Canon.range _) h
  exact ⟨hc, pending_none hp⟩

/-- What `unify` finds equates the two types. -/
theorem unify_sound {τ₁ τ₂ : Ty} {σ : Subst} (h : unify τ₁ τ₂ = some σ) :
    TyEq (τ₁.subst σ) (τ₂.subst σ) := by
  obtain ⟨lab, hl, hcons, rfl⟩ := unify_eq h
  obtain ⟨hc, hs⟩ := closeLoop_canon hl
  have hk := nodes_closed τ₁ τ₂
  have h₁ := extract_sound hk hc hs hcons τ₁ (mem_nodes_left τ₁ τ₂)
  have h₂ := extract_sound hk hc hs hcons τ₂ (mem_nodes_right τ₁ τ₂)
  have h₁₂ : labOf lab (nodeIdx (nodes τ₁ τ₂) τ₁) = labOf lab (nodeIdx (nodes τ₁ τ₂) τ₂) :=
    hs (nodeIdx (nodes τ₁ τ₂) τ₁, nodeIdx (nodes τ₁ τ₂) τ₂) (by simp [genPairs])
  rw [h₁₂] at h₁
  exact h₁.trans h₂.symm

/-- Whenever a substitution equates the two types, `unify` succeeds, and
the substitution factors through what it finds, up to equality. -/
theorem unify_mgu {τ₁ τ₂ : Ty} {ψ : Subst} (h : TyEq (τ₁.subst ψ) (τ₂.subst ψ)) :
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, TyEq ((τ.subst σ).subst ψ) (τ.subst ψ) := by
  have hk := nodes_closed τ₁ τ₂
  have hm₁ := mem_nodes_left τ₁ τ₂
  have hm₂ := mem_nodes_right τ₁ τ₂
  have hg := genPairs_in hk (nodeIdx_lt hm₁) (nodeIdx_lt hm₂)
  have he : TyEq ((node (nodes τ₁ τ₂) (nodeIdx (nodes τ₁ τ₂) τ₁)).subst ψ)
      ((node (nodes τ₁ τ₂) (nodeIdx (nodes τ₁ τ₂) τ₂)).subst ψ) := by
    rw [node_nodeIdx hm₁, node_nodeIdx hm₂]; exact h
  obtain ⟨lab, hl⟩ := closeLoop_some hk hg _ _ (Canon.range _)
    (Nat.lt_succ_of_le (roots_le _ _))
  obtain ⟨⟨hc, hr⟩, hp⟩ := closeLoop_inv (fun lab => Canon (nodes τ₁ τ₂).length lab ∧
      Resp ψ (nodes τ₁ τ₂) lab) (fun lab p q ⟨hc, hr⟩ hp => by
      obtain ⟨hm, -⟩ := pending_some hp
      have hpq : p < (nodes τ₁ τ₂).length ∧ q < (nodes τ₁ τ₂).length := by
        rcases List.mem_append.mp hm with h | h
        · exact hg _ h
        · exact congPairs_in hk lab _ h
      exact ⟨hc.merge hpq.1 hpq.2, hr.merge hc.1 hpq.1 hpq.2 (pending_resp hk he hr _ hm)⟩)
    _ _ _ ⟨Canon.range _, Resp.range ψ _⟩ hl
  have hs := pending_none hp
  have hcons := consistent_of_resp hr
  refine ⟨unifySubst (nodes τ₁ τ₂) lab, by simp [unify, hl, hcons], fun τ => ?_⟩
  rw [← Ty.subst_compose]
  refine Ty.subst_tyEq_congr (fun a _ => ?_)
  rw [Ty.subst_compose]
  by_cases ha : Ty.var a ∈ nodes τ₁ τ₂
  · have hv : (Ty.var a).subst (unifySubst (nodes τ₁ τ₂) lab) = nodeVal (nodes τ₁ τ₂) lab (.var a) := by
      simp [Ty.subst, unifySubst_find, ha]
    rw [hv]
    exact ((unroll_tyEq _ _ _).subst ψ).trans (extract_mgu hk hc hs hr _ ha)
  · have hv : (Ty.var a).subst (unifySubst (nodes τ₁ τ₂) lab) = .var a := by
      simp [Ty.subst, unifySubst_find, ha]
    rw [hv]; exact TyEq.refl _

/-! ## Variables of the unifier -/

theorem unroll_ftv : ∀ (k : Nat) (seen : List Nat) (τ : Ty), ∀ b ∈ (unroll k seen τ).ftv, b ∈ τ.ftv
  | 0, _, τ, b, h => h
  | k + 1, seen, .mu ℓ sys, b, h => by
    unfold unroll at h
    split at h
    · exact h
    · split at h
      · rename_i c xs hv
        simp only [Ty.ftv_app, List.mem_flatMap, List.mem_map] at h
        obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := h
        exact Ty.view_ftv hv b (by
          simp only [Ty.ftv_app, List.mem_flatMap]; exact ⟨x, hx, unroll_ftv k _ x b h⟩)
      · rename_i a hv
        exact Ty.view_ftv hv b h
      · exact h
  | k + 1, seen, .app c xs, b, h => by
    unfold unroll at h
    simp only [Ty.ftv_app, List.mem_flatMap, List.mem_map] at h ⊢
    obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := h
    exact ⟨x, hx, unroll_ftv k seen x b h⟩
  | _ + 1, _, .var a, b, h => by unfold unroll at h; exact h

/-- A node's class's type mentions only the nodes' variables. -/
theorem classTy_ftv {ns : List Ty} {i₁ i₂ : Nat} {lab : List Nat} (hk : KidsClosed ns)
    (hs : Stable ns (genPairs ns i₁ i₂) lab) {x : Ty} (hx : x ∈ ns) :
    ∀ b ∈ (classTy ns lab (labOf lab (nodeIdx ns x))).ftv, ∃ y ∈ ns, b ∈ y.ftv := by
  -- A reference to a node's class mentions a variable node's variable.
  have href : ∀ y ∈ ns, ∀ b ∈ (classRef ns lab y).ftv, ∃ z ∈ ns, b ∈ z.ftv := by
    intro y hy b hb
    simp only [classRef] at hb
    by_cases hvo : varOnly ns lab (labOf lab (nodeIdx ns y)) = true
    · simp only [hvo, ↓reduceIte] at hb
      obtain ⟨j, hj, -, hnj⟩ := varOnly_var hk hs hy hvo
      refine ⟨node ns j, node_mem hj, ?_⟩
      rw [hnj]; simpa [RTy.ftv] using hb
    · simp only [hvo, Bool.false_eq_true, ↓reduceIte] at hb; simp [RTy.ftv] at hb
  intro b hb
  unfold classTy at hb
  split at hb
  · rename_i hvo
    obtain ⟨j, hj, -, hnj⟩ := varOnly_var hk hs hx hvo
    exact ⟨node ns j, node_mem hj, by rw [hnj]; exact hb⟩
  · simp only [Ty.ftv_mu, classSys, List.mem_flatMap, List.mem_map, List.mem_range] at hb
    obtain ⟨_, ⟨j, -, rfl⟩, hb⟩ := hb
    unfold classEq at hb
    split at hb
    · rename_i f hf
      obtain ⟨hfl, -, -⟩ := firstApp_some hf
      split at hb
      · rename_i c args hn
        simp only [RTy.ftv_app, List.mem_flatMap, List.mem_map] at hb
        obtain ⟨_, ⟨y, hy, rfl⟩, hb⟩ := hb
        exact href y (hk _ (hn ▸ node_mem hfl) y (by simp [Ty.kids, hy])) b hb
      · simp [RTy.ftv] at hb
    · simp [RTy.ftv] at hb

/-- `unify` binds only the two types' variables, to types of their
variables. -/
theorem unify_ftv {τ₁ τ₂ : Ty} {σ : Subst} (h : unify τ₁ τ₂ = some σ) {a : Nat} {t : Ty}
    (ht : σ.find a = some t) :
    (a ∈ τ₁.ftv ∨ a ∈ τ₂.ftv) ∧ ∀ b ∈ t.ftv, b ∈ τ₁.ftv ∨ b ∈ τ₂.ftv := by
  obtain ⟨lab, hl, -, rfl⟩ := unify_eq h
  obtain ⟨-, hs⟩ := closeLoop_canon hl
  have hk := nodes_closed τ₁ τ₂
  rw [unifySubst_find] at ht
  split at ht
  · rename_i ha
    cases ht
    refine ⟨nodes_ftv ha a (by simp), fun b hb => ?_⟩
    obtain ⟨y, hy, hb⟩ := classTy_ftv hk hs ha b (unroll_ftv _ _ _ b hb)
    exact nodes_ftv hy b hb
  · cases ht

end Inty
