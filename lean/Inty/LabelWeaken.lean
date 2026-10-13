import Inty.Rigid

/-!
# Typing is stable under fresh labels

The typing rules give records a slot for each of the program's labels `L`
(Rémy's flat rows). A derivation over `L` is one over `L ++ L'`, for labels
`L'` apart from `L`, once every record over exactly `L` gets an absent slot
(`Ty.absSlot`) for each new label (`Ty.ext`). The translation reaches
every type of the derivation: those of the context, the constraints, the
return type, a class's parameter (`Cls.inject T`) and a binding's
annotation (`Expr.extAnn`). A record over the labels `L` is a leaf of the
trees types unfold to, so the translation grafts the new slots there
(`Ty.approx_ext`), and equal types stay equal. The model is
`HasTypeS.rsub` (`Inty.Rigid`).
-/

namespace Inty

/-! ## The translation -/

/-- The constructor a record over `L` becomes: a record over `L ++ L'`. -/
def Con.extL (L L' : List String) (c : Con) : Con :=
  match c with
  | .record ls => .record (if ls = L then L ++ L' else ls)
  | c => c

/-- The arguments a constructor gains: a record over `L`, an `x` for each
new label. -/
def Con.padL {α : Type} (L L' : List String) (c : Con) (x : α) : List α :=
  match c with
  | .record ls => if ls = L then L'.map (fun _ => x) else []
  | _ => []

theorem Con.padL_map {α β : Type} (L L' : List String) (c : Con) (x : α) (f : α → β) :
    (c.padL L L' x).map f = c.padL L L' (f x) := by
  unfold Con.padL; split
  · split <;> simp
  · rfl

theorem Con.mem_padL {α : Type} {L L' : List String} {c : Con} {x y : α}
    (h : y ∈ c.padL L L' x) : y = x := by
  unfold Con.padL at h; split at h
  · split at h
    · simp only [List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · cases h
  · cases h

/-- A constructor is kept and gains nothing, or it is the record over `L`. -/
theorem Con.extL_cases {α : Type} (L L' : List String) (c : Con) (x : α) :
    (c.extL L L' = c ∧ c.padL L L' x = []) ∨
      (c = .record L ∧ c.extL L L' = .record (L ++ L') ∧ c.padL L L' x = L'.map (fun _ => x)) := by
  unfold Con.extL Con.padL
  split
  · rename_i ls
    by_cases h : ls = L
    · subst h; simp
    · simp [h]
  · exact .inl ⟨rfl, rfl⟩

@[simp] theorem Con.extL_of_ne {L L' : List String} {c : Con} (h : ∀ ls, c ≠ .record ls) :
    c.extL L L' = c := by
  cases c <;> simp_all [Con.extL]

@[simp] theorem Con.padL_of_ne {α : Type} {L L' : List String} {c : Con} (h : ∀ ls, c ≠ .record ls) (x : α) :
    c.padL L L' x = [] := by
  cases c <;> simp_all [Con.padL]

@[simp] theorem Con.extL_record_self (L L' : List String) :
    (Con.record L).extL L L' = .record (L ++ L') := by simp [Con.extL]

@[simp] theorem Con.padL_record_self {α : Type} (L L' : List String) (x : α) :
    (Con.record L).padL L L' x = L'.map (fun _ => x) := by simp [Con.padL]

/-- The constructors that aren't records are kept. -/
theorem Con.extL_eq_iff {L L' : List String} {c d : Con} (hd : ∀ ls, d ≠ .record ls) :
    c.extL L L' = d ↔ c = d := by
  rcases Con.extL_cases L L' c () with ⟨h, -⟩ | ⟨rfl, h, -⟩
  · rw [h]
  · rw [h]; constructor
    · intro e; exact absurd e.symm (hd _)
    · intro e; exact absurd e.symm (hd _)

@[simp] theorem Con.extL_isRigid (L L' : List String) (c : Con) : (c.extL L L').isRigid = c.isRigid := by
  rcases Con.extL_cases L L' c () with ⟨h, -⟩ | ⟨rfl, h, -⟩ <;> rw [h] <;> rfl

@[simp] theorem Con.extL_typeTag (L L' : List String) (c : Con) : (c.extL L L').typeTag = c.typeTag := by
  rcases Con.extL_cases L L' c () with ⟨h, -⟩ | ⟨rfl, h, -⟩ <;> rw [h] <;> rfl

@[simp] theorem Con.extL_rkeys (L L' : List String) (c : Con) : (c.extL L L').rkeys = c.rkeys := by
  rcases Con.extL_cases L L' c () with ⟨h, -⟩ | ⟨rfl, h, -⟩ <;> rw [h] <;> rfl

mutual
def RTy.ext (L L' : List String) : RTy → RTy
  | .free a => .free a
  | .self j => .self j
  | .app c args => .app (c.extL L L') (RTy.exts L L' args ++ c.padL L L' Ty.absSlot.toRTy)
  | .mu i sys => .mu i (RTy.exts L L' sys)
def RTy.exts (L L' : List String) : List RTy → List RTy
  | [] => []
  | r :: rs => r.ext L L' :: RTy.exts L L' rs
end

@[simp] theorem RTy.exts_eq (L L' : List String) (rs : List RTy) :
    RTy.exts L L' rs = rs.map (RTy.ext L L') := by
  induction rs <;> simp_all [RTy.exts]

@[simp] theorem RTy.ext_app (L L' : List String) (c : Con) (args : List RTy) :
    (RTy.app c args).ext L L' =
      .app (c.extL L L') (args.map (·.ext L L') ++ c.padL L L' Ty.absSlot.toRTy) := by
  simp [RTy.ext]

@[simp] theorem RTy.ext_mu (L L' : List String) (i : Nat) (sys : List RTy) :
    (RTy.mu i sys).ext L L' = .mu i (sys.map (·.ext L L')) := by simp [RTy.ext]

@[simp] theorem RTy.ext_free (L L' : List String) (a : Nat) : (RTy.free a).ext L L' = .free a := rfl
@[simp] theorem RTy.ext_self (L L' : List String) (j : Nat) : (RTy.self j).ext L L' = .self j := rfl

mutual
/-- A type with every record over exactly `L` given an absent slot for each
label of `L'`. -/
def Ty.ext (L L' : List String) : Ty → Ty
  | .var a => .var a
  | .app c args => .app (c.extL L L') (Ty.exts L L' args ++ c.padL L L' Ty.absSlot)
  | .mu i sys => .mu i (RTy.exts L L' sys)
def Ty.exts (L L' : List String) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.ext L L' :: Ty.exts L L' τs
end

@[simp] theorem Ty.exts_eq (L L' : List String) (τs : List Ty) :
    Ty.exts L L' τs = τs.map (Ty.ext L L') := by
  induction τs <;> simp_all [Ty.exts]

@[simp] theorem Ty.ext_app (L L' : List String) (c : Con) (args : List Ty) :
    (Ty.app c args).ext L L' =
      .app (c.extL L L') (args.map (·.ext L L') ++ c.padL L L' Ty.absSlot) := by
  simp [Ty.ext]

@[simp] theorem Ty.ext_mu (L L' : List String) (i : Nat) (sys : List RTy) :
    (Ty.mu i sys).ext L L' = .mu i (sys.map (·.ext L L')) := by simp [Ty.ext]

@[simp] theorem Ty.ext_var (L L' : List String) (a : Nat) : (Ty.var a).ext L L' = .var a := rfl

/-- A constructor other than a record is kept. -/
theorem Ty.ext_app_nr {L L' : List String} {c : Con} (h : ∀ ls, c ≠ .record ls) (args : List Ty) :
    (Ty.app c args).ext L L' = .app c (args.map (·.ext L L')) := by
  simp [Con.extL_of_ne h, Con.padL_of_ne h]

@[simp] theorem Ty.ext_record_self (L L' : List String) (ss : List Ty) :
    (Ty.record L ss).ext L L' =
      .record (L ++ L') (ss.map (·.ext L L') ++ L'.map (fun _ => Ty.absSlot)) := by
  simp [Ty.record]

@[simp] theorem Ty.ext_fn (L L' : List String) (θ : Ty) (τs : List Ty) (ρ : Ty) :
    (Ty.fn θ τs ρ).ext L L' = .fn (θ.ext L L') (τs.map (·.ext L L')) (ρ.ext L L') := by
  simp [Ty.fn]

@[simp] theorem Ty.ext_slot (L L' : List String) (p k τ : Ty) :
    (Ty.slot p k τ).ext L L' = .slot (p.ext L L') (k.ext L L') (τ.ext L L') := by
  simp [Ty.slot]

@[simp] theorem Ty.ext_array (L L' : List String) (τ : Ty) :
    (Ty.array τ).ext L L' = .array (τ.ext L L') := by
  simp [Ty.array]

@[simp] theorem Ty.ext_maybe (L L' : List String) (z : Nothing) (τ : Ty) :
    (Ty.maybe z τ).ext L L' = .maybe z (τ.ext L L') := by
  simp [Ty.maybe]

@[simp] theorem Ty.ext_absSlot (L L' : List String) : Ty.absSlot.ext L L' = .absSlot := by
  simp [Ty.absSlot, Ty.slot, Ty.abs, Ty.data, Ty.undefined, Con.extL, Con.padL]

@[simp] theorem Ty.ext_undefined (L L' : List String) : Ty.undefined.ext L L' = .undefined := by
  simp [Ty.undefined, Con.extL, Con.padL]

theorem Ty.toRTy_ext (L L' : List String) (τ : Ty) : (τ.toRTy).ext L L' = (τ.ext L L').toRTy := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.ext_app, Ty.ext_app, List.map_append, List.map_map,
      Con.padL_map, RTy.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys => simp [Ty.toRTy]

/-! ## Unfolding -/

theorem RTy.open_ext (L L' : List String) (env : Nat → Ty) (r : RTy) :
    (r.ext L L').open (fun j => (env j).ext L L') = (r.open env).ext L L' := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RTy.ext_app, RTy.open_app, Ty.ext_app, List.map_append, List.map_map,
      Con.padL_map, Function.comp_def, RTy.open_toRTy, Ty.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys _ => simp [RTy.open]

theorem muEnv_ext (L L' : List String) (sys : List RTy) :
    muEnv (sys.map (·.ext L L')) = fun j => (muEnv sys j).ext L L' := by
  funext j; simp [muEnv]

theorem RTy.head_ext (L L' : List String) (r : RTy) (env : Nat → Ty) :
    (r.ext L L').head (fun j => (env j).ext L L') = (r.head env).map (Ty.ext L L') := by
  induction r using RTy.ind generalizing env with
  | free a => simp [RTy.head]
  | self j => simp [RTy.head]
  | app c args _ =>
    rw [RTy.ext_app, RTy.head, RTy.head]
    simp only [List.map_append, List.map_map, Con.padL_map, Function.comp_def, RTy.open_toRTy,
      RTy.open_ext, Option.map_some, Ty.ext_app]
  | mu i sys ih =>
    simp only [RTy.ext_mu, RTy.head_mu, List.getElem?_map]
    cases hr : sys[i]? with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [muEnv_ext]
      exact ih r (List.mem_of_getElem? hr) (muEnv sys)

theorem Ty.view_ext (L L' : List String) (τ : Ty) :
    (τ.ext L L').view = τ.view.map (Ty.ext L L') := by
  have := RTy.head_ext L L' τ.toRTy (fun _ => .undefined)
  rw [Ty.toRTy_ext, RTy.head_toRTy, RTy.head_toRTy] at this
  exact this

/-- Unfolding commutes with the translation. -/
theorem Ty.whnf_ext (L L' : List String) (τ : Ty) : (τ.ext L L').whnf = τ.whnf.ext L L' := by
  unfold Ty.whnf
  rw [Ty.view_ext]
  cases τ.view <;> rfl

/-- `t` with the new slots grafted at its records over `L`, at the depth
that remains. -/
def Tree.graftE (L L' : List String) : Nat → Tree → Tree
  | 0, _ => .bot
  | _ + 1, .bot => .bot
  | _ + 1, .var a => .var a
  | n + 1, .node c ts =>
    .node (c.extL L L') (ts.map (Tree.graftE L L' n) ++ c.padL L L' (Ty.absSlot.approx n))

theorem Ty.approx_ext (L L' : List String) :
    ∀ (n : Nat) (τ : Ty), (τ.ext L L').approx n = (τ.approx n).graftE L L' n
  | 0, _ => rfl
  | n + 1, τ => by
    rw [Ty.approx_succ, Ty.approx_succ, Ty.view_ext]
    cases hv : τ.view with
    | none => rfl
    | some t =>
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · rfl
      · simp only [Option.map_some, Ty.ext_app, Tree.graftE, List.map_append, List.map_map,
          Con.padL_map]
        congr 2
        exact List.map_congr_left (fun a _ => Ty.approx_ext L L' n a)

/-- Equal types stay equal. -/
theorem TyEq.ext (L L' : List String) {s t : Ty} (h : TyEq s t) : TyEq (s.ext L L') (t.ext L L') :=
  fun n => by rw [Ty.approx_ext, Ty.approx_ext, h n]

/-! ## Free type variables and rigid names -/

theorem flatMap_congr_ext {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr_ext (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem Con.padL_flatMap {α β : Type} {L L' : List String} {c : Con} {x : α} {f : α → List β}
    (h : f x = []) : (c.padL L L' x).flatMap f = [] :=
  List.flatMap_eq_nil_iff.mpr fun _ hy => (Con.mem_padL hy) ▸ h

theorem RTy.ftv_ext (L L' : List String) (r : RTy) : (r.ext L L').ftv = r.ftv := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RTy.ext_app, RTy.ftv_app, List.flatMap_append, List.flatMap_map,
      Con.padL_flatMap (f := RTy.ftv) (x := Ty.absSlot.toRTy) rfl, List.append_nil]
    exact flatMap_congr_ext ih
  | mu i sys ih =>
    simp only [RTy.ext_mu, RTy.ftv_mu, List.flatMap_map]
    exact flatMap_congr_ext ih

theorem Ty.ftv_ext (L L' : List String) (τ : Ty) : (τ.ext L L').ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.ext_app, Ty.ftv_app, List.flatMap_append, List.flatMap_map,
      Con.padL_flatMap (f := Ty.ftv) (x := Ty.absSlot) rfl, List.append_nil]
    exact flatMap_congr_ext ih
  | mu i sys =>
    simp only [Ty.ext_mu, Ty.ftv_mu, List.flatMap_map]
    exact flatMap_congr_ext fun r _ => RTy.ftv_ext L L' r

/-! ## Scheme bodies, schemes and constraints -/

mutual
def PTy.ext (L L' : List String) : PTy → PTy
  | .free a => .free a
  | .bound i => .bound i
  | .self j => .self j
  | .app c args => .app (c.extL L L') (PTy.exts L L' args ++ c.padL L L' Ty.absSlot.toPTy)
  | .mu i sys => .mu i (PTy.exts L L' sys)
def PTy.exts (L L' : List String) : List PTy → List PTy
  | [] => []
  | p :: ps => p.ext L L' :: PTy.exts L L' ps
end

@[simp] theorem PTy.exts_eq (L L' : List String) (ps : List PTy) :
    PTy.exts L L' ps = ps.map (PTy.ext L L') := by
  induction ps <;> simp_all [PTy.exts]

@[simp] theorem PTy.ext_app (L L' : List String) (c : Con) (args : List PTy) :
    (PTy.app c args).ext L L' =
      .app (c.extL L L') (args.map (·.ext L L') ++ c.padL L L' Ty.absSlot.toPTy) := by
  simp [PTy.ext]

@[simp] theorem PTy.ext_mu (L L' : List String) (i : Nat) (sys : List PTy) :
    (PTy.mu i sys).ext L L' = .mu i (sys.map (·.ext L L')) := by simp [PTy.ext]

@[simp] theorem PTy.ext_free (L L' : List String) (a : Nat) : (PTy.free a).ext L L' = .free a := rfl
@[simp] theorem PTy.ext_bound (L L' : List String) (i : Nat) : (PTy.bound i).ext L L' = .bound i := rfl
@[simp] theorem PTy.ext_self (L L' : List String) (j : Nat) : (PTy.self j).ext L L' = .self j := rfl

theorem List.getD_map_ext (L L' : List String) (τs : List Ty) (i : Nat) :
    (τs.map (·.ext L L')).getD i .undefined = (τs.getD i .undefined).ext L L' := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases τs[i]? <;> simp

theorem PTy.instR_ext (L L' : List String) (τs : List Ty) (p : PTy) :
    (p.ext L L').instR (τs.map (·.ext L L')) = (p.instR τs).ext L L' := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => simp only [PTy.ext_bound, PTy.instR, List.getD_map_ext, Ty.toRTy_ext]
  | self j => rfl
  | app c args ih =>
    simp only [PTy.ext_app, PTy.instR_app, RTy.ext_app, List.map_append, List.map_map,
      Con.padL_map, Ty.toPTy_instR, RTy.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [PTy.ext_mu, PTy.instR_mu, RTy.ext_mu, List.map_map, RTy.mu.injEq, true_and]
    exact List.map_congr_left ih

theorem PTy.inst_ext (L L' : List String) (τs : List Ty) (p : PTy) :
    (p.ext L L').inst (τs.map (·.ext L L')) = (p.inst τs).ext L L' := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => simp only [PTy.ext_bound, PTy.inst, List.getD_map_ext]
  | self j => simp [PTy.inst]
  | app c args ih =>
    simp only [PTy.ext_app, PTy.inst_app, Ty.ext_app, List.map_append, List.map_map,
      Con.padL_map, Ty.toPTy_inst, Ty.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys _ =>
    simp only [PTy.ext_mu, PTy.inst_mu, Ty.ext_mu, List.map_map, Ty.mu.injEq, true_and]
    exact List.map_congr_left (fun p _ => PTy.instR_ext L L' τs p)

theorem RTy.toPTy_ext (L L' : List String) (r : RTy) : (r.ext L L').toPTy = r.toPTy.ext L L' := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RTy.ext_app, RTy.toPTy_app, PTy.ext_app, List.map_append, List.map_map,
      Con.padL_map, Ty.toRTy_toPTy, PTy.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.ext_mu, RTy.toPTy_mu, PTy.ext_mu, List.map_map, PTy.mu.injEq, true_and]
    exact List.map_congr_left ih

theorem Ty.toPTy_ext (L L' : List String) (τ : Ty) : (τ.ext L L').toPTy = τ.toPTy.ext L L' := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.ext_app, Ty.toPTy_app, PTy.ext_app, List.map_append, List.map_map,
      Con.padL_map, PTy.app.injEq, true_and]
    congr 1
    exact List.map_congr_left ih
  | mu i sys =>
    simp only [Ty.ext_mu, Ty.toPTy_mu, PTy.ext_mu, List.map_map, PTy.mu.injEq, true_and]
    exact List.map_congr_left fun r _ => RTy.toPTy_ext L L' r

theorem PTy.ftv_ext (L L' : List String) (p : PTy) : (p.ext L L').ftv = p.ftv := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => rfl
  | self j => rfl
  | app c args ih =>
    simp only [PTy.ext_app, PTy.ftv_app, List.flatMap_append, List.flatMap_map,
      Con.padL_flatMap (f := PTy.ftv) (x := Ty.absSlot.toPTy) rfl, List.append_nil]
    exact flatMap_congr_ext ih
  | mu i sys ih =>
    simp only [PTy.ext_mu, PTy.ftv_mu, List.flatMap_map]
    exact flatMap_congr_ext ih

theorem PTy.rkeys_ext (L L' : List String) (p : PTy) : (p.ext L L').rkeys = p.rkeys := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => rfl
  | self j => rfl
  | app c args ih =>
    simp only [PTy.ext_app, PTy.rkeys, PTy.rkeysL_eq, List.flatMap_append, List.flatMap_map,
      Con.padL_flatMap (f := PTy.rkeys) (x := Ty.absSlot.toPTy) rfl, List.append_nil,
      Con.extL_rkeys]
    congr 1
    exact flatMap_congr_ext ih
  | mu i sys ih =>
    simp only [PTy.ext_mu, PTy.rkeys, PTy.rkeysL_eq, List.flatMap_map]
    exact flatMap_congr_ext ih

/-- A class with its parameter translated. -/
def Cls.ext (L L' : List String) : Cls → Cls
  | .inject T => .inject (T.ext L L')
  | c => c

def Pred.ext (L L' : List String) (p : Pred) : Pred := ⟨p.cls.ext L L', p.args.map (·.ext L L')⟩

def PPred.ext (L L' : List String) (p : PPred) : PPred := ⟨p.cls.ext L L', p.args.map (·.ext L L')⟩

def Scheme.ext (L L' : List String) (s : Scheme) : Scheme :=
  ⟨s.arity, s.body.ext L L', s.preds.map (PPred.ext L L')⟩

@[simp] theorem Cls.ext_of_ne {L L' : List String} {c : Cls} (h : ∀ T, c ≠ .inject T) :
    c.ext L L' = c := by
  cases c <;> simp_all [Cls.ext]

@[simp] theorem Pred.ext_mk_nr (L L' : List String) {c : Cls} (h : ∀ T, c ≠ .inject T)
    (args : List Ty) : Pred.ext L L' ⟨c, args⟩ = ⟨c, args.map (·.ext L L')⟩ := by
  simp [Pred.ext, Cls.ext_of_ne h]

@[simp] theorem Scheme.ext_arity (L L' : List String) (s : Scheme) : (s.ext L L').arity = s.arity := rfl

theorem PPred.inst_ext (L L' : List String) (τs : List Ty) (p : PPred) :
    (p.ext L L').inst (τs.map (·.ext L L')) = (p.inst τs).ext L L' := by
  simp [PPred.ext, PPred.inst, Pred.ext, PTy.inst_ext]

theorem Scheme.inst_ext (L L' : List String) (τs : List Ty) (s : Scheme) :
    (s.ext L L').inst (τs.map (·.ext L L')) = (s.inst τs).ext L L' := PTy.inst_ext L L' τs s.body

theorem Scheme.instPreds_ext (L L' : List String) (τs : List Ty) (s : Scheme) :
    (s.ext L L').instPreds (τs.map (·.ext L L')) = (s.instPreds τs).map (Pred.ext L L') := by
  simp only [Scheme.instPreds, Scheme.ext, List.map_map]
  exact List.map_congr_left fun p _ => PPred.inst_ext L L' τs p

@[simp] theorem varBlock_ext (L L' : List String) (m k : Nat) :
    (varBlock m k).map (·.ext L L') = varBlock m k := by
  simp [varBlock, Function.comp_def]

theorem Scheme.open_ext (L L' : List String) (s : Scheme) (m : Nat) :
    (s.ext L L').open m = (s.open m).ext L L' := by
  have := Scheme.inst_ext L L' (varBlock m s.arity) s
  rwa [varBlock_ext] at this

theorem Scheme.openPreds_ext (L L' : List String) (s : Scheme) (m : Nat) :
    (s.ext L L').openPreds m = (s.openPreds m).map (Pred.ext L L') := by
  have := Scheme.instPreds_ext L L' (varBlock m s.arity) s
  rwa [varBlock_ext] at this

theorem Scheme.mono_ext (L L' : List String) (τ : Ty) :
    (Scheme.mono τ).ext L L' = .mono (τ.ext L L') := by
  simp [Scheme.mono, Scheme.ext, Ty.toPTy_ext]

@[simp] theorem rigids_ext (L L' : List String) (k n : Nat) :
    (rigids k n).map (·.ext L L') = rigids k n := by
  simp [rigids, Function.comp_def, Con.extL, Con.padL]

theorem Scheme.ftv_ext (L L' : List String) (s : Scheme) : (s.ext L L').ftv = s.ftv := by
  simp only [Scheme.ftv, Scheme.ext, PTy.ftv_ext, List.flatMap_map]
  congr 1
  refine flatMap_congr_ext fun p _ => ?_
  simp [PPred.ftv, PPred.ext, List.flatMap_map, PTy.ftv_ext]

theorem Scheme.rkeys_nil_ext (L L' : List String) {s : Scheme} (hp : s.preds = [])
    (h : s.rkeys = []) : (s.ext L L').rkeys = [] := by
  simp only [Scheme.rkeys, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h ⊢
  simp [Scheme.ext, hp, PTy.rkeys_ext, h.1]

/-- An annotation stays one. -/
theorem Annotated.ext (L L' : List String) {ann : Option Scheme} {s : Scheme}
    (h : Annotated ann s) : Annotated (ann.map (Scheme.ext L L')) (s.ext L L') := by
  intro a ha
  obtain ⟨a₀, rfl, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨rfl, h0, hp, hf, hr⟩ := h a₀ rfl
  exact ⟨rfl, h0, by simp [Scheme.ext, hp], by rw [Scheme.ftv_ext, hf],
    Scheme.rkeys_nil_ext L L' hp hr⟩

@[simp] theorem annMode_ext (L L' : List String) (ann : Option Scheme) :
    annMode (ann.map (Scheme.ext L L')) = annMode ann := by
  cases ann <;> rfl

/-! ## Tree variables -/

theorem Ty.approx_graftE_hasVar (L L' : List String) {a : Nat} :
    ∀ (n : Nat) (τ : Ty), (τ.approx n).HasVar a → ((τ.approx n).graftE L L' n).HasVar a
  | 0, _, h => absurd h Ty.approx_zero_hasVar
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h ⊢
    cases hv : τ.view with
    | none => rw [hv] at h; cases h
    | some t =>
      rw [hv] at h
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · simpa [Tree.graftE] using h
      · dsimp only at h ⊢
        cases h with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          simp only [Tree.graftE, List.map_map]
          exact .node (List.mem_append_left _
            (List.mem_map_of_mem (f := (Tree.graftE L L' n) ∘ Ty.approx n) hx))
            (Ty.approx_graftE_hasVar L L' n x ht)

/-- The translation keeps the tree variables. -/
theorem Ty.TV.ext (L L' : List String) {τ : Ty} {a : Nat} (h : τ.TV a) : (τ.ext L L').TV a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [Ty.approx_ext]; exact Ty.approx_graftE_hasVar L L' n τ hn⟩

theorem PTy.TreeBound.ext {k : Nat} {p : PTy} {i : Nat} (hi : i < k) (h : p.TreeBound k i)
    (L L' : List String) : (p.ext L L').TreeBound k i := by
  have hN := lt_maxPlusOne (l := p.ftv ++ (p.ext L L').ftv)
  generalize maxPlusOne (p.ftv ++ (p.ext L L').ftv) = N at hN
  rw [PTy.treeBound_iff hi (fun a ha => hN a (by simp [ha]))] at h
  rw [PTy.treeBound_iff hi (fun a ha => hN a (by simp [ha]))]
  rw [← varBlock_ext L L' N k, PTy.inst_ext]
  exact h.ext L L'

theorem Scheme.Simple.ext {s : Scheme} (hs : s.Simple) (L L' : List String) :
    (s.ext L L').Simple := by
  intro p hp
  simp only [Scheme.ext, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rcases hs q hq with ⟨hcls, hlen, i, hi, rest, h⟩ | ⟨q', k, τ, t, r, h, hb⟩
  · refine .inl ⟨?_, ?_, i, hi, rest.map (·.ext L L'), ?_⟩
    · obtain ⟨c, args⟩ := q
      cases c <;> simp_all [PPred.ext, Cls.ext]
    · obtain ⟨c, args⟩ := q
      cases c <;> simp_all [PPred.ext, Cls.ext, Cls.arity]
    · simp [PPred.ext, h]
  · subst h
    obtain ⟨i, hi, x, hx, hb⟩ := hb
    refine .inr ⟨q'.ext L L', k.ext L L', τ.ext L L', t.ext L L', r.ext L L',
      by simp [PPred.ext, Cls.ext], i, by simpa [Scheme.ext] using hi, x.ext L L', ?_,
      by simpa using hb.ext hi L L'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp

/-! ## Expressions: annotations -/

mutual
/-- An expression with its annotations translated: a binding's annotation
is the only type an expression carries. -/
def Expr.extAnn (L L' : List String) : Expr → Expr
  | .lit l => .lit l
  | .var i => .var i
  | .func n body => .func n (body.extAnn L L')
  | .app f args => .app (f.extAnn L L') (Expr.extAnns L L' args)
  | .let_ m a e₁ e₂ => .let_ m (a.map (Scheme.ext L L')) (e₁.extAnn L L') (e₂.extAnn L L')
  | .assign i e => .assign i (e.extAnn L L')
  | .cond c t e => .cond (c.extAnn L L') (t.extAnn L L') (e.extAnn L L')
  | .unop op e => .unop op (e.extAnn L L')
  | .binop op e₁ e₂ => .binop op (e₁.extAnn L L') (e₂.extAnn L L')
  | .ret e => .ret (e.extAnn L L')
  | .throw_ e => .throw_ (e.extAnn L L')
  | .seq e₁ e₂ => .seq (e₁.extAnn L L') (e₂.extAnn L L')
  | .while_ c body => .while_ (c.extAnn L L') (body.extAnn L L')
  | .break_ => .break_
  | .continue_ => .continue_
  | .tryCatch body handler => .tryCatch (body.extAnn L L') (handler.extAnn L L')
  | .tryFinally body fin => .tryFinally (body.extAnn L L') (fin.extAnn L L')
  | .obj ls es ks => .obj ls (Expr.extAnns L L' es) ks
  | .get e l => .get (e.extAnn L L') l
  | .set e l v => .set (e.extAnn L L') l (v.extAnn L L')
  | .spread e₁ e₂ => .spread (e₁.extAnn L L') (e₂.extAnn L L')
  | .arr es => .arr (Expr.extAnns L L' es)
  | .index e i => .index (e.extAnn L L') (i.extAnn L L')
  | .setIndex e i v => .setIndex (e.extAnn L L') (i.extAnn L L') (v.extAnn L L')
  | .mcall e l args => .mcall (e.extAnn L L') l (Expr.extAnns L L' args)
  | .cls ls es ks => .cls ls (Expr.extAnns L L' es) ks
  | .ctor n body => .ctor n (body.extAnn L L')
  | .new_ f args => .new_ (f.extAnn L L') (Expr.extAnns L L' args)
  | .unwrap e₁ e₂ e₃ => .unwrap (e₁.extAnn L L') (e₂.extAnn L L') (e₃.extAnn L L')
  | .caseTag e₁ d t e₂ e₃ => .caseTag (e₁.extAnn L L') d t (e₂.extAnn L L') (e₃.extAnn L L')
def Expr.extAnns (L L' : List String) : List Expr → List Expr
  | [] => []
  | e :: es => e.extAnn L L' :: Expr.extAnns L L' es
end

@[simp] theorem Expr.extAnns_eq (L L' : List String) (es : List Expr) :
    Expr.extAnns L L' es = es.map (Expr.extAnn L L') := by
  induction es <;> simp_all [Expr.extAnns]

attribute [simp] Expr.extAnn

theorem Expr.IsValue.extAnn (L L' : List String) {e : Expr} (h : e.IsValue) :
    (e.extAnn L L').IsValue := by
  cases h <;> constructor

theorem Expr.writesList_extAnn (L L' : List String) (i : Nat) :
    ∀ {es : List Expr}, (∀ e ∈ es, ∀ i, (e.extAnn L L').writes i = e.writes i) →
      Expr.writesList i (es.map (Expr.extAnn L L')) = Expr.writesList i es
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.map_cons, Expr.writesList, h e List.mem_cons_self,
      Expr.writesList_extAnn L L' i (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

theorem Expr.writesCls_extAnn (L L' : List String) (i : Nat) :
    ∀ (d : Nat) {es : List Expr} (ks : List ClassKind),
      (∀ e ∈ es, ∀ i, (e.extAnn L L').writes i = e.writes i) →
      Expr.writesCls i d (es.map (Expr.extAnn L L')) ks = Expr.writesCls i d es ks
  | _, [], _, _ => by simp [Expr.writesCls]
  | _, _ :: _, [], _ => by simp [Expr.writesCls]
  | d, e :: es, k :: ks, h => by
    have he := h e List.mem_cons_self
    have hes := fun d => Expr.writesCls_extAnn L L' i d ks
      (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    cases k <;> simp only [List.map_cons, Expr.writesCls, he, hes]

/-- The translation keeps the assignments. -/
theorem Expr.writes_extAnn (L L' : List String) (e : Expr) :
    ∀ i, (e.extAnn L L').writes i = e.writes i := by
  induction e using Expr.ind <;> intro i <;>
    simp_all [Expr.writes, Expr.writesList_extAnn, Expr.writesCls_extAnn]

theorem litTag_extAnn (L L' : List String) (l : String) : ∀ (ls : List String) (es : List Expr),
    litTag l ls (es.map (Expr.extAnn L L')) = litTag l ls es
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, e :: es => by
    simp only [List.map_cons, litTag]
    split
    · cases e with
      | lit lit => cases lit <;> rfl
      | _ => rfl
    · exact litTag_extAnn L L' l ls es

/-! ## Fields and slots -/

theorem Ty.field_ext (L L' : List String) (l : String) :
    ∀ (ls : List String) (fs : List Ty),
      Ty.field l ls (fs.map (·.ext L L')) = (Ty.field l ls fs).map (·.ext L L')
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l' :: ls, τ :: τs => by
    simp only [List.map_cons, Ty.field]
    split
    · rfl
    · exact Ty.field_ext L L' l ls τs

theorem Ty.field_append_of_some {l : String} {s : Ty} :
    ∀ {ls : List String} {fs : List Ty}, Ty.field l ls fs = some s →
      ∀ (ls' : List String) (fs' : List Ty), Ty.field l (ls ++ ls') (fs ++ fs') = some s
  | [], _, h, _, _ => by simp [Ty.field] at h
  | _ :: _, [], h, _, _ => by simp [Ty.field] at h
  | l' :: ls, f :: fs, h, ls', fs' => by
    simp only [Ty.field] at h
    simp only [List.cons_append, Ty.field]
    split
    · simp_all
    · simp only [*, ite_false] at h
      exact Ty.field_append_of_some h ls' fs'

theorem Ty.field_none_of_not_mem {l : String} :
    ∀ {ls : List String} (fs : List Ty), l ∉ ls → Ty.field l ls fs = none
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | l' :: ls, _ :: fs, h => by
    simp only [List.mem_cons, not_or] at h
    have hne : l' ≠ l := Ne.symm h.1
    simp only [Ty.field, hne, ↓reduceIte]
    exact Ty.field_none_of_not_mem fs h.2

/-- A record's field, through the translation. -/
theorem Ty.field_ext_rec (L L' : List String) {l : String} {ls : List String} {fs : List Ty} {s : Ty}
    (h : Ty.field l ls fs = some s) :
    Ty.field l (if ls = L then L ++ L' else ls)
      (fs.map (·.ext L L') ++ (Con.record ls).padL L L' Ty.absSlot) = some (s.ext L L') := by
  have h' : Ty.field l ls (fs.map (·.ext L L')) = some (s.ext L L') := by
    rw [Ty.field_ext, h]; rfl
  by_cases hl : ls = L
  · subst hl; simpa using Ty.field_append_of_some h' L' _
  · simpa [Con.padL, hl] using h'

/-- The slots of an object over `L ++ L'`: those over `L`, then the new
labels' absent ones, since the object has none of them. -/
theorem objSlots_ext {L L' : List String} (hL : ∀ l ∈ L', l ∉ L) {ls : List String}
    (hls : ∀ l ∈ ls, l ∈ L) (ss : List Ty) :
    (objSlots L ls ss).map (·.ext L L') ++ L'.map (fun _ => Ty.absSlot) =
      objSlots (L ++ L') ls (ss.map (·.ext L L')) := by
  simp only [objSlots, List.map_append, List.map_map, ← List.map_reverse, Ty.field_ext]
  congr 1
  · apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply]
    generalize Ty.field l ls.reverse ss.reverse = o
    cases o <;> simp
  · apply List.map_congr_left
    intro l hl
    have : l ∉ ls.reverse := fun h => hL l hl (hls l (List.mem_reverse.mp h))
    simp [Ty.field_none_of_not_mem _ this]

theorem mergePreds_ext (L L' : List String) : ∀ (ps ks τs ss rs : List Ty),
    (mergePreds ps ks τs ss rs).map (Pred.ext L L') =
      mergePreds (ps.map (·.ext L L')) (ks.map (·.ext L L')) (τs.map (·.ext L L'))
        (ss.map (·.ext L L')) (rs.map (·.ext L L'))
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs => by
    simp only [mergePreds, List.map_cons, ← mergePreds_ext L L' ps ks τs ss rs]
    simp [Pred.ext, Cls.ext]
  | [], _, _, _, _ | _ :: _, [], _, _, _ | _ :: _, _ :: _, [], _, _
  | _ :: _, _ :: _, _ :: _, [], _ | _ :: _, _ :: _, _ :: _, _ :: _, [] => by
    simp [mergePreds]

theorem mergePreds_append : ∀ (ps ks τs ss rs ps' ks' τs' ss' rs' : List Ty),
    ks.length = ps.length → τs.length = ps.length → ss.length = ps.length →
    rs.length = ps.length →
    mergePreds (ps ++ ps') (ks ++ ks') (τs ++ τs') (ss ++ ss') (rs ++ rs') =
      mergePreds ps ks τs ss rs ++ mergePreds ps' ks' τs' ss' rs'
  | [], [], [], [], [], _, _, _, _, _, _, _, _, _ => rfl
  | p :: ps, k :: ks, τ :: τs, s :: ss, r :: rs, ps', ks', τs', ss', rs', h₁, h₂, h₃, h₄ => by
    simp only [List.cons_append, mergePreds]
    rw [mergePreds_append ps ks τs ss rs ps' ks' τs' ss' rs' (by simpa using h₁)
      (by simpa using h₂) (by simpa using h₃) (by simpa using h₄)]
  | [], _ :: _, _, _, _, _, _, _, _, _, h, _, _, _
  | _ :: _, [], _, _, _, _, _, _, _, _, h, _, _, _ => by simp at h
  | [], [], _ :: _, _, _, _, _, _, _, _, _, h, _, _
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, h, _, _ => by simp at h
  | [], [], [], _ :: _, _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, h, _ => by simp at h
  | [], [], [], [], _ :: _, _, _, _, _, _, _, _, _, h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, h => by simp at h

/-- The new labels' `Merge`s: absent over absent. -/
theorem mergePreds_abs (L' : List String) :
    mergePreds (L'.map fun _ => Ty.abs) (L'.map fun _ => Ty.data) (L'.map fun _ => Ty.undefined)
      (L'.map fun _ => Ty.absSlot) (L'.map fun _ => Ty.absSlot) =
      L'.map fun _ => ⟨.merge, [.abs, .data, .undefined, .absSlot, .absSlot]⟩ := by
  induction L' with
  | nil => rfl
  | cons _ L' ih => simp only [List.map_cons, mergePreds, ih]

theorem slots3_ext (L L' : List String) : ∀ (ps ks τs : List Ty),
    (slots3 ps ks τs).map (·.ext L L') =
      slots3 (ps.map (·.ext L L')) (ks.map (·.ext L L')) (τs.map (·.ext L L'))
  | p :: ps, k :: ks, τ :: τs => by
    simp only [slots3, List.map_cons, slots3_ext L L' ps ks τs]
    simp
  | [], _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] => by simp [slots3]

theorem slots3_append : ∀ (ps ks τs ps' ks' τs' : List Ty),
    ks.length = ps.length → τs.length = ps.length →
    slots3 (ps ++ ps') (ks ++ ks') (τs ++ τs') = slots3 ps ks τs ++ slots3 ps' ks' τs'
  | [], [], [], _, _, _, _, _ => rfl
  | p :: ps, k :: ks, τ :: τs, ps', ks', τs', h₁, h₂ => by
    simp only [List.cons_append, slots3]
    rw [slots3_append ps ks τs ps' ks' τs' (by simpa using h₁) (by simpa using h₂)]
  | [], _ :: _, _, _, _, _, h, _ | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | [], [], _ :: _, _, _, _, _, h | _ :: _, _ :: _, [], _, _, _, _, h => by simp at h

theorem slots3_abs (L' : List String) :
    slots3 (L'.map fun _ => Ty.abs) (L'.map fun _ => Ty.data) (L'.map fun _ => Ty.undefined) =
      L'.map fun _ => Ty.absSlot := by
  induction L' with
  | nil => rfl
  | cons _ L' ih => simp only [List.map_cons, slots3, ih]

theorem SlotCopy.ext (L L' : List String) (h : SlotCopy s r) : SlotCopy (s.ext L L') (r.ext L L') := by
  cases h <;> simp <;> constructor

theorem PredEq.ext (L L' : List String) {p q : Pred} (h : PredEq p q) :
    PredEq (p.ext L L') (q.ext L L') := by
  obtain ⟨hc, hl, hz⟩ := h
  refine ⟨by simp [Pred.ext, hc], by simp [Pred.ext, hl], fun x hx => ?_⟩
  simp only [Pred.ext] at hx
  rw [List.zip_map] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact TyEq.ext L L' (hz y hy)

theorem Ty.whnf_ext_of_app {L L' : List String} {T : Ty} {c : Con} {xs : List Ty}
    (h : T.whnf = .app c xs) : (T.ext L L').whnf = (Ty.app c xs).ext L L' := by
  rw [Ty.whnf_ext, h]

theorem Ty.whnf_ext_nr {L L' : List String} {T : Ty} {c : Con} {xs : List Ty}
    (h : T.whnf = .app c xs) (hc : ∀ ls, c ≠ .record ls) :
    (T.ext L L').whnf = .app c (xs.map (·.ext L L')) := by
  rw [Ty.whnf_ext, h, Ty.ext_app_nr hc]

theorem Ty.tagOf_ext (L L' : List String) {l : String} {R : Ty} {t : Tag}
    (h : R.tagOf l = some t) : (R.ext L L').tagOf l = some t := by
  unfold Ty.tagOf at h ⊢
  split at h
  · rename_i ls slots hR
    rw [Ty.whnf_ext, hR, Ty.ext_app]
    simp only [Con.extL]
    split at h
    · rename_i s hs
      rw [Ty.field_ext_rec L L' hs]
      simp only
      split at h
      · rename_i p k τ hsw
        rw [Ty.whnf_ext_nr hsw (by simp)]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_ext_nr hp (by simp), Ty.whnf_ext_nr hk (by simp)]
          simp only [List.map_nil, and_self, ↓reduceIte]
          split at h
          · rename_i t' hτ
            rw [Ty.whnf_ext_nr hτ (by simp)]
            simpa using h
          · rename_i b hτ
            rw [Ty.whnf_ext_nr hτ (by simp)]
            simpa using h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem Ty.dataField_ext (L L' : List String) {T : Ty} {l : String} {τ : Ty}
    (h : T.dataField l = some τ) : (T.ext L L').dataField l = some (τ.ext L L') := by
  unfold Ty.dataField at h ⊢
  split at h
  · rename_i ls slots hT
    rw [Ty.whnf_ext, hT, Ty.ext_app]
    simp only [Con.extL]
    split at h
    · rename_i s hs
      rw [Ty.field_ext_rec L L' hs]
      simp only
      split at h
      · rename_i p k τ' hsw
        rw [Ty.whnf_ext_nr hsw (by simp)]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_ext_nr hp (by simp), Ty.whnf_ext_nr hk (by simp)]
          simp only [List.map_nil, and_self, ↓reduceIte]
          simp only [Option.some.injEq] at h ⊢
          rw [h]
        · cases h
      · cases h
    · cases h
  · cases h

theorem Ty.dataFields_ext (L L' : List String) {T : Ty} : ∀ {ls : List String} {τs : List Ty},
    T.dataFields ls = some τs → (T.ext L L').dataFields ls = some (τs.map (·.ext L L'))
  | [], τs, h => by
    simp only [Ty.dataFields, Option.some.injEq] at h ⊢
    subst h; rfl
  | l :: ls, τs, h => by
    simp only [Ty.dataFields] at h ⊢
    split at h
    · rename_i τ τs' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rw [Ty.dataField_ext L L' h1, Ty.dataFields_ext L L' h2]
      rfl
    · cases h

theorem variantRest_ext (L L' : List String) (d : Disc) (ts : List Tag) (Rs : List Ty) :
    (variantRest d ts Rs).ext L L' = variantRest d ts (Rs.map (·.ext L L')) := by
  match Rs with
  | [] => simp [variantRest]
  | [_] => rfl
  | _ :: _ :: _ => simp [variantRest]

theorem ObjCase.ext (L L' : List String) {ls : List String} {es : List Expr} {T P : Ty}
    (h : ObjCase ls es T P) : ObjCase ls (es.map (Expr.extAnn L L')) (T.ext L L') (P.ext L L') := by
  cases h with
  | self => exact .self
  | variant hw hl hi hP ht =>
    exact .variant (Ty.whnf_ext_nr hw (by simp)) (by rw [litTag_extAnn]; exact hl) hi
      (by simp [hP]) (Ty.tagOf_ext L L' ht)

/-! ## Instances and entailment -/

@[simp] theorem Nothing.ty_ext (L L' : List String) (z : Nothing) : z.ty.ext L L' = z.ty := by
  cases z <;> simp [Nothing.ty, Nothing.con]

theorem Inst.ext (L L' : List String) {p : Pred} (h : Inst p) : Inst (p.ext L L') := by
  induction h with
  | plusNumber => simpa [Pred.ext, Cls.ext] using Inst.plusNumber
  | plusString => simpa [Pred.ext, Cls.ext] using Inst.plusString
  | @hasProp l ls fs k σ hf =>
    have := Inst.hasProp (k := k.ext L L') (Ty.field_ext_rec L L' hf)
    simpa [Pred.ext, Cls.ext, Con.extL] using this
  | mergeData => simpa [Pred.ext, Cls.ext] using Inst.mergeData
  | mergeGetter => simpa [Pred.ext, Cls.ext] using Inst.mergeGetter
  | mergeAbs hs => simpa [Pred.ext, Cls.ext] using Inst.mergeAbs (k := _) (τ := _) (hs.ext L L')
  | mergeProto hs => simpa [Pred.ext, Cls.ext] using Inst.mergeProto (τ := _) (hs.ext L L')
  | lengthArray => simpa [Pred.ext, Cls.ext] using Inst.lengthArray
  | lengthString => simpa [Pred.ext, Cls.ext] using Inst.lengthString
  | indexArray => simpa [Pred.ext, Cls.ext] using Inst.indexArray
  | indexString => simpa [Pred.ext, Cls.ext] using Inst.indexString
  | writeArray => simpa [Pred.ext, Cls.ext] using Inst.writeArray
  | @notNew c args hn =>
    have hn' : ¬ (c.extL L L' = .newTarget ∨ (c.extL L L').isRigid) := by
      rw [Con.extL_eq_iff (by simp), Con.extL_isRigid]; exact hn
    simpa [Pred.ext, Cls.ext] using Inst.notNew (args := args.map (·.ext L L') ++
      c.padL L L' Ty.absSlot) hn'
  | @injectSelf T hT =>
    simpa [Pred.ext, Cls.ext] using Inst.injectSelf (T := T.ext L L') (by rw [Ty.ftv_ext, hT])
  | injectNothing he hT =>
    simpa [Pred.ext, Cls.ext] using
      Inst.injectNothing (TyEq.ext L L' he) (by rw [Ty.ftv_ext, hT])
  | @injectSome T z c args he hT ha hc hn =>
    have he' := TyEq.ext L L' he
    have hT' : (T.ext L L').ftv = [] := by rw [Ty.ftv_ext, hT]
    have ha' : ((Ty.app c args).ext L L').ftv = [] := by rw [Ty.ftv_ext, ha]
    simp only [Ty.maybe, Ty.ext_app_nr (c := .maybe z) (by simp), List.map_cons,
      List.map_nil] at he'
    rcases Con.extL_cases L L' c Ty.absSlot with ⟨h1, h2⟩ | ⟨rfl, h1, h2⟩
    · rw [Ty.ext_app, h1, h2, List.append_nil] at he' ha'
      simpa [Pred.ext, Cls.ext, h1, h2] using
        Inst.injectSome he' hT' ha' hc (fun ⟨e, h⟩ => hn ⟨e, by simpa using h⟩)
    · rw [Ty.ext_app, h1, h2] at he' ha'
      have := Inst.injectSome he' hT' ha' (by simp) (by cases z <;> simp [Nothing.con])
      simpa [Pred.ext, Cls.ext, h1, h2] using this
  | @injectArm t ts i Rs R c args T hT hw hn hc hi hR he ha =>
    have := Inst.injectArm (T := T.ext L L') (Rs := Rs.map (·.ext L L')) (R := R.ext L L')
      (c := c.extL L L') (args := args.map (·.ext L L') ++ c.padL L L' Ty.absSlot)
      (by rw [Ty.ftv_ext, hT]) (Ty.whnf_ext_nr hw (by simp)) hn (by simpa using hc) hi
      (by simp [hR]) (by simpa using TyEq.ext L L' he)
      (by simpa using (show ((Ty.app c args).ext L L').ftv = [] by rw [Ty.ftv_ext, ha]))
    simpa [Pred.ext, Cls.ext] using this
  | injectLit _ hx ih =>
    simpa [Pred.ext, Cls.ext] using
      Inst.injectLit (by simpa [Pred.ext, Cls.ext] using ih) (by simpa using TyEq.ext L L' hx)
  | stripSome => simpa [Pred.ext, Cls.ext] using Inst.stripSome
  | @stripSelf c args hm hn hu =>
    rcases Con.extL_cases L L' c Ty.absSlot with ⟨h1, h2⟩ | ⟨rfl, h1, h2⟩
    · simpa [Pred.ext, Cls.ext, h1, h2] using
        Inst.stripSelf (args := args.map (·.ext L L')) hm hn hu
    · simpa [Pred.ext, Cls.ext, h1, h2] using
        Inst.stripSelf (c := .record (L ++ L')) (args := args.map (·.ext L L') ++
          L'.map (fun _ => Ty.absSlot)) (by simp) (by simp) (by simp)
  | @caseHit ts i t Rs R d hn hi hR =>
    have := Inst.caseHit (d := d) (Rs := Rs.map (·.ext L L')) (R := R.ext L L') hn hi
      (by simp [hR])
    simpa [Pred.ext, Cls.ext, variantRest_ext, ← eraseIdx_map] using this

theorem InstEq.ext (L L' : List String) {p : Pred} (h : InstEq p) : InstEq (p.ext L L') := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.ext L L', hpq.ext L L', hq.ext L L'⟩

theorem InstW.ext (L L' : List String) {p : Pred} (h : InstW p) : InstW (p.ext L L') := by
  cases h with
  | narrow h hc =>
    refine .narrow (h.ext L L') fun T e => ?_
    obtain ⟨c, args⟩ := p
    simp only at hc
    simp only [Pred.ext, Cls.ext_of_ne hc] at e
    exact hc T e
  | injectSelf => simpa [Pred.ext, Cls.ext] using InstW.injectSelf
  | injectNothing => simpa [Pred.ext, Cls.ext] using InstW.injectNothing
  | injectSome => simpa [Pred.ext, Cls.ext] using InstW.injectSome
  | @injectArm Rs i R c xs t ts hR hw hc hi =>
    have := InstW.injectArm (Rs := Rs.map (·.ext L L')) (by simp [hR])
      (Ty.whnf_ext_of_app (L := L) (L' := L') hw) (by simpa using hc) hi
    simpa [Pred.ext, Cls.ext] using this
  | injectLitSelf => simpa [Pred.ext, Cls.ext] using InstW.injectLitSelf
  | injectLitSome => simpa [Pred.ext, Cls.ext] using InstW.injectLitSome
  | @injectLitArm Rs i R ts s hR hw hi =>
    have := InstW.injectLitArm (s := s) (Rs := Rs.map (·.ext L L')) (by simp [hR])
      (Ty.whnf_ext_of_app (L := L) (L' := L') hw) hi
    simpa [Pred.ext, Cls.ext] using this
  | stripSelf => simpa [Pred.ext, Cls.ext] using InstW.stripSelf

theorem InstEqW.ext (L L' : List String) {p : Pred} (h : InstEqW p) : InstEqW (p.ext L L') := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.ext L L', hpq.ext L L', hq.ext L L'⟩

/-- A system whose instances, expected types and injections survive the
translation, and in which a new label's `Merge`, absent over absent,
holds. -/
structure Sys.LExtable (S : Sys) (L L' : List String) : Prop where
  inst : ∀ {p : Pred}, S.inst p → S.inst (p.ext L L')
  closed : ∀ {T : Ty}, S.closed T → S.closed (T.ext L L')
  injPred : ∀ τ T, (S.injPred τ T).ext L L' = S.injPred (τ.ext L L') (T.ext L L')
  mergeAbs : S.inst ⟨.merge, [.abs, .data, .undefined, .absSlot, .absSlot]⟩

theorem Sys.narrow_lextable (L L' : List String) : Sys.narrow.LExtable L L' where
  inst := InstEq.ext L L'
  closed := fun h => by
    show Ty.ftv _ = []
    rw [Ty.ftv_ext]; exact h
  injPred _ _ := rfl
  mergeAbs := (Inst.mergeAbs SlotCopy.abs).instEq

theorem Sys.wide_lextable (L L' : List String) : Sys.wide.LExtable L L' where
  inst := InstEqW.ext L L'
  closed := fun _ => trivial
  injPred _ _ := rfl
  mergeAbs := ⟨_, PredEq.refl _, InstW.narrow (Inst.mergeAbs SlotCopy.abs) (by simp)⟩

theorem EntailsS.extS {S : Sys} {L L' : List String} (hS : S.LExtable L L') {C : List Pred}
    {p : Pred} (h : EntailsS S C p) : EntailsS S (C.map (Pred.ext L L')) (p.ext L L') :=
  h.elim (fun h => .inl (hS.inst h))
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.ext L L', List.mem_map_of_mem hq, hpq.ext L L'⟩)

theorem Ty.whnf_ext_var {L L' : List String} {t : Ty} {a : Nat} (h : t.whnf = .var a) :
    (t.ext L L').whnf = .var a := by
  rw [Ty.whnf_ext, h]; rfl

theorem Ty.whnf_ext_con {L L' : List String} {t : Ty} {c : Con} (h : t.whnf = .app c [])
    (hc : ∀ ls, c ≠ .record ls) : (t.ext L L').whnf = .app c [] := by
  rw [Ty.whnf_ext_nr h hc]; rfl

theorem Ty.SlotOnVar.ext (L L' : List String) {s : Ty} (h : s.SlotOnVar) : (s.ext L L').SlotOnVar := by
  unfold Ty.SlotOnVar at h ⊢
  generalize hw : s.whnf = w at h
  match w, h with
  | .var a, _ => rw [Ty.whnf_ext_var hw]; trivial
  | .slot p k τ, h =>
    rw [Ty.whnf_ext_nr hw (by simp)]
    simp only [List.map_cons, List.map_nil]
    rcases h with ⟨a, ha⟩ | ⟨hpre, a, ha⟩
    · exact .inl ⟨a, Ty.whnf_ext_var ha⟩
    · exact .inr ⟨Ty.whnf_ext_con hpre (by simp), a, Ty.whnf_ext_var ha⟩

theorem Pred.OnVar.ext (L L' : List String) {p : Pred} (h : p.OnVar) : (p.ext L L').OnVar := by
  rcases h with ⟨t, a, rest, he, hw⟩ | hm
  · exact .inl ⟨t.ext L L', a, rest.map (·.ext L L'), by simp [Pred.ext, he], Ty.whnf_ext_var hw⟩
  · right
    obtain ⟨c, args⟩ := p
    unfold Pred.MergeOnVar at hm
    split at hm
    · rename_i q k τ s r heq
      simp only [Pred.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Pred.ext_mk_nr L L' (c := .merge) (by simp), List.map_cons, List.map_nil]
      unfold Pred.MergeOnVar
      rcases hm with ⟨hpre, a, ha⟩ | ⟨hqk, hsv⟩
      · exact .inl ⟨Ty.whnf_ext_con hpre (by simp), a, Ty.whnf_ext_var ha⟩
      · refine .inr ⟨?_, hsv.ext L L'⟩
        rcases hqk with ⟨hpre, hpro⟩ | habs
        · exact .inl ⟨Ty.whnf_ext_con hpre (by simp), Ty.whnf_ext_con hpro (by simp)⟩
        · exact .inr (Ty.whnf_ext_con habs (by simp))
    · exact hm.elim

/-- The constraints that hold or are on type variables still do. -/
theorem HoldsOrVarS.ext {S : Sys} {L L' : List String} (hS : S.LExtable L L') {C : List Pred}
    (h : HoldsOrVarS S C) : HoldsOrVarS S (C.map (Pred.ext L L')) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).imp hS.inst (Pred.OnVar.ext L L')

/-! ## Members -/

theorem FieldSlot.ext (L L' : List String) (h : FieldSlot T k e τ s) :
    FieldSlot (T.ext L L') k (e.extAnn L L') (τ.ext L L') (s.ext L L') := by
  cases h with
  | data => simpa using FieldSlot.data (T := T.ext L L') (e := e.extAnn L L') (τ := τ.ext L L')
  | method he => simpa [Ty.fn] using FieldSlot.method (τs := _) (ρ := _) (he.ext L L')
  | getter he => simpa [Ty.fn] using FieldSlot.getter (σ := _) (he.ext L L')

theorem MemberSlotS.ext {S : Sys} {L L' : List String} (hS : S.LExtable L L')
    (h : MemberSlotS S C T k e τ s) :
    MemberSlotS S (C.map (Pred.ext L L')) (T.ext L L') k (e.extAnn L L') (τ.ext L L')
      (s.ext L L') := by
  cases h with
  | data =>
    simpa using MemberSlotS.data (S := S) (C := C.map (Pred.ext L L')) (T := T.ext L L')
      (e := e.extAnn L L') (τ := τ.ext L L')
  | arrow he hn =>
    simpa [Ty.fn] using MemberSlotS.arrow (τs := _) (ρ := _) (he.ext L L')
      (by simpa using hn.extS hS)
  | method he => simpa [Ty.fn] using MemberSlotS.method (τs := _) (ρ := _) (he.ext L L')
  | getter he => simpa [Ty.fn] using MemberSlotS.getter (σ := _) (he.ext L L')

theorem memberCtx_ext (L L' : List String) (Γ : Ctx) (ks : List ClassKind) (τs : List Ty)
    (i : Nat) (k : ClassKind) :
    (memberCtx Γ ks τs i k).map (Scheme.ext L L') =
      memberCtx (Γ.map (Scheme.ext L L')) ks (τs.map (·.ext L L')) i k := by
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
      cases k <;> simp_all [Scheme.mono_ext]
  | _ => rfl

theorem zip4_map' {α δ β γ : Type} (h : δ → δ) (f : β → β) (g : γ → γ) :
    ∀ (ks : List α) (es : List δ) (τs : List β) (ss : List γ),
      ks.zip ((es.map h).zip ((τs.map f).zip (ss.map g))) =
        (ks.zip (es.zip (τs.zip ss))).map (fun x => (x.1, h x.2.1, f x.2.2.1, g x.2.2.2))
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | k :: ks, e :: es, t :: ts, s :: ss => by simp [zip4_map' h f g ks es ts ss]

/-! ## Derivations -/

/-- Typing is stable when the program's labels `L` are extended with labels
`L'` apart from them: every record over `L` gets an absent slot for each new
label, through the whole derivation (its constraints, context, return type,
type and annotations), in a system whose instances, expected types and
injections survive that (`Sys.LExtable`), as the narrow and the wide ones
do. -/
theorem HasTypeS.extLabels {S : Sys} {L L' : List String} (hS : S.LExtable L L')
    (hL : ∀ l ∈ L', l ∉ L) (h : HasTypeS S L C Γ R rm md e τ) :
    HasTypeS S (L ++ L') (C.map (Pred.ext L L')) (Γ.map (Scheme.ext L L')) (R.map (Ty.ext L L'))
      rm md (e.extAnn L L') (τ.ext L L') := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen hc =>
    rw [← Scheme.inst_ext]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa using hlen) ?_
    intro c hc'
    rw [Scheme.instPreds_ext] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).extS hS
  | func hlen _ ih =>
    rw [Ty.ext_fn]
    refine .func (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_ext] using ih
  | funcCheck hT hT₀ hlen _ ih =>
    refine .funcCheck (by rw [Ty.whnf_ext, hT, Ty.ext_fn]) (hS.closed hT₀) (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_ext] using ih
  | app _ hlen _ ihf iha =>
    simp only [Expr.extAnn, Expr.extAnns_eq]
    refine .app (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_)
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    simp only [Expr.extAnn]
    refine .let_ (s.ext L L') F (fun m hm => ?_) ?_ (hs.imp id (·.ext L L')) (ha.ext L L')
      (by simpa using ih₂)
    · rw [Scheme.open_ext, Scheme.openPreds_ext, ← List.map_append, annMode_ext]
      exact ih₁ m hm
    · rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, by simp [Scheme.ext, h2]⟩
      · exact .inr ⟨h1.extAnn L L', by rw [Expr.writes_extAnn]; exact h2⟩
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ =>
    simp only [Expr.extAnn, Option.map_some]
    refine .letPoly (a.ext L L') K h0 (by simp [Scheme.ext, hp]) (by rw [Scheme.ftv_ext]; exact hf)
      (Scheme.rkeys_nil_ext L L' hp hr) (fun k hk => ?_) (hv.extAnn L L')
      (by rw [Expr.writes_extAnn]; exact hw) (by simpa using ih₂)
    have := ih₁ k hk
    rwa [← Scheme.inst_ext, rigids_ext] at this
  | assign hi ha hp _ ih =>
    rw [← Scheme.inst_ext]
    refine .assign (by simp [List.getElem?_map, hi]) (by simpa using ha)
      (by simp [Scheme.ext, hp]) ?_
    simpa [← Scheme.inst_ext] using ih
  | @assignCheck _ i s T _ _ _ _ hs hi ha hp hT hc _ ih =>
    refine .assignCheck (s := s.ext L L') hs (by simp [List.getElem?_map, hi]) (by simpa using ha)
      (by simp [Scheme.ext, hp]) ?_ (hS.closed hc) ih
    have := TyEq.ext L L' hT
    rwa [← Scheme.inst_ext, List.map_nil] at this
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih =>
    cases hop with
    | not => exact .unop .not ih
    | typeof => exact .unop .typeof ih
    | neg => exact .unop .neg ih
  | binop hop _ _ ih₁ ih₂ =>
    cases hop with
    | plus hc => exact .binop (.plus (by simpa using hc.extS hS)) ih₁ ih₂
    | num h =>
      rw [show ∀ o : BinOp, o.resTy.ext L L' = o.resTy from fun o => by cases o <;> rfl]
      exact .binop (.num h) ih₁ ih₂
    | strictEq => exact .binop .strictEq ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb (by simpa [Scheme.mono_ext] using ihh)
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ =>
    exact .unwrap ih₁ (by simpa using hs.extS hS) ih₂ (by simpa [Scheme.mono_ext] using ih₃)
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf
  | @obj ls C Γ R rm ss es ks τs hes hks hτs hss hls _ hm ih =>
    simp only [Expr.extAnn, Expr.extAnns_eq, Ty.ext_record_self, objSlots_ext hL hls]
    refine .obj (τs := τs.map (·.ext L L')) (by simpa using hes) hks (by simpa using hτs)
      (by simpa using hss) (fun l hl => List.mem_append_left _ (hls l hl)) (fun p hp => ?_)
      (fun x hx => ?_)
    · rw [List.zip_map] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
    · rw [zip4_map'] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).ext L L'
      rwa [Ty.ext_record_self, objSlots_ext hL hls] at this
  | @cls ls es ks τs C Γ ss R rm hes hks hτs hss hnd hls _ hm ih =>
    simp only [Expr.extAnn, Expr.extAnns_eq, Ty.ext_record_self, objSlots_ext hL hls]
    refine .cls (τs := τs.map (·.ext L L')) (by simpa using hes) hks (by simpa using hτs)
      (by simpa using hss) hnd (fun l hl => List.mem_append_left _ (hls l hl))
      (fun i e k τ he hk hτ => ?_) (fun x hx => ?_)
    · rw [List.getElem?_map] at hτ he
      obtain ⟨τ₀, hτ₀, rfl⟩ := Option.map_eq_some_iff.mp hτ
      obtain ⟨e₀, he₀, rfl⟩ := Option.map_eq_some_iff.mp he
      have := ih i e₀ k τ₀ he₀ hk hτ₀
      rw [memberCtx_ext] at this
      simpa using this
    · rw [zip4_map'] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).ext hS
      rwa [Ty.ext_record_self, objSlots_ext hL hls] at this
  | ctor hlen _ ih =>
    rw [Ty.ext_fn]
    refine .ctor (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def, Scheme.mono_ext] using ih
  | @new_ C Γ R rm f τs ρ ss args _ hlen _ hρ hss ihf iha =>
    simp only [Expr.extAnn, Expr.extAnns_eq]
    refine .new_ (ss := ss.map (·.ext L L') ++ L'.map (fun _ => Ty.absSlot)) (by simpa using ihf)
      (by simpa using hlen) (fun p hp => ?_) (by simpa using hρ.ext L L') (by simp [hss])
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | get _ hp ih => exact .get ih (by simpa using hp.extS hS)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa using hp.extS hS) ihv
  | @spread C Γ R rm e₁ ss e₂ ps ks τs rs hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    simp only [Expr.extAnn, Ty.ext_record_self] at ih₁ ih₂ ⊢
    refine .spread (ps := ps.map (·.ext L L') ++ L'.map (fun _ => .abs))
      (ks := ks.map (·.ext L L') ++ L'.map (fun _ => .data))
      (τs := τs.map (·.ext L L') ++ L'.map (fun _ => .undefined))
      (by simp [hps]) (by simp [hks]) (by simp [hτs]) (by simp [hss]) (by simp [hrs]) ih₁ ?_
      (fun p hp => ?_)
    · rw [slots3_append _ _ _ _ _ _ (by simp [hks, hps]) (by simp [hτs, hps]), ← slots3_ext,
        slots3_abs]
      exact ih₂
    · rw [mergePreds_append _ _ _ _ _ _ _ _ _ _ (by simp [hks, hps]) (by simp [hτs, hps])
        (by simp [hss, hps]) (by simp [hrs, hps]), ← mergePreds_ext, mergePreds_abs] at hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact (hm q hq).extS hS
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
        exact .inl hS.mergeAbs
  | arr _ ih =>
    simp only [Expr.extAnn, Expr.extAnns_eq, Ty.ext_array]
    refine .arr (fun e he => ?_)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    exact ih e₀ he₀
  | arrCheck hT hT₀ _ ih =>
    simp only [Expr.extAnn, Expr.extAnns_eq]
    refine .arrCheck (by rw [Ty.whnf_ext, hT, Ty.ext_array]) (hS.closed hT₀) (fun e he => ?_)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    exact ih e₀ he₀
  | index _ _ hp ihe ihi => exact .index ihe ihi (by simpa using hp.extS hS)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    exact .setIndex ihe ihi (by simpa using hp.extS hS) (by simpa using hw.extS hS) ihv
  | mcall _ hp hlen _ ihe iha =>
    simp only [Expr.extAnn, Expr.extAnns_eq]
    refine .mcall ihe (by simpa using hp.extS hS) (by simpa using hlen) (fun p hp => ?_)
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | conv _ he ih => exact .conv ih (he.ext L L')
  | inj _ hT hi ih => exact .inj ih (hS.closed hT) (by rw [← hS.injPred]; exact hi.extS hS)
  | drop _ ih => exact .drop ih
  | litStr hw => exact .litStr (by rw [Ty.whnf_ext, hw]; rfl)
  | litBool hw => exact .litBool (by rw [Ty.whnf_ext, hw]; rfl)
  | objCheck hc hn hk hl hls hd he _ ih =>
    simp only [Expr.extAnn, Expr.extAnns_eq]
    refine .objCheck (hc.ext L L') hn hk (by simpa using hl)
      (fun l h => List.mem_append_left _ (hls l h)) (Ty.dataFields_ext L L' hd) ?_ (fun p hp => ?_)
    · have := he.ext L L'
      rw [Ty.ext_record_self, objSlots_ext hL hls] at this
      simpa [List.map_map, Function.comp_def] using this
    · rw [List.zip_map] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ =>
    exact .caseTag ih₁ (by simpa [Pred.ext, Cls.ext] using hc.extS hS)
      (by simpa [Scheme.mono_ext] using ih₂) (by simpa [Scheme.mono_ext] using ih₃)

/-- In the narrow system, the one inference implements: a derivation over
the labels `L` is one over `L ++ L'`, for labels `L'` apart from `L`. -/
theorem HasType.extLabels {L L' : List String} (hL : ∀ l ∈ L', l ∉ L)
    (h : HasType L C Γ R rm md e τ) :
    HasType (L ++ L') (C.map (Pred.ext L L')) (Γ.map (Scheme.ext L L')) (R.map (Ty.ext L L'))
      rm md (e.extAnn L L') (τ.ext L L') :=
  HasTypeS.extLabels (Sys.narrow_lextable L L') hL h

end Inty
