import Inty.Syntax
import Inty.Classes
import Inty.TreeVars

/-!
# Declarative typing

`HasType L C Γ R e τ` is the specification the inference engine (`src/infer`)
implements: it says which types an expression may have, not how to find one.
`C` lists the class constraints assumed to hold: a polymorphic function
whose body uses `+` on its parameter is typed assuming its scheme's
constraints (`Plus a`), and each use of it must establish them.

The operator rules are split out as `UnOpTy` / `BinOpTy`, one constructor per
operator rule, mirroring the operator catalog in `src/operators`. Class
instances and entailment are in `Inty.Classes`.
-/

namespace Inty

/-- The type of a literal: its base type. Literal types (`42`, `"err"`) come
later, and so does `Int`: inty types an integral literal as `Int` or
`Number`, and this calculus folds both into `number`. -/
inductive LitTy : Lit → Ty → Prop where
  | number : LitTy (.number n) .number
  | string : LitTy (.string s) .string
  | boolean : LitTy (.boolean b) .boolean
  | undefined : LitTy .undefined .undefined
  | null : LitTy .null .null

/-- Typing rules of the unary operators: operand type, result type. -/
inductive UnOpTy : UnOp → Ty → Ty → Prop where
  | not : UnOpTy .not τ .boolean
  | typeof : UnOpTy .typeof τ .string
  | neg : UnOpTy .neg .number .number

/-- Typing rules of the binary operators under assumptions `C`: operand
types, result type. Both operands of `+` have the same type, one instance of
`Plus`: inty's `+` never mixes a `Number` with a `String`. -/
inductive BinOpTyS (S : Sys) (C : List Pred) : BinOp → Ty → Ty → Ty → Prop where
  | plus : EntailsS S C ⟨.plus, [τ]⟩ → BinOpTyS S C .plus τ τ τ
  | minus : BinOpTyS S C .minus .number .number .number

/-- The operator rules of the narrow system. -/
abbrev BinOpTy := BinOpTyS Sys.narrow

/-- A scheme's constraints are on its quantified variables: their first
argument is one, as in `<a> where Plus a => …` or
`<a, b> where a has {name: b} => …`. inty decides a constraint on a type
already known when it generalises (`InferState::generalize`), so no scheme
carries one that could fail at a use; and a `HasProp` whose receiver the
environment fixes fixes its field type too (`env_fixed_vars`), so it stays
outside the scheme.

A `Merge` is different: its decision waits for the operand's presence,
which a later substitution may decide, so it stays in the scheme as it is
whatever its presence, as long as one of the scheme's variables is in the
trees of the arguments that determine its result (`PTy.TreeBound`: not
merely in an equation of a recursive type its unfolding never reaches).
(Deciding it when the presence is known would make the rule depend on when
that is, which no rule closed under substitution can.) -/
def Scheme.Simple (s : Scheme) : Prop :=
  ∀ p ∈ s.preds, (p.cls ≠ .merge ∧ p.args.length = p.cls.arity ∧
      ∃ i < s.arity, ∃ rest, p.args = .bound i :: rest) ∨
    ∃ q k τ t r, p = ⟨.merge, [q, k, τ, t, r]⟩ ∧
      ∃ i < s.arity, ∃ x ∈ [q, k, τ, t], x.TreeBound s.arity i

/-! ## Rigid type variables -/

/-- The rigid type variables named `k`, one for each of an annotation's `n`
quantified variables. -/
def rigids (k n : Nat) : List Ty := (List.range n).map fun i => .app (.rigid k i) []

/-- The names of the rigid type variables a constructor is. -/
def Con.rkeys : Con → List Nat
  | .rigid s _ => [s]
  | _ => []

mutual
def RTy.rkeys : RTy → List Nat
  | .free _ | .self _ => []
  | .app c args => c.rkeys ++ RTy.rkeysL args
  | .mu _ sys => RTy.rkeysL sys
def RTy.rkeysL : List RTy → List Nat
  | [] => []
  | r :: rs => r.rkeys ++ RTy.rkeysL rs
end

mutual
/-- The names of the rigid type variables in a type. -/
def Ty.rkeys : Ty → List Nat
  | .var _ => []
  | .app c args => c.rkeys ++ Ty.rkeysL args
  | .mu _ sys => RTy.rkeysL sys
def Ty.rkeysL : List Ty → List Nat
  | [] => []
  | τ :: τs => τ.rkeys ++ Ty.rkeysL τs
end

mutual
def PTy.rkeys : PTy → List Nat
  | .free _ | .bound _ | .self _ => []
  | .app c args => c.rkeys ++ PTy.rkeysL args
  | .mu _ sys => PTy.rkeysL sys
def PTy.rkeysL : List PTy → List Nat
  | [] => []
  | p :: ps => p.rkeys ++ PTy.rkeysL ps
end

def Cls.rkeys : Cls → List Nat
  | .inject T => T.rkeys
  | _ => []

def Pred.rkeys (p : Pred) : List Nat := p.cls.rkeys ++ Ty.rkeysL p.args
def PPred.rkeys (p : PPred) : List Nat := p.cls.rkeys ++ PTy.rkeysL p.args
def Scheme.rkeys (s : Scheme) : List Nat := s.body.rkeys ++ s.preds.flatMap PPred.rkeys
def ctxRkeys (Γ : Ctx) : List Nat := Γ.flatMap Scheme.rkeys
def Ret.rkeys (R : Option Ty) : List Nat := (R.map Ty.rkeys).getD []

/-- An annotation `ann` on a binding declares its scheme `s`, a type with no
type variables, `/** const x: Number */`, in this rule; a polymorphic
annotation's quantified variables are rigid in the initialiser (`letPoly`). -/
def Annotated (ann : Option Scheme) (s : Scheme) : Prop :=
  ∀ a, ann = some a → a = s ∧ s.arity = 0 ∧ s.preds = [] ∧ s.ftv = [] ∧ s.rkeys = []

/-- How an object literal's field written as `k`, its expression `e` of the
type `τ`, sits in the literal's record type `T`: its slot. A method and a
getter are written as functions (`m() {…}`, `get g() {…}`), whose `this` is
the literal's type, as inty types it (`shared_this` in `infer_object`); a
getter's slot is what it gives. -/
inductive FieldSlot (T : Ty) : FieldKind → Expr → Ty → Ty → Prop where
  | data : FieldSlot T .data e τ (.slot .pre .data τ)
  | method : TyEq θ T →
      FieldSlot T .method (.func n b) (.fn θ τs ρ) (.slot .pre .data (.fn θ τs ρ))
  | getter : TyEq θ T → FieldSlot T .getter (.func 0 b) (.fn θ [] σ) (.slot .pre .getter σ)

/-- How a class's member written as `k`, its expression `e` of the type `τ`,
sits in the instance's record type `T`: a field holds a value; an arrow
field, a method and a getter are written as functions, whose `this` is the
instance; a method and a getter are on the prototype. An arrow field's
`this` is bound to the instance, so it may be called on anything, outside
a receiver too, but not by `new`, as an arrow function isn't a
constructor: under the class assumptions `C`, its slot's `this` is
`NotNew`. -/
inductive MemberSlotS (S : Sys) (C : List Pred) (T : Ty) : ClassKind → Expr → Ty → Ty → Prop where
  | data : MemberSlotS S C T .data e τ (.slot .pre .data τ)
  | arrow : TyEq θ T → EntailsS S C ⟨.notNew, [θ']⟩ →
      MemberSlotS S C T .arrow (.func n b) (.fn θ τs ρ) (.slot .pre .data (.fn θ' τs ρ))
  | method : TyEq θ T →
      MemberSlotS S C T .method (.func n b) (.fn θ τs ρ) (.slot .pre .proto (.fn θ τs ρ))
  | getter : TyEq θ T → MemberSlotS S C T .getter (.func 0 b) (.fn θ [] σ) (.slot .pre .proto σ)

/-- Class members' slots in the narrow system. -/
abbrev MemberSlot := MemberSlotS Sys.narrow

/-- The type of the field `l` of `T`, if it is present and holds a value
(each looked at unfolded). -/
def Ty.dataField (T : Ty) (l : String) : Option Ty :=
  match T.whnf with
  | .app (.record ls) slots =>
    match Ty.field l ls slots with
    | some s =>
      match s.whnf with
      | .app .slot [p, k, τ] => if p.whnf = .pre ∧ k.whnf = .data then some τ else none
      | _ => none
    | none => none
  | _ => none

/-- The types of the fields `ls` of `T`, each present and holding a value. -/
def Ty.dataFields (T : Ty) : List String → Option (List Ty)
  | [] => some []
  | l :: ls =>
    match T.dataField l, T.dataFields ls with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

theorem Ty.dataFields_length {T : Ty} : ∀ {ls : List String} {τs : List Ty},
    T.dataFields ls = some τs → τs.length = ls.length
  | [], τs, h => by simp only [Ty.dataFields, Option.some.injEq] at h; subst h; rfl
  | l :: ls, τs, h => by
    simp only [Ty.dataFields] at h
    split at h
    · rename_i τ τs' _ h₂
      simp only [Option.some.injEq] at h; subst h
      simp [Ty.dataFields_length h₂]
    · cases h

/-- The tag an object literal with the labels `ls` and the expressions `es`
writes in its field `l`: a string literal. -/
def litTag (l : String) : List String → List Expr → Option String
  | l' :: ls, e :: es =>
    if l' = l then (match e with | .lit (.string t) => some t | _ => none) else litTag l ls es
  | _, _ => none

/-- What an object literal with the labels `ls` and the expressions `es`,
checked against `T`, is checked against: `T` itself, or, `T` a variant
tagged by `l`, the case of the tag the literal writes in its field `l`. -/
inductive ObjCase (ls : List String) (es : List Expr) : Ty → Ty → Prop where
  | self : ObjCase ls es T T
  | variant : T.whnf = .variant (.field l) ts Ps → litTag l ls es = some t →
      firstIdx t ts = some i →
      Ps[i]? = some P → P.tagOf l = some t → ObjCase ls es T P

/-- The context a class's member `i`, written as `k`, is checked in: a
field's initialiser sees the fields before it, the latest first; the
other members see the class's context. -/
def memberCtx (Γ : Ctx) (ks : List ClassKind) (τs : List Ty) (i : Nat) : ClassKind → Ctx
  | .data => (((ks.zip τs).take i).filter (·.1 == .data)).reverse.map (fun p => .mono p.2) ++ Γ
  | _ => Γ

theorem Ty.closed_subst {T : Ty} (h : T.ftv = []) (φ : Subst) : T.subst φ = T :=
  Ty.subst_id (fun x hx => by rw [h] at hx; cases hx)

theorem Ty.ftv_nil_of_whnf {T t : Ty} (h : T.whnf = t) (hT : T.ftv = []) : t.ftv = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    have := Ty.whnf_ftv (τ := T) (a := x) (by rw [h]; exact hx)
    rw [hT] at this; cases this

/-- How an expression is typed: its type is synthesised (`synth`), or it is
checked against an expected type (`check`), an annotation's, which is
pushed into the branches of `?:`, the last statement of a sequence or a
block, an array literal's elements and a function literal's body and
`return`s, and where it meets any other expression, takes that
expression's value into the annotation's sum (`HasTypeS.inj`). -/
inductive Mode where
  | synth
  | check
  deriving DecidableEq, Repr

/-- The mode an annotation gives a binding's initialiser. -/
def annMode : Option Scheme → Mode
  | none => .synth
  | some _ => .check

/-- The typing judgement: with records over the program's labels `L`, under
the class assumptions `C`, the context `Γ` and the enclosing function's
return type `R` (`none` at the top level), whose `return`s are typed in the
mode `rm`, `e` has type `τ` in the mode `md`. A rule's premise for a
subexpression into which an expected type is pushed has the mode `md`;
the others synthesise. -/
inductive HasTypeS (S : Sys) (L : List String) :
    List Pred → Ctx → Option Ty → Mode → Mode → Expr → Ty → Prop where
  | lit : LitTy l τ → HasTypeS S L C Γ R rm .synth (.lit l) τ
  /-- A variable has any instance of its scheme whose constraints hold. -/
  | var : Γ[i]? = some s → τs.length = s.arity →
      (∀ c ∈ s.instPreds τs, EntailsS S C c) →
      HasTypeS S L C Γ R rm .synth (.var i) (s.inst τs)
  /-- A function's body sees its parameters, itself and `this`, and returns
  `ρ`, by `return` or as its value. Checked against a function type, its
  body and `return`s are checked against `ρ`. -/
  | func : τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .synth .synth body ρ →
      HasTypeS S L C Γ R rm .synth (.func n body) (.fn θ τs ρ)
  /-- Checked against a function type (an annotation's, without type
  variables), a function's body and `return`s are checked against its
  result type. -/
  | funcCheck : T.whnf = .fn θ τs ρ → S.closed T → τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .check .check body ρ →
      HasTypeS S L C Γ R rm .check (.func n body) T
  /-- A call has one argument per parameter, each of its parameter's type. A
  call outside any receiver binds `this` to `undefined`, so the function's
  `this` type must be `undefined`: inty unifies it with `Undefined`
  (`src/infer/features/functions.rs`), which rejects a detached method. -/
  | app : HasTypeS S L C Γ R rm .synth f (.fn .undefined τs ρ) → args.length = τs.length →
      (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      HasTypeS S L C Γ R rm .synth (.app f args) ρ
  /-- `const x = e₁; e₂` or `let x = e₁; e₂` gives `x` a scheme `s`. The
  first premise says `e₁` has every opening of `s` at fresh type variables,
  assuming the opened constraints: `m` ranges over all starting points
  above a finite set `F`, which is how a locally nameless development says
  "for fresh variables" (cofinite quantification). It implies the usual
  side condition, that the generalised variables don't occur free in `Γ`.
  Only a syntactic value generalises (the value restriction), and only if
  `e₂` never assigns to `x`: a `let` that is written has one type, which
  each assignment must have. Otherwise `s` quantifies nothing and has no
  constraints. Its constraints are on its quantified variables
  (`Scheme.Simple`). An annotation fixes `s` (`Annotated`), and `e₁` is
  checked against it. -/
  | let_ (s : Scheme) (F : List Nat) :
      (∀ m, (∀ a ∈ F, a < m) →
        HasTypeS S L (C ++ s.openPreds m) Γ R rm (annMode ann) e₁ (s.open m)) →
      (s.arity = 0 ∧ s.preds = []) ∨ (e₁.IsValue ∧ e₂.writes 0 = false) → s.Simple →
      Annotated ann s → HasTypeS S L C (s :: Γ) R rm md e₂ τ₂ →
      HasTypeS S L C Γ R rm md (.let_ mb ann e₁ e₂) τ₂
  /-- A binding annotated with a polymorphic scheme `a`
  (`/** const id: <a>(a) => a */`): the initialiser, a syntactic value, is
  checked against `a` with its quantified variables rigid, as fresh
  constants (`rigids k`, for any `k` outside a finite set: they are
  bound, so the assumptions `C` and the context can't mention them), and
  the binding has every instance of `a`. -/
  | letPoly (a : Scheme) (K : List Nat) :
      0 < a.arity → a.preds = [] → a.ftv = [] → a.rkeys = [] →
      (∀ k, k ∉ K → HasTypeS S L C Γ R rm .check e₁ (a.inst (rigids k a.arity))) →
      e₁.IsValue → e₂.writes 0 = false → HasTypeS S L C (a :: Γ) R rm md e₂ τ₂ →
      HasTypeS S L C Γ R rm md (.let_ mb (some a) e₁ e₂) τ₂
  /-- `x = e` stores a value of `x`'s type, which is a monotype: a binding
  that is assigned is never generalised. Its value is the assignment's.
  (That `x` is a `let` or a parameter, not a `const`, is checked apart,
  by `Expr.assignsMutable`.) -/
  | assign : Γ[i]? = some s → s.arity = 0 → s.preds = [] →
      HasTypeS S L C Γ R rm .synth e (s.inst []) →
      HasTypeS S L C Γ R rm .synth (.assign i e) (s.inst [])
  /-- Both branches have one type, as in Hindley–Milner: inty doesn't guess
  that disagreeing branches form a union. An expected type is pushed into
  each branch. -/
  | cond : HasTypeS S L C Γ R rm .synth c τc → HasTypeS S L C Γ R rm md t τ →
      HasTypeS S L C Γ R rm md e τ → HasTypeS S L C Γ R rm md (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasTypeS S L C Γ R rm .synth e τ₁ →
      HasTypeS S L C Γ R rm .synth (.unop op e) τ
  | binop : BinOpTyS S C op τ₁ τ₂ τ → HasTypeS S L C Γ R rm .synth e₁ τ₁ →
      HasTypeS S L C Γ R rm .synth e₂ τ₂ → HasTypeS S L C Γ R rm .synth (.binop op e₁ e₂) τ
  /-- `return e;` gives the enclosing function's return type, in its mode;
  it doesn't complete, so it may stand for any type. -/
  | ret : HasTypeS S L C Γ (some τr) rm rm e τr → HasTypeS S L C Γ (some τr) rm md (.ret e) τ
  /-- `throw e;` throws any value and doesn't complete. -/
  | throw_ : HasTypeS S L C Γ R rm .synth e τe → HasTypeS S L C Γ R rm .synth (.throw_ e) τ
  | seq : HasTypeS S L C Γ R rm .check e₁ .unknown → HasTypeS S L C Γ R rm md e₂ τ →
      HasTypeS S L C Γ R rm md (.seq e₁ e₂) τ
  /-- `while (c) body`: any test, read by truthiness; it completes with
  `undefined` (`infer_stmt_while`). -/
  | while_ : HasTypeS S L C Γ R rm .synth c τc → HasTypeS S L C Γ R rm .check body .unknown →
      HasTypeS S L C Γ R rm .synth (.while_ c body) .undefined
  /-- `break;` and `continue;` don't complete, so they stand for any type.
  (That they are in a loop is checked apart, by `Expr.jumpsInLoop`.) -/
  | break_ : HasTypeS S L C Γ R rm md .break_ τ
  | continue_ : HasTypeS S L C Γ R rm md .continue_ τ
  /-- `try { body } catch (e) { handler }`: anything can be thrown, so `e`
  has the opaque type `unknown` (inty's rigid type variable). -/
  | tryCatch : HasTypeS S L C Γ R rm md body τ → HasTypeS S L C (.mono .unknown :: Γ) R rm md handler τ →
      HasTypeS S L C Γ R rm md (.tryCatch body handler) τ
  /-- `try { body } finally { fin }` has `body`'s type; `fin`'s value is
  dropped. -/
  | tryFinally : HasTypeS S L C Γ R rm md body τ → HasTypeS S L C Γ R rm .check fin .unknown →
      HasTypeS S L C Γ R rm md (.tryFinally body fin) τ
  /-- An object literal has a record type over the program's labels, with
  its fields present (`objSlots`), each slot as its kind says
  (`FieldSlot`). -/
  | obj : es.length = ls.length → ks.length = ls.length → τs.length = ls.length →
      ss.length = ls.length → (∀ l ∈ ls, l ∈ L) →
      (∀ p ∈ es.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      (∀ x ∈ ks.zip (es.zip (τs.zip ss)),
        FieldSlot (.record L (objSlots L ls ss)) x.1 x.2.1 x.2.2.1 x.2.2.2) →
      HasTypeS S L C Γ R rm .synth (.obj ls es ks) (.record L (objSlots L ls ss))
  /-- A class's instance has a record type over the program's labels, its
  members present (`objSlots`), each checked in its context (`memberCtx`)
  and slotted as its kind says (`MemberSlot`). Its labels are distinct. -/
  | cls : es.length = ls.length → ks.length = ls.length → τs.length = ls.length →
      ss.length = ls.length → ls.Nodup → (∀ l ∈ ls, l ∈ L) →
      (∀ i e k τ, es[i]? = some e → ks[i]? = some k → τs[i]? = some τ →
        HasTypeS S L C (memberCtx Γ ks τs i k) none .synth .synth e τ) →
      (∀ x ∈ ks.zip (es.zip (τs.zip ss)),
        MemberSlotS S C (.record L (objSlots L ls ss)) x.1 x.2.1 x.2.2.1 x.2.2.2) →
      HasTypeS S L C Γ R rm .synth (.cls ls es ks) (.record L (objSlots L ls ss))
  /-- A constructor is a function whose `this` is what `new` makes, which
  nothing else gives (`newTarget`). -/
  | ctor : τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn .newTarget τs ρ) :: .mono .newTarget :: Γ)
        (some ρ) .synth .synth body ρ →
      HasTypeS S L C Γ R rm .synth (.ctor n body) (.fn .newTarget τs ρ)
  /-- `new f(…)` calls a constructor, one argument per parameter, which
  gives an object, a record over the program's labels, so that it is the
  result. -/
  | new_ : HasTypeS S L C Γ R rm .synth f (.fn .newTarget τs ρ) → args.length = τs.length →
      (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) → TyEq ρ (.record L ss) →
      ss.length = L.length → HasTypeS S L C Γ R rm .synth (.new_ f args) ρ
  /-- `e.l` reads a property of `e`'s type, of any kind, `HasProp l τ k σ`:
  a present field of a record, or what a scheme's constraint promises. -/
  | get : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, k, σ]⟩ →
      HasTypeS S L C Γ R rm .synth (.get e l) σ
  /-- `e.l = v` stores a value of the field's type, which is the
  assignment's, in an object's field that holds a value (`HasProp l τ data
  σ`: not a getter or a class's method, nor an array's or a string's
  `length`). -/
  | set : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, .data, σ]⟩ →
      HasTypeS S L C Γ R rm .synth v σ → HasTypeS S L C Γ R rm .synth (.set e l v) σ
  /-- `{...e₁, ...e₂}`: `e₂`'s slot for each label, with presence `p`, kind
  `k` and type `τ`, merged over `e₁`'s slot `s` gives the result's slot
  `r` (`Merge p k τ s r`): `e₂`'s own field if it has one, `e₁`'s copied
  if not. -/
  | spread : ps.length = L.length → ks.length = L.length → τs.length = L.length →
      ss.length = L.length → rs.length = L.length →
      HasTypeS S L C Γ R rm .synth e₁ (.record L ss) →
      HasTypeS S L C Γ R rm .synth e₂ (.record L (slots3 ps ks τs)) →
      (∀ p ∈ mergePreds ps ks τs ss rs, EntailsS S C p) →
      HasTypeS S L C Γ R rm .synth (.spread e₁ e₂) (.record L rs)
  /-- An array literal's elements have one type, as in Hindley–Milner; an
  expected element type is pushed into each. -/
  | arr : (∀ e ∈ es, HasTypeS S L C Γ R rm .synth e τ) → HasTypeS S L C Γ R rm .synth (.arr es) (.array τ)
  /-- Checked against an array type, each element is checked against its
  element type. -/
  | arrCheck : T.whnf = .array σ → S.closed T → (∀ e ∈ es, HasTypeS S L C Γ R rm .check e σ) →
      HasTypeS S L C Γ R rm .check (.arr es) T
  /-- `e[i]`: `Indexable τ ι σ`, an array's element or a string's
  character, or what a scheme's constraint promises. -/
  | index : HasTypeS S L C Γ R rm .synth e τ → HasTypeS S L C Γ R rm .synth i ι →
      EntailsS S C ⟨.indexable, [τ, ι, σ]⟩ → HasTypeS S L C Γ R rm .synth (.index e i) σ
  /-- `e[i] = v` stores a value of the element type, in a container that
  takes stores (`IndexWrite`, not a string). -/
  | setIndex : HasTypeS S L C Γ R rm .synth e τ → HasTypeS S L C Γ R rm .synth i ι →
      EntailsS S C ⟨.indexable, [τ, ι, σ]⟩ → EntailsS S C ⟨.indexWrite, [τ]⟩ →
      HasTypeS S L C Γ R rm .synth v σ → HasTypeS S L C Γ R rm .synth (.setIndex e i v) σ
  /-- `e.l(a₀, …)`: the receiver's property `l` is a function whose `this`
  is the receiver's type, as inty unifies a method's `this` with its
  receiver (`method_receiver` in `src/infer/features/functions.rs`); one
  argument per parameter. A method that returns `this`, or reads a
  property of it that holds a method, makes the receiver's type
  recursive. -/
  | mcall : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, k, .fn τ τs ρ]⟩ →
      args.length = τs.length → (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      HasTypeS S L C Γ R rm .synth (.mcall e l args) ρ
  /-- `unwrap e₁ e₂ e₃` eliminates a sum: `e₃` sees what isn't nothing of
  `e₁`'s value at the type `Strip` leaves of `e₁`'s. Both branches have one
  type, and an expected type is pushed into each. -/
  | unwrap : HasTypeS S L C Γ R rm .synth e₁ τ₁ → EntailsS S C ⟨.strip, [τ₁, σ]⟩ →
      HasTypeS S L C Γ R rm md e₂ τ → HasTypeS S L C (.mono σ :: Γ) R rm md e₃ τ →
      HasTypeS S L C Γ R rm md (.unwrap e₁ e₂ e₃) τ
  /-- A string literal checked against its own string type: a variant's
  tag. -/
  | litStr : T.whnf = .strLit s → HasTypeS S L C Γ R rm .check (.lit (.string s)) T
  /-- An object literal whose fields all hold values, checked against a
  record type equal to the one with those fields (present, holding values)
  and no others, or a variant with such a case (`ObjCase`): each field
  against its type in the record. -/
  | objCheck : ObjCase ls es T P → ls.Nodup → ks = ls.map (fun _ => .data) →
      es.length = ls.length → (∀ l ∈ ls, l ∈ L) → P.dataFields ls = some τs →
      TyEq P (.record L (objSlots L ls (τs.map fun τ => .slot .pre .data τ))) →
      (∀ p ∈ es.zip τs, HasTypeS S L C Γ R rm .check p.1 p.2) →
      HasTypeS S L C Γ R rm .check (.obj ls es ks) T
  /-- Taking a variant apart by its tag `t`: `e₃` sees `e₁`'s value as the
  case of the tag `t` (`σ`), `e₂` as the rest (`ρ`): `Case_{l,t} τ₁ σ ρ`.
  Both branches have one type, and an expected type is pushed into each. -/
  | caseTag : HasTypeS S L C Γ R rm .synth e₁ τ₁ → EntailsS S C ⟨.caseTag d t, [τ₁, σ, ρ]⟩ →
      HasTypeS S L C (.mono ρ :: Γ) R rm md e₂ τ → HasTypeS S L C (.mono σ :: Γ) R rm md e₃ τ →
      HasTypeS S L C Γ R rm md (.caseTag e₁ d t e₂ e₃) τ
  /-- A type may be replaced by an equal one (`TyEq`): a recursive type by
  its unfolding, or the other way round. -/
  | conv : HasTypeS S L C Γ R rm .synth e τ → TyEq τ τ' → HasTypeS S L C Γ R rm .synth e τ'
  /-- Checked against an annotation's type `T`, an expression of the type
  `τ` has `T` if a value of `τ` is one of `T` (`Inject T τ`: `τ` is `T`,
  or `T` is `Nullable τ`, …). `T` has no type variables. -/
  | inj : HasTypeS S L C Γ R rm .synth e τ → S.closed T → EntailsS S C (S.injPred τ T) →
      HasTypeS S L C Γ R rm .check e T
  /-- An expression whose value is discarded is checked against `unknown`,
  the type of every value: a statement's, but a function body's last or a
  program's (`e₁` of `e₁; e₂`, a loop's body, a `finally` block). Its type
  is dropped, so the branches of a statement needn't have one type, as
  inty types `if (c) { 1; } else { "a"; }`. -/
  | drop : HasTypeS S L C Γ R rm .synth e τ → HasTypeS S L C Γ R rm .check e .unknown

/-- A `HasType` derivation's last rule, other than a conversion: every
derivation is one of these followed by conversions (`HasTypeS.top`), which
lets a proof by cases on the last rule ignore conversions. -/
inductive HasTypeTopS (S : Sys) (L : List String) :
    List Pred → Ctx → Option Ty → Mode → Mode → Expr → Ty → Prop where
  | lit : LitTy l τ → HasTypeTopS S L C Γ R rm .synth (.lit l) τ
  | var : Γ[i]? = some s → τs.length = s.arity →
      (∀ c ∈ s.instPreds τs, EntailsS S C c) →
      HasTypeTopS S L C Γ R rm .synth (.var i) (s.inst τs)
  | func : τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .synth .synth body ρ →
      HasTypeTopS S L C Γ R rm .synth (.func n body) (.fn θ τs ρ)
  /-- Checked against a function type (an annotation's, without type
  variables), a function's body and `return`s are checked against its
  result type. -/
  | funcCheck : T.whnf = .fn θ τs ρ → S.closed T → τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn θ τs ρ) :: .mono θ :: Γ) (some ρ) .check .check body ρ →
      HasTypeTopS S L C Γ R rm .check (.func n body) T
  | app : HasTypeS S L C Γ R rm .synth f (.fn .undefined τs ρ) → args.length = τs.length →
      (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      HasTypeTopS S L C Γ R rm .synth (.app f args) ρ
  | let_ (s : Scheme) (F : List Nat) :
      (∀ m, (∀ a ∈ F, a < m) →
        HasTypeS S L (C ++ s.openPreds m) Γ R rm (annMode ann) e₁ (s.open m)) →
      (s.arity = 0 ∧ s.preds = []) ∨ (e₁.IsValue ∧ e₂.writes 0 = false) → s.Simple →
      Annotated ann s → HasTypeS S L C (s :: Γ) R rm md e₂ τ₂ →
      HasTypeTopS S L C Γ R rm md (.let_ mb ann e₁ e₂) τ₂
  | letPoly (a : Scheme) (K : List Nat) :
      0 < a.arity → a.preds = [] → a.ftv = [] → a.rkeys = [] →
      (∀ k, k ∉ K → HasTypeS S L C Γ R rm .check e₁ (a.inst (rigids k a.arity))) →
      e₁.IsValue → e₂.writes 0 = false → HasTypeS S L C (a :: Γ) R rm md e₂ τ₂ →
      HasTypeTopS S L C Γ R rm md (.let_ mb (some a) e₁ e₂) τ₂
  | assign : Γ[i]? = some s → s.arity = 0 → s.preds = [] →
      HasTypeS S L C Γ R rm .synth e (s.inst []) →
      HasTypeTopS S L C Γ R rm .synth (.assign i e) (s.inst [])
  | cond : HasTypeS S L C Γ R rm .synth c τc → HasTypeS S L C Γ R rm md t τ →
      HasTypeS S L C Γ R rm md e τ → HasTypeTopS S L C Γ R rm md (.cond c t e) τ
  | unop : UnOpTy op τ₁ τ → HasTypeS S L C Γ R rm .synth e τ₁ →
      HasTypeTopS S L C Γ R rm .synth (.unop op e) τ
  | binop : BinOpTyS S C op τ₁ τ₂ τ → HasTypeS S L C Γ R rm .synth e₁ τ₁ →
      HasTypeS S L C Γ R rm .synth e₂ τ₂ → HasTypeTopS S L C Γ R rm .synth (.binop op e₁ e₂) τ
  | ret : HasTypeS S L C Γ (some τr) rm rm e τr → HasTypeTopS S L C Γ (some τr) rm md (.ret e) τ
  | throw_ : HasTypeS S L C Γ R rm .synth e τe → HasTypeTopS S L C Γ R rm .synth (.throw_ e) τ
  | seq : HasTypeS S L C Γ R rm .check e₁ .unknown → HasTypeS S L C Γ R rm md e₂ τ →
      HasTypeTopS S L C Γ R rm md (.seq e₁ e₂) τ
  | while_ : HasTypeS S L C Γ R rm .synth c τc → HasTypeS S L C Γ R rm .check body .unknown →
      HasTypeTopS S L C Γ R rm .synth (.while_ c body) .undefined
  | break_ : HasTypeTopS S L C Γ R rm md .break_ τ
  | continue_ : HasTypeTopS S L C Γ R rm md .continue_ τ
  | tryCatch : HasTypeS S L C Γ R rm md body τ →
      HasTypeS S L C (.mono .unknown :: Γ) R rm md handler τ →
      HasTypeTopS S L C Γ R rm md (.tryCatch body handler) τ
  | tryFinally : HasTypeS S L C Γ R rm md body τ → HasTypeS S L C Γ R rm .check fin .unknown →
      HasTypeTopS S L C Γ R rm md (.tryFinally body fin) τ
  | obj : es.length = ls.length → ks.length = ls.length → τs.length = ls.length →
      ss.length = ls.length → (∀ l ∈ ls, l ∈ L) →
      (∀ p ∈ es.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      (∀ x ∈ ks.zip (es.zip (τs.zip ss)),
        FieldSlot (.record L (objSlots L ls ss)) x.1 x.2.1 x.2.2.1 x.2.2.2) →
      HasTypeTopS S L C Γ R rm .synth (.obj ls es ks) (.record L (objSlots L ls ss))
  | cls : es.length = ls.length → ks.length = ls.length → τs.length = ls.length →
      ss.length = ls.length → ls.Nodup → (∀ l ∈ ls, l ∈ L) →
      (∀ i e k τ, es[i]? = some e → ks[i]? = some k → τs[i]? = some τ →
        HasTypeS S L C (memberCtx Γ ks τs i k) none .synth .synth e τ) →
      (∀ x ∈ ks.zip (es.zip (τs.zip ss)),
        MemberSlotS S C (.record L (objSlots L ls ss)) x.1 x.2.1 x.2.2.1 x.2.2.2) →
      HasTypeTopS S L C Γ R rm .synth (.cls ls es ks) (.record L (objSlots L ls ss))
  | ctor : τs.length = n →
      HasTypeS S L C (τs.map .mono ++ .mono (.fn .newTarget τs ρ) :: .mono .newTarget :: Γ)
        (some ρ) .synth .synth body ρ →
      HasTypeTopS S L C Γ R rm .synth (.ctor n body) (.fn .newTarget τs ρ)
  | new_ : HasTypeS S L C Γ R rm .synth f (.fn .newTarget τs ρ) → args.length = τs.length →
      (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) → TyEq ρ (.record L ss) →
      ss.length = L.length → HasTypeTopS S L C Γ R rm .synth (.new_ f args) ρ
  | get : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, k, σ]⟩ →
      HasTypeTopS S L C Γ R rm .synth (.get e l) σ
  | set : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, .data, σ]⟩ →
      HasTypeS S L C Γ R rm .synth v σ → HasTypeTopS S L C Γ R rm .synth (.set e l v) σ
  | spread : ps.length = L.length → ks.length = L.length → τs.length = L.length →
      ss.length = L.length → rs.length = L.length →
      HasTypeS S L C Γ R rm .synth e₁ (.record L ss) →
      HasTypeS S L C Γ R rm .synth e₂ (.record L (slots3 ps ks τs)) →
      (∀ p ∈ mergePreds ps ks τs ss rs, EntailsS S C p) →
      HasTypeTopS S L C Γ R rm .synth (.spread e₁ e₂) (.record L rs)
  | arr : (∀ e ∈ es, HasTypeS S L C Γ R rm .synth e τ) → HasTypeTopS S L C Γ R rm .synth (.arr es) (.array τ)
  /-- Checked against an array type, each element is checked against its
  element type. -/
  | arrCheck : T.whnf = .array σ → S.closed T → (∀ e ∈ es, HasTypeS S L C Γ R rm .check e σ) →
      HasTypeTopS S L C Γ R rm .check (.arr es) T
  | index : HasTypeS S L C Γ R rm .synth e τ → HasTypeS S L C Γ R rm .synth i ι →
      EntailsS S C ⟨.indexable, [τ, ι, σ]⟩ → HasTypeTopS S L C Γ R rm .synth (.index e i) σ
  | setIndex : HasTypeS S L C Γ R rm .synth e τ → HasTypeS S L C Γ R rm .synth i ι →
      EntailsS S C ⟨.indexable, [τ, ι, σ]⟩ → EntailsS S C ⟨.indexWrite, [τ]⟩ →
      HasTypeS S L C Γ R rm .synth v σ → HasTypeTopS S L C Γ R rm .synth (.setIndex e i v) σ
  | mcall : HasTypeS S L C Γ R rm .synth e τ → EntailsS S C ⟨.hasProp l, [τ, k, .fn τ τs ρ]⟩ →
      args.length = τs.length → (∀ p ∈ args.zip τs, HasTypeS S L C Γ R rm .synth p.1 p.2) →
      HasTypeTopS S L C Γ R rm .synth (.mcall e l args) ρ
  | unwrap : HasTypeS S L C Γ R rm .synth e₁ τ₁ → EntailsS S C ⟨.strip, [τ₁, σ]⟩ →
      HasTypeS S L C Γ R rm md e₂ τ → HasTypeS S L C (.mono σ :: Γ) R rm md e₃ τ →
      HasTypeTopS S L C Γ R rm md (.unwrap e₁ e₂ e₃) τ
  | litStr : T.whnf = .strLit s → HasTypeTopS S L C Γ R rm .check (.lit (.string s)) T
  | objCheck : ObjCase ls es T P → ls.Nodup → ks = ls.map (fun _ => .data) →
      es.length = ls.length → (∀ l ∈ ls, l ∈ L) → P.dataFields ls = some τs →
      TyEq P (.record L (objSlots L ls (τs.map fun τ => .slot .pre .data τ))) →
      (∀ p ∈ es.zip τs, HasTypeS S L C Γ R rm .check p.1 p.2) →
      HasTypeTopS S L C Γ R rm .check (.obj ls es ks) T
  | caseTag : HasTypeS S L C Γ R rm .synth e₁ τ₁ → EntailsS S C ⟨.caseTag d t, [τ₁, σ, ρ]⟩ →
      HasTypeS S L C (.mono ρ :: Γ) R rm md e₂ τ → HasTypeS S L C (.mono σ :: Γ) R rm md e₃ τ →
      HasTypeTopS S L C Γ R rm md (.caseTag e₁ d t e₂ e₃) τ

/-- The narrow system's typing judgement, the one inference implements. -/
abbrev HasType := HasTypeS Sys.narrow

/-- The narrow system's last rules. -/
abbrev HasTypeTop := HasTypeTopS Sys.narrow

/-- How the type a derivation's last rule gives, `τ₀` in the mode `md₀`,
comes to be the derivation's, `τ` in the mode `md`: by conversions of a
synthesised type, or checked against an annotation's type `τ`, as it is or
by an injection (`HasTypeS.inj`), or dropped, checked against `unknown`
(`HasTypeS.drop`). -/
def LiftS (S : Sys) (C : List Pred) (md md₀ : Mode) (τ₀ τ : Ty) : Prop :=
  (md₀ = md ∧ TyEq τ₀ τ ∧ (md = .check → τ₀ = τ)) ∨
    (md = .check ∧ md₀ = .synth ∧ S.closed τ ∧ EntailsS S C (S.injPred τ₀ τ)) ∨
    (md = .check ∧ md₀ = .synth ∧ τ = .unknown)

/-- Lifting in the narrow system. -/
abbrev Lift := LiftS Sys.narrow

theorem LiftS.refl {S : Sys} {C : List Pred} {md : Mode} {τ : Ty} : LiftS S C md md τ τ :=
  .inl ⟨rfl, .refl _, fun _ => rfl⟩

/-- A derivation is its last rule other than a conversion or an injection,
then conversions (of a synthesised type) and at most one injection. -/
theorem HasTypeS.top {S : Sys} (h : HasTypeS S L C Γ R rm md e τ) :
    ∃ md₀ τ₀, HasTypeTopS S L C Γ R rm md₀ e τ₀ ∧ LiftS S C md md₀ τ₀ τ := by
  induction h with
  | conv _ he ih =>
    obtain ⟨md₀, τ₀, ht, hl⟩ := ih
    rcases hl with ⟨h₁, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨md₀, τ₀, ht, .inl ⟨h₁, h₂.trans he, fun h => by cases h⟩⟩
    · cases h
    · cases h
  | inj _ hT hi ih =>
    obtain ⟨md₀, τ₀, ht, hl⟩ := ih
    rcases hl with ⟨rfl, h₀, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · refine ⟨_, τ₀, ht, .inr (.inl ⟨rfl, rfl, hT, ?_⟩)⟩
      exact EntailsS.of_predEq (S.injPred_eq h₀.symm) hi
    · cases h
    · cases h
  | drop _ ih =>
    obtain ⟨md₀, τ₀, ht, hl⟩ := ih
    rcases hl with ⟨rfl, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨_, τ₀, ht, .inr (.inr ⟨rfl, rfl, rfl⟩)⟩
    · cases h
    · cases h
  | lit hl => exact ⟨_, _, .lit hl, .refl⟩
  | var hi hl hc => exact ⟨_, _, .var hi hl hc, .refl⟩
  | func hl hb => exact ⟨_, _, .func hl hb, .refl⟩
  | funcCheck hw hT hl hb => exact ⟨_, _, .funcCheck hw hT hl hb, .refl⟩
  | app hf hl ha => exact ⟨_, _, .app hf hl ha, .refl⟩
  | let_ s F h₁ hv hs ha h₂ => exact ⟨_, _, .let_ s F h₁ hv hs ha h₂, .refl⟩
  | letPoly a K h0 h1 h2 h3 h₁ hv hw h₂ =>
    exact ⟨_, _, .letPoly a K h0 h1 h2 h3 h₁ hv hw h₂, .refl⟩
  | assign hi ha hp he => exact ⟨_, _, .assign hi ha hp he, .refl⟩
  | cond hc ht he => exact ⟨_, _, .cond hc ht he, .refl⟩
  | unop hop he => exact ⟨_, _, .unop hop he, .refl⟩
  | binop hop h₁ h₂ => exact ⟨_, _, .binop hop h₁ h₂, .refl⟩
  | ret he => exact ⟨_, _, .ret he, .refl⟩
  | throw_ he => exact ⟨_, _, .throw_ he, .refl⟩
  | seq h₁ h₂ => exact ⟨_, _, .seq h₁ h₂, .refl⟩
  | while_ hc hb => exact ⟨_, _, .while_ hc hb, .refl⟩
  | break_ => exact ⟨_, _, .break_, .refl⟩
  | continue_ => exact ⟨_, _, .continue_, .refl⟩
  | unwrap h₁ hs h₂ h₃ => exact ⟨_, _, .unwrap h₁ hs h₂ h₃, .refl⟩
  | litStr hw => exact ⟨_, _, .litStr hw, .refl⟩
  | objCheck hc hn hk hl hL hd he hf => exact ⟨_, _, .objCheck hc hn hk hl hL hd he hf, .refl⟩
  | caseTag h₁ hc h₂ h₃ => exact ⟨_, _, .caseTag h₁ hc h₂ h₃, .refl⟩
  | tryCatch hb hh => exact ⟨_, _, .tryCatch hb hh, .refl⟩
  | tryFinally hb hf => exact ⟨_, _, .tryFinally hb hf, .refl⟩
  | obj hes hks hτs hss hL hargs hm => exact ⟨_, _, .obj hes hks hτs hss hL hargs hm, .refl⟩
  | cls hes hks hτs hss hnd hL hargs hm =>
    exact ⟨_, _, .cls hes hks hτs hss hnd hL hargs hm, .refl⟩
  | ctor hl hb => exact ⟨_, _, .ctor hl hb, .refl⟩
  | new_ hf hl ha hρ hss => exact ⟨_, _, .new_ hf hl ha hρ hss, .refl⟩
  | get he hp => exact ⟨_, _, .get he hp, .refl⟩
  | set he hp hv => exact ⟨_, _, .set he hp hv, .refl⟩
  | spread hps hks hτs hss hrs h₁ h₂ hm =>
    exact ⟨_, _, .spread hps hks hτs hss hrs h₁ h₂ hm, .refl⟩
  | arr hes => exact ⟨_, _, .arr hes, .refl⟩
  | arrCheck hw hT hes => exact ⟨_, _, .arrCheck hw hT hes, .refl⟩
  | index he hi hp => exact ⟨_, _, .index he hi hp, .refl⟩
  | setIndex he hi hp hw hv => exact ⟨_, _, .setIndex he hi hp hw hv, .refl⟩
  | mcall he hp hl ha => exact ⟨_, _, .mcall he hp hl ha, .refl⟩

/-- A synthesised type's derivation is its last rule, then conversions. -/
theorem HasTypeS.top_synth {S : Sys} (h : HasTypeS S L C Γ R rm .synth e τ) :
    ∃ τ₀, TyEq τ₀ τ ∧ HasTypeTopS S L C Γ R rm .synth e τ₀ := by
  obtain ⟨md₀, τ₀, ht, hl⟩ := h.top
  rcases hl with ⟨rfl, h₀, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨τ₀, h₀, ht⟩
  · cases h
  · cases h

/-- A variable whose scheme is a monotype has that type. -/
theorem HasTypeS.var_mono (h : Γ[i]? = some (Scheme.mono τ)) :
    HasType L C Γ R rm .synth (.var i) τ := by
  simpa using HasTypeS.var (S := Sys.narrow) (C := C) (R := R) (rm := rm) (τs := []) h rfl
    (by simp [Scheme.instPreds, Scheme.mono])

/-- A monomorphic `const`. -/
theorem HasTypeS.let_mono (h₁ : HasType L C Γ R rm .synth e₁ τ₁)
    (h₂ : HasType L C (.mono τ₁ :: Γ) R rm md e₂ τ₂) :
    HasType L C Γ R rm md (.let_ mb none e₁ e₂) τ₂ :=
  .let_ (.mono τ₁) [] (fun _ _ => by simpa [Scheme.open, Scheme.openPreds,
    Scheme.instPreds, Scheme.mono, Scheme.inst, annMode] using h₁) (.inl ⟨rfl, rfl⟩)
    (fun _ h => by simp [Scheme.mono] at h) (fun _ h => by cases h) h₂

end Inty

