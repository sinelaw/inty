import Inty.Infer
import Inty.Semantics

/-!
# Wire format for differential testing

The Rust side generates core programs, writes each one for inty as
JavaScript and for this model as an s-expression, one program per line:

```
(num M E)   M × 10^-E      (str s:abc)   a string, `s:` then its text, `%XX`
               for a character of hex code XX a token can't hold (also in
               labels)
(bool true) (undef) (null) (var i)  (func N BODY)  (app F A₀ A₁ …)
(let E₁ E₂) (letmut E₁ E₂) (assign I E)   `const`, `let` and `x = e` (to an
               annotated `let`, read as `x = (const t: T = e; t)`)
(letann T E₁ E₂) (letmutann T E₁ E₂)   annotated `/** const v: T */`, with T
               number, string, boolean, undefined, null, (arr T),
               (nullable T), (optional T) or (fn R A₀ A₁ …), a function
               called detached
(letpoly N T E₁ E₂)   `/** const v: <a, b, …>T */`, a scheme quantifying N
               variables, written (tv I) in T
(unwrap E₁ E₂ E₃)   `const x = E₁; x != null ? E₃ : E₂`, x as var 0 in E₃
(casetag E₁ s:l s:t E₂ E₃)   `const x = E₁; x.l === "t" ? E₃ : E₂`, x as var 0
               in both; the tag `true` or `false` for `x.l === true`
(typetest E₁ s:t E₂ E₃)   `const x = E₁; typeof x === "t" ? E₃ : E₂`, alike
annotations also take (rec (s:x T) …), a record, (strlit s:t), the type of
the string t, (boollit true) and (boollit false), and (variant s:l (rec …) …),
a variant tagged by its field l, whose cases are records with a string's or
a boolean's type at l, and (sum T …), a sum told
apart by `typeof` (`Number | String`)
(cond C T E)   (not E) (typeof E) (neg E)  (plus A B) (minus A B)
(times A B) (div A B)   `*`, `/`   (lt A B) (le A B) (gt A B) (ge A B)   `<` … `>=`
(eq A B) (ne A B)   `===`, `!==`
(ret E)     (throw E)      (seq A B)
(while C B) (break) (continue) (trycatch B H) (tryfinally B F)
(obj (field s:x E) (method s:m F) (getter s:g F) …)   an object literal, a
               `method` field written `m(…) {…}` and a `getter` `get g() {…}`,
               each F a function   (get E s:x)   (set E s:x V)
(class (field s:x E) (arrow s:f F) (method s:m F) (getter s:g F) …)   a class's
               instance: fields with initialisers, arrow fields, and
               methods and getters on the prototype
(ctor N BODY)  a constructor   (new F A₀ A₁ …)  `new F(A₀, A₁, …)`
(spread A B)   `{...A, ...B}`
(arr E₀ E₁ …)  `[E₀, E₁, …]`    (index E I)  `E[I]`    (setindex E I V)  `E[I] = V`
(mcall E s:x A₀ A₁ …)  `E.x(A₀, A₁, …)`
```

`inty-model` (`Main.lean`) answers each line with the model's verdicts, as
`verdict` prints them. The parser and printer aren't part of what is proved;
they only carry programs and answers across.
-/

namespace Inty.Wire

open Inty

/-- Split a line into `(`, `)` and atoms. -/
def tokenize (s : String) : List String :=
  let spaced := s.replace "(" " ( " |>.replace ")" " ) "
  spaced.splitOn " " |>.filter (· ≠ "")

/-- A string's or a label's text as a token: `unescape`'s inverse. -/
def escape (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = '%' then
      let h := Nat.toDigits 16 c.toNat
      "%" ++ String.ofList ((if h.length < 2 then ['0'] else []) ++ h.map Char.toUpper)
    else c.toString)

/-- A hexadecimal digit's value. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A string's or a label's text in a token: `%XX` is the character of the
hexadecimal code `XX`, for what a token can't hold (whitespace, `(`, `)`
and `%`). -/
def unescape (s : String) : String :=
  let rec go : List Char → List Char
    | '%' :: a :: b :: rest =>
      match hexVal a, hexVal b with
      | some x, some y => Char.ofNat (16 * x + y) :: go rest
      | _, _ => '%' :: go (a :: b :: rest)
    | c :: rest => c :: go rest
    | [] => []
  String.ofList (go s.toList)

/-- Parse an annotation's type from the front of the tokens. -/
partial def parseTy (L : Option (List String)) : List String → Option (Ty × List String)
  | "number" :: rest => some (.number, rest)
  | "string" :: rest => some (.string, rest)
  | "boolean" :: rest => some (.boolean, rest)
  | "undefined" :: rest => some (.undefined, rest)
  | "null" :: rest => some (.null, rest)
  | "(" :: "tv" :: i :: ")" :: rest => do some (.var (← i.toNat?), rest)
  | "(" :: "arr" :: rest => do
    let (t, rest) ← parseTy L rest
    match rest with
    | ")" :: rest => some (.array t, rest)
    | _ => none
  | "(" :: "nullable" :: rest => do
    let (t, rest) ← parseTy L rest
    match rest with
    | ")" :: rest => some (.nullable t, rest)
    | _ => none
  | "(" :: "optional" :: rest => do
    let (t, rest) ← parseTy L rest
    match rest with
    | ")" :: rest => some (.optional t, rest)
    | _ => none
  | "(" :: "fn" :: rest => do
    let (r, rest) ← parseTy L rest
    let rec params (ts : List String) (acc : List Ty) : Option (List Ty × List String) :=
      match ts with
      | ")" :: rest => some (acc.reverse, rest)
      | _ => do
        let (t, rest) ← parseTy L ts
        params rest (t :: acc)
    let (ps, rest) ← params rest []
    some (.fn .undefined ps r, rest)
  | "(" :: "strlit" :: t :: ")" :: rest =>
    if t.startsWith "s:" then some (.strLit (unescape (t.drop 2).toString), rest) else none
  | "(" :: "boollit" :: "true" :: ")" :: rest => some (.boolLit true, rest)
  | "(" :: "boollit" :: "false" :: ")" :: rest => some (.boolLit false, rest)
  -- A record: its fields over the program's labels `L`, once they are
  -- known, and over its own labels before.
  | "(" :: "rec" :: rest => do
    let rec fields (ts : List String) (acc : List (String × Ty)) :
        Option (List (String × Ty) × List String) :=
      match ts with
      | ")" :: rest => some (acc.reverse, rest)
      | "(" :: l :: ts =>
        if l.startsWith "s:" then do
          let (t, rest) ← parseTy L ts
          match rest with
          | ")" :: rest => fields rest ((unescape (l.drop 2).toString, t) :: acc)
          | _ => none
        else none
      | _ => none
    let (fs, rest) ← fields rest []
    let ls := fs.map (·.1)
    let ss := fs.map fun f => Ty.slot .pre .data f.2
    match L with
    | some L => some (.record L (objSlots L ls ss), rest)
    | none => some (.record ls ss, rest)
  -- A variant tagged by `l`: its cases, each with a tag.
  | "(" :: "variant" :: l :: rest => do
    unless l.startsWith "s:" do none
    let l := unescape (l.drop 2).toString
    let rec cases (ts : List String) (acc : List Ty) : Option (List Ty × List String) :=
      match ts with
      | ")" :: rest => some (acc.reverse, rest)
      | _ => do
        let (t, rest) ← parseTy L ts
        cases rest (t :: acc)
    let (Rs, rest) ← cases rest []
    let tags ← Rs.mapM (·.tagOf l)
    if tags.Nodup then some (.variant (.field l) tags Rs, rest) else none
  -- A sum told apart by `typeof`: its cases, each tagged by its head's
  -- `typeof`.
  | "(" :: "sum" :: rest => do
    let rec arms (ts : List String) (acc : List Ty) : Option (List Ty × List String) :=
      match ts with
      | ")" :: rest => some (acc.reverse, rest)
      | _ => do
        let (t, rest) ← parseTy L ts
        arms rest (t :: acc)
    let (Rs, rest) ← arms rest []
    let tags ← Rs.mapM fun R => match R.whnf with
      | .app c _ => c.typeTag
      | _ => none
    -- (At least two cases: inty reads `Number` alone as `Number`.)
    if tags.Nodup ∧ 2 ≤ tags.length then some (.variant .typeOf tags Rs, rest) else none
  | _ => none

mutual
/-- A polymorphic annotation's type, whose variable `i` (`(tv i)`) is the
scheme's quantified variable `i`. -/
def bindVars : Ty → PTy
  | .var i => .bound i
  | .app c args => .app c (bindVarsL args)
  | .mu i sys => .mu i (sys.map RTy.toPTy)
/-- `bindVars`, for a list of types. -/
def bindVarsL : List Ty → List PTy
  | [] => []
  | t :: ts => bindVars t :: bindVarsL ts
end

mutual
/-- Parse one expression from the front of the tokens. -/
partial def parseExpr (L : Option (List String)) : List String → Option (Expr × List String)
  | "(" :: tag :: rest => do
    let (e, rest) ← parseForm L tag rest
    match rest with
    | ")" :: rest => some (e, rest)
    | _ => none
  | _ => none

partial def parseForm (L : Option (List String)) (tag : String) (ts : List String) :
    Option (Expr × List String) :=
  match tag, ts with
  | "num", m :: e :: rest => do
    let m ← m.toNat?
    let e ← e.toNat?
    some (.lit (.number (Float.ofScientific m true e)), rest)
  | "str", s :: rest =>
    if s.startsWith "s:" then some (.lit (.string (unescape (s.drop 2).toString)), rest) else none
  | "bool", "true" :: rest => some (.lit (.boolean true), rest)
  | "bool", "false" :: rest => some (.lit (.boolean false), rest)
  | "undef", rest => some (.lit .undefined, rest)
  | "null", rest => some (.lit .null, rest)
  | "var", i :: rest => do some (.var (← i.toNat?), rest)
  | "func", n :: rest => do
    let n ← n.toNat?
    let (b, rest) ← parseExpr L rest
    some (.func n b, rest)
  | "app", rest => do
    let (f, rest) ← parseExpr L rest
    let (args, rest) ← parseMany L rest
    some (.app f args, rest)
  | "let", rest => do
    let (e₁, rest) ← parseExpr L rest
    let (e₂, rest) ← parseExpr L rest
    some (.let_ false none e₁ e₂, rest)
  | "letmut", rest => do
    let (e₁, rest) ← parseExpr L rest
    let (e₂, rest) ← parseExpr L rest
    some (.let_ true none e₁ e₂, rest)
  | "letann", rest => do
    let (t, rest) ← parseTy L rest
    let (e₁, rest) ← parseExpr L rest
    let (e₂, rest) ← parseExpr L rest
    some (.let_ false (some (.mono t)) e₁ e₂, rest)
  | "letpoly", n :: rest => do
    let n ← n.toNat?
    let (t, rest) ← parseTy L rest
    let (e₁, rest) ← parseExpr L rest
    let (e₂, rest) ← parseExpr L rest
    some (.let_ false (some ⟨n, bindVars t, []⟩) e₁ e₂, rest)
  | "letmutann", rest => do
    let (t, rest) ← parseTy L rest
    let (e₁, rest) ← parseExpr L rest
    let (e₂, rest) ← parseExpr L rest
    some (.let_ true (some (.mono t)) e₁ e₂, rest)
  | "assign", i :: rest => do
    let i ← i.toNat?
    let (e, rest) ← parseExpr L rest
    some (.assign i e, rest)
  | "cond", rest => do
    let (c, rest) ← parseExpr L rest
    let (t, rest) ← parseExpr L rest
    let (e, rest) ← parseExpr L rest
    some (.cond c t e, rest)
  | "not", rest => do let (e, rest) ← parseExpr L rest; some (.unop .not e, rest)
  | "typeof", rest => do let (e, rest) ← parseExpr L rest; some (.unop .typeof e, rest)
  | "neg", rest => do let (e, rest) ← parseExpr L rest; some (.unop .neg e, rest)
  | "plus", rest => do
    let (a, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    some (.binop .plus a b, rest)
  | "minus", rest => do
    let (a, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    some (.binop .minus a b, rest)
  | "times", rest => parseBin L .times rest
  | "mod", rest => parseBin L .mod rest
  | "div", rest => parseBin L .div rest
  | "lt", rest => parseBin L .lt rest
  | "le", rest => parseBin L .le rest
  | "gt", rest => parseBin L .gt rest
  | "ge", rest => parseBin L .ge rest
  | "eq", rest => parseBin L (.strictEq false) rest
  | "ne", rest => parseBin L (.strictEq true) rest
  | "ret", rest => do let (e, rest) ← parseExpr L rest; some (.ret e, rest)
  | "throw", rest => do let (e, rest) ← parseExpr L rest; some (.throw_ e, rest)
  | "seq", rest => do
    let (a, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    some (.seq a b, rest)
  | "while", rest => do
    let (c, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    some (.while_ c b, rest)
  | "break", rest => some (.break_, rest)
  | "continue", rest => some (.continue_, rest)
  | "trycatch", rest => do
    let (b, rest) ← parseExpr L rest
    let (h, rest) ← parseExpr L rest
    some (.tryCatch b h, rest)
  | "unwrap", rest => do
    let (a, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    let (c, rest) ← parseExpr L rest
    some (.unwrap a b c, rest)
  | "casetag", rest => do
    let (a, rest) ← parseExpr L rest
    let (l, rest) ← parseLabel rest
    let (t, rest) ← match rest with
      | "true" :: rest => some (Tag.bool true, rest)
      | "false" :: rest => some (Tag.bool false, rest)
      | _ => (parseLabel rest).map fun (t, rest) => (Tag.str t, rest)
    let (b, rest) ← parseExpr L rest
    let (c, rest) ← parseExpr L rest
    some (.caseTag a (.field l) t b c, rest)
  | "typetest", rest => do
    let (a, rest) ← parseExpr L rest
    let (t, rest) ← parseLabel rest
    let (b, rest) ← parseExpr L rest
    let (c, rest) ← parseExpr L rest
    some (.caseTag a .typeOf (.str t) b c, rest)
  | "tryfinally", rest => do
    let (b, rest) ← parseExpr L rest
    let (f, rest) ← parseExpr L rest
    some (.tryFinally b f, rest)
  | "obj", rest => do
    let (fs, rest) ← parseFields L rest
    let ks ← fs.mapM fun f => match f.2.2 with
      | "field" => some FieldKind.data
      | "method" => some .method
      | "getter" => some .getter
      | _ => none
    some (.obj (fs.map (·.1)) (fs.map (·.2.1)) ks, rest)
  | "class", rest => do
    let (fs, rest) ← parseFields L rest
    let ks ← fs.mapM fun f => match f.2.2 with
      | "field" => some ClassKind.data
      | "arrow" => some .arrow
      | "method" => some .method
      | "getter" => some .getter
      | _ => none
    some (.cls (fs.map (·.1)) (fs.map (·.2.1)) ks, rest)
  | "ctor", n :: rest => do
    let n ← n.toNat?
    let (b, rest) ← parseExpr L rest
    some (.ctor n b, rest)
  | "new", rest => do
    let (f, rest) ← parseExpr L rest
    let (args, rest) ← parseMany L rest
    some (.new_ f args, rest)
  | "get", rest => do
    let (e, rest) ← parseExpr L rest
    let (l, rest) ← parseLabel rest
    some (.get e l, rest)
  | "set", rest => do
    let (e, rest) ← parseExpr L rest
    let (l, rest) ← parseLabel rest
    let (v, rest) ← parseExpr L rest
    some (.set e l v, rest)
  | "spread", rest => do
    let (a, rest) ← parseExpr L rest
    let (b, rest) ← parseExpr L rest
    some (.spread a b, rest)
  | "arr", rest => do
    let (es, rest) ← parseMany L rest
    some (.arr es, rest)
  | "index", rest => do
    let (e, rest) ← parseExpr L rest
    let (i, rest) ← parseExpr L rest
    some (.index e i, rest)
  | "setindex", rest => do
    let (e, rest) ← parseExpr L rest
    let (i, rest) ← parseExpr L rest
    let (v, rest) ← parseExpr L rest
    some (.setIndex e i v, rest)
  | "mcall", rest => do
    let (e, rest) ← parseExpr L rest
    let (l, rest) ← parseLabel rest
    let (args, rest) ← parseMany L rest
    some (.mcall e l args, rest)
  | _, _ => none

/-- A binary operator's operands. -/
partial def parseBin (L : Option (List String)) (op : BinOp) (ts : List String) :
    Option (Expr × List String) := do
  let (a, rest) ← parseExpr L ts
  let (b, rest) ← parseExpr L rest
  some (.binop op a b, rest)

/-- A property label, written `s:` then the label. -/
partial def parseLabel : List String → Option (String × List String)
  | l :: rest => if l.startsWith "s:" then some (unescape (l.drop 2).toString, rest) else none
  | [] => none

/-- An object literal's or a class's members, `(KIND s:x E)` each, with
its kind, up to a closing `)`, which is left in place. -/
partial def parseFields (L : Option (List String)) :
    List String → Option (List (String × Expr × String) × List String)
  | ")" :: rest => some ([], ")" :: rest)
  | "(" :: kind :: ts => do
    let (l, rest) ← parseLabel ts
    let (e, rest) ← parseExpr L rest
    match rest with
    | ")" :: rest => do
      let (fs, rest) ← parseFields L rest
      some ((l, e, kind) :: fs, rest)
    | _ => none
  | _ => none

/-- Parse expressions up to a closing `)`, which is left in place. -/
partial def parseMany (L : Option (List String)) : List String → Option (List Expr × List String)
  | ")" :: rest => some ([], ")" :: rest)
  | ts => do
    let (e, rest) ← parseExpr L ts
    let (es, rest) ← parseMany L rest
    some (e :: es, rest)
end

mutual
/-- Read an assignment to an annotated `let`, `x = e`, as
`x = (const t: T = e; t)`, so that `e` is checked against `x`'s
annotation `T` (inty subsumes `e` into it), and its value taken into `T`'s
sum if it's one: `anns` gives each variable's annotation, if it's an
annotated `let`. The two evaluate alike. -/
partial def annAssigns (anns : List (Option Scheme)) : Expr → Expr
  | .func n body => .func n (annAssigns (List.replicate n none ++ none :: none :: anns) body)
  | .ctor n body => .ctor n (annAssigns (List.replicate n none ++ none :: none :: anns) body)
  | .app f args => .app (annAssigns anns f) (args.map (annAssigns anns))
  | .let_ m s e₁ e₂ =>
    .let_ m s (annAssigns anns e₁) (annAssigns ((if m then s else none) :: anns) e₂)
  | .assign j e =>
    match anns[j]? with
    | some (some s) => .assign j (.let_ false (some s) (annAssigns anns e) (.var 0))
    | _ => .assign j (annAssigns anns e)
  | .cond c t e => .cond (annAssigns anns c) (annAssigns anns t) (annAssigns anns e)
  | .unop o e => .unop o (annAssigns anns e)
  | .ret e => .ret (annAssigns anns e)
  | .throw_ e => .throw_ (annAssigns anns e)
  | .binop o a b => .binop o (annAssigns anns a) (annAssigns anns b)
  | .seq a b => .seq (annAssigns anns a) (annAssigns anns b)
  | .while_ a b => .while_ (annAssigns anns a) (annAssigns anns b)
  | .tryFinally a b => .tryFinally (annAssigns anns a) (annAssigns anns b)
  | .spread a b => .spread (annAssigns anns a) (annAssigns anns b)
  | .index a b => .index (annAssigns anns a) (annAssigns anns b)
  | .tryCatch b h => .tryCatch (annAssigns anns b) (annAssigns (none :: anns) h)
  | .obj ls es ks => .obj ls (es.map (annAssigns anns)) ks
  | .arr es => .arr (es.map (annAssigns anns))
  | .setIndex e i v => .setIndex (annAssigns anns e) (annAssigns anns i) (annAssigns anns v)
  | .get e l => .get (annAssigns anns e) l
  | .set e l v => .set (annAssigns anns e) l (annAssigns anns v)
  | .mcall e l args => .mcall (annAssigns anns e) l (args.map (annAssigns anns))
  | .new_ f args => .new_ (annAssigns anns f) (args.map (annAssigns anns))
  | .cls ls es ks => .cls ls (annAssignsCls anns 0 es ks) ks
  | .unwrap a b c => .unwrap (annAssigns anns a) (annAssigns anns b) (annAssigns (none :: anns) c)
  | .caseTag a d t b c =>
    .caseTag (annAssigns anns a) d t (annAssigns (none :: anns) b) (annAssigns (none :: anns) c)
  | e => e

/-- `annAssigns`, for a class's members: an initialiser sees the fields
before it. -/
partial def annAssignsCls (anns : List (Option Scheme)) :
    Nat → List Expr → List ClassKind → List Expr
  | d, e :: es, .data :: ks =>
    annAssigns (List.replicate d none ++ anns) e :: annAssignsCls anns (d + 1) es ks
  | d, e :: es, _ :: ks => annAssigns anns e :: annAssignsCls anns d es ks
  | _, es, _ => es
end

/-- The labels of the annotations' records: an `s:` token right after `(`. -/
def annLabels : List String → List String
  | "(" :: l :: rest => if l.startsWith "s:" then unescape (l.drop 2).toString :: annLabels rest
    else annLabels (l :: rest)
  | _ :: rest => annLabels rest
  | [] => []

/-- Parse a whole line, with the labels its records are over: the
program's and its annotations'. The annotations' records are over the
labels once these are known, so the line is parsed twice. -/
def parse (s : String) : Option (List String × Expr) :=
  let ts := tokenize s
  match parseExpr none ts with
  | some (e₀, []) =>
    let L := (e₀.labels ++ annLabels ts).eraseDups
    match parseExpr (some L) ts with
    | some (e, []) => some (L, annAssigns [] e)
    | _ => none
  | _ => none

def tyWire : Ty → String
  | .number => "number"
  | .string => "string"
  | .boolean => "boolean"
  | .undefined => "undefined"
  | .null => "null"
  | .fn .. => "fun"
  | .record .. => "obj"
  | .array _ => "array"
  | .nullable _ => "nullable"
  | .optional _ => "optional"
  -- inty's type for what a `catch` binds is a rigid type variable.
  | .unknown | .var _ => "var"
  -- A sum told apart by `typeof`, inty's union of its cases.
  | .variant .typeOf _ _ => "union"
  -- A recursive type, by its unfolding.
  | .mu i sys =>
    match (Ty.mu i sys).view with
    | some (.app .fn _) => "fun"
    | some (.app (.record _) _) => "obj"
    | _ => "other"
  | _ => "other"

/-- Inference's verdict: `type T`, or `reject`, which includes a constraint
no type could satisfy (`Plus` on `undefined`, or on a function; a property
an object doesn't have) and a program failing the scope checks (an
assignment to a `const`, a `break` outside a loop). A constraint left on a
type variable is harmless, and inty leaves it in place; `T` keeps the
variable, as inty's type does. -/
def inferVerdict (L : List String) (e : Expr) : String :=
  match inferIn L [] e with
  | none => "reject"
  | some τ => s!"type {tyWire τ}"

def valueWire : Value → String
  | .number n => s!"num {n.toBits}"
  | .string s => s!"str s:{escape s}"
  | .boolean b => s!"bool {b}"
  | .undefined => "undef"
  | .null => "null"
  | .closure .. | .prim _ | .bound .. => "fun"
  | .obj _ => "obj"
  | .arr _ => "arr"
  -- An object's and an array's contents are in its cell, never a
  -- program's value.
  | .fields _ => "fields"
  | .items _ => "items"

def stuckWire : Stuck → String
  | .undefinedVariable => "undefinedVariable"
  | .notCallable => "notCallable"
  | .typeMismatch => "typeMismatch"
  | .arityMismatch => "arityMismatch"
  | .notIndexable => "notIndexable"
  | .propertyNotFound => "propertyNotFound"
  | .badAssignmentTarget => "badAssignmentTarget"
  | .notSpreadable => "notSpreadable"
  | .readOnly => "readOnly"

/-- The interpreter's verdict: `value V`, `stuck R`, or `timeout`. -/
def evalVerdict (clock : Nat) (e : Expr) : String :=
  match eval clock [] [] e with
  | .ok v => s!"value {valueWire v}"
  | .stuck s => s!"stuck {stuckWire s}"
  | .timeout => "timeout"
  | .thrown v => s!"thrown {valueWire v}"
  -- Only inside a function; at the top level the typing rules rule it out.
  | .returned v => s!"returned {valueWire v}"
  -- Only in a program that fails the scope checks.
  | .broke => "stuck break"
  | .continued => "stuck continue"
  -- A fault the typing rules allow, such as an index out of bounds.
  | .fault .outOfBounds => "fault outOfBounds"

/-- The answer to one line. -/
def verdict (clock : Nat) (line : String) : String :=
  match parse line with
  | none => "error unparsable"
  | some (L, e) => s!"{inferVerdict L e};{evalVerdict clock e}"

#guard verdict 100 "(app (func 1 (var 0)) (num 15 1))" ==
  s!"type number;value num {(1.5 : Float).toBits}"
#guard verdict 100 "(plus (num 1 0) (str s:a))" == "reject;stuck typeMismatch"
-- A function is always truthy, so testing one is rejected (`Testable`).
#guard verdict 100 "(not (func 1 (plus (var 0) (var 0))))" == "reject;value bool false"
#guard verdict 100 "(not (num 0 0))" == "type boolean;value bool true"
#guard verdict 100 "(let (func 1 (var 0)) (app (var 0) (str s:)))" == "type string;value str s:"
#guard verdict 100 "(app (func 2 (var 1)) (num 1 0) (str s:a))" == "type string;value str s:a"
#guard verdict 100 "(app (func 0 (var 1)))" == "type undefined;value undef"
#guard verdict 100 "(app (func 2 (var 1)) (num 1 0))" == "reject;stuck arityMismatch"
-- An extra argument is ignored, as in JavaScript; the typing rules still
-- want one argument per parameter (optional parameters come with phase 10).
#guard verdict 100 "(app (func 0 (str s:a)) (num 1 0))" == "reject;value str s:a"
#guard verdict 100 "(app (num 1 0" == "error unparsable"
-- A string's and an array's methods, natives by their number of arguments.
#guard verdict 100 "(mcall (str s:hello) s:slice/1 (num 1 0))" == "type string;value str s:ello"
#guard verdict 100 "(get (mcall (arr (num 1 0) (num 2 0)) s:slice/1 (num 1 0)) s:length)" ==
  s!"type number;value num {(1 : Float).toBits}"
#guard verdict 100 "(mcall (num 1 0) s:slice/1 (num 1 0))" == "reject;stuck notIndexable"
-- A sum told apart by `typeof`: a value of a case is injected into it, and a
-- test of its `typeof` takes it apart; it can't be used as a case.
#guard verdict 100
  "(letann (sum number string) (num 1 0) (typetest (var 0) s:number (num 0 0) (minus (var 0) (num 1 0))))"
  == s!"type number;value num {(0 : Float).toBits}"
#guard verdict 100
  "(letann (sum number string) (str s:ab) (typetest (var 0) s:number (str s:no) (str s:yes)))"
  == "type string;value str s:no"
#guard verdict 100 "(letann (sum number string) (num 1 0) (minus (var 0) (num 1 0)))" ==
  s!"reject;value num {(0 : Float).toBits}"
#guard verdict 100 "(letann (sum number string) (bool true) (num 0 0))" ==
  s!"reject;value num {(0 : Float).toBits}"
#guard verdict 100
  "(letann (sum number (fn number number)) (func 1 (var 0)) (typetest (var 0) s:function (num 0 0) (app (var 0) (num 2 0))))"
  == s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100
  "(letann (sum number string) (num 1 0) (typetest (var 0) s:boolean (num 0 0) (num 1 0)))" ==
  s!"reject;value num {(0 : Float).toBits}"
-- A variant tagged by `k`: an object literal checked against it takes its
-- tag's case, and a test of the tag takes it apart, the case's fields
-- readable in its branch and only the rest's in the other.
#guard verdict 100
  "(letann (variant s:k (rec (s:k (strlit s:a)) (s:x number)) (rec (s:k (strlit s:b)))) (obj (field s:k (str s:a)) (field s:x (num 1 0))) (casetag (var 0) s:k s:a (num 0 0) (get (var 0) s:x)))"
  == s!"type number;value num {(1 : Float).toBits}"
#guard verdict 100
  "(letann (variant s:k (rec (s:k (strlit s:a)) (s:x number)) (rec (s:k (strlit s:b)))) (obj (field s:k (str s:b))) (casetag (var 0) s:k s:a (str s:no) (str s:yes)))"
  == "type string;value str s:no"
#guard verdict 100
  "(letann (variant s:k (rec (s:k (strlit s:a)) (s:x number)) (rec (s:k (strlit s:b)))) (obj (field s:k (str s:b))) (casetag (var 0) s:k s:a (get (var 0) s:x) (num 0 0)))"
  == s!"reject;stuck propertyNotFound"
#guard verdict 100 "(letann (variant s:k (rec (s:k (strlit s:a)) (s:x number)) (rec (s:k (strlit s:b)))) (obj (field s:k (str s:c))) (num 0 0))" ==
  s!"reject;value num {(0 : Float).toBits}"
#guard verdict 100 "(letann (variant s:k (rec (s:k (strlit s:a)) (s:x number)) (rec (s:k (strlit s:b)))) (obj (field s:k (str s:a))) (num 0 0))" ==
  s!"reject;value num {(0 : Float).toBits}"
#guard verdict 100
  "(let (obj (field s:k (str s:a))) (casetag (var 0) s:k s:a (num 0 0) (num 1 0)))"
  == s!"reject;value num {(1 : Float).toBits}"
#guard verdict 100 "(app (func 1 (seq (ret (str s:a)) (str s:b))) (null))" == "type string;value str s:a"
-- A polymorphic annotation: the initialiser is checked with its variables
-- rigid; one that isn't polymorphic enough, or whose rigid variable would
-- escape into a parameter's type, is rejected.
#guard verdict 100 "(letpoly 1 (fn (tv 0) (tv 0)) (func 1 (var 0)) (app (var 0) (str s:)))" ==
  "type string;value str s:"
#guard verdict 100 "(letpoly 1 (fn (tv 0) (tv 0)) (func 1 (num 5 0)) (app (var 0) (str s:)))" ==
  s!"reject;value num {(5 : Float).toBits}"
#guard verdict 100
  "(app (func 1 (letpoly 1 (fn (tv 0) (tv 0)) (func 1 (seq (arr (var 3) (var 0)) (var 0))) (var 1))) (num 1 0))" ==
  s!"reject;value num {(1 : Float).toBits}"
-- A statement's value is dropped: the branches of an `if` whose value
-- nothing uses needn't have one type.
#guard verdict 100 "(seq (cond (bool true) (num 1 0) (str s:a)) (num 2 0))" ==
  s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(cond (bool true) (num 1 0) (str s:a))" == s!"reject;value num {(1 : Float).toBits}"
#guard verdict 100 "(throw (num 1 0))" == s!"type var;thrown num {(1 : Float).toBits}"
#guard verdict 100 "(ret (num 1 0))" == "reject;returned num 4607182418800017408"
#guard verdict 100 "(letmut (num 1 0) (seq (assign 0 (str s:a)) (var 0)))" ==
  "reject;value str s:a"
#guard verdict 100 "(letmut (num 1 0) (seq (assign 0 (num 2 0)) (var 0)))" ==
  s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(let (num 1 0) (assign 0 (num 2 0)))" ==
  s!"reject;value num {(2 : Float).toBits}"
#guard verdict 100 "(trycatch (throw (str s:x)) (typeof (var 0)))" == "type string;value str s:string"
#guard verdict 100 "(break)" == "reject;stuck break"
-- The operators of numbers, and `===`.
#guard verdict 100 "(lt (times (num 3 0) (num 2 0)) (div (num 13 0) (num 2 0)))" ==
  "type boolean;value bool true"
#guard verdict 100 "(eq (str s:a) (num 1 0))" == "type boolean;value bool false"
#guard verdict 100 "(ne (null) (undef))" == "type boolean;value bool true"
-- The comparisons: two numbers or two strings, by UTF-16 code units; no
-- coercion between types.
#guard verdict 100 "(lt (str s:a) (str s:b))" == "type boolean;value bool true"
#guard verdict 100 "(ge (str s:ab) (str s:a))" == "type boolean;value bool true"
#guard verdict 100 "(lt (str s:a) (num 1 0))" == "reject;stuck typeMismatch"
#guard verdict 100 "(lt (bool true) (bool false))" == "reject;stuck typeMismatch"
#guard unitsLt "😀".utf16 "｡".utf16 && !unitsLt "｡".utf16 "😀".utf16

#guard verdict 100 "(letmut (num 2 0) (seq (while (var 0) (assign 0 (minus (var 0) (num 1 0)))) (var 0)))"
  == s!"type number;value num {(0 : Float).toBits}"
#guard verdict 100 "(get (obj (field s:x (num 1 0)) (field s:y (str s:a))) s:y)" ==
  "type string;value str s:a"
#guard verdict 100 "(get (obj (field s:x (num 1 0))) s:y)" == "reject;stuck propertyNotFound"
#guard verdict 100 "(let (obj (field s:x (num 1 0))) (seq (set (var 0) s:x (num 2 0)) (get (var 0) s:x)))"
  == s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(let (obj (field s:x (num 1 0))) (set (var 0) s:x (str s:a)))" ==
  "reject;value str s:a"
-- A function reading a property works on any object with it.
#guard verdict 100
  "(let (func 1 (get (var 0) s:x)) (plus (app (var 0) (obj (field s:x (num 1 0)))) (app (var 0) (obj (field s:x (num 2 0)) (field s:y (null))))))"
  == s!"type number;value num {(3 : Float).toBits}"
#guard verdict 100 "(get (num 1 0) s:x)" == "reject;stuck notIndexable"
-- Writing a property an object hasn't adds it, as in JavaScript; the typing
-- rules reject it, since a record has the fields of its literal.
#guard verdict 100 "(let (obj) (seq (set (var 0) s:y (num 1 0)) (get (var 0) s:y)))" ==
  s!"reject;value num {(1 : Float).toBits}"
-- A later field overrides an earlier one, as in JavaScript.
#guard verdict 100 "(get (obj (field s:x (num 1 0)) (field s:x (str s:a))) s:x)" ==
  "type string;value str s:a"
-- A spread's later operand wins where it has the field, the earlier one
-- where it hasn't.
#guard verdict 100 "(get (spread (obj (field s:x (num 1 0))) (obj (field s:x (str s:a)))) s:x)" ==
  "type string;value str s:a"
#guard verdict 100 "(get (spread (obj (field s:x (num 1 0))) (obj (field s:y (null)))) s:x)" ==
  s!"type number;value num {(1 : Float).toBits}"
-- `function (o) { return {a: 1, ...o}; }`: the result's `a` is `o`'s if it
-- has one, so its type waits for `o`'s.
#guard verdict 100
  "(let (func 1 (spread (obj (field s:a (num 1 0))) (var 0))) (minus (get (app (var 0) (obj (field s:a (str s:s)))) s:a) (num 1 0)))"
  == "reject;stuck typeMismatch"
#guard verdict 100
  "(let (func 1 (spread (obj (field s:a (num 1 0))) (var 0))) (minus (get (app (var 0) (obj)) s:a) (num 1 0)))"
  == s!"type number;value num {(0 : Float).toBits}"
#guard verdict 100 "(spread (num 1 0) (obj))" == "reject;stuck notSpreadable"
-- Arrays: one element type; an index in bounds reads and writes, one just
-- past the end appends, and any other is a fault.
#guard verdict 100 "(index (arr (num 1 0) (num 2 0)) (num 1 0))" ==
  s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(arr (num 1 0) (str s:a))" == "reject;value arr"
#guard verdict 100 "(get (arr (num 1 0) (num 2 0)) s:length)" ==
  s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(index (str s:ab) (num 1 0))" == "type string;value str s:b"
#guard verdict 100 "(index (arr (num 1 0)) (num 3 0))" == "type number;fault outOfBounds"
#guard verdict 100
  "(let (arr (num 1 0)) (seq (setindex (var 0) (num 1 0) (num 5 0)) (get (var 0) s:length)))" ==
  s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100 "(setindex (str s:ab) (num 0 0) (str s:c))" == "reject;stuck badAssignmentTarget"
#guard verdict 100 "(set (arr) s:length (num 0 0))" == "reject;stuck badAssignmentTarget"
#guard verdict 100 "(let (func 1 (index (var 0) (num 0 0))) (app (var 0) (arr (bool true))))" ==
  "type boolean;value bool true"

-- A method's `this` is its receiver; `c.inc().inc()` types through a
-- recursive type.
#guard verdict 100
  "(let (obj (field s:v (num 0 0)) (field s:inc (func 0 (seq (set (var 1) s:v (plus (get (var 1) s:v) (num 1 0))) (ret (var 1)))))) (get (mcall (mcall (var 0) s:inc) s:inc) s:v))"
  == s!"type number;value num {(2 : Float).toBits}"
#guard verdict 100
  "(let (obj (field s:me (func 0 (var 1)))) (mcall (var 0) s:me))" == "type obj;value obj"
#guard verdict 100 "(mcall (obj (field s:f (num 1 0))) s:f)" == "reject;stuck notCallable"
#guard verdict 100 "(mcall (obj) s:f)" == "reject;stuck propertyNotFound"

end Inty.Wire
