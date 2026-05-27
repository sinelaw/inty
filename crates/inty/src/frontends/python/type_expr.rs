//! Parser for Python *type expressions* (the things after `:` / `->`, and
//! generic arguments) into the frontend-neutral [`TypeAst`] IR.
//!
//! This is the Bucket-A mapping from `docs/pyi-import-mapping.md`:
//! primitives, `Optional`/`Union`/`|`, `list`/`dict`/`tuple`/sequences,
//! `Callable`, `Literal`, and the erasable wrappers (`Final`, `Annotated`,
//! …). Anything outside it becomes [`TypeAst::Opaque`].
//!
//! It is allocator-free (produces an IR, not a `Type`), so it is shared by
//! both the `.pyi` stub reader and — eventually — `.py` annotation
//! checking (#35). Lowering to a real type happens in
//! `InferState::lower_type_ast`.

use std::collections::HashSet;

use super::lexer::Tok;
use crate::span::Spanned;
use crate::types::{LitValue, TypeAst};

/// Parse a Python type expression beginning at `pos` in `toks`, returning
/// the IR and the position just past it. `toks` must be terminated by
/// `Tok::Eof` (the Python lexer guarantees this).
///
/// No names are treated as type variables; every bare name maps to a
/// primitive or [`TypeAst::Opaque`]. Use [`parse_type_with_vars`] to have
/// declared `TypeVar`s lower as shareable [`TypeAst::Var`] nodes.
pub fn parse_type(toks: &[Spanned<Tok>], pos: usize) -> (TypeAst, usize) {
    let empty = HashSet::new();
    parse_type_with_vars(toks, pos, &empty)
}

/// Like [`parse_type`], but a bare name in `type_vars` parses to
/// [`TypeAst::Var`] (a named type variable) instead of degrading to
/// opaque, so generic positions (`Generic[T]` fields, generic-function
/// signatures) can tie their occurrences together when lowered.
pub fn parse_type_with_vars(
    toks: &[Spanned<Tok>],
    pos: usize,
    type_vars: &HashSet<String>,
) -> (TypeAst, usize) {
    let mut c = Cursor {
        toks,
        pos,
        type_vars,
    };
    let ast = c.parse_type();
    (ast, c.pos)
}

struct Cursor<'a> {
    toks: &'a [Spanned<Tok>],
    pos: usize,
    type_vars: &'a HashSet<String>,
}

impl Cursor<'_> {
    fn cur(&self) -> &Tok {
        &self.toks[self.pos].value
    }

    fn at_eof(&self) -> bool {
        matches!(self.cur(), Tok::Eof)
    }

    fn advance(&mut self) -> Tok {
        let t = self.toks[self.pos].value.clone();
        if !self.at_eof() {
            self.pos += 1;
        }
        t
    }

    fn check(&self, t: &Tok) -> bool {
        self.cur() == t
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.check(t) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// `type ::= atom ('|' atom)*` — a `|` chain is a union (`int | None`).
    fn parse_type(&mut self) -> TypeAst {
        let mut members = vec![self.parse_atom()];
        while self.eat(&Tok::Pipe) {
            members.push(self.parse_atom());
        }
        if members.len() == 1 {
            members.pop().unwrap()
        } else {
            TypeAst::Union(members)
        }
    }

    fn parse_atom(&mut self) -> TypeAst {
        match self.cur().clone() {
            Tok::None => {
                self.advance();
                TypeAst::Null
            }
            Tok::Name(name) => {
                self.advance();
                // Collect a dotted path `a.b.C`. The full path is preserved
                // so lowering can resolve it through the import environment
                // (a qualified `mod.Class` goes through the `mod` namespace;
                // a bare name binds in the local scope). The final segment
                // is used only to recognise the built-in / typing
                // constructors (`typing.List[int]` ≡ `List[int]`).
                let mut segments = vec![name];
                while self.check(&Tok::Dot) {
                    self.advance();
                    if let Tok::Name(n) = self.cur().clone() {
                        self.advance();
                        segments.push(n);
                    } else {
                        break;
                    }
                }
                let qualified = segments.len() > 1;
                let last = segments.last().unwrap().clone();
                if self.check(&Tok::LBracket) {
                    self.parse_generic(&segments.join("."), &last)
                } else if !qualified && self.type_vars.contains(&last) {
                    TypeAst::Var(last)
                } else if !qualified {
                    // Bare name: primitive, or a `Ref` to be resolved in
                    // scope (alias / local class / imported class).
                    map_simple_name(&last)
                } else {
                    // Qualified bare name: resolved through the module
                    // namespace at lowering time.
                    TypeAst::Ref(segments.join("."), Vec::new())
                }
            }
            // A string forward-ref (`"Node"`) reached directly: opaque.
            Tok::Str(_) => {
                self.advance();
                TypeAst::Opaque
            }
            // Parenthesised type or tuple — model leniently as opaque.
            Tok::LParen => {
                self.skip_balanced(Tok::LParen, Tok::RParen);
                TypeAst::Opaque
            }
            Tok::LBracket => {
                self.skip_balanced(Tok::LBracket, Tok::RBracket);
                TypeAst::Opaque
            }
            _ => TypeAst::Opaque,
        }
    }

    /// `NAME [ args ]` — a subscripted (generic) type. `head` is the full
    /// (possibly dotted) name; `last` is its final segment, used to
    /// recognise the built-in / typing constructors (so `typing.List[int]`
    /// behaves like `List[int]`). An unknown constructor keeps the full
    /// `head` in its `Ref` so lowering can resolve it through scope.
    fn parse_generic(&mut self, head: &str, last: &str) -> TypeAst {
        // Forms needing raw access to their subscript tokens.
        if last == "Literal" {
            return self.parse_literal_args();
        }
        if last == "Callable" {
            return self.parse_callable_args();
        }
        let mut args = self.parse_type_args();
        match last {
            "list" | "List" | "Sequence" | "Iterable" | "Iterator" | "MutableSequence"
            | "frozenset" | "set" | "Set" => {
                TypeAst::Array(Box::new(first_or_opaque(args)))
            }
            "tuple" | "Tuple" => {
                // Homogeneous `tuple[T, ...]` → T[]; heterogeneous → the
                // union of the element types (lossy).
                match args.len() {
                    0 => TypeAst::Array(Box::new(TypeAst::Opaque)),
                    1 => TypeAst::Array(Box::new(args.pop().unwrap())),
                    _ => TypeAst::Array(Box::new(TypeAst::Union(args))),
                }
            }
            "dict" | "Dict" | "Mapping" | "MutableMapping" => {
                // Map is string-keyed; the value is the 2nd arg.
                let value = if args.len() >= 2 {
                    args.swap_remove(1)
                } else {
                    TypeAst::Opaque
                };
                TypeAst::Map(Box::new(value))
            }
            "Optional" => TypeAst::Union(vec![first_or_opaque(args), TypeAst::Null]),
            "Union" => TypeAst::Union(args),
            "Final" | "ClassVar" | "Annotated" | "InitVar" | "TypeGuard" => {
                // Erase the wrapper, keep the first argument.
                first_or_opaque(args)
            }
            // Unknown subscripted name: a reference to a (possibly
            // aliased) generic type — `Pair[int, str]`, a user class, etc.
            _ => TypeAst::Ref(head.to_string(), args),
        }
    }

    /// `Literal[ m, … ]` → a union of singleton-literal types. Members that
    /// aren't plain literals (e.g. `Literal[Color.RED]`) degrade to opaque.
    fn parse_literal_args(&mut self) -> TypeAst {
        if !self.eat(&Tok::LBracket) {
            return TypeAst::Opaque;
        }
        let mut members = Vec::new();
        while !self.check(&Tok::RBracket) && !self.at_eof() {
            let member = match self.cur().clone() {
                Tok::Str(s) => {
                    self.advance();
                    TypeAst::Lit(LitValue::String(s))
                }
                Tok::Number(n) => {
                    self.advance();
                    TypeAst::Lit(LitValue::Number(n))
                }
                Tok::True => {
                    self.advance();
                    TypeAst::Lit(LitValue::Bool(true))
                }
                Tok::False => {
                    self.advance();
                    TypeAst::Lit(LitValue::Bool(false))
                }
                Tok::None => {
                    self.advance();
                    TypeAst::Null
                }
                _ => {
                    self.skip_to_arg_end();
                    TypeAst::Opaque
                }
            };
            members.push(member);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.eat(&Tok::RBracket);
        match members.len() {
            0 => TypeAst::Opaque,
            1 => members.pop().unwrap(),
            _ => TypeAst::Union(members),
        }
    }

    /// `Callable[[A, B], R]` → `(A, B) => R`. `Callable[..., R]` (arbitrary
    /// args, inexpressible in inty) and malformed forms degrade to opaque
    /// so an over-broad callable still accepts any call.
    fn parse_callable_args(&mut self) -> TypeAst {
        if !self.eat(&Tok::LBracket) {
            return TypeAst::Opaque;
        }
        // First argument: a `[A, B]` parameter list, or `...` (Ellipsis).
        let params = if self.check(&Tok::LBracket) {
            Some(self.parse_type_args())
        } else {
            while !self.check(&Tok::Comma) && !self.check(&Tok::RBracket) && !self.at_eof() {
                self.advance();
            }
            None
        };
        self.eat(&Tok::Comma);
        let ret = if self.check(&Tok::RBracket) {
            TypeAst::Opaque
        } else {
            self.parse_type()
        };
        self.eat(&Tok::RBracket);

        match params {
            Some(ps) => TypeAst::Func(ps, Box::new(ret)),
            None => TypeAst::Opaque,
        }
    }

    /// Parse `[ T, U, … ]` into mapped argument types. A nested `[A, B]`
    /// group (a Callable param list reached out of context) is skipped;
    /// stray literal arguments are taken as opaque.
    fn parse_type_args(&mut self) -> Vec<TypeAst> {
        let mut out = Vec::new();
        if !self.eat(&Tok::LBracket) {
            return out;
        }
        while !self.check(&Tok::RBracket) && !self.at_eof() {
            if self.check(&Tok::LBracket) {
                self.skip_balanced(Tok::LBracket, Tok::RBracket);
            } else if matches!(self.cur(), Tok::Str(_) | Tok::Number(_)) {
                self.advance();
                out.push(TypeAst::Opaque);
            } else {
                out.push(self.parse_type());
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.eat(&Tok::RBracket);
        out
    }

    /// Skip a single subscript argument's tokens up to a top-level `,` or
    /// the closing `]`.
    fn skip_to_arg_end(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.cur() {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBrace => depth -= 1,
                Tok::RBracket if depth == 0 => break,
                Tok::RBracket => depth -= 1,
                Tok::Comma if depth == 0 => break,
                Tok::Eof | Tok::Newline => break,
                _ => {}
            }
            self.advance();
        }
    }

    /// Skip a balanced bracketed run starting at the current `open` token.
    fn skip_balanced(&mut self, open: Tok, close: Tok) {
        if !self.eat(&open) {
            return;
        }
        let mut depth = 1;
        while depth > 0 && !self.at_eof() {
            let t = self.advance();
            if t == open {
                depth += 1;
            } else if t == close {
                depth -= 1;
            }
        }
    }
}

/// Map a bare type name with no subscript.
fn map_simple_name(name: &str) -> TypeAst {
    match name {
        "int" | "float" | "complex" => TypeAst::Number,
        "str" => TypeAst::String,
        "bool" => TypeAst::Boolean,
        "bytes" | "bytearray" => TypeAst::String, // lossy: bytes ≈ String
        "None" | "NoneType" => TypeAst::Null,
        // `object` / `Any` are genuinely unconstrained → opaque.
        "object" | "Any" | "any" => TypeAst::Opaque,
        // Any other bare name is a reference to a (possibly aliased) type;
        // lowering resolves it against the alias table, or treats it as
        // opaque if unknown.
        other => TypeAst::Ref(other.to_string(), Vec::new()),
    }
}

fn first_or_opaque(args: Vec<TypeAst>) -> TypeAst {
    args.into_iter().next().unwrap_or(TypeAst::Opaque)
}

#[cfg(test)]
mod tests {
    use super::super::lexer::tokenize;
    use super::parse_type;
    use crate::infer::InferState;
    use crate::types::{LitValue, Type};
    use proptest::prelude::*;

    /// Parse a Python type expression string and lower it to a `Type`.
    fn ty(s: &str) -> Type {
        let toks = tokenize(s).expect("tokenize");
        let (ast, _) = parse_type(&toks, 0);
        InferState::new().lower_type_ast(&ast)
    }

    #[test]
    fn known_type_var_parses_to_var_and_shares_in_scope() {
        use super::parse_type_with_vars;
        use std::collections::{HashMap, HashSet};

        let vars: HashSet<String> = ["T".to_string()].into_iter().collect();
        // A name not in the set stays opaque; one in the set is a `Var`.
        let toks = tokenize("T").expect("tokenize");
        let (ast, _) = parse_type_with_vars(&toks, 0, &vars);
        assert_eq!(ast, super::TypeAst::Var("T".to_string()));

        // Lowering two `T` references through one scope yields the *same*
        // variable; an unrelated name lowers to a different one.
        let mut state = InferState::new();
        let mut scope: HashMap<String, Type> = HashMap::new();
        let t1 = state.lower_type_ast_scoped(&super::TypeAst::Var("T".into()), &mut scope);
        let t2 = state.lower_type_ast_scoped(&super::TypeAst::Var("T".into()), &mut scope);
        let u = state.lower_type_ast_scoped(&super::TypeAst::Var("U".into()), &mut scope);
        assert_eq!(t1, t2);
        assert_ne!(t1, u);

        // A fresh scope (the default `lower_type_ast`) does not share.
        let other = state.lower_type_ast(&super::TypeAst::Var("T".into()));
        assert_ne!(t1, other);
    }

    // ---- concrete Bucket-A mappings ----

    #[test]
    fn primitives_and_containers() {
        assert_eq!(ty("int"), Type::Number);
        assert_eq!(ty("float"), Type::Number);
        assert_eq!(ty("str"), Type::String);
        assert_eq!(ty("bool"), Type::Boolean);
        assert_eq!(ty("None"), Type::Null);
        assert_eq!(ty("list[int]"), Type::array(Type::Number));
        assert_eq!(ty("dict[str, int]"), Type::map(Type::Number));
    }

    #[test]
    fn callable_maps_to_function() {
        let expected = Type::wrap_callable(Type::raw_func_with_params(
            None,
            vec![crate::types::FuncParam::required(Type::Number)],
            Type::String,
        ));
        assert_eq!(ty("Callable[[int], str]"), expected);
    }

    #[test]
    fn literal_maps_to_literal_union() {
        assert_eq!(
            ty("Literal[\"a\", \"b\"]"),
            Type::union(vec![
                Type::Literal(LitValue::String("a".into())),
                Type::Literal(LitValue::String("b".into())),
            ])
        );
    }

    // ---- metamorphic: surface forms that must mean the same type ----

    #[test]
    fn optional_equals_union_with_none() {
        assert_eq!(ty("Optional[int]"), ty("int | None"));
    }

    #[test]
    fn union_keyword_equals_pipe() {
        assert_eq!(ty("Union[int, str]"), ty("int | str"));
    }

    #[test]
    fn union_is_commutative() {
        // `Type::union` sorts members, so order is irrelevant.
        assert_eq!(ty("int | str"), ty("str | int"));
    }

    #[test]
    fn erasable_wrappers_are_transparent() {
        assert_eq!(ty("Final[int]"), Type::Number);
        assert_eq!(ty("ClassVar[str]"), Type::String);
        assert_eq!(ty("Annotated[bool, \"doc\"]"), Type::Boolean);
    }

    #[test]
    fn dotted_names_parse_and_resolve() {
        // A qualified *constructor* still maps by its final segment, so a
        // qualified container generic behaves like its bare form.
        assert_eq!(ty("typing.List[int]"), Type::array(Type::Number));
        assert_eq!(ty("t.Optional[str]"), Type::union(vec![Type::String, Type::Null]));
        // A qualified *name* (no in-scope env in this helper) parses and
        // lowers to a fresh variable (opaque) rather than erroring; with an
        // import environment it would resolve through the namespace (see
        // the `python_imports` end-to-end tests).
        assert!(matches!(ty("subprocess.CompletedProcess"), Type::Var(_)));
        assert!(matches!(ty("builtins.int"), Type::Var(_)));
        assert!(matches!(ty("a.b.c.Unknown"), Type::Var(_)));
    }

    // ---- property tests over the IR + lowering ----

    fn ast_strategy() -> impl Strategy<Value = super::TypeAst> {
        use super::TypeAst;
        let leaf = prop_oneof![
            Just(TypeAst::Number),
            Just(TypeAst::String),
            Just(TypeAst::Boolean),
            Just(TypeAst::Null),
            Just(TypeAst::Opaque),
            "[a-z]".prop_map(TypeAst::Var),
            "[A-Z][a-z]*".prop_map(|n| TypeAst::Ref(n, Vec::new())),
            (-1000i64..1000).prop_map(|n| TypeAst::Lit(LitValue::Number(n as f64))),
        ];
        leaf.prop_recursive(4, 32, 3, |inner| {
            prop_oneof![
                inner.clone().prop_map(|t| TypeAst::Array(Box::new(t))),
                inner.clone().prop_map(|t| TypeAst::Map(Box::new(t))),
                prop::collection::vec(inner.clone(), 1..3).prop_map(TypeAst::Union),
                (prop::collection::vec(inner.clone(), 0..3), inner)
                    .prop_map(|(ps, r)| TypeAst::Func(ps, Box::new(r))),
            ]
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 200, ..ProptestConfig::default() })]

        /// Lowering is total: it never panics on any well-formed IR.
        #[test]
        fn lowering_is_total(ast in ast_strategy()) {
            let _ = InferState::new().lower_type_ast(&ast);
        }

        /// Lowering is a pure function of the IR and the starting state:
        /// two fresh states produce identical types (variable IDs are
        /// allocated deterministically).
        #[test]
        fn lowering_is_deterministic(ast in ast_strategy()) {
            let t1 = InferState::new().lower_type_ast(&ast);
            let t2 = InferState::new().lower_type_ast(&ast);
            prop_assert_eq!(t1, t2);
        }

        /// The top-level constructor is preserved for the non-normalising
        /// nodes (unions/opaque are intentionally rewritten by lowering).
        #[test]
        fn top_constructor_preserved(ast in ast_strategy()) {
            use super::TypeAst;
            let t = InferState::new().lower_type_ast(&ast);
            match &ast {
                TypeAst::Number => prop_assert_eq!(t, Type::Number),
                TypeAst::String => prop_assert_eq!(t, Type::String),
                TypeAst::Boolean => prop_assert_eq!(t, Type::Boolean),
                TypeAst::Null => prop_assert_eq!(t, Type::Null),
                TypeAst::Lit(v) => prop_assert_eq!(t, Type::Literal(v.clone())),
                TypeAst::Array(_) => prop_assert!(matches!(t, Type::Array(_))),
                TypeAst::Map(_) => prop_assert!(matches!(t, Type::Map(_))),
                TypeAst::Func(..) => prop_assert!(matches!(t, Type::Row(_))),
                TypeAst::Var(_) => prop_assert!(matches!(t, Type::Var(_))),
                // An unknown reference lowers to a fresh variable (no alias
                // table in this test), just like opaque.
                TypeAst::Ref(_, _) => prop_assert!(matches!(t, Type::Var(_))),
                TypeAst::Opaque | TypeAst::Union(_) => {}
            }
        }
    }
}
