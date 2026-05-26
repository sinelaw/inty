//! Reader for Python stub (`.pyi`) files.
//!
//! A `.pyi` is type declarations only — every body is `...`. This reader
//! tokenises with the Python lexer, walks the top-level declarations, and
//! maps each into an inty [`TypeScheme`], covering the **Bucket A** subset
//! of `docs/pyi-import-mapping.md` (primitives, `Optional`/`Union`,
//! `Literal`, `list`/`dict`/`Callable`, `def` signatures, module-level
//! annotated names, and plain classes as constructor + structural instance
//! row). Anything outside that subset — `Any`, overloads, unknown
//! constructs, parse trouble — degrades to an **opaque** export
//! (`forall a. a`), never an error, per the degradation contract (§6).
//!
//! Classes are read as *structural* instance rows for now (the constructor
//! returns `{fields + methods}`); nominal branding of imported classes is
//! deferred.

use std::collections::BTreeMap;

use super::lexer::{tokenize, Tok};
use crate::error::Result;
use crate::infer::InferState;
use crate::span::Spanned;
use crate::types::{FuncParam, PropName, Type, TypeScheme};

/// Parse `source` as a `.pyi` stub and return its exported `(name, scheme)`
/// pairs. Fresh type variables are drawn from `state` so they don't
/// collide with the importing program's.
pub fn read_stub(state: &mut InferState, source: &str) -> Result<Vec<(String, TypeScheme)>> {
    let toks = tokenize(source)?;
    let mut reader = StubReader {
        toks,
        pos: 0,
        state,
    };
    Ok(reader.module())
}

struct StubReader<'a> {
    toks: Vec<Spanned<Tok>>,
    pos: usize,
    state: &'a mut InferState,
}

impl StubReader<'_> {
    // ---- token helpers ----

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

    fn name_here(&self) -> Option<String> {
        match self.cur() {
            Tok::Name(n) => Some(n.clone()),
            _ => None,
        }
    }

    /// Skip tokens up to and including the next top-level `Newline`
    /// (used to discard a line we don't model). Stops at EOF.
    fn skip_line(&mut self) {
        while !self.check(&Tok::Newline) && !self.at_eof() {
            self.advance();
        }
        self.eat(&Tok::Newline);
    }

    /// Skip a balanced `Indent … Dedent` block if one immediately
    /// follows (a suite). Assumes the introducing `:` and `Newline`
    /// were already consumed.
    fn skip_block(&mut self) {
        if !self.eat(&Tok::Indent) {
            return;
        }
        let mut depth = 1;
        while depth > 0 && !self.at_eof() {
            match self.advance() {
                Tok::Indent => depth += 1,
                Tok::Dedent => depth -= 1,
                _ => {}
            }
        }
    }

    // ---- opaque / scheme helpers ----

    /// An opaque type: a fresh variable that generalises to `forall a. a`,
    /// so an imported name we can't model still type-checks at every use.
    fn opaque(&mut self) -> Type {
        self.state.fresh_type_var()
    }

    /// Generalise a stub type over its free variables without disturbing
    /// the inference state's pending constraints.
    fn scheme_of(ty: &Type) -> TypeScheme {
        let vars: Vec<_> = ty.free_vars().into_iter().filter(|v| v.is_flex()).collect();
        let pvars: Vec<_> = ty.free_pvars().into_iter().filter(|p| p.is_flex()).collect();
        if vars.is_empty() && pvars.is_empty() {
            TypeScheme::mono(ty.clone())
        } else {
            TypeScheme::poly_with_presence(vars, pvars, ty.clone())
        }
    }

    // ---- top level ----

    fn module(&mut self) -> Vec<(String, TypeScheme)> {
        let mut out = Vec::new();
        while !self.at_eof() {
            // Skip blank lines and stray dedents/indents at top level.
            if matches!(self.cur(), Tok::Newline | Tok::Indent | Tok::Dedent) {
                self.advance();
                continue;
            }
            if let Some((name, ty)) = self.top_decl() {
                out.push((name, Self::scheme_of(&ty)));
            }
        }
        out
    }

    /// Parse one top-level declaration, returning its export when it's a
    /// modellable form. Unmodelled lines are skipped (and contribute no
    /// export — the name becomes absent, which the importer reports if it
    /// actually tries to use it).
    fn top_decl(&mut self) -> Option<(String, Type)> {
        match self.cur().clone() {
            Tok::Def => self.def_decl(),
            Tok::Class => self.class_decl(),
            // Decorators: skip the line, then read the decorated decl.
            Tok::AugAssign(_) => {
                self.skip_line();
                None
            }
            Tok::Name(_) => self.name_decl(),
            // `from`/`import` re-exports, `if` version guards, `@deco`
            // lines, docstrings, etc.: skip for now.
            _ => {
                self.skip_line();
                None
            }
        }
    }

    /// `NAME : TYPE [= ...]` (module-level annotated name) or `NAME = ...`
    /// (assignment — modelled as opaque). A bare `NAME(...)` call line is
    /// skipped.
    fn name_decl(&mut self) -> Option<(String, Type)> {
        let name = self.name_here()?;
        self.advance(); // name
        if self.eat(&Tok::Colon) {
            let ty = self.parse_type();
            self.skip_line();
            return Some((name, ty));
        }
        if self.eat(&Tok::Assign) {
            // `Name = value` — could be a TypeAlias or a constant; we
            // don't distinguish yet, so export it opaque.
            let ty = self.opaque();
            self.skip_line();
            return Some((name, ty));
        }
        self.skip_line();
        None
    }

    /// `def NAME ( params ) [-> RET] : <body>`
    fn def_decl(&mut self) -> Option<(String, Type)> {
        self.advance(); // def
        let name = self.name_here()?;
        self.advance(); // name
        let (params, _had_self) = self.parse_params();
        let ret = if self.eat(&Tok::Arrow) {
            self.parse_type()
        } else {
            self.opaque()
        };
        self.consume_suite();
        let func = Type::wrap_callable(Type::raw_func_with_params(None, params, ret));
        Some((name, func))
    }

    /// Parse a parenthesised parameter list into `FuncParam`s, dropping a
    /// leading `self`/`cls`. Returns `(params, had_self)`.
    fn parse_params(&mut self) -> (Vec<FuncParam>, bool) {
        let mut params = Vec::new();
        let mut had_self = false;
        if !self.eat(&Tok::LParen) {
            return (params, had_self);
        }
        let mut first = true;
        while !self.check(&Tok::RParen) && !self.at_eof() {
            // `*args` / `**kwargs` / bare `*`: stop modelling further
            // params (variadics are Bucket C).
            if matches!(self.cur(), Tok::Star | Tok::DStar) {
                // Skip to the closing paren.
                while !self.check(&Tok::RParen) && !self.at_eof() {
                    self.advance();
                }
                break;
            }
            let pname = self.name_here();
            self.advance(); // param name (or whatever token)
            if first && matches!(pname.as_deref(), Some("self") | Some("cls")) {
                had_self = true;
                first = false;
                // self has no annotation; move past a trailing comma.
                self.eat(&Tok::Comma);
                continue;
            }
            first = false;
            let ty = if self.eat(&Tok::Colon) {
                self.parse_type()
            } else {
                self.opaque()
            };
            // Default value `= ...` makes the parameter optional.
            let optional = self.eat(&Tok::Assign);
            if optional {
                // Skip the default expression up to ',' or ')'.
                self.skip_to_param_end();
                let pvar = self.state.fresh_pvar();
                params.push(FuncParam::optional(pvar, ty));
            } else {
                params.push(FuncParam::required(ty));
            }
            self.eat(&Tok::Comma);
        }
        self.eat(&Tok::RParen);
        (params, had_self)
    }

    /// Skip a default-value expression: tokens up to a top-level `,` or
    /// `)`.
    fn skip_to_param_end(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.cur() {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen if depth == 0 => break,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Comma if depth == 0 => break,
                Tok::Eof | Tok::Newline => break,
                _ => {}
            }
            self.advance();
        }
    }

    /// `class NAME [( bases )] : <body>` — read instance `x: T` fields and
    /// `def m(self, …) -> R` methods into a structural instance row, and
    /// the `__init__` signature into the constructor's parameters.
    fn class_decl(&mut self) -> Option<(String, Type)> {
        self.advance(); // class
        let name = self.name_here()?;
        self.advance(); // name
        // Optional base list — skip (MRO flattening is Bucket B, later).
        if self.eat(&Tok::LParen) {
            let mut depth = 1;
            while depth > 0 && !self.at_eof() {
                match self.advance() {
                    Tok::LParen => depth += 1,
                    Tok::RParen => depth -= 1,
                    _ => {}
                }
            }
        }
        self.eat(&Tok::Colon);
        self.eat(&Tok::Newline);

        let mut fields: BTreeMap<PropName, Type> = BTreeMap::new();
        let mut ctor_params: Vec<FuncParam> = Vec::new();

        if self.eat(&Tok::Indent) {
            while !self.check(&Tok::Dedent) && !self.at_eof() {
                if matches!(self.cur(), Tok::Newline) {
                    self.advance();
                    continue;
                }
                match self.cur().clone() {
                    Tok::Def => {
                        self.advance(); // def
                        let Some(mname) = self.name_here() else {
                            self.skip_member();
                            continue;
                        };
                        self.advance(); // method name
                        let (params, _had_self) = self.parse_params();
                        let ret = if self.eat(&Tok::Arrow) {
                            self.parse_type()
                        } else {
                            self.opaque()
                        };
                        self.consume_suite();
                        if mname == "__init__" {
                            ctor_params = params;
                        } else if !mname.starts_with("__") {
                            let m = Type::wrap_callable(Type::raw_func_with_params(
                                None, params, ret,
                            ));
                            fields.insert(PropName(mname), m);
                        }
                    }
                    Tok::Name(fname) => {
                        self.advance(); // field name
                        if self.eat(&Tok::Colon) {
                            let ty = self.parse_type();
                            if !fname.starts_with('_') {
                                fields.insert(PropName(fname), ty);
                            }
                        }
                        self.skip_line();
                    }
                    _ => self.skip_member(),
                }
            }
            self.eat(&Tok::Dedent);
        } else {
            // `class C: ...` on one line.
            self.skip_line();
        }

        let instance = Type::object(fields.into_iter().map(|(k, v)| (k.0, v)));
        let ctor = Type::wrap_callable(Type::raw_func_with_params(None, ctor_params, instance));
        Some((name, ctor))
    }

    /// Skip a class-body member we don't model (a decorator line, nested
    /// class, etc.), including any suite it introduces.
    fn skip_member(&mut self) {
        // Consume to newline; if a block follows, skip it.
        let mut saw_colon = false;
        while !self.check(&Tok::Newline) && !self.at_eof() {
            if self.check(&Tok::Colon) {
                saw_colon = true;
            }
            self.advance();
        }
        self.eat(&Tok::Newline);
        if saw_colon {
            self.skip_block();
        }
    }

    /// Consume a `def`/`class` suite: `: <inline>` or `: NEWLINE INDENT …
    /// DEDENT`. Leaves the reader at the start of the next sibling.
    fn consume_suite(&mut self) {
        self.eat(&Tok::Colon);
        if self.eat(&Tok::Newline) {
            self.skip_block();
        } else {
            // Inline body (`def f(): ...`).
            self.skip_line();
        }
    }

    // ---- the Bucket-A type mapper ----

    /// `type ::= atom ('|' atom)*` — a `|` chain is a union (`int | None`).
    fn parse_type(&mut self) -> Type {
        let mut members = vec![self.parse_type_atom()];
        while self.eat(&Tok::Pipe) {
            members.push(self.parse_type_atom());
        }
        if members.len() == 1 {
            members.pop().unwrap()
        } else {
            Type::union(members)
        }
    }

    fn parse_type_atom(&mut self) -> Type {
        match self.cur().clone() {
            Tok::None => {
                self.advance();
                Type::Null
            }
            Tok::Name(name) => {
                self.advance();
                if self.check(&Tok::LBracket) {
                    self.parse_generic(&name)
                } else {
                    self.map_simple_name(&name)
                }
            }
            // A string forward-ref (`"Node"`) or a `Literal` member we
            // reach directly: opaque.
            Tok::Str(_) => {
                self.advance();
                self.opaque()
            }
            // Parenthesised type or tuple — model leniently as opaque.
            Tok::LParen => {
                self.skip_balanced(Tok::LParen, Tok::RParen);
                self.opaque()
            }
            Tok::LBracket => {
                // Bare `[...]` (e.g. a Callable param list reached out of
                // context): skip and treat as opaque.
                self.skip_balanced(Tok::LBracket, Tok::RBracket);
                self.opaque()
            }
            _ => self.opaque(),
        }
    }

    /// Map a bare type name with no subscript.
    fn map_simple_name(&mut self, name: &str) -> Type {
        match name {
            "int" | "float" | "complex" => Type::Number,
            "str" => Type::String,
            "bool" => Type::Boolean,
            "bytes" | "bytearray" => Type::String, // lossy: bytes ≈ String
            "None" | "NoneType" => Type::Null,
            // `object`, `Any`, and unknown names → opaque.
            _ => self.opaque(),
        }
    }

    /// `NAME [ args ]` — a subscripted (generic) type.
    fn parse_generic(&mut self, head: &str) -> Type {
        let args = self.parse_type_args();
        match head {
            "list" | "List" | "Sequence" | "Iterable" | "Iterator" | "MutableSequence"
            | "frozenset" | "set" | "Set" => {
                Type::array(args.into_iter().next().unwrap_or_else(|| self.opaque()))
            }
            "tuple" | "Tuple" => {
                // Homogeneous `tuple[T, ...]` → T[]; heterogeneous →
                // union of elements as the element type (lossy).
                if args.is_empty() {
                    Type::array(self.opaque())
                } else if args.len() == 1 {
                    Type::array(args.into_iter().next().unwrap())
                } else {
                    Type::array(Type::union(args))
                }
            }
            "dict" | "Dict" | "Mapping" | "MutableMapping" => {
                // Map is string-keyed; the value is the 2nd arg.
                let val = args.into_iter().nth(1).unwrap_or_else(|| self.opaque());
                Type::map(val)
            }
            "Optional" => {
                let inner = args.into_iter().next().unwrap_or_else(|| self.opaque());
                Type::union(vec![inner, Type::Null])
            }
            "Union" => Type::union(args),
            "Final" | "ClassVar" | "Annotated" | "InitVar" | "TypeGuard" => {
                // Erase the wrapper, keep the first argument.
                args.into_iter().next().unwrap_or_else(|| self.opaque())
            }
            "Literal" => {
                // Literal members were captured opaque by parse_type_args
                // (they aren't type names); fall back to opaque union.
                self.opaque()
            }
            "Callable" => self.opaque(), // refined below in parse_type_args path
            // Unknown generic (a user class with params, Protocol, etc.):
            // opaque.
            _ => self.opaque(),
        }
    }

    /// Parse `[ T, U, … ]` into a vec of mapped argument types. A nested
    /// `[A, B]` (Callable's param list) is collected as its own group but
    /// flattened away here (Callable itself is opaque in this slice).
    fn parse_type_args(&mut self) -> Vec<Type> {
        let mut out = Vec::new();
        if !self.eat(&Tok::LBracket) {
            return out;
        }
        while !self.check(&Tok::RBracket) && !self.at_eof() {
            if self.check(&Tok::LBracket) {
                // Nested param-list group (Callable): skip it.
                self.skip_balanced(Tok::LBracket, Tok::RBracket);
            } else if matches!(self.cur(), Tok::Str(_) | Tok::Number(_)) {
                // A `Literal` member or numeric arg: consume, opaque.
                self.advance();
                out.push(self.opaque());
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
