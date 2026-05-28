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

use std::collections::{BTreeMap, HashMap, HashSet};

use super::lexer::{tokenize, Tok};
use crate::error::Result;
use crate::infer::InferState;
use crate::span::Spanned;
use crate::types::{FuncParam, PropName, RowType, TVarName, Type, TypeDef, TypeScheme, CALLABLE_KEY};

/// The result of reading a `.pyi`: directly-declared exports plus the
/// re-export requests (`from X import …`) the caller must resolve and
/// merge (the reader has no path/resolver context).
pub struct StubModule {
    pub exports: Vec<(String, TypeScheme)>,
    pub reexports: Vec<ReExport>,
}

/// A `from SOURCE import …` line encountered in a stub. `source` keeps
/// any leading dots (relative imports).
pub struct ReExport {
    pub source: String,
    pub names: ReExportNames,
}

pub enum ReExportNames {
    /// `from SOURCE import *`
    Star,
    /// `from SOURCE import a, b as c` — `(imported, local)` pairs.
    Named(Vec<(String, String)>),
}

/// Parse `source` as a `.pyi` stub. Fresh type variables are drawn from
/// `state` so they don't collide with the importing program's.
pub fn read_stub(state: &mut InferState, source: &str) -> Result<StubModule> {
    let toks = tokenize(source)?;
    let mut reader = StubReader {
        toks,
        pos: 0,
        state,
        reexports: Vec::new(),
        type_vars: HashSet::new(),
        scope: HashMap::new(),
        env: crate::infer::TypeEnv::empty(),
    };
    let exports = reader.module();
    Ok(StubModule {
        exports,
        reexports: reader.reexports,
    })
}

struct StubReader<'a> {
    toks: Vec<Spanned<Tok>>,
    pos: usize,
    state: &'a mut InferState,
    reexports: Vec<ReExport>,
    /// Names declared as type variables (`T = TypeVar("T")`), so a bare
    /// `T` in a later type expression lowers to a shareable variable
    /// rather than opaque.
    type_vars: HashSet<String>,
    /// Type-variable scope for the declaration currently being read. Reset
    /// per top-level declaration (see `module`), so a class body shares
    /// its type vars (they become the class's brand parameters) and each
    /// generic `def` shares across its own signature.
    scope: HashMap<String, Type>,
    /// Accumulated bindings for declarations read so far, so a class
    /// referenced by a later declaration's annotation (`def run() ->
    /// CompletedProcess`) resolves to the class's brand within the stub.
    env: crate::infer::TypeEnv,
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
        let pvars: Vec<_> = ty
            .free_pvars()
            .into_iter()
            .filter(|p| p.is_flex())
            .collect();
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
            // Each top-level declaration gets a fresh type-var scope: a
            // class body shares one scope across all its fields/methods,
            // and a generic `def` shares across its own signature.
            self.scope.clear();
            if let Some((name, ty)) = self.top_decl() {
                let scheme = Self::scheme_of(&ty);
                // Make this declaration visible to later declarations'
                // annotations (e.g. a class referenced by a `def`'s return
                // type further down the stub).
                self.env = self.env.extend(name.clone(), scheme.clone());
                out.push((name, scheme));
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
            Tok::At => {
                let decos = self.read_decorators();
                self.decorated_decl(&decos)
            }
            Tok::Def => self.def_decl(&[]),
            Tok::Class => self.class_decl(),
            Tok::From => {
                self.read_reexport();
                None
            }
            Tok::Name(_) => self.name_decl(),
            // `import …`, `if` version guards, docstrings, etc.: skip.
            _ => {
                self.skip_line();
                None
            }
        }
    }

    /// Collect a run of `@decorator` lines, returning the decorator head
    /// names (e.g. `["overload"]`, `["property"]`). Call arguments and
    /// dotted prefixes are ignored — only the final name matters for the
    /// handful of decorators we model.
    fn read_decorators(&mut self) -> Vec<String> {
        let mut decos = Vec::new();
        while self.eat(&Tok::At) {
            // The decorator's head name is the last `Name` before `(` or
            // newline (so `abc.abstractmethod` → "abstractmethod").
            let mut last = None;
            while !self.check(&Tok::Newline) && !self.check(&Tok::LParen) && !self.at_eof() {
                if let Tok::Name(n) = self.cur() {
                    last = Some(n.clone());
                }
                self.advance();
            }
            if let Some(n) = last {
                decos.push(n);
            }
            self.skip_line();
            while self.check(&Tok::Newline) {
                self.advance();
            }
        }
        decos
    }

    /// Read the declaration following a decorator run, applying the
    /// modelled decorators (`@overload` → opaque, others fall through).
    fn decorated_decl(&mut self, decos: &[String]) -> Option<(String, Type)> {
        match self.cur().clone() {
            Tok::Def => {
                if decos.iter().any(|d| d == "overload") {
                    // Overloaded signature: inty has no intersection
                    // types, so export the name opaque (see §5.3).
                    let (name, _) = self.read_def_signature();
                    return name.map(|n| (n, self.opaque()));
                }
                self.def_decl(decos)
            }
            Tok::Class => self.class_decl(),
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
            // `T = TypeVar("T")` (also `ParamSpec`/`TypeVarTuple`, possibly
            // dotted like `typing.TypeVar`) declares a *type variable*, not
            // a value: register the name so later type expressions tie its
            // occurrences together, and don't export it as a binding.
            if matches!(self.cur(), Tok::Name(_)) {
                let head = self.dotted_name();
                let last = head.rsplit('.').next().unwrap_or(&head);
                if matches!(last, "TypeVar" | "ParamSpec" | "TypeVarTuple") {
                    self.type_vars.insert(name);
                    self.skip_line();
                    return None;
                }
            }
            // Otherwise `Name = value` is a TypeAlias or constant; we don't
            // distinguish yet, so export it opaque.
            let ty = self.opaque();
            self.skip_line();
            return Some((name, ty));
        }
        self.skip_line();
        None
    }

    /// `def NAME ( params ) [-> RET] : <body>`
    fn def_decl(&mut self, _decos: &[String]) -> Option<(String, Type)> {
        let (name, ty) = self.read_def_signature();
        name.map(|n| (n, ty))
    }

    /// Parse a `def` header into `(name, function-type)`, consuming the
    /// body. Shared by module-level and (decorator-stripped) class
    /// methods.
    fn read_def_signature(&mut self) -> (Option<String>, Type) {
        self.advance(); // def
        let name = self.name_here();
        if name.is_some() {
            self.advance(); // name
        }
        let (params, _had_self) = self.parse_params();
        let ret = if self.eat(&Tok::Arrow) {
            self.parse_type()
        } else {
            self.opaque()
        };
        self.consume_suite();
        let func = Type::wrap_callable(Type::raw_func_with_params(None, params, ret));
        (name, func)
    }

    /// `from SOURCE import (* | a [as b], …)` — record a re-export for the
    /// caller to resolve. `import …` lines are intentionally not recorded
    /// (those bind a module for internal stub use, not a public name).
    fn read_reexport(&mut self) {
        self.advance(); // from
        let mut source = String::new();
        while self.check(&Tok::Dot) {
            source.push('.');
            self.advance();
        }
        if matches!(self.cur(), Tok::Name(_)) {
            source.push_str(&self.dotted_name());
        }
        if !self.eat(&Tok::Import) {
            self.skip_line();
            return;
        }
        if self.eat(&Tok::Star) {
            self.skip_line();
            self.reexports.push(ReExport {
                source,
                names: ReExportNames::Star,
            });
            return;
        }
        let parens = self.eat(&Tok::LParen);
        let mut names = Vec::new();
        loop {
            let Some(imported) = self.name_here() else {
                break;
            };
            self.advance();
            let local = if self.eat(&Tok::As) {
                match self.name_here() {
                    Some(n) => {
                        self.advance();
                        n
                    }
                    None => imported.clone(),
                }
            } else {
                imported.clone()
            };
            names.push((imported, local));
            if !self.eat(&Tok::Comma) {
                break;
            }
            if parens && self.check(&Tok::RParen) {
                break;
            }
        }
        if parens {
            self.eat(&Tok::RParen);
        }
        self.skip_line();
        self.reexports.push(ReExport {
            source,
            names: ReExportNames::Named(names),
        });
    }

    /// Parse `NAME ('.' NAME)*`, joined with dots.
    fn dotted_name(&mut self) -> String {
        let mut parts = Vec::new();
        if let Some(n) = self.name_here() {
            parts.push(n);
            self.advance();
        }
        while self.check(&Tok::Dot) {
            self.advance();
            match self.name_here() {
                Some(n) => {
                    parts.push(n);
                    self.advance();
                }
                None => break,
            }
        }
        parts.join(".")
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
            // `/` is the positional-only marker — not a parameter; skip
            // it (and a following comma) and continue.
            if self.check(&Tok::Slash) {
                self.advance();
                self.eat(&Tok::Comma);
                continue;
            }
            // `*args` / `**kwargs` / bare `*`: stop modelling further
            // params (variadics / keyword-only are Bucket C).
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
            }
            let mut fp = if optional {
                FuncParam::optional(self.state.fresh_pvar(), ty)
            } else {
                FuncParam::required(ty)
            };
            if let Some(n) = &pname {
                fp = fp.with_name(n.clone());
            }
            params.push(fp);
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
        let mut static_fields: BTreeMap<PropName, Type> = BTreeMap::new();
        let mut ctor_params: Vec<FuncParam> = Vec::new();

        if self.eat(&Tok::Indent) {
            while !self.check(&Tok::Dedent) && !self.at_eof() {
                if matches!(self.cur(), Tok::Newline) {
                    self.advance();
                    continue;
                }
                match self.cur().clone() {
                    Tok::At => {
                        let decos = self.read_decorators();
                        if self.check(&Tok::Def) {
                            self.read_method(
                                &decos,
                                &mut fields,
                                &mut static_fields,
                                &mut ctor_params,
                            );
                        } else {
                            self.skip_member();
                        }
                    }
                    Tok::Def => {
                        self.read_method(
                            &[],
                            &mut fields,
                            &mut static_fields,
                            &mut ctor_params,
                        );
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

        // Brand the instance row nominally so an imported stub class has a
        // distinct identity — two stub classes of identical shape no longer
        // interchange, mirroring source-class branding (PR #33,
        // `brand_class_factory`). Free flex vars of the instance row become
        // the brand's parameters, so `scheme_of` generalises the ctor and
        // each call mints a fresh instantiation. For a generic class these
        // are the declared `TypeVar`s, shared across the body via
        // `self.scope`, so `class Box(Generic[T])` brands as `Box<T>` with
        // its `T`-typed members tied together. Field/method access sees
        // *through* the brand to this representation; only identity is
        // opaque. See `docs/pyi-import-mapping.md` §4.1/§5.1/§8.
        let mut brand_vars: Vec<TVarName> = instance
            .free_vars()
            .into_iter()
            .filter(|v| v.is_flex())
            .collect();
        brand_vars.sort_by_key(|v| v.id());

        let id = self.state.fresh_type_id();
        self.state.register_named_type(TypeDef::nominal(
            id,
            name.clone(),
            brand_vars.clone(),
            instance,
        ));
        self.state.class_brand_ids.insert(name.clone(), id);

        let args: Vec<Type> = brand_vars.iter().map(|v| Type::var(v.clone())).collect();
        let branded = Type::Named(id, args);
        let func = Type::raw_func_with_params(None, ctor_params, branded);
        let ctor = if static_fields.is_empty() {
            Type::wrap_callable(func)
        } else {
            // Class with `@classmethod` / `@staticmethod` members: the
            // constructor is a callable row that ALSO carries those as
            // accessible properties (`Cls.method` reads them).
            let mut props = static_fields;
            props.insert(PropName(CALLABLE_KEY.to_string()), func);
            Type::Row(RowType::closed(props))
        };
        Some((name, ctor))
    }

    /// Read one `def` class member into either the constructor params
    /// (`__init__`) or an instance-row field, applying modelled
    /// decorators: `@property`/`@cached_property` make the member a field
    /// of its return type (§4.8); `@overload` makes it opaque (§5.3);
    /// `@classmethod`/`@staticmethod` route the member into the
    /// constructor's static slot so `Cls.m(...)` resolves (§4.7).
    /// Dunder methods other than `__init__` are dropped.
    fn read_method(
        &mut self,
        decos: &[String],
        fields: &mut BTreeMap<PropName, Type>,
        static_fields: &mut BTreeMap<PropName, Type>,
        ctor_params: &mut Vec<FuncParam>,
    ) {
        self.advance(); // def
        let Some(mname) = self.name_here() else {
            self.skip_member();
            return;
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
            *ctor_params = params;
            return;
        }
        if mname.starts_with("__") {
            return;
        }
        let is_property = decos
            .iter()
            .any(|d| d == "property" || d == "cached_property");
        let is_overload = decos.iter().any(|d| d == "overload");
        let is_static = decos
            .iter()
            .any(|d| d == "classmethod" || d == "staticmethod");
        let value = if is_property {
            ret
        } else if is_overload {
            self.opaque()
        } else {
            Type::wrap_callable(Type::raw_func_with_params(None, params, ret))
        };
        if is_static {
            static_fields.insert(PropName(mname), value);
        } else {
            fields.insert(PropName(mname), value);
        }
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

    // ---- type expressions ----

    /// Parse a Python type expression into the shared [`TypeAst`] IR
    /// (via [`super::type_expr`]) and lower it to a `Type`. Declared type
    /// variables (`self.type_vars`) parse to [`TypeAst::Var`] and are
    /// resolved through `self.scope`, so occurrences of the same name
    /// within one declaration share a variable; opaque/unknown nodes mint
    /// fresh variables here.
    fn parse_type(&mut self) -> Type {
        let (ast, new_pos) =
            super::type_expr::parse_type_with_vars(&self.toks, self.pos, &self.type_vars);
        self.pos = new_pos;
        // Lower with the stub's accumulated env in scope so a reference to
        // a class declared earlier in the stub resolves to its brand.
        self.state
            .lower_type_ast_scoped_in_env(&ast, &mut self.scope, &self.env)
    }
}
