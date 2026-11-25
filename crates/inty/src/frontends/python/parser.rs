//! Recursive-descent parser for the Python subset.
//!
//! Lowers Python surface syntax onto the shared [`crate::ast`]. Python has
//! no `var`/`local`, so a bare-name assignment is also a declaration: the
//! parser tracks declared names per function scope and lowers the *first*
//! assignment to a hoisted `var` (which inty scopes to the function, like
//! Python), and later assignments to a plain assignment. Constructs the
//! type system can't express are rejected with `ParseError::Unsupported`.

use std::collections::HashSet;

use super::lexer::{tokenize, AugOp, Tok, TypeComment};
use crate::ast::*;
use crate::error::{ParseError, Result};
use crate::span::{Span, Spanned};
use crate::types::TypeAst;

/// Name bookkeeping for one function scope (the module is the outermost
/// such scope). Python binds a name to the *innermost* scope that assigns
/// it, so we track each scope's own bindings separately rather than
/// flattening across the stack.
#[derive(Default)]
struct Scope {
    /// Names bound locally in this scope (assignments, `for`/`with`
    /// targets, parameters). Drives declaration-vs-assignment.
    locals: HashSet<String>,
    /// Names this scope declared `global`: assignments to them rebind the
    /// module-level variable instead of creating a local.
    globals: HashSet<String>,
}

/// A call's positional and keyword arguments.
type CallArgs = (Vec<Expr>, Vec<(String, Expr)>);

pub struct Parser {
    toks: Vec<Spanned<Tok>>,
    pos: usize,
    temp: usize,
    /// One [`Scope`] per enclosing function scope (module is the
    /// outermost). Used to decide declaration-vs-assignment and to resolve
    /// `global`.
    scopes: Vec<Scope>,
    /// Name of the receiver parameter (`self`) while parsing a method
    /// body. When set, references to that name lower to `Expr::This`, so
    /// Python's explicit `self` maps onto inty's `this` row-polymorphism.
    self_name: Option<String>,
    /// Names of the factory functions that `class` declarations lowered
    /// to, in declaration order. Surfaced on `Program::class_brands` so
    /// inference brands each one's inferred instance row nominally.
    class_names: Vec<String>,
    /// Type aliases collected from `type X = …` / `X: TypeAlias = …` /
    /// `X = Literal[…]`, surfaced on `Program::type_aliases`.
    type_aliases: Vec<TypeAlias>,
    /// Names mentioned in a `global` statement anywhere in the program.
    /// At the end of parsing, any of these that never received a
    /// module-level binding get a synthetic module-scope `var` so the
    /// in-function assignments that target them resolve to a real
    /// (module-scoped) declaration. See [`Self::global_stmt`].
    globals: HashSet<String>,
    /// Parsing the Starlark dialect: the Python subset minus what
    /// Starlark leaves out (classes, exceptions, `while`, `import`, …),
    /// plus `load()`, and Starlark's static rules (no top-level `if`/
    /// `for`, globals bound once, no recursion). See
    /// [`crate::frontends::starlark`].
    starlark: bool,
    /// Starlark: the module-level `def` whose body is being parsed.
    top_def: Option<String>,
    /// Starlark: every module-level `def`, with its name's span, in order.
    top_defs: Vec<(String, Span)>,
    /// Starlark: `(caller, callee, span)` for each call, inside a
    /// module-level `def`, of a name that no enclosing function binds.
    /// Feeds the recursion check in [`Self::parse_program`].
    top_calls: Vec<(String, String, Span)>,
    /// The file's PEP 484 type comments (`# type: T`), in source order;
    /// see [`Self::type_comment_between`].
    type_comments: Vec<TypeComment>,
}

impl Parser {
    pub fn new(toks: Vec<Spanned<Tok>>) -> Self {
        Parser {
            toks,
            pos: 0,
            temp: 0,
            scopes: vec![Scope::default()],
            self_name: None,
            class_names: Vec::new(),
            type_aliases: Vec::new(),
            globals: HashSet::new(),
            starlark: false,
            top_def: None,
            top_defs: Vec::new(),
            top_calls: Vec::new(),
            type_comments: Vec::new(),
        }
    }

    /// Attach the file's type comments (from
    /// [`super::lexer::tokenize_with_type_comments`]).
    pub fn with_type_comments(mut self, comments: Vec<TypeComment>) -> Self {
        self.type_comments = comments;
        self
    }

    /// The type comment that starts in `[from, to)`, if any.
    fn type_comment_between(&self, from: usize, to: usize) -> Option<TypeComment> {
        self.type_comments
            .iter()
            .find(|c| c.offset >= from && c.offset < to)
            .cloned()
    }

    /// Tokenize a type comment's text, with spans placed in the file.
    fn comment_tokens(c: &TypeComment) -> Result<Vec<Spanned<Tok>>> {
        Ok(tokenize(&c.text)?
            .into_iter()
            .map(|t| {
                let span = Span::new(t.span.start + c.offset, t.span.end + c.offset);
                Spanned::new(t.value, span)
            })
            .collect())
    }

    /// The type a variable's type comment states (`x = [] # type: list[str]`).
    fn comment_type(c: &TypeComment) -> Result<TypeAst> {
        let toks = Self::comment_tokens(c)?;
        let mut p = Parser::new(toks);
        let ty = p.parse_type_ast();
        p.end_of_comment()?;
        Ok(ty)
    }

    /// The signature a function's type comment states, PEP 484's
    /// `(T1, T2) -> R`: the parameter types (`None` for `(...) -> R`,
    /// which states only the return type) and the return type.
    fn comment_signature(c: &TypeComment) -> Result<(Option<Vec<TypeAst>>, TypeAst)> {
        let toks = Self::comment_tokens(c)?;
        let mut p = Parser::new(toks);
        p.expect(
            &Tok::LParen,
            "'(' starting a signature type comment `(T, …) -> R`",
        )?;
        let params = if p.check(&Tok::Dot) {
            for _ in 0..3 {
                p.expect(&Tok::Dot, "'...'")?;
            }
            p.expect(&Tok::RParen, "')'")?;
            None
        } else {
            let mut params = Vec::new();
            while !p.eat(&Tok::RParen) {
                params.push(p.parse_type_ast());
                if !p.eat(&Tok::Comma) {
                    p.expect(&Tok::RParen, "')'")?;
                    break;
                }
            }
            Some(params)
        };
        p.expect(&Tok::Arrow, "'->' and the return type")?;
        let ret = p.parse_type_ast();
        p.end_of_comment()?;
        Ok((params, ret))
    }

    /// Require that a type comment's tokens are all consumed.
    fn end_of_comment(&mut self) -> Result<()> {
        self.eat(&Tok::Newline);
        if self.at_eof() {
            Ok(())
        } else {
            Err(self.unexpected("the end of the type comment"))
        }
    }

    /// A parser for the Starlark dialect (see the `starlark` field).
    pub fn new_starlark(toks: Vec<Spanned<Tok>>) -> Self {
        Parser {
            starlark: true,
            ..Parser::new(toks)
        }
    }

    /// The error for a construct Starlark leaves out of Python, with a
    /// hint at what to write instead (empty for none).
    fn not_starlark(&self, what: &str, instead: &str) -> crate::error::IntyError {
        if instead.is_empty() {
            self.unsupported(&format!("{what} is not part of Starlark"))
        } else {
            self.unsupported(&format!("{what} is not part of Starlark; {instead}"))
        }
    }

    /// Whether `name` is bound by an enclosing function (not the module):
    /// a call or a read of it then means that binding, not the module-level
    /// function or builtin of the same name.
    fn bound_in_function(&self, name: &str) -> bool {
        self.scopes[1..].iter().any(|s| s.locals.contains(name))
    }

    /// Whether `name` means the Starlark builtin of that name: nothing in
    /// the file binds it.
    fn is_builtin(&self, name: &str) -> bool {
        !self.scopes.iter().any(|s| s.locals.contains(name))
    }

    /// Look at the token `n` positions ahead (saturating at the trailing
    /// `Eof`), without consuming.
    fn peek_tok(&self, n: usize) -> &Tok {
        let i = (self.pos + n).min(self.toks.len().saturating_sub(1));
        &self.toks[i].value
    }

    // ---- token helpers ----

    fn cur(&self) -> &Tok {
        &self.toks[self.pos].value
    }

    fn cur_span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
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

    fn expect(&mut self, t: &Tok, what: &str) -> Result<()> {
        if self.check(t) {
            self.advance();
            Ok(())
        } else {
            Err(self.unexpected(what))
        }
    }

    fn unexpected(&self, expected: &str) -> crate::error::IntyError {
        ParseError::UnexpectedToken {
            found: self.cur().describe(),
            expected: expected.to_string(),
            span: self.cur_span(),
        }
        .into()
    }

    fn unsupported(&self, feature: &str) -> crate::error::IntyError {
        ParseError::Unsupported {
            feature: feature.to_string(),
            span: self.cur_span(),
        }
        .into()
    }

    fn expect_name(&mut self, what: &str) -> Result<String> {
        match self.cur().clone() {
            Tok::Name(n) => {
                self.advance();
                Ok(n)
            }
            _ => Err(self.unexpected(what)),
        }
    }

    fn fresh_temp(&mut self) -> String {
        let n = self.temp;
        self.temp += 1;
        format!("$py${}", n)
    }

    // ---- scope helpers ----

    /// Whether `name` is already bound in the *current* (innermost) scope.
    /// Python scoping is not flattened across the stack: a name bound in an
    /// enclosing scope is still a fresh local here once we assign to it, so
    /// we only consult the top scope.
    fn local_declared(&self, name: &str) -> bool {
        self.scopes.last().unwrap().locals.contains(name)
    }

    /// Whether the current scope declared `name` with a `global` statement.
    fn is_global(&self, name: &str) -> bool {
        self.scopes.last().unwrap().globals.contains(name)
    }

    /// Whether we are parsing inside a function/method body (i.e. not at
    /// module scope), where the local-by-default binding rule applies.
    fn in_function(&self) -> bool {
        self.scopes.len() > 1
    }

    fn declare(&mut self, name: &str) {
        self.scopes
            .last_mut()
            .unwrap()
            .locals
            .insert(name.to_string());
    }

    /// Record `name` as `global` in the current scope, and globally so
    /// [`Self::parse_program`] can backfill a module binding if needed.
    fn declare_global(&mut self, name: &str) {
        self.scopes
            .last_mut()
            .unwrap()
            .globals
            .insert(name.to_string());
        self.globals.insert(name.to_string());
    }

    // ---- program / suites ----

    pub fn parse_program(&mut self) -> Result<Program> {
        let start = self.cur_span().start;
        let mut statements = Vec::new();
        while !self.at_eof() {
            if self.eat(&Tok::Newline) {
                continue;
            }
            statements.extend(self.statement()?);
        }
        if self.starlark {
            self.check_no_recursion()?;
        }
        // Backfill a module-scope `var` for every `global` name that never
        // received a module-level binding (e.g. one only ever assigned from
        // inside a function). Without it, those in-function assignments
        // would reference an undeclared name. Module `var`s are hoisted by
        // the checker, so the leading position is fine.
        let span = Span::new(start, self.prev_span().end);
        let mut backfill: Vec<Stmt> = self
            .globals
            .iter()
            .filter(|name| !self.scopes[0].locals.contains(*name))
            .map(|name| Stmt::Var {
                kind: VarKind::Var,
                declarations: vec![VarDeclarator {
                    name: name.clone(),
                    init: None,
                    type_annotation: None,
                    type_ast: None,
                    kind: VarKind::Var,
                    span,
                }],
                span,
            })
            .collect();
        // Deterministic order (HashSet iteration is not stable).
        backfill.sort_by(|a, b| match (a, b) {
            (
                Stmt::Var {
                    declarations: da, ..
                },
                Stmt::Var {
                    declarations: db, ..
                },
            ) => da[0].name.cmp(&db[0].name),
            _ => std::cmp::Ordering::Equal,
        });
        backfill.extend(statements);
        let statements = backfill;
        Ok(Program {
            statements,
            span: Span::new(start, self.prev_span().end),
            type_aliases: std::mem::take(&mut self.type_aliases),
            class_brands: std::mem::take(&mut self.class_names),
            class_decls: Vec::new(),
            language: if self.starlark {
                crate::ast::SourceLanguage::Starlark
            } else {
                crate::ast::SourceLanguage::Python
            },
        })
    }

    /// A `:`-introduced suite: either an inline simple line, or a
    /// NEWLINE INDENT block DEDENT. The caller has already consumed the
    /// `:`.
    fn suite(&mut self) -> Result<Box<Stmt>> {
        let start = self.cur_span().start;
        let body = if self.check(&Tok::Newline) {
            self.advance();
            self.expect(&Tok::Indent, "an indented block")?;
            let mut body = Vec::new();
            while !self.check(&Tok::Dedent) && !self.at_eof() {
                if self.eat(&Tok::Newline) {
                    continue;
                }
                body.extend(self.statement()?);
            }
            self.expect(&Tok::Dedent, "dedent")?;
            body
        } else {
            self.simple_line()?
        };
        Ok(Box::new(Stmt::Block {
            body,
            span: Span::new(start, self.prev_span().end),
        }))
    }

    /// A suite's statements, unwrapped from the `Block` that [`Self::suite`]
    /// produces. Used where a compound statement wants to splice a suite's
    /// declarations into its own scope rather than nest a fresh one.
    fn suite_body(&mut self) -> Result<Vec<Stmt>> {
        match *self.suite()? {
            Stmt::Block { body, .. } => Ok(body),
            other => Ok(vec![other]),
        }
    }

    // ---- statements ----

    fn statement(&mut self) -> Result<Vec<Stmt>> {
        if self.starlark {
            if let Some(stmts) = self.starlark_statement()? {
                return Ok(stmts);
            }
        }
        match self.cur() {
            Tok::At => self.decorated_stmt(),
            Tok::Def => Ok(vec![self.def_stmt()?]),
            Tok::Class => Ok(vec![self.class_stmt()?]),
            Tok::Import => self.import_stmt(),
            Tok::From => Ok(vec![self.import_from_stmt()?]),
            Tok::If => Ok(vec![self.if_stmt()?]),
            Tok::While => Ok(vec![self.while_stmt()?]),
            Tok::For => Ok(vec![self.for_stmt()?]),
            Tok::Try => Ok(vec![self.try_stmt()?]),
            Tok::With => self.with_stmt(),
            Tok::Reserved(k) if self.starlark => Err(self.not_starlark(&format!("'{k}'"), "")),
            Tok::Reserved(k) => {
                Err(self.unsupported(&format!("'{}' is not supported in the Python subset", k)))
            }
            _ => self.simple_line(),
        }
    }

    /// `simple_stmt (';' simple_stmt)* NEWLINE`
    fn simple_line(&mut self) -> Result<Vec<Stmt>> {
        let mut stmts = self.simple_stmt()?;
        while self.eat(&Tok::Semi) {
            if self.check(&Tok::Newline) || self.at_eof() {
                break;
            }
            stmts.extend(self.simple_stmt()?);
        }
        if !self.at_eof() {
            self.expect(&Tok::Newline, "newline")?;
        }
        Ok(stmts)
    }

    fn simple_stmt(&mut self) -> Result<Vec<Stmt>> {
        match self.cur() {
            Tok::Pass => {
                let span = self.cur_span();
                self.advance();
                Ok(vec![Stmt::Empty { span }])
            }
            Tok::Break => {
                let span = self.cur_span();
                self.advance();
                Ok(vec![Stmt::Break { label: None, span }])
            }
            Tok::Continue => {
                let span = self.cur_span();
                self.advance();
                Ok(vec![Stmt::Continue { label: None, span }])
            }
            Tok::Return => {
                let start = self.cur_span().start;
                self.advance();
                let argument = if self.check(&Tok::Newline)
                    || self.check(&Tok::Semi)
                    || self.at_eof()
                {
                    None
                } else {
                    let e = self.expr()?;
                    // `return a, b` returns a tuple.
                    if self.check(&Tok::Comma) {
                        let mut elements = vec![e];
                        while self.eat(&Tok::Comma) {
                            if self.check(&Tok::Newline) || self.check(&Tok::Semi) || self.at_eof()
                            {
                                break; // trailing comma
                            }
                            elements.push(self.expr()?);
                        }
                        Some(Expr::Tuple {
                            elements,
                            span: Span::new(start, self.prev_span().end),
                        })
                    } else {
                        Some(e)
                    }
                };
                Ok(vec![Stmt::Return {
                    argument,
                    span: Span::new(start, self.prev_span().end),
                }])
            }
            Tok::Raise if self.starlark => Err(self.not_starlark("'raise'", "call fail()")),
            Tok::Raise => {
                let start = self.cur_span().start;
                self.advance();
                // `raise EXPR` evaluates the exception (so a malformed
                // expression is still type-checked); bare `raise`
                // re-raises and carries no operand. Either way the
                // statement diverges, modelled by `Stmt::Throw`.
                let argument =
                    if self.check(&Tok::Newline) || self.check(&Tok::Semi) || self.at_eof() {
                        let span = Span::new(start, self.prev_span().end);
                        Expr::Lit {
                            value: Literal::Null,
                            span,
                        }
                    } else {
                        let e = self.expr()?;
                        // `raise E from cause` — evaluate and discard the cause.
                        if self.check(&Tok::From) {
                            self.advance();
                            let _ = self.expr()?;
                        }
                        e
                    };
                Ok(vec![Stmt::Throw {
                    argument,
                    span: Span::new(start, self.prev_span().end),
                }])
            }
            Tok::Global if self.starlark => Err(self.not_starlark("'global'", "")),
            Tok::Global => Ok(vec![self.global_stmt()?]),
            Tok::Reserved(k) if self.starlark => Err(self.not_starlark(&format!("'{k}'"), "")),
            Tok::Reserved(k) => {
                Err(self.unsupported(&format!("'{}' is not supported in the Python subset", k)))
            }
            _ => self.expr_or_assign(),
        }
    }

    /// The Starlark-specific statement rules, checked before the Python
    /// dispatch. `Some` when the statement is handled here (`load`), an
    /// error for a statement Starlark leaves out or disallows where it is,
    /// `None` to parse it as Python.
    fn starlark_statement(&mut self) -> Result<Option<Vec<Stmt>>> {
        let top = !self.in_function();
        match self.cur() {
            Tok::Name(n) if n == "load" && matches!(self.peek_tok(1), Tok::LParen) => {
                if !top {
                    return Err(self.unsupported("load() is only allowed at the top level"));
                }
                Ok(Some(vec![self.load_stmt()?]))
            }
            Tok::At => Err(self.not_starlark("a decorator", "")),
            Tok::Class => Err(self.not_starlark("'class'", "use struct() or a dict")),
            Tok::Import | Tok::From => Err(self.not_starlark("'import'", "use load()")),
            Tok::While => Err(self.not_starlark("'while'", "use a for loop")),
            Tok::Try => Err(self.not_starlark("'try'", "report errors with fail()")),
            Tok::With => Err(self.not_starlark("'with'", "")),
            Tok::If | Tok::For if top => {
                let kw = if self.check(&Tok::If) { "if" } else { "for" };
                Err(self.unsupported(&format!(
                    "'{kw}' is not allowed at the top level of a Starlark file; \
                     move it into a function"
                )))
            }
            _ => Ok(None),
        }
    }

    /// `load("label", "name", local = "name", …)` → an import of each
    /// named symbol from the module the label names. The label is kept
    /// verbatim as the import source; [`crate::frontends::starlark`]
    /// resolves it to a file.
    fn load_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // load
        self.advance(); // (
        let source = match self.cur().clone() {
            Tok::Str(label) => {
                self.advance();
                label
            }
            _ => return Err(self.unexpected("a module label string")),
        };
        let mut specifiers = Vec::new();
        while self.eat(&Tok::Comma) {
            if self.check(&Tok::RParen) {
                break; // trailing comma
            }
            let spec_span = self.cur_span();
            let (local, imported) = match self.cur().clone() {
                Tok::Str(name) => {
                    self.advance();
                    (name.clone(), name)
                }
                Tok::Name(local) if matches!(self.peek_tok(1), Tok::Assign) => {
                    self.advance(); // local
                    self.advance(); // =
                    match self.cur().clone() {
                        Tok::Str(name) => {
                            self.advance();
                            (local, name)
                        }
                        _ => return Err(self.unexpected("the loaded symbol's name, a string")),
                    }
                }
                _ => return Err(self.unexpected("a symbol to load: \"name\" or local = \"name\"")),
            };
            if local.starts_with('_') || imported.starts_with('_') {
                return Err(ParseError::Unsupported {
                    feature: format!("'{imported}' is private to its module and cannot be loaded"),
                    span: spec_span,
                }
                .into());
            }
            if self.local_declared(&local) {
                return Err(self.reassigned_global(&local, spec_span));
            }
            self.declare(&local);
            specifiers.push(ImportSpecifier::Named {
                imported,
                local,
                span: spec_span,
            });
        }
        self.expect(&Tok::RParen, "')'")?;
        if specifiers.is_empty() {
            return Err(self.unexpected("at least one symbol to load"));
        }
        if !self.at_eof() {
            self.expect(&Tok::Newline, "newline")?;
        }
        Ok(Stmt::Import {
            specifiers,
            source,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Starlark binds a global once: a second assignment to it (or a
    /// second `def`/`load` of the name) is an error.
    fn reassigned_global(&self, name: &str, span: Span) -> crate::error::IntyError {
        ParseError::Unsupported {
            feature: format!(
                "'{name}' is already bound at the top level; a Starlark global is bound once"
            ),
            span,
        }
        .into()
    }

    /// Starlark forbids recursion. Reject any module-level `def` that can
    /// reach a call of itself through calls of module-level `def`s
    /// (directly, or through others). A call counts when its callee is a
    /// bare name that no enclosing function binds. A function only passed
    /// around, not called, is not followed, so a call through a parameter
    /// isn't seen (Starlark reports that one when it runs).
    fn check_no_recursion(&self) -> Result<()> {
        use std::collections::HashMap;
        let defs: HashMap<&str, Span> = self
            .top_defs
            .iter()
            .map(|(n, sp)| (n.as_str(), *sp))
            .collect();
        let mut edges: HashMap<&str, Vec<(&str, Span)>> = HashMap::new();
        for (caller, callee, span) in &self.top_calls {
            if defs.contains_key(callee.as_str()) {
                edges
                    .entry(caller.as_str())
                    .or_default()
                    .push((callee.as_str(), *span));
            }
        }
        for (name, _) in &self.top_defs {
            // Depth-first search from `name`'s callees, keeping the path.
            let mut stack: Vec<(&str, Vec<&str>, Span)> = edges
                .get(name.as_str())
                .into_iter()
                .flatten()
                .map(|(c, sp)| (*c, vec![name.as_str(), *c], *sp))
                .collect();
            let mut seen = HashSet::new();
            while let Some((cur, path, first_span)) = stack.pop() {
                if cur == name {
                    return Err(ParseError::Unsupported {
                        feature: format!(
                            "recursion is not allowed in Starlark ({})",
                            path.join(" → ")
                        ),
                        span: first_span,
                    }
                    .into());
                }
                if !seen.insert(cur) {
                    continue;
                }
                for (next, _) in edges.get(cur).into_iter().flatten() {
                    let mut p = path.clone();
                    p.push(next);
                    stack.push((next, p, first_span));
                }
            }
        }
        Ok(())
    }

    /// `global NAME (',' NAME)*`.
    ///
    /// `global` declares that the named bindings live at module scope, so
    /// assignments to them inside the current function lower to plain
    /// assignments against the module binding rather than fresh
    /// function-scoped `var`s. We record each name as `global` in the
    /// current scope (so [`Self::declare_or_assign_single`] targets the
    /// module binding) and globally so [`Self::parse_program`] can backfill
    /// a module-level `var` for any global that never receives one
    /// otherwise. The statement itself carries no runtime effect, so it
    /// lowers to an empty statement.
    fn global_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // global
        loop {
            let name = self.expect_name("name after 'global'")?;
            self.declare_global(&name);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(Stmt::Empty {
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Recognise a type-alias statement and, if matched, parse its body as
    /// a *type expression* (so comma-bearing forms like `Literal["a","b"]`
    /// parse) and register it on `type_aliases`. Recognised, unambiguously,
    /// as:
    ///   - `type NAME = <type>`            (PEP 695)
    ///   - `NAME: TypeAlias = <type>`      (PEP 613)
    ///   - `NAME = Head[…]` where `Head` is a typing special form
    ///     (`Literal`, `Optional`, `Union`, …) — always a type, never a
    ///     value, so no ambiguity with ordinary assignment.
    ///
    /// A type alias introduces a *type name*, not a runtime value, so it
    /// lowers to an empty statement.
    fn try_type_alias(&mut self) -> Option<Stmt> {
        let start = self.cur_span().start;
        let name = if matches!(self.cur(), Tok::Name(n) if n == "type")
            && matches!(self.peek_tok(1), Tok::Name(_))
            && matches!(self.peek_tok(2), Tok::Assign)
        {
            self.advance(); // `type`
            let Tok::Name(name) = self.advance() else {
                unreachable!()
            };
            self.advance(); // `=`
            name
        } else if matches!(self.cur(), Tok::Name(_))
            && matches!(self.peek_tok(1), Tok::Colon)
            && matches!(self.peek_tok(2), Tok::Name(n) if n == "TypeAlias")
            && matches!(self.peek_tok(3), Tok::Assign)
        {
            let Tok::Name(name) = self.advance() else {
                unreachable!()
            };
            self.advance(); // `:`
            self.advance(); // `TypeAlias`
            self.advance(); // `=`
            name
        } else if matches!(self.cur(), Tok::Name(_))
            && matches!(self.peek_tok(1), Tok::Assign)
            && matches!(self.peek_tok(2), Tok::Name(h) if is_typing_special_form(h))
            && matches!(self.peek_tok(3), Tok::LBracket)
        {
            let Tok::Name(name) = self.advance() else {
                unreachable!()
            };
            self.advance(); // `=`
            name
        } else {
            return None;
        };

        let body_ast = self.parse_type_ast();
        let span = Span::new(start, self.prev_span().end);
        self.type_aliases.push(TypeAlias {
            name,
            params: Vec::new(),
            body: String::new(),
            body_ast: Some(body_ast),
            span,
            nominal: false,
            content_start: None,
        });
        Some(Stmt::Empty { span })
    }

    fn expr_or_assign(&mut self) -> Result<Vec<Stmt>> {
        if let Some(stmt) = self.try_type_alias() {
            return Ok(vec![stmt]);
        }
        let start = self.cur_span().start;
        let first = self.expr()?;

        // annotated: `target: T [= value]`
        if self.check(&Tok::Colon) {
            self.advance();
            let type_ast = Some(self.parse_type_ast());
            let name = self.as_simple_name(&first)?;
            let init = if self.eat(&Tok::Assign) {
                Some(self.expr()?)
            } else {
                None
            };
            return Ok(vec![self.declare_or_assign_single(
                name,
                init,
                type_ast,
                Span::new(start, self.prev_span().end),
            )?]);
        }

        // augmented: `target op= value`
        if let Tok::AugAssign(op) = self.cur().clone() {
            self.advance();
            let value = self.expr()?;
            if !first.is_valid_assignment_target() {
                return Err(ParseError::InvalidAssignmentTarget { span: first.span() }.into());
            }
            // An augmented assignment reads its target before writing it, so
            // a bare name must already be bound. Inside a function an unbound
            // bare name would otherwise become a fresh local — Python's
            // read-before-assignment trap. Require an explicit `global` to
            // rebind a module-level variable.
            if let Some(name) = self.bare_name(&first) {
                if self.starlark && !self.in_function() {
                    return Err(self.reassigned_global(&name, first.span()));
                }
                if self.in_function() && !self.local_declared(&name) && !self.is_global(&name) {
                    return Err(ParseError::LocalReferencedBeforeAssignment {
                        name,
                        span: first.span(),
                    }
                    .into());
                }
            }
            let span = Span::new(start, self.prev_span().end);
            return Ok(vec![Stmt::Expr {
                expression: Expr::Assign {
                    op: aug_to_assign(op),
                    left: Box::new(first),
                    right: Box::new(value),
                    span,
                },
                span,
            }]);
        }

        // tuple unpacking: `a, b = ...`
        if self.check(&Tok::Comma) {
            let mut targets = vec![first];
            while self.eat(&Tok::Comma) {
                if self.check(&Tok::Assign) {
                    break;
                }
                targets.push(self.expr()?);
            }
            self.expect(&Tok::Assign, "'='")?;
            let values = self.value_list()?;
            return self.lower_tuple_assign(
                targets,
                values,
                Span::new(start, self.prev_span().end),
            );
        }

        // plain / chained assignment: `a = e` or `a = b = e`
        if self.check(&Tok::Assign) {
            let mut targets = vec![first];
            self.advance();
            let mut value = self.expr()?;
            while self.eat(&Tok::Assign) {
                targets.push(value);
                value = self.expr()?;
            }
            // A trailing comma on the final value makes it a tuple:
            // `x = a, b`.
            value = self.finish_tuple_if_comma(value, start)?;
            let span = Span::new(start, self.prev_span().end);
            return Ok(vec![self.lower_chained_assign(targets, value, span)?]);
        }

        // bare expression statement
        let span = first.span();
        // Starlark's `fail(…)` statement stops evaluation: lower it to a
        // `throw` of the call (so its arguments are still checked), which
        // makes the code after it unreachable for narrowing and returns.
        if self.starlark {
            if let Expr::Call { callee, .. } = &first {
                if matches!(&**callee, Expr::Ident { name, .. } if name == "fail" && self.is_builtin("fail"))
                {
                    return Ok(vec![Stmt::Throw {
                        argument: first,
                        span,
                    }]);
                }
            }
        }
        Ok(vec![Stmt::Expr {
            expression: first,
            span,
        }])
    }

    /// Lower `a = b = value` (every target gets `value`). Targets that are
    /// new bare names become declarations.
    fn lower_chained_assign(
        &mut self,
        targets: Vec<Expr>,
        value: Expr,
        span: Span,
    ) -> Result<Stmt> {
        if targets.len() == 1 {
            let t = &targets[0];
            if let Some(name) = self.bare_name(t) {
                // A type comment at the end of the line declares the type:
                // `names = []  # type: list[str]`.
                let type_ast = match self.type_comment_between(span.end, self.cur_span().start) {
                    Some(c) => Some(Self::comment_type(&c)?),
                    None => None,
                };
                return self.declare_or_assign_single(name, Some(value), type_ast, span);
            }
            if !t.is_valid_assignment_target() {
                return Err(ParseError::InvalidAssignmentTarget { span: t.span() }.into());
            }
            return Ok(Stmt::Expr {
                expression: Expr::Assign {
                    op: AssignOp::Assign,
                    left: Box::new(targets.into_iter().next().unwrap()),
                    right: Box::new(value),
                    span,
                },
                span,
            });
        }
        // multiple targets share one value: stash in a temp, then assign.
        let tmp = self.fresh_temp();
        let mut body = vec![Stmt::Var {
            kind: VarKind::Var,
            declarations: vec![VarDeclarator {
                name: tmp.clone(),
                init: Some(value),
                type_annotation: None,
                type_ast: None,
                kind: VarKind::Var,
                span,
            }],
            span,
        }];
        for t in targets {
            body.push(self.assign_target(
                t,
                Expr::Ident {
                    name: tmp.clone(),
                    span,
                },
                span,
            )?);
        }
        Ok(Stmt::Block { body, span })
    }

    /// Lower a tuple assignment into a flat list of statements (no scoping
    /// block, so `var` declarations escape to the enclosing scope like
    /// Python). Handles `a, b = t` (destructure one tuple by indexing) and
    /// `a, b = e1, e2` (matched arity, parallel via temporaries).
    fn lower_tuple_assign(
        &mut self,
        targets: Vec<Expr>,
        mut values: Vec<Expr>,
        span: Span,
    ) -> Result<Vec<Stmt>> {
        // `a, b = t` — destructure a single tuple/sequence value by
        // indexing it: `tmp = t; a = tmp[0]; b = tmp[1]`. Reuses tuple
        // element-access inference, so `a`/`b` get the component types.
        if targets.len() > 1 && values.len() == 1 {
            let mut body = Vec::new();
            let tmp = self.fresh_temp();
            body.push(Stmt::Var {
                kind: VarKind::Var,
                declarations: vec![VarDeclarator {
                    name: tmp.clone(),
                    init: Some(values.pop().unwrap()),
                    type_annotation: None,
                    type_ast: None,
                    kind: VarKind::Var,
                    span,
                }],
                span,
            });
            for (i, target) in targets.into_iter().enumerate() {
                let idx = Expr::ComputedMember {
                    object: Box::new(Expr::Ident {
                        name: tmp.clone(),
                        span,
                    }),
                    property: Box::new(Expr::Lit {
                        value: Literal::Number(i as f64),
                        span,
                    }),
                    span,
                };
                body.push(self.assign_target(target, idx, span)?);
            }
            return Ok(body);
        }

        if targets.len() != values.len() {
            return Err(ParseError::Unsupported {
                feature: "tuple assignment requires equal numbers of targets and values \
                          (starred/unpacking targets are not supported)"
                    .to_string(),
                span,
            }
            .into());
        }
        let mut body = Vec::new();
        let mut temps = Vec::new();
        for v in values {
            let t = self.fresh_temp();
            body.push(Stmt::Var {
                kind: VarKind::Var,
                declarations: vec![VarDeclarator {
                    name: t.clone(),
                    init: Some(v),
                    type_annotation: None,
                    type_ast: None,
                    kind: VarKind::Var,
                    span,
                }],
                span,
            });
            temps.push(t);
        }
        for (target, t) in targets.into_iter().zip(temps) {
            body.push(self.assign_target(target, Expr::Ident { name: t, span }, span)?);
        }
        Ok(body)
    }

    /// Assign `value` to a target, declaring it first if it's a new name.
    fn assign_target(&mut self, target: Expr, value: Expr, span: Span) -> Result<Stmt> {
        if let Some(name) = self.bare_name(&target) {
            // Start the binding at the target's own name: in `a, b = t`
            // every target shares the statement span, and a declaration
            // is located (and its type keyed) by where its span starts.
            let span = Span::new(target.span().start, span.end);
            return self.declare_or_assign_single(name, Some(value), None, span);
        }
        if !target.is_valid_assignment_target() {
            return Err(ParseError::InvalidAssignmentTarget {
                span: target.span(),
            }
            .into());
        }
        Ok(Stmt::Expr {
            expression: Expr::Assign {
                op: AssignOp::Assign,
                left: Box::new(target),
                right: Box::new(value),
                span,
            },
            span,
        })
    }

    /// Lower an assignment to a bare name, applying Python's binding rule.
    ///
    /// - A name declared `global` (or already bound) in the current scope
    ///   becomes a plain assignment — for a global that targets the
    ///   module-level variable, for a local it reassigns it.
    /// - Otherwise this is the name's first binding in this scope, so it
    ///   becomes a fresh function-scoped `var`. In a function that shadows
    ///   any same-named module/enclosing binding, matching Python: a name
    ///   assigned in a function is local unless declared `global`.
    fn declare_or_assign_single(
        &mut self,
        name: String,
        init: Option<Expr>,
        type_ast: Option<TypeAst>,
        span: Span,
    ) -> Result<Stmt> {
        if self.starlark && !self.in_function() && self.local_declared(&name) {
            return Err(self.reassigned_global(&name, span));
        }
        Ok(if self.is_global(&name) || self.local_declared(&name) {
            // already bound (global rebind or local reassignment); a bare
            // annotation with no value is a no-op.
            match init {
                Some(value) => Stmt::Expr {
                    expression: Expr::Assign {
                        op: AssignOp::Assign,
                        left: Box::new(Expr::Ident { name, span }),
                        right: Box::new(value),
                        span,
                    },
                    span,
                },
                None => Stmt::Empty { span },
            }
        } else {
            self.declare(&name);
            Stmt::Var {
                kind: VarKind::Var,
                declarations: vec![VarDeclarator {
                    name,
                    init,
                    type_annotation: None,
                    type_ast,
                    kind: VarKind::Var,
                    span,
                }],
                span,
            }
        })
    }

    fn bare_name(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::Ident { name, .. } => Some(name.clone()),
            _ => None,
        }
    }

    fn as_simple_name(&self, e: &Expr) -> Result<String> {
        self.bare_name(e)
            .ok_or_else(|| ParseError::InvalidAssignmentTarget { span: e.span() }.into())
    }

    fn value_list(&mut self) -> Result<Vec<Expr>> {
        let mut out = vec![self.expr()?];
        while self.eat(&Tok::Comma) {
            out.push(self.expr()?);
        }
        Ok(out)
    }

    /// If a `,` follows `first`, collect `first, …` (to end of statement)
    /// into a tuple literal; otherwise return `first` unchanged. Used for
    /// unparenthesised tuple values like `x = a, b`.
    fn finish_tuple_if_comma(&mut self, first: Expr, start: usize) -> Result<Expr> {
        if !self.check(&Tok::Comma) {
            return Ok(first);
        }
        let mut elements = vec![first];
        while self.eat(&Tok::Comma) {
            if self.check(&Tok::Newline) || self.check(&Tok::Semi) || self.at_eof() {
                break; // trailing comma
            }
            elements.push(self.expr()?);
        }
        Ok(Expr::Tuple {
            elements,
            span: Span::new(start, self.prev_span().end),
        })
    }

    // ---- compound statements ----

    /// One or more `@decorator` lines followed by the `def`/`class` they
    /// decorate. The decorator's *effect* is not modelled (a known
    /// simplification); the lines are consumed so the decorated
    /// declaration parses.
    fn decorated_stmt(&mut self) -> Result<Vec<Stmt>> {
        while self.check(&Tok::At) {
            // Consume `@ <expr>` up to the end of the line.
            while !self.check(&Tok::Newline) && !self.at_eof() {
                self.advance();
            }
            self.eat(&Tok::Newline);
            // Skip blank lines between stacked decorators.
            while self.eat(&Tok::Newline) {}
        }
        self.statement()
    }

    /// Build a `Param` from an optional default expression, applying the
    /// `=None` special case: any default makes the parameter optional,
    /// but only a *non-`None`* default constrains its type. `type_ast`
    /// carries the parameter's declared type, if annotated.
    fn param_from_default(
        name: String,
        span: Span,
        default: Option<Expr>,
        type_ast: Option<TypeAst>,
    ) -> Param {
        let mut param = match default {
            None => Param::new(name, span),
            Some(Expr::Lit {
                value: Literal::Null,
                ..
            }) => Param::optional(name, span),
            Some(expr) => Param::with_default(name, span, expr),
        };
        param.type_ast = type_ast;
        param
    }

    /// Consume a bare `*,` in a parameter list: the marker after which
    /// parameters are keyword-only (`def f(a, *, b)`). The parameters
    /// that follow are lowered as ordinary named parameters, so a call
    /// that passes them by keyword is checked; one that passes them by
    /// position is accepted although Python and Starlark reject it.
    fn eat_keyword_only_marker(&mut self) -> bool {
        if self.check(&Tok::Star) && matches!(self.peek_tok(1), Tok::Comma) {
            self.advance(); // *
            self.advance(); // ,
            true
        } else {
            false
        }
    }

    /// Apply a PEP 484 signature type comment, `# type: (T1, T2) -> R`,
    /// written after a `def` header's `:` (on that line or as the first
    /// line of the body), to the parameters and return type. A type
    /// written inline (`a: T`, `-> R`) takes precedence over the comment.
    fn apply_signature_comment(
        &mut self,
        params: &mut [Param],
        ret: &mut Option<TypeAst>,
    ) -> Result<()> {
        let from = self.prev_span().end;
        // Up to the first token of the body.
        let to = self.toks[self.pos..]
            .iter()
            .find(|t| !matches!(t.value, Tok::Newline | Tok::Indent))
            .map_or(usize::MAX, |t| t.span.start);
        let Some(c) = self.type_comment_between(from, to) else {
            return Ok(());
        };
        let (param_types, ret_type) = Self::comment_signature(&c)?;
        if let Some(types) = param_types {
            if types.len() != params.len() {
                return Err(ParseError::Unsupported {
                    feature: format!(
                        "the type comment gives {} parameter type(s) but the function has {}",
                        types.len(),
                        params.len()
                    ),
                    span: Span::new(c.offset, c.offset + c.text.len()),
                }
                .into());
            }
            for (p, t) in params.iter_mut().zip(types) {
                if p.type_ast.is_none() {
                    p.type_ast = Some(t);
                }
            }
        }
        if ret.is_none() {
            *ret = Some(ret_type);
        }
        Ok(())
    }

    fn def_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // def
        let name = self.expect_name("function name")?;
        let name_span = self.prev_span();
        self.expect(&Tok::LParen, "'('")?;
        let mut params = Vec::new();
        if !self.check(&Tok::RParen) {
            loop {
                if self.eat_keyword_only_marker() {
                    continue;
                }
                if matches!(self.cur(), Tok::Star | Tok::DStar) {
                    return Err(self.unsupported("*args / **kwargs are not supported"));
                }
                let pspan = self.cur_span();
                let pname = self.expect_name("parameter name")?;
                // Annotation `: T` — parsed into the shared TypeAst IR so
                // inference can check the parameter's declared type.
                let type_ast = if self.eat(&Tok::Colon) {
                    Some(self.parse_type_ast())
                } else {
                    None
                };
                // A default value (`x=expr`) makes the parameter optional.
                // A non-`None` default also constrains the parameter's
                // type; a bare `=None` is Python's idiomatic optional and
                // carries no useful type, so it imposes no constraint.
                let default = if self.eat(&Tok::Assign) {
                    Some(self.expr()?)
                } else {
                    None
                };
                params.push(Self::param_from_default(pname, pspan, default, type_ast));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        // Optional return annotation (`-> T`), parsed into the shared
        // TypeAst IR so inference can check the body against it.
        let mut return_type_ast = if self.eat(&Tok::Arrow) {
            Some(self.parse_type_ast())
        } else {
            None
        };
        self.expect(&Tok::Colon, "':'")?;
        self.apply_signature_comment(&mut params, &mut return_type_ast)?;

        let starlark_top = self.starlark && !self.in_function();
        if starlark_top {
            if self.local_declared(&name) {
                return Err(self.reassigned_global(&name, name_span));
            }
            self.declare(&name);
            self.top_defs.push((name.clone(), name_span));
            self.top_def = Some(name.clone());
        }
        self.scopes.push(Scope::default());
        for p in &params {
            self.declare(&p.name);
        }
        let body = self.suite();
        self.scopes.pop();
        if starlark_top {
            self.top_def = None;
        }
        let body = body?;

        Ok(Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation: None,
            return_type_ast,
            name_span: Some(name_span),
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse a `class` declaration and lower it to a factory function
    /// returning a structural row of fields + methods — the same shape
    /// the JavaScript frontend desugars classes to. Instances are
    /// structural (no nominal brand yet; see
    /// `docs/pyi-import-mapping.md` §8). `self` maps to inty's `this`.
    fn class_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // class
        let name = self.expect_name("class name")?;
        let name_span = self.prev_span();

        // Optional base-class list. Inheritance is out of scope
        // (instances are structural rows); accept only an empty `()`.
        if self.eat(&Tok::LParen) {
            if !self.check(&Tok::RParen) {
                return Err(self.unsupported(
                    "base classes / inheritance are not supported \
                     (instances are structural; compose explicitly)",
                ));
            }
            self.expect(&Tok::RParen, "')'")?;
        }
        self.expect(&Tok::Colon, "':'")?;
        self.expect(&Tok::Newline, "newline")?;
        self.expect(&Tok::Indent, "an indented class body")?;

        let mut ctor_params: Vec<Param> = Vec::new();
        let mut props: Vec<PropDef> = Vec::new();

        while !self.check(&Tok::Dedent) && !self.at_eof() {
            if self.eat(&Tok::Newline) {
                continue;
            }
            match self.cur().clone() {
                Tok::Pass => {
                    self.advance();
                    if !self.at_eof() {
                        self.expect(&Tok::Newline, "newline")?;
                    }
                }
                // Decorator on a method (`@property`, …): the effect is
                // not modelled; skip the line and let the next iteration
                // parse the decorated `def`.
                Tok::At => {
                    while !self.check(&Tok::Newline) && !self.at_eof() {
                        self.advance();
                    }
                    self.eat(&Tok::Newline);
                }
                // Tolerate a docstring (a bare string-literal line).
                Tok::Str(_) => {
                    self.advance();
                    if !self.at_eof() {
                        self.expect(&Tok::Newline, "newline")?;
                    }
                }
                Tok::Def => {
                    let mspan = self.cur_span();
                    self.advance(); // def
                    let mname = self.expect_name("method name")?;
                    self.expect(&Tok::LParen, "'('")?;
                    // The first parameter is the receiver (`self`); the
                    // rest are the method's own parameters.
                    let mut self_param: Option<String> = None;
                    let mut params: Vec<Param> = Vec::new();
                    if !self.check(&Tok::RParen) {
                        let mut idx = 0;
                        loop {
                            if self.eat_keyword_only_marker() {
                                continue;
                            }
                            if matches!(self.cur(), Tok::Star | Tok::DStar) {
                                return Err(self.unsupported("*args / **kwargs are not supported"));
                            }
                            let pspan = self.cur_span();
                            let pname = self.expect_name("parameter name")?;
                            let type_ast = if self.eat(&Tok::Colon) {
                                Some(self.parse_type_ast())
                            } else {
                                None
                            };
                            let default = if self.eat(&Tok::Assign) {
                                Some(self.expr()?)
                            } else {
                                None
                            };
                            if idx == 0 {
                                self_param = Some(pname);
                            } else {
                                params.push(Self::param_from_default(
                                    pname, pspan, default, type_ast,
                                ));
                            }
                            idx += 1;
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RParen, "')'")?;
                    let return_type_ast = if self.eat(&Tok::Arrow) {
                        Some(self.parse_type_ast())
                    } else {
                        None
                    };
                    self.expect(&Tok::Colon, "':'")?;

                    // Parse the body with `self` lowered to `this`.
                    let saved_self = self.self_name.take();
                    self.self_name = self_param.clone();
                    self.scopes.push(Scope::default());
                    if let Some(s) = &self_param {
                        self.declare(s);
                    }
                    for p in &params {
                        self.declare(&p.name);
                    }
                    let body = self.suite()?;
                    self.scopes.pop();
                    self.self_name = saved_self;

                    if mname == "__init__" {
                        // The initialiser's params become the factory's
                        // constructor params; its `self.X = expr` lines
                        // become instance fields.
                        ctor_params = params;
                        self.extract_init_fields(&body, &mut props)?;
                    } else {
                        props.push(PropDef::Method {
                            key: PropKey::Ident(mname),
                            params,
                            body,
                            return_type_ast,
                            proto: false,
                            span: Span::new(mspan.start, self.prev_span().end),
                        });
                    }
                }
                Tok::Name(fname) => {
                    // Class-level field. Two shapes are accepted:
                    //   `name: T`            (annotation-only declaration)
                    //   `name [: T] = expr`  (initialised field)
                    // The annotation is lowered to the shared `TypeAst`
                    // IR and carried on the property so inference can pin
                    // the field's type, mirroring the param / return
                    // annotations elsewhere in this frontend.
                    let fspan = self.cur_span();
                    self.advance();
                    let type_ast = if self.eat(&Tok::Colon) {
                        Some(self.parse_type_ast())
                    } else {
                        None
                    };
                    let value = if self.eat(&Tok::Assign) {
                        self.expr()?
                    } else if type_ast.is_some() {
                        // Annotation-only field (`bar: str`): synthesise a
                        // placeholder initialiser. The declared type is
                        // authoritative; inference declares the field at
                        // the annotation and skips checking the
                        // placeholder against it (the htmx `@type` +
                        // placeholder pattern, on the Python IR channel).
                        Expr::Lit {
                            value: Literal::Undefined,
                            span: fspan,
                        }
                    } else {
                        // `name` with neither annotation nor initialiser
                        // isn't a declaration we can type.
                        return Err(self.unsupported(
                            "a class field needs a type annotation (`name: T`) \
                             or an initialiser (`name = expr`)",
                        ));
                    };
                    if !self.at_eof() {
                        self.expect(&Tok::Newline, "newline")?;
                    }
                    props.push(PropDef::Property {
                        key: PropKey::Ident(fname),
                        value,
                        type_annotation: None,
                        type_ast,
                        span: Span::new(fspan.start, self.prev_span().end),
                    });
                }
                _ => {
                    return Err(self.unsupported(
                        "only method definitions and field assignments \
                         are allowed in a class body",
                    ));
                }
            }
        }
        self.expect(&Tok::Dedent, "dedent")?;

        Self::merge_class_field_annotations(&mut props);

        let span = Span::new(start, self.prev_span().end);
        let obj = Expr::Object {
            properties: props,
            span,
        };
        let ret = Stmt::Return {
            argument: Some(obj),
            span,
        };
        let body = Box::new(Stmt::Block {
            body: vec![ret],
            span,
        });

        self.class_names.push(name.clone());
        Ok(Stmt::FunctionDecl {
            name,
            params: ctor_params,
            body,
            type_annotation: None,
            return_type_ast: None,
            name_span: Some(name_span),
            span,
        })
    }

    /// `import a[.b.c] [as alias] (',' …)*`
    ///
    /// Each clause binds the module namespace under a local name. A
    /// dotted path with no `as` binds its **first** segment (Python
    /// binds the top package); `import a.b.c as d` binds `d` to the
    /// `a.b.c` module. Lowers to a `Stmt::Import` with a `Namespace`
    /// specifier per clause; the dotted module spec is the `source`.
    fn import_stmt(&mut self) -> Result<Vec<Stmt>> {
        self.advance(); // import
                        // Each comma-separated clause becomes its own top-level
                        // `Stmt::Import` (one `source` slot per import in the shared
                        // AST). Returned as a flat list so they stay in module scope.
        let mut stmts = Vec::new();
        loop {
            let clause_span = self.cur_span();
            let dotted = self.parse_dotted_name()?;
            let local = if self.eat(&Tok::As) {
                self.expect_name("import alias")?
            } else {
                // `import a.b.c` binds the top segment `a`.
                dotted.split('.').next().unwrap_or(&dotted).to_string()
            };
            self.declare(&local);
            stmts.push(Stmt::Import {
                specifiers: vec![ImportSpecifier::Namespace {
                    local,
                    span: clause_span,
                }],
                source: dotted,
                span: Span::new(clause_span.start, self.prev_span().end),
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        if !self.at_eof() {
            self.expect(&Tok::Newline, "newline")?;
        }
        Ok(stmts)
    }

    /// `from MODULE import (NAME [as alias] (',' …)* | '*')`
    ///
    /// `MODULE` may carry leading dots for relative imports
    /// (`from . import x`, `from ..pkg.mod import y`). `import *` lowers
    /// to a side-effect import (empty specifier list → merge all
    /// exports). The module spec — leading dots plus dotted path — is
    /// the `source`.
    fn import_from_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // from

        // Leading dots for relative imports.
        let mut source = String::new();
        while self.check(&Tok::Dot) {
            source.push('.');
            self.advance();
        }
        // Optional dotted module path (absent for `from . import x`).
        if matches!(self.cur(), Tok::Name(_)) {
            source.push_str(&self.parse_dotted_name()?);
        } else if source.is_empty() {
            return Err(self.unexpected("a module name after 'from'"));
        }

        self.expect(&Tok::Import, "'import'")?;

        // `from m import *` → side-effect import (merge all exports).
        if self.eat(&Tok::Star) {
            if !self.at_eof() {
                self.expect(&Tok::Newline, "newline")?;
            }
            return Ok(Stmt::Import {
                specifiers: Vec::new(),
                source,
                span: Span::new(start, self.prev_span().end),
            });
        }

        // Optional surrounding parens (Python allows a parenthesised,
        // possibly multi-line, import list).
        let parens = self.eat(&Tok::LParen);
        let mut specifiers = Vec::new();
        loop {
            let spec_span = self.cur_span();
            let imported = self.expect_name("imported name")?;
            let local = if self.eat(&Tok::As) {
                self.expect_name("import alias")?
            } else {
                imported.clone()
            };
            self.declare(&local);
            specifiers.push(ImportSpecifier::Named {
                imported,
                local,
                span: spec_span,
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
            // Allow a trailing comma before `)`.
            if parens && self.check(&Tok::RParen) {
                break;
            }
        }
        if parens {
            self.expect(&Tok::RParen, "')'")?;
        }
        if !self.at_eof() {
            self.expect(&Tok::Newline, "newline")?;
        }
        Ok(Stmt::Import {
            specifiers,
            source,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse a dotted name `NAME ('.' NAME)*`, returning it joined with
    /// dots (e.g. `"a.b.c"`).
    fn parse_dotted_name(&mut self) -> Result<String> {
        let mut parts = vec![self.expect_name("module name")?];
        while self.eat(&Tok::Dot) {
            parts.push(self.expect_name("module name segment")?);
        }
        Ok(parts.join("."))
    }

    /// Fold an annotation-only field declaration (`x: T`, lowered to a
    /// placeholder `Property` carrying `type_ast`) into a same-named
    /// field that has a real initialiser — typically the `self.x = …`
    /// assignment extracted from `__init__`. The declared type is moved
    /// onto the initialised field so inference unifies the initialiser
    /// against the annotation, and the now-redundant placeholder is
    /// dropped. Without this, the two same-keyed properties would both
    /// flow into the factory's row and the later one would silently win,
    /// discarding the declared type.
    fn merge_class_field_annotations(props: &mut Vec<PropDef>) {
        // A placeholder declaration is the synthetic `name: T` form: an
        // `undefined` value with a declared `type_ast`. An initialised
        // field is any other `Property` with a real value.
        fn ident(p: &PropDef) -> Option<&str> {
            match p {
                PropDef::Property {
                    key: PropKey::Ident(n),
                    ..
                } => Some(n),
                _ => None,
            }
        }
        fn is_placeholder_decl(p: &PropDef) -> bool {
            matches!(
                p,
                PropDef::Property {
                    value: Expr::Lit {
                        value: Literal::Undefined,
                        ..
                    },
                    type_ast: Some(_),
                    ..
                }
            )
        }

        // Names that have an initialised (non-placeholder) field.
        let initialised: std::collections::HashSet<String> = props
            .iter()
            .filter(|p| !is_placeholder_decl(p))
            .filter_map(|p| ident(p).map(str::to_owned))
            .collect();

        // Declared types for placeholder-only declarations, keyed by name.
        let declared: std::collections::HashMap<String, crate::types::TypeAst> = props
            .iter()
            .filter(|p| is_placeholder_decl(p) && ident(p).is_some_and(|n| initialised.contains(n)))
            .filter_map(|p| match p {
                PropDef::Property {
                    key: PropKey::Ident(n),
                    type_ast: Some(t),
                    ..
                } => Some((n.clone(), t.clone())),
                _ => None,
            })
            .collect();

        if declared.is_empty() {
            return;
        }

        // Attach the declared type to the initialised field (unless it
        // already carries its own annotation, e.g. `x: T = v`), then drop
        // the placeholder declarations that were merged.
        for p in props.iter_mut() {
            if is_placeholder_decl(p) {
                continue;
            }
            if let PropDef::Property {
                key: PropKey::Ident(n),
                type_ast: slot @ None,
                ..
            } = p
            {
                if let Some(t) = declared.get(n) {
                    *slot = Some(t.clone());
                }
            }
        }
        props.retain(|p| {
            !(is_placeholder_decl(p) && ident(p).is_some_and(|n| declared.contains_key(n)))
        });
    }

    /// Pull `self.<field> = <expr>` lines out of a parsed `__init__`
    /// body (where `self` has already been lowered to `this`) and turn
    /// each into an instance-field property of the factory's row.
    fn extract_init_fields(&self, body: &Stmt, props: &mut Vec<PropDef>) -> Result<()> {
        let stmts: &[Stmt] = match body {
            Stmt::Block { body, .. } => body.as_slice(),
            other => std::slice::from_ref(other),
        };
        for s in stmts {
            match s {
                Stmt::Empty { .. } => {}
                Stmt::Expr {
                    expression:
                        Expr::Assign {
                            op: AssignOp::Assign,
                            left,
                            right,
                            ..
                        },
                    ..
                } => {
                    if let Expr::Member {
                        object,
                        property,
                        span,
                    } = left.as_ref()
                    {
                        if matches!(object.as_ref(), Expr::This { .. }) {
                            props.push(PropDef::Property {
                                key: PropKey::Ident(property.clone()),
                                value: (**right).clone(),
                                type_annotation: None,
                                type_ast: None,
                                span: *span,
                            });
                            continue;
                        }
                    }
                    return Err(self.unsupported(
                        "only `self.<field> = <expr>` assignments are supported in __init__",
                    ));
                }
                _ => {
                    return Err(self.unsupported(
                        "only `self.<field> = <expr>` assignments are supported in __init__",
                    ));
                }
            }
        }
        Ok(())
    }

    /// Parse a type annotation (a Python type expression) into the shared
    /// [`TypeAst`] IR, advancing past it.
    fn parse_type_ast(&mut self) -> TypeAst {
        let (ast, new_pos) = super::type_expr::parse_type(&self.toks, self.pos);
        self.pos = new_pos;
        ast
    }

    fn if_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // if
        let test = self.expr()?;
        self.expect(&Tok::Colon, "':'")?;
        let consequent = self.suite()?;
        let alternate = self.if_tail(start)?;
        Ok(Stmt::If {
            test,
            consequent,
            alternate,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn if_tail(&mut self, start: usize) -> Result<Option<Box<Stmt>>> {
        if self.check(&Tok::Elif) {
            self.advance();
            let test = self.expr()?;
            self.expect(&Tok::Colon, "':'")?;
            let consequent = self.suite()?;
            let alternate = self.if_tail(start)?;
            Ok(Some(Box::new(Stmt::If {
                test,
                consequent,
                alternate,
                span: Span::new(start, self.prev_span().end),
            })))
        } else if self.check(&Tok::Else) {
            self.advance();
            self.expect(&Tok::Colon, "':'")?;
            Ok(Some(self.suite()?))
        } else {
            Ok(None)
        }
    }

    fn while_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance();
        let test = self.expr()?;
        self.expect(&Tok::Colon, "':'")?;
        let body = self.suite()?;
        Ok(Stmt::While {
            test,
            body,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// `try: SUITE (except [E (',' E)* | E 'as' e]: SUITE)* [else: SUITE] [finally: SUITE]`.
    ///
    /// Per PEP 758 (Python 3.14+) the exception position accepts an
    /// unparenthesised list of types — `except A, B:` — equivalent to the
    /// older `except (A, B):`. The `as NAME` binding only applies to a single
    /// expression, so binding multiple types still needs parentheses:
    /// `except (A, B) as e:` (an unparenthesised list with `as` is rejected).
    ///
    /// `except*` (PEP 654, exception groups) is accepted with the same type
    /// grammar, but a `try` may not mix `except` and `except*`, and `except*`
    /// must name a type (no bare `except*:`). Since the exception object is
    /// unmodelled, both forms lower identically — the `*` is parse-only.
    ///
    /// Lowered onto the shared `Stmt::Try { block, handler, finalizer }`:
    ///   - `block` is the try-suite with the `else`-suite appended (the
    ///     `else` runs only when the body completes without raising, so for
    ///     type-checking it joins the no-exception path).
    ///   - `handler`, when there is at least one `except`, is a single
    ///     `CatchClause` whose body runs every `except`-suite; each `as e`
    ///     name is bound to an opaque (fresh) variable, since the exception
    ///     object's type is unmodelled.
    ///   - `finalizer` is the `finally`-suite.
    fn try_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // try
        self.expect(&Tok::Colon, "':'")?;
        // Flatten the suite into the surrounding statement list so its
        // declarations thread through `var` (function-scope) hoisting
        // rather than being trapped in a nested `Block`'s scope.
        let mut block_body = self.suite_body()?;

        let mut handler_body: Vec<Stmt> = Vec::new();
        let mut saw_except = false;
        // `except*` (PEP 654) handles members of an `ExceptionGroup`. A single
        // `try` must use one form throughout — `except` and `except*` cannot be
        // mixed — so remember which form the first clause picked.
        let mut star_form: Option<bool> = None;
        while self.check(&Tok::Except) {
            saw_except = true;
            self.advance(); // except
            let is_star = self.eat(&Tok::Star); // `except*`
            match star_form {
                None => star_form = Some(is_star),
                Some(prev) if prev != is_star => {
                    return Err(self.unexpected(if is_star {
                        "'except' (cannot mix `except` and `except*` in one `try`)"
                    } else {
                        "'except*' (cannot mix `except` and `except*` in one `try`)"
                    }));
                }
                Some(_) => {}
            }
            // Optional exception type, then optional `as NAME`.
            let mut bound: Option<String> = None;
            if !self.check(&Tok::Colon) {
                let _ = self.expr()?; // the exception class
                                      // An unparenthesised list of exception types — `except A, B:` —
                                      // catches any of them (Python 3.14+, PEP 758). Equivalent to
                                      // the older `except (A, B):`. Each class is parsed (and
                                      // discarded) so the names are still type-checked.
                let mut multiple = false;
                while self.eat(&Tok::Comma) {
                    // Tolerate a trailing comma before `as`/`:`.
                    if self.check(&Tok::As) || self.check(&Tok::Colon) {
                        break;
                    }
                    multiple = true;
                    let _ = self.expr()?;
                }
                if self.check(&Tok::As) {
                    // PEP 758 only drops the parentheses for the no-binding
                    // form: `except A, B as e:` is a syntax error and must be
                    // written `except (A, B) as e:`.
                    if multiple {
                        return Err(self.unexpected(
                            "':' (parenthesise the exception types to bind \
                             with `as`, e.g. `except (A, B) as e:`)",
                        ));
                    }
                    self.advance(); // as
                    bound = Some(self.expect_name("exception variable")?);
                }
            } else if is_star {
                // A bare `except*:` is a syntax error — a group handler must
                // name the exception type(s) it splits out.
                return Err(self.unexpected("an exception type (`except*` cannot be bare)"));
            }
            self.expect(&Tok::Colon, "':'")?;
            let body = self.suite_body()?;
            // Bind `as NAME` opaquely for this handler's body.
            if let Some(name) = bound {
                let span = Span::new(start, self.prev_span().end);
                handler_body.push(Stmt::Var {
                    kind: VarKind::Var,
                    declarations: vec![VarDeclarator {
                        name,
                        init: None,
                        type_annotation: None,
                        type_ast: None,
                        kind: VarKind::Var,
                        span,
                    }],
                    span,
                });
            }
            handler_body.extend(body);
        }

        // Optional `else:` — append to the try-block (no-exception path).
        if self.check(&Tok::Else) {
            self.advance();
            self.expect(&Tok::Colon, "':'")?;
            block_body.extend(self.suite_body()?);
        }

        let finalizer = if self.check(&Tok::Finally) {
            self.advance();
            self.expect(&Tok::Colon, "':'")?;
            Some(self.suite()?)
        } else {
            None
        };

        if !saw_except && finalizer.is_none() {
            return Err(self.unexpected("'except' or 'finally' after 'try'"));
        }

        let span = Span::new(start, self.prev_span().end);
        let handler = if saw_except {
            Some(CatchClause {
                param: self.fresh_temp(),
                body: Box::new(Stmt::Block {
                    body: handler_body,
                    span,
                }),
                span,
            })
        } else {
            None
        };

        Ok(Stmt::Try {
            block: Box::new(Stmt::Block {
                body: block_body,
                span,
            }),
            handler,
            finalizer,
            span,
        })
    }

    /// `with EXPR ['as' NAME] (',' EXPR ['as' NAME])* ':' SUITE`.
    ///
    /// Lowered to a flat statement sequence: for each manager, either bind
    /// `NAME = EXPR` (when `as NAME` is present) or evaluate `EXPR` as an
    /// expression statement; then splice in the suite body. The
    /// `__enter__` / `__exit__` protocol isn't modelled — the manager
    /// expression itself stands in for the value bound by `as`, and any
    /// resource teardown is treated as a runtime concern outside the type
    /// system. The body's declarations are flattened into the surrounding
    /// scope (Python's `with` doesn't introduce a new scope).
    fn with_stmt(&mut self) -> Result<Vec<Stmt>> {
        self.advance(); // with
        let mut out: Vec<Stmt> = Vec::new();
        loop {
            let item_start = self.cur_span().start;
            let value = self.expr()?;
            let bound: Option<String> = if self.eat(&Tok::As) {
                Some(self.expect_name("context manager binding")?)
            } else {
                None
            };
            let span = Span::new(item_start, self.prev_span().end);
            match bound {
                Some(name) => {
                    out.push(self.declare_or_assign_single(name, Some(value), None, span)?)
                }
                None => out.push(Stmt::Expr {
                    expression: value,
                    span,
                }),
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::Colon, "':'")?;
        out.extend(self.suite_body()?);
        Ok(out)
    }

    fn for_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // for

        // Each target keeps its own name span, so the LSP anchors the
        // loop variable's type hint on the name, not the whole header.
        let mut targets = vec![self.expect_name("loop variable")?];
        let mut target_spans = vec![self.prev_span()];
        while self.eat(&Tok::Comma) {
            targets.push(self.expect_name("loop variable")?);
            target_spans.push(self.prev_span());
        }
        self.expect(&Tok::In, "'in'")?;
        let right = self.expr()?;
        self.expect(&Tok::Colon, "':'")?;

        // Simple `for x in xs` — bind `x` directly to the element type.
        if targets.len() == 1 {
            let name = targets.pop().unwrap();
            self.declare(&name);
            let body = self.suite()?;
            return Ok(Stmt::ForOf {
                left: ForInLhs::VarDecl(name, None, target_spans[0], VarKind::Var),
                right,
                body,
                span: Span::new(start, self.prev_span().end),
            });
        }

        // `for k, v in items` — iterate a fresh element variable and
        // destructure it by indexing at the top of the body, so `k`/`v`
        // get the tuple component types.
        let tmp = self.fresh_temp();
        for t in &targets {
            self.declare(t);
        }
        self.declare(&tmp);
        let span_so_far = Span::new(start, self.prev_span().end);
        let inner = self.suite()?;
        let mut body = destructure_targets(&tmp, &targets, &target_spans, span_so_far);
        body.push(*inner);
        let span = Span::new(start, self.prev_span().end);
        Ok(Stmt::ForOf {
            left: ForInLhs::VarDecl(tmp, None, span_so_far, VarKind::Var),
            right,
            body: Box::new(Stmt::Block { body, span }),
            span,
        })
    }

    // ---- expressions ----

    fn expr(&mut self) -> Result<Expr> {
        if self.check(&Tok::Lambda) {
            return self.lambda();
        }
        self.ternary()
    }

    fn lambda(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        self.advance(); // lambda
        let mut params = Vec::new();
        if !self.check(&Tok::Colon) {
            loop {
                if matches!(self.cur(), Tok::Star | Tok::DStar) {
                    return Err(self.unsupported("*args / **kwargs are not supported in lambda"));
                }
                let pspan = self.cur_span();
                let pname = self.expect_name("parameter name")?;
                if self.check(&Tok::Assign) {
                    return Err(self.unsupported("default parameters are not supported in lambda"));
                }
                params.push(Param::new(pname, pspan));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::Colon, "':'")?;
        let body_expr = self.expr()?;
        let span = Span::new(start, self.prev_span().end);
        let body = Box::new(Stmt::Block {
            body: vec![Stmt::Return {
                argument: Some(body_expr),
                span,
            }],
            span,
        });
        Ok(Expr::Function {
            name: None,
            params,
            body,
            type_annotation: None,
            arrow: false,
            span,
        })
    }

    fn ternary(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let e = self.or_expr()?;
        // `consequent if test else alternate`
        if self.check(&Tok::If) {
            self.advance();
            let test = self.or_expr()?;
            self.expect(&Tok::Else, "'else' in conditional expression")?;
            let alternate = self.expr()?;
            return Ok(Expr::Conditional {
                test: Box::new(test),
                consequent: Box::new(e),
                alternate: Box::new(alternate),
                span: Span::new(start, self.prev_span().end),
            });
        }
        Ok(e)
    }

    fn or_expr(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::Or, BinOp::Or)], Self::and_expr)
    }

    fn and_expr(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::And, BinOp::And)], Self::not_expr)
    }

    fn not_expr(&mut self) -> Result<Expr> {
        if self.check(&Tok::Not) {
            let start = self.cur_span().start;
            self.advance();
            let argument = Box::new(self.not_expr()?);
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                argument,
                span: Span::new(start, self.prev_span().end),
            });
        }
        self.comparison()
    }

    /// Comparisons are non-associative in this subset: a chain like
    /// `a < b < c` (which Python treats specially) is rejected rather than
    /// silently parsed left-associatively.
    ///
    /// `is` / `is not` are lowered to strict (in)equality — sufficient for
    /// the common `x is None` idiom under the strict type system. `==` /
    /// `!=` are lowered to loose (in)equality: they call `__eq__`, which
    /// an object may define as it likes, so narrowing reads them less
    /// strictly than `is` (see `narrow::Narrowing::PyEq`). `in` /
    /// `not in` are lowered to the membership `BinOp::In` (with an outer
    /// `not` for the negated form); both yield `bool`.
    fn comparison(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let left = self.bitor()?;
        if self.starlark && self.check(&Tok::Is) {
            return Err(self.not_starlark("'is'", "use =="));
        }
        // Two-token operators (`is not`, `not in`) need lookahead.
        let (op, negate, advance_tokens) = match (self.cur(), self.peek_tok(1)) {
            (Tok::Is, Tok::Not) => (Some(BinOp::EqEqEq), true, 2),
            (Tok::Is, _) => (Some(BinOp::EqEqEq), false, 1),
            (Tok::Not, Tok::In) => (Some(BinOp::In), true, 2),
            (Tok::In, _) => (Some(BinOp::In), false, 1),
            (Tok::Eq, _) => (Some(BinOp::EqEq), false, 1),
            (Tok::Ne, _) => (Some(BinOp::NotEq), false, 1),
            (Tok::Lt, _) => (Some(BinOp::Lt), false, 1),
            (Tok::Gt, _) => (Some(BinOp::Gt), false, 1),
            (Tok::Le, _) => (Some(BinOp::LtEq), false, 1),
            (Tok::Ge, _) => (Some(BinOp::GtEq), false, 1),
            _ => (None, false, 0),
        };
        let Some(op) = op else { return Ok(left) };
        for _ in 0..advance_tokens {
            self.advance();
        }
        let right = self.bitor()?;
        // reject chained comparisons
        if matches!(
            self.cur(),
            Tok::Eq | Tok::Ne | Tok::Lt | Tok::Gt | Tok::Le | Tok::Ge | Tok::Is | Tok::In
        ) || matches!((self.cur(), self.peek_tok(1)), (Tok::Not, Tok::In))
        {
            return Err(self.unsupported(
                "chained comparisons (e.g. 'a < b < c') are not supported; use 'and'",
            ));
        }
        let span = Span::new(start, self.prev_span().end);
        let cmp = Expr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
            span,
        };
        Ok(if negate {
            Expr::Unary {
                op: UnaryOp::Not,
                argument: Box::new(cmp),
                span,
            }
        } else {
            cmp
        })
    }

    fn bitor(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::Pipe, BinOp::BitOr)], Self::bitxor)
    }

    fn bitxor(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::Caret, BinOp::BitXor)], Self::bitand)
    }

    fn bitand(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::Amp, BinOp::BitAnd)], Self::shift)
    }

    fn shift(&mut self) -> Result<Expr> {
        self.left_assoc(
            &[(Tok::Shl, BinOp::LShift), (Tok::Shr, BinOp::RShift)],
            Self::arith,
        )
    }

    fn arith(&mut self) -> Result<Expr> {
        self.left_assoc(
            &[(Tok::Plus, BinOp::Add), (Tok::Minus, BinOp::Sub)],
            Self::term,
        )
    }

    fn term(&mut self) -> Result<Expr> {
        self.left_assoc(
            &[
                (Tok::Star, BinOp::Mul),
                (Tok::Slash, BinOp::Div),
                (Tok::DSlash, BinOp::FloorDiv),
                (Tok::Percent, BinOp::Mod),
            ],
            Self::factor,
        )
    }

    fn left_assoc(
        &mut self,
        ops: &[(Tok, BinOp)],
        next: fn(&mut Self) -> Result<Expr>,
    ) -> Result<Expr> {
        let start = self.cur_span().start;
        let mut left = next(self)?;
        while let Some((_, op)) = ops.iter().find(|(t, _)| self.check(t)) {
            let op = *op;
            self.advance();
            let right = next(self)?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
                span: Span::new(start, self.prev_span().end),
            };
        }
        Ok(left)
    }

    fn factor(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let op = match self.cur() {
            Tok::Plus => Some(UnaryOp::Pos),
            Tok::Minus => Some(UnaryOp::Neg),
            Tok::Tilde => Some(UnaryOp::BitNot),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let argument = Box::new(self.factor()?);
            return Ok(Expr::Unary {
                op,
                argument,
                span: Span::new(start, self.prev_span().end),
            });
        }
        self.power()
    }

    fn power(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let base = self.postfix()?;
        if self.check(&Tok::DStar) {
            if self.starlark {
                return Err(self.not_starlark("the '**' operator", ""));
            }
            self.advance();
            let exp = self.factor()?; // right-associative, allows unary
            return Ok(Expr::Binary {
                op: BinOp::Pow,
                left: Box::new(base),
                right: Box::new(exp),
                span: Span::new(start, self.prev_span().end),
            });
        }
        Ok(base)
    }

    /// The rest of a slice subscript `e[lower:upper:step]`, positioned at
    /// the first `:`. Lowered to a call of the `__slice__` method that the
    /// Python `str` and `list` method surfaces provide, with `None` for an
    /// omitted bound: `xs[1:]` ⇒ `xs.__slice__(1, None, None)`. The result
    /// has the receiver's type (a string or a list of the same element).
    fn slice(&mut self, start: usize, object: Expr, lower: Option<Expr>) -> Result<Expr> {
        let none = |span: Span| Expr::Lit {
            value: Literal::Null,
            span,
        };
        let colon_span = self.cur_span();
        self.expect(&Tok::Colon, "':'")?;
        let bound = |p: &mut Self| -> Result<Option<Expr>> {
            if matches!(p.cur(), Tok::Colon | Tok::RBracket) {
                Ok(None)
            } else {
                Ok(Some(p.expr()?))
            }
        };
        let upper = bound(self)?;
        let step = if self.eat(&Tok::Colon) {
            bound(self)?
        } else {
            None
        };
        self.expect(&Tok::RBracket, "']'")?;
        let span = Span::new(start, self.prev_span().end);
        let arguments = [lower, upper, step]
            .into_iter()
            .map(|b| b.unwrap_or_else(|| none(colon_span)))
            .collect();
        Ok(Expr::Call {
            callee: Box::new(Expr::Member {
                object: Box::new(object),
                property: SLICE_METHOD.to_string(),
                span,
            }),
            arguments,
            keywords: vec![],
            span,
        })
    }

    fn postfix(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let mut e = self.atom()?;
        loop {
            match self.cur() {
                Tok::Dot => {
                    self.advance();
                    let property = self.expect_name("attribute name")?;
                    e = Expr::Member {
                        object: Box::new(e),
                        property,
                        span: Span::new(start, self.prev_span().end),
                    };
                }
                Tok::LBracket => {
                    self.advance();
                    let lower = if self.check(&Tok::Colon) {
                        None
                    } else {
                        Some(self.expr()?)
                    };
                    if self.check(&Tok::Colon) {
                        e = self.slice(start, e, lower)?;
                        continue;
                    }
                    let index = lower.expect("a subscript without ':' has an index");
                    self.expect(&Tok::RBracket, "']'")?;
                    let span = Span::new(start, self.prev_span().end);
                    // `d["name"]` (string-literal key) is a field access,
                    // which the type system resolves on rows; other keys
                    // stay dynamic indexing.
                    e = match index {
                        Expr::Lit {
                            value: Literal::String(name),
                            ..
                        } => Expr::Member {
                            object: Box::new(e),
                            property: name,
                            span,
                        },
                        _ => Expr::ComputedMember {
                            object: Box::new(e),
                            property: Box::new(index),
                            span,
                        },
                    };
                }
                Tok::LParen => {
                    self.advance();
                    let (arguments, keywords) = self.call_args()?;
                    let span = Span::new(start, self.prev_span().end);
                    if self.starlark {
                        if let Expr::Ident { name, .. } = &e {
                            // `struct(a = 1, b = x)` builds a record.
                            if name == "struct"
                                && arguments.is_empty()
                                && !keywords.is_empty()
                                && self.is_builtin("struct")
                            {
                                e = struct_literal(keywords, span);
                                continue;
                            }
                            if let Some(caller) = &self.top_def {
                                if !self.bound_in_function(name) {
                                    self.top_calls.push((caller.clone(), name.clone(), span));
                                }
                            }
                        }
                    }
                    e = Expr::Call {
                        callee: Box::new(e),
                        arguments,
                        keywords,
                        span,
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    /// Parse a call's argument list into `(positional, keyword)`. A
    /// `name=value` argument is a keyword; positional arguments may not
    /// follow a keyword (a Python `SyntaxError`).
    fn call_args(&mut self) -> Result<CallArgs> {
        let mut args = Vec::new();
        let mut kwargs: Vec<(String, Expr)> = Vec::new();
        if self.check(&Tok::RParen) {
            self.advance();
            return Ok((args, kwargs));
        }
        loop {
            if matches!(self.cur(), Tok::Star | Tok::DStar) {
                return Err(self.unsupported("argument unpacking (*/**) is not supported"));
            }
            // Keyword argument `name=value`.
            if let Tok::Name(name) = self.cur().clone() {
                if matches!(
                    self.toks.get(self.pos + 1).map(|s| &s.value),
                    Some(Tok::Assign)
                ) {
                    self.advance(); // name
                    self.advance(); // '='
                    let value = self.expr()?;
                    kwargs.push((name, value));
                    if !self.eat(&Tok::Comma) || self.check(&Tok::RParen) {
                        break;
                    }
                    continue;
                }
            }
            if !kwargs.is_empty() {
                return Err(self.unsupported("positional argument follows keyword argument"));
            }
            let arg_start = self.cur_span().start;
            let arg = self.expr()?;
            // A generator expression as the sole argument
            // (`any(x > 0 for x in xs)`): lowered to a list comprehension.
            if args.is_empty() && self.check(&Tok::For) {
                args.push(self.comprehension(arg_start, arg)?);
                self.expect(&Tok::RParen, "')'")?;
                return Ok((args, kwargs));
            }
            args.push(arg);
            if !self.eat(&Tok::Comma) {
                break;
            }
            if self.check(&Tok::RParen) {
                break;
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        Ok((args, kwargs))
    }

    /// Parse the source of one f-string interpolation into an expression.
    /// Runs a fresh sub-parser that inherits the receiver name, so
    /// `f"{self.x}"` inside a method still lowers `self` to `this`. Only
    /// the leading expression is taken; any trailing tokens (an unparsed
    /// remnant) are ignored.
    fn parse_embedded_expr(&self, src: &str) -> Result<Expr> {
        let toks = tokenize(src)?;
        let mut p = Parser::new(toks);
        p.self_name = self.self_name.clone();
        p.expr()
    }

    fn atom(&mut self) -> Result<Expr> {
        let span = self.cur_span();
        match self.cur().clone() {
            Tok::Number(n) => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Number(n),
                    span,
                })
            }
            Tok::Str(s) => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::String(s),
                    span,
                })
            }
            // An f-string desugars to a template literal: it always
            // evaluates to `String`, and each interpolation is re-parsed
            // and type-checked as an embedded expression.
            Tok::FString { .. } if self.starlark => {
                Err(self.not_starlark("an f-string", "use % or .format()"))
            }
            Tok::FString { quasis, exprs } => {
                self.advance();
                let mut expressions = Vec::with_capacity(exprs.len());
                for src in &exprs {
                    expressions.push(self.parse_embedded_expr(src)?);
                }
                Ok(Expr::TemplateLiteral {
                    quasis,
                    expressions,
                    span,
                })
            }
            Tok::True => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Boolean(true),
                    span,
                })
            }
            Tok::False => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Boolean(false),
                    span,
                })
            }
            Tok::None => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Null,
                    span,
                })
            }
            Tok::Name(name) => {
                self.advance();
                // Inside a method body, the receiver parameter lowers to
                // `this` so member access (`self.x`) types via inty's
                // `this` row-polymorphism.
                if self.self_name.as_deref() == Some(name.as_str()) {
                    Ok(Expr::This { span })
                } else {
                    Ok(Expr::Ident { name, span })
                }
            }
            Tok::LParen => {
                self.advance();
                // Empty tuple `()`.
                if self.eat(&Tok::RParen) {
                    return Ok(Expr::Tuple {
                        elements: Vec::new(),
                        span: Span::new(span.start, self.prev_span().end),
                    });
                }
                let first = self.expr()?;
                // `(e for x in xs)`: a generator expression, lowered to a
                // list comprehension (its consumers all take a list).
                if self.check(&Tok::For) {
                    let comp = self.comprehension(span.start, first)?;
                    self.expect(&Tok::RParen, "')'")?;
                    return Ok(comp);
                }
                // A comma makes it a tuple (`(a, b)`, `(a,)`); otherwise the
                // parentheses are just grouping.
                if self.check(&Tok::Comma) {
                    let mut elements = vec![first];
                    while self.eat(&Tok::Comma) {
                        if self.check(&Tok::RParen) {
                            break; // trailing comma, e.g. `(a,)`
                        }
                        elements.push(self.expr()?);
                    }
                    self.expect(&Tok::RParen, "')'")?;
                    return Ok(Expr::Tuple {
                        elements,
                        span: Span::new(span.start, self.prev_span().end),
                    });
                }
                self.expect(&Tok::RParen, "')'")?;
                Ok(first)
            }
            Tok::LBracket => self.list(),
            Tok::LBrace => self.dict(),
            Tok::Lambda => self.lambda(),
            _ => Err(self.unexpected("an expression")),
        }
    }

    fn list(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        self.advance(); // [
        let mut elements = Vec::new();
        while !self.check(&Tok::RBracket) {
            let element = self.expr()?;
            if elements.is_empty() && self.check(&Tok::For) {
                let comp = self.comprehension(start, element)?;
                self.expect(&Tok::RBracket, "']'")?;
                return Ok(comp);
            }
            elements.push(Some(element));
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBracket, "']'")?;
        Ok(Expr::Array {
            elements,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse the `for … in …` / `if …` clauses of a comprehension whose
    /// element expression is already parsed, and lower the whole thing to
    /// an immediately-called arrow function that builds the list:
    ///
    /// ```text
    /// [e for x in xs if c for y in ys]
    ///   ⇒ ((it) => { var acc = [];
    ///                for (var x of it) if (c) for (var y of ys) acc.append(e);
    ///                return acc; })(xs)
    /// ```
    ///
    /// The loop variables are `var`s of the arrow function, so they are
    /// local to the comprehension and never leak into (or get declared in)
    /// the enclosing scope, as in Python 3 and Starlark. The first iterable
    /// is evaluated in the enclosing scope, as Python does, so it is passed
    /// in as the argument rather than read inside the function, where a
    /// loop variable of the same name would shadow it (`[x for x in x]`).
    /// The arrow function keeps the enclosing `this`, so `self.f` inside a
    /// method's comprehension still means the receiver. Tuple targets
    /// (`for k, v in pairs`) destructure by index, as a `for` statement
    /// does. Used for list comprehensions and for a generator expression
    /// passed as a call's sole argument (`any(x > 0 for x in xs)`), whose
    /// consumers all take a list.
    fn comprehension(&mut self, start: usize, element: Expr) -> Result<Expr> {
        enum Clause {
            For {
                targets: Vec<String>,
                spans: Vec<Span>,
                iter: Expr,
                span: Span,
            },
            If(Expr),
        }
        let mut clauses = Vec::new();
        loop {
            if self.check(&Tok::For) {
                let clause_start = self.cur_span().start;
                self.advance(); // for
                let mut targets = vec![self.expect_name("loop variable")?];
                let mut spans = vec![self.prev_span()];
                while self.eat(&Tok::Comma) {
                    targets.push(self.expect_name("loop variable")?);
                    spans.push(self.prev_span());
                }
                self.expect(&Tok::In, "'in'")?;
                let iter = self.or_expr()?;
                clauses.push(Clause::For {
                    targets,
                    spans,
                    iter,
                    span: Span::new(clause_start, self.prev_span().end),
                });
            } else if self.check(&Tok::If) {
                self.advance(); // if
                clauses.push(Clause::If(self.or_expr()?));
            } else {
                break;
            }
        }
        let span = Span::new(start, self.prev_span().end);

        let acc = self.fresh_temp();
        let first_iter = self.fresh_temp();
        let ident = |name: &str| Expr::Ident {
            name: name.to_string(),
            span,
        };
        // Innermost: `acc.append(element)`.
        let mut inner = Stmt::Expr {
            expression: Expr::Call {
                callee: Box::new(Expr::Member {
                    object: Box::new(ident(&acc)),
                    property: "append".to_string(),
                    span,
                }),
                arguments: vec![element],
                keywords: vec![],
                span,
            },
            span,
        };
        let mut first = None;
        for (i, clause) in clauses.into_iter().enumerate().rev() {
            inner = match clause {
                Clause::If(test) => Stmt::If {
                    test,
                    consequent: Box::new(inner),
                    alternate: None,
                    span,
                },
                Clause::For {
                    mut targets,
                    spans,
                    iter,
                    span: clause_span,
                } => {
                    // The first clause iterates the argument instead.
                    let right = if i == 0 {
                        first = Some(iter);
                        ident(&first_iter)
                    } else {
                        iter
                    };
                    if targets.len() == 1 {
                        Stmt::ForOf {
                            left: ForInLhs::VarDecl(
                                targets.pop().unwrap(),
                                None,
                                spans[0],
                                VarKind::Var,
                            ),
                            right,
                            body: Box::new(inner),
                            span: clause_span,
                        }
                    } else {
                        let tmp = self.fresh_temp();
                        let mut body = destructure_targets(&tmp, &targets, &spans, clause_span);
                        body.push(inner);
                        Stmt::ForOf {
                            left: ForInLhs::VarDecl(tmp, None, clause_span, VarKind::Var),
                            right,
                            body: Box::new(Stmt::Block {
                                body,
                                span: clause_span,
                            }),
                            span: clause_span,
                        }
                    }
                }
            };
        }
        let Some(first) = first else {
            return Err(self.unexpected("'for' in comprehension"));
        };
        let body = Stmt::Block {
            body: vec![
                Stmt::Var {
                    kind: VarKind::Var,
                    declarations: vec![VarDeclarator {
                        name: acc.clone(),
                        init: Some(Expr::Array {
                            elements: vec![],
                            span,
                        }),
                        type_annotation: None,
                        type_ast: None,
                        kind: VarKind::Var,
                        span,
                    }],
                    span,
                },
                inner,
                Stmt::Return {
                    argument: Some(ident(&acc)),
                    span,
                },
            ],
            span,
        };
        Ok(Expr::Call {
            callee: Box::new(Expr::Function {
                name: None,
                params: vec![Param::new(first_iter, span)],
                body: Box::new(body),
                type_annotation: None,
                arrow: true,
                span,
            }),
            arguments: vec![first],
            keywords: vec![],
            span,
        })
    }

    fn dict(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        self.advance(); // {
        let mut props = Vec::new();
        while !self.check(&Tok::RBrace) {
            let field_span = self.cur_span();
            let key =
                match self.cur().clone() {
                    Tok::Str(s) => {
                        self.advance();
                        PropKey::String(s)
                    }
                    Tok::Number(n) => {
                        self.advance();
                        PropKey::Number(n)
                    }
                    _ => return Err(self.unsupported(
                        "dict keys must be string or number literals (or this is a set literal, \
                         which is unsupported)",
                    )),
                };
            self.expect(&Tok::Colon, "':' in dict")?;
            let value = self.expr()?;
            props.push(PropDef::Property {
                key,
                value,
                type_annotation: None,
                type_ast: None,
                span: field_span,
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace, "'}'")?;
        Ok(Expr::Object {
            properties: props,
            span: Span::new(start, self.prev_span().end),
        })
    }
}

/// `struct(a = 1, b = x)` ⇒ the record `{a: 1, b: x}`: Starlark's
/// `struct` is a record whose fields are its keyword arguments.
fn struct_literal(keywords: Vec<(String, Expr)>, span: Span) -> Expr {
    Expr::Object {
        properties: keywords
            .into_iter()
            .map(|(name, value)| PropDef::Property {
                span: value.span(),
                key: PropKey::Ident(name),
                value,
                type_annotation: None,
                type_ast: None,
            })
            .collect(),
        span,
    }
}

/// The method a slice subscript (`xs[a:b:c]`) lowers to. The Python
/// `str` and `list` method surfaces define it (`builtins::python_*_method_type`).
pub const SLICE_METHOD: &str = "__slice__";

/// `var t0 = tmp[0]; var t1 = tmp[1]; …` — the statements that bind the
/// names of a tuple target (`for k, v in …`) from the element `tmp`. Each
/// declaration keeps its name's span, so the LSP anchors the type hint on
/// the name.
fn destructure_targets(tmp: &str, targets: &[String], spans: &[Span], span: Span) -> Vec<Stmt> {
    targets
        .iter()
        .zip(spans)
        .enumerate()
        .map(|(i, (t, t_span))| Stmt::Var {
            kind: VarKind::Var,
            declarations: vec![VarDeclarator {
                name: t.clone(),
                init: Some(Expr::ComputedMember {
                    object: Box::new(Expr::Ident {
                        name: tmp.to_string(),
                        span,
                    }),
                    property: Box::new(Expr::Lit {
                        value: Literal::Number(i as f64),
                        span,
                    }),
                    span,
                }),
                type_annotation: None,
                type_ast: None,
                kind: VarKind::Var,
                span: *t_span,
            }],
            span,
        })
        .collect()
}

/// Typing special forms that are *only* type-level — assigning one is
/// always a type alias, never a value computation. Used to recognise the
/// bare `NAME = Head[…]` alias form without ambiguity. Excludes the
/// lowercase builtin generics (`list`/`dict`/…), which can be runtime
/// values; those need the explicit `type X =` / `: TypeAlias` form.
fn is_typing_special_form(name: &str) -> bool {
    matches!(
        name,
        "Literal"
            | "Optional"
            | "Union"
            | "Callable"
            | "Tuple"
            | "Type"
            | "Annotated"
            | "Final"
            | "ClassVar"
    )
}

fn aug_to_assign(op: AugOp) -> AssignOp {
    match op {
        AugOp::Add => AssignOp::AddAssign,
        AugOp::Sub => AssignOp::SubAssign,
        AugOp::Mul => AssignOp::MulAssign,
        AugOp::Div | AugOp::FloorDiv => AssignOp::DivAssign,
        AugOp::Mod => AssignOp::ModAssign,
        AugOp::Pow => AssignOp::PowAssign,
        AugOp::BitAnd => AssignOp::BitAndAssign,
        AugOp::BitOr => AssignOp::BitOrAssign,
        AugOp::BitXor => AssignOp::BitXorAssign,
        AugOp::Shl => AssignOp::LShiftAssign,
        AugOp::Shr => AssignOp::RShiftAssign,
    }
}
