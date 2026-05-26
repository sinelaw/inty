//! Recursive-descent parser for the Python subset.
//!
//! Lowers Python surface syntax onto the shared [`crate::ast`]. Python has
//! no `var`/`local`, so a bare-name assignment is also a declaration: the
//! parser tracks declared names per function scope and lowers the *first*
//! assignment to a hoisted `var` (which inty scopes to the function, like
//! Python), and later assignments to a plain assignment. Constructs the
//! type system can't express are rejected with `ParseError::Unsupported`.

use std::collections::HashSet;

use super::lexer::{AugOp, Tok};
use crate::ast::*;
use crate::error::{ParseError, Result};
use crate::span::{Span, Spanned};

pub struct Parser {
    toks: Vec<Spanned<Tok>>,
    pos: usize,
    temp: usize,
    /// One set of declared names per enclosing function scope (module is
    /// the outermost). Used to decide declaration-vs-assignment.
    scopes: Vec<HashSet<String>>,
    /// Name of the receiver parameter (`self`) while parsing a method
    /// body. When set, references to that name lower to `Expr::This`, so
    /// Python's explicit `self` maps onto inty's `this` row-polymorphism.
    self_name: Option<String>,
    /// Names of the factory functions that `class` declarations lowered
    /// to, in declaration order. Surfaced on `Program::class_brands` so
    /// inference brands each one's inferred instance row nominally.
    class_names: Vec<String>,
}

impl Parser {
    pub fn new(toks: Vec<Spanned<Tok>>) -> Self {
        Parser {
            toks,
            pos: 0,
            temp: 0,
            scopes: vec![HashSet::new()],
            self_name: None,
            class_names: Vec::new(),
        }
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

    fn declared(&self, name: &str) -> bool {
        self.scopes.iter().any(|s| s.contains(name))
    }

    fn declare(&mut self, name: &str) {
        self.scopes.last_mut().unwrap().insert(name.to_string());
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
        Ok(Program {
            statements,
            span: Span::new(start, self.prev_span().end),
            type_aliases: Vec::new(),
            class_brands: std::mem::take(&mut self.class_names),
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

    // ---- statements ----

    fn statement(&mut self) -> Result<Vec<Stmt>> {
        match self.cur() {
            Tok::Def => Ok(vec![self.def_stmt()?]),
            Tok::Class => Ok(vec![self.class_stmt()?]),
            Tok::Import => self.import_stmt(),
            Tok::From => Ok(vec![self.from_import_stmt()?]),
            Tok::If => Ok(vec![self.if_stmt()?]),
            Tok::While => Ok(vec![self.while_stmt()?]),
            Tok::For => Ok(vec![self.for_stmt()?]),
            Tok::Reserved(k) => Err(self.unsupported(&format!(
                "'{}' is not supported in the Python subset",
                k
            ))),
            _ => self.simple_line(),
        }
    }

    /// `simple_stmt (';' simple_stmt)* NEWLINE`
    fn simple_line(&mut self) -> Result<Vec<Stmt>> {
        let mut stmts = vec![self.simple_stmt()?];
        while self.eat(&Tok::Semi) {
            if self.check(&Tok::Newline) || self.at_eof() {
                break;
            }
            stmts.push(self.simple_stmt()?);
        }
        if !self.at_eof() {
            self.expect(&Tok::Newline, "newline")?;
        }
        Ok(stmts)
    }

    fn simple_stmt(&mut self) -> Result<Stmt> {
        match self.cur() {
            Tok::Pass => {
                let span = self.cur_span();
                self.advance();
                Ok(Stmt::Empty { span })
            }
            Tok::Break => {
                let span = self.cur_span();
                self.advance();
                Ok(Stmt::Break { label: None, span })
            }
            Tok::Continue => {
                let span = self.cur_span();
                self.advance();
                Ok(Stmt::Continue { label: None, span })
            }
            Tok::Return => {
                let start = self.cur_span().start;
                self.advance();
                let argument = if self.check(&Tok::Newline) || self.check(&Tok::Semi) || self.at_eof()
                {
                    None
                } else {
                    let e = self.expr()?;
                    if self.check(&Tok::Comma) {
                        return Err(self.unsupported(
                            "returning multiple values (a tuple) is not supported",
                        ));
                    }
                    Some(e)
                };
                Ok(Stmt::Return {
                    argument,
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Tok::Reserved(k) => Err(self.unsupported(&format!(
                "'{}' is not supported in the Python subset",
                k
            ))),
            _ => self.expr_or_assign(),
        }
    }

    fn expr_or_assign(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        let first = self.expr()?;

        // annotated: `target: T [= value]`
        if self.check(&Tok::Colon) {
            self.advance();
            self.skip_annotation();
            let name = self.as_simple_name(&first)?;
            let init = if self.eat(&Tok::Assign) {
                Some(self.expr()?)
            } else {
                None
            };
            return Ok(self.declare_or_assign_single(name, init, Span::new(start, self.prev_span().end)));
        }

        // augmented: `target op= value`
        if let Tok::AugAssign(op) = self.cur().clone() {
            self.advance();
            let value = self.expr()?;
            if !first.is_valid_assignment_target() {
                return Err(ParseError::InvalidAssignmentTarget { span: first.span() }.into());
            }
            let span = Span::new(start, self.prev_span().end);
            return Ok(Stmt::Expr {
                expression: Expr::Assign {
                    op: aug_to_assign(op),
                    left: Box::new(first),
                    right: Box::new(value),
                    span,
                },
                span,
            });
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
            return self.lower_tuple_assign(targets, values, Span::new(start, self.prev_span().end));
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
            let span = Span::new(start, self.prev_span().end);
            return self.lower_chained_assign(targets, value, span);
        }

        // bare expression statement
        let span = first.span();
        Ok(Stmt::Expr {
            expression: first,
            span,
        })
    }

    /// Lower `a = b = value` (every target gets `value`). Targets that are
    /// new bare names become declarations.
    fn lower_chained_assign(&mut self, targets: Vec<Expr>, value: Expr, span: Span) -> Result<Stmt> {
        if targets.len() == 1 {
            let t = &targets[0];
            if let Some(name) = self.bare_name(t) {
                return Ok(self.declare_or_assign_single(name, Some(value), span));
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
                kind: VarKind::Var,
                span,
            }],
            span,
        }];
        for t in targets {
            body.push(self.assign_target(t, Expr::Ident { name: tmp.clone(), span }, span)?);
        }
        Ok(Stmt::Block { body, span })
    }

    /// Lower `a, b = e1, e2` (matched arity), evaluating all values first.
    fn lower_tuple_assign(
        &mut self,
        targets: Vec<Expr>,
        values: Vec<Expr>,
        span: Span,
    ) -> Result<Stmt> {
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
        Ok(Stmt::Block { body, span })
    }

    /// Assign `value` to a target, declaring it first if it's a new name.
    fn assign_target(&mut self, target: Expr, value: Expr, span: Span) -> Result<Stmt> {
        if let Some(name) = self.bare_name(&target) {
            return Ok(self.declare_or_assign_single(name, Some(value), span));
        }
        if !target.is_valid_assignment_target() {
            return Err(ParseError::InvalidAssignmentTarget { span: target.span() }.into());
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

    /// First assignment to a bare name becomes a hoisted `var` declaration;
    /// subsequent ones become assignments.
    fn declare_or_assign_single(&mut self, name: String, init: Option<Expr>, span: Span) -> Stmt {
        if self.declared(&name) {
            // already declared; if there's no value it's a no-op annotation.
            match init {
                Some(value) => Stmt::Expr {
                    expression: Expr::Assign {
                        op: AssignOp::Assign,
                        left: Box::new(Expr::Ident {
                            name,
                            span,
                        }),
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
                    kind: VarKind::Var,
                    span,
                }],
                span,
            }
        }
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

    /// Skip a type annotation: tokens up to a top-level `=`, NEWLINE, or
    /// `;` (annotations are not mapped onto inty types in this subset).
    fn skip_annotation(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.cur() {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Assign | Tok::Newline | Tok::Semi | Tok::Eof if depth <= 0 => break,
                _ => {}
            }
            self.advance();
        }
    }

    // ---- compound statements ----

    fn def_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // def
        let name = self.expect_name("function name")?;
        self.expect(&Tok::LParen, "'('")?;
        let mut params = Vec::new();
        if !self.check(&Tok::RParen) {
            loop {
                if matches!(self.cur(), Tok::Star | Tok::DStar) {
                    return Err(self.unsupported("*args / **kwargs are not supported"));
                }
                let pspan = self.cur_span();
                let pname = self.expect_name("parameter name")?;
                // optional `: annotation`
                if self.eat(&Tok::Colon) {
                    self.skip_param_annotation();
                }
                if self.check(&Tok::Assign) {
                    return Err(self.unsupported("default parameter values are not supported"));
                }
                params.push(Param::new(pname, pspan));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        // optional return annotation
        if self.eat(&Tok::Arrow) {
            self.skip_annotation();
        }
        self.expect(&Tok::Colon, "':'")?;

        self.scopes.push(HashSet::new());
        for p in &params {
            self.declare(&p.name);
        }
        let body = self.suite()?;
        self.scopes.pop();

        Ok(Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation: None,
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
                            if matches!(self.cur(), Tok::Star | Tok::DStar) {
                                return Err(
                                    self.unsupported("*args / **kwargs are not supported")
                                );
                            }
                            let pspan = self.cur_span();
                            let pname = self.expect_name("parameter name")?;
                            if self.eat(&Tok::Colon) {
                                self.skip_param_annotation();
                            }
                            if self.check(&Tok::Assign) {
                                return Err(self
                                    .unsupported("default parameter values are not supported"));
                            }
                            if idx == 0 {
                                self_param = Some(pname);
                            } else {
                                params.push(Param::new(pname, pspan));
                            }
                            idx += 1;
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RParen, "')'")?;
                    if self.eat(&Tok::Arrow) {
                        self.skip_annotation();
                    }
                    self.expect(&Tok::Colon, "':'")?;

                    // Parse the body with `self` lowered to `this`.
                    let saved_self = self.self_name.take();
                    self.self_name = self_param.clone();
                    self.scopes.push(HashSet::new());
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
                            span: Span::new(mspan.start, self.prev_span().end),
                        });
                    }
                }
                Tok::Name(fname) => {
                    // Class-level field: `name [: ann] = expr`.
                    let fspan = self.cur_span();
                    self.advance();
                    if self.eat(&Tok::Colon) {
                        self.skip_annotation();
                    }
                    self.expect(&Tok::Assign, "'='")?;
                    let value = self.expr()?;
                    if !self.at_eof() {
                        self.expect(&Tok::Newline, "newline")?;
                    }
                    props.push(PropDef::Property {
                        key: PropKey::Ident(fname),
                        value,
                        type_annotation: None,
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
    fn from_import_stmt(&mut self) -> Result<Stmt> {
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

    /// Skip a parameter annotation: up to a top-level `,` or `)`.
    fn skip_param_annotation(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.cur() {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::RParen if depth == 0 => break,
                Tok::RParen => depth -= 1,
                Tok::Comma | Tok::Assign if depth <= 0 => break,
                Tok::Eof | Tok::Newline => break,
                _ => {}
            }
            self.advance();
        }
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

    fn for_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // for
        let name = self.expect_name("loop variable")?;
        if self.check(&Tok::Comma) {
            return Err(self.unsupported(
                "tuple targets in 'for' (e.g. 'for k, v in ...') are not supported",
            ));
        }
        self.expect(&Tok::In, "'in'")?;
        let right = self.expr()?;
        self.expect(&Tok::Colon, "':'")?;
        self.declare(&name);
        let span_so_far = Span::new(start, self.prev_span().end);
        let body = self.suite()?;
        Ok(Stmt::ForOf {
            left: ForInLhs::VarDecl(name, None, span_so_far),
            right,
            body,
            span: Span::new(start, self.prev_span().end),
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
    fn comparison(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let left = self.bitor()?;
        let op = match self.cur() {
            Tok::Eq => Some(BinOp::EqEqEq),
            Tok::Ne => Some(BinOp::NotEqEq),
            Tok::Lt => Some(BinOp::Lt),
            Tok::Gt => Some(BinOp::Gt),
            Tok::Le => Some(BinOp::LtEq),
            Tok::Ge => Some(BinOp::GtEq),
            Tok::Is | Tok::In => {
                return Err(self.unsupported("'is' / 'in' comparisons are not supported"))
            }
            _ => None,
        };
        let Some(op) = op else { return Ok(left) };
        self.advance();
        let right = self.bitor()?;
        // reject chained comparisons
        if matches!(
            self.cur(),
            Tok::Eq | Tok::Ne | Tok::Lt | Tok::Gt | Tok::Le | Tok::Ge | Tok::Is | Tok::In
        ) {
            return Err(self.unsupported(
                "chained comparisons (e.g. 'a < b < c') are not supported; use 'and'",
            ));
        }
        Ok(Expr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
            span: Span::new(start, self.prev_span().end),
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
        self.left_assoc(&[(Tok::Shl, BinOp::LShift), (Tok::Shr, BinOp::RShift)], Self::arith)
    }

    fn arith(&mut self) -> Result<Expr> {
        self.left_assoc(&[(Tok::Plus, BinOp::Add), (Tok::Minus, BinOp::Sub)], Self::term)
    }

    fn term(&mut self) -> Result<Expr> {
        self.left_assoc(
            &[
                (Tok::Star, BinOp::Mul),
                (Tok::Slash, BinOp::Div),
                (Tok::DSlash, BinOp::Div),
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
        loop {
            let Some((_, op)) = ops.iter().find(|(t, _)| self.check(t)) else {
                break;
            };
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
                    let index = self.expr()?;
                    if self.check(&Tok::Colon) {
                        return Err(self.unsupported("slicing is not supported"));
                    }
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
                    let arguments = self.call_args()?;
                    e = Expr::Call {
                        callee: Box::new(e),
                        arguments,
                        span: Span::new(start, self.prev_span().end),
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn call_args(&mut self) -> Result<Vec<Expr>> {
        let mut args = Vec::new();
        if self.check(&Tok::RParen) {
            self.advance();
            return Ok(args);
        }
        loop {
            if matches!(self.cur(), Tok::Star | Tok::DStar) {
                return Err(self.unsupported("argument unpacking (*/**) is not supported"));
            }
            // reject keyword args `name=value`
            if let Tok::Name(_) = self.cur() {
                if matches!(self.toks.get(self.pos + 1).map(|s| &s.value), Some(Tok::Assign)) {
                    return Err(self.unsupported("keyword arguments are not supported"));
                }
            }
            args.push(self.expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
            if self.check(&Tok::RParen) {
                break;
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        Ok(args)
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
                if self.check(&Tok::RParen) {
                    return Err(self.unsupported("the empty tuple '()' is not supported"));
                }
                let inner = self.expr()?;
                if self.check(&Tok::Comma) {
                    return Err(self.unsupported("tuples are not supported"));
                }
                self.expect(&Tok::RParen, "')'")?;
                Ok(inner)
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
            elements.push(Some(self.expr()?));
            if self.check(&Tok::For) {
                return Err(self.unsupported("list comprehensions are not supported"));
            }
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

    fn dict(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        self.advance(); // {
        let mut props = Vec::new();
        while !self.check(&Tok::RBrace) {
            let field_span = self.cur_span();
            let key = match self.cur().clone() {
                Tok::Str(s) => {
                    self.advance();
                    PropKey::String(s)
                }
                Tok::Number(n) => {
                    self.advance();
                    PropKey::Number(n)
                }
                _ => {
                    return Err(self.unsupported(
                        "dict keys must be string or number literals (or this is a set literal, \
                         which is unsupported)",
                    ))
                }
            };
            self.expect(&Tok::Colon, "':' in dict")?;
            let value = self.expr()?;
            props.push(PropDef::Property {
                key,
                value,
                type_annotation: None,
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
