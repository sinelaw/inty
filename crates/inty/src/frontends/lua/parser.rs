//! Recursive-descent parser for the Lua subset.
//!
//! Lowers Lua surface syntax onto the shared [`crate::ast`]. Constructs
//! that the type system can't express cleanly are rejected with a
//! `ParseError::Unsupported` carrying a span and a short reason, rather
//! than mis-typed. See the module docs in `mod.rs` for the subset.

use super::lexer::Tok;
use crate::ast::*;
use crate::error::{ParseError, Result};
use crate::span::{Span, Spanned};

pub struct Parser {
    toks: Vec<Spanned<Tok>>,
    pos: usize,
    temp: usize,
}

impl Parser {
    pub fn new(toks: Vec<Spanned<Tok>>) -> Self {
        Parser {
            toks,
            pos: 0,
            temp: 0,
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
        format!("$lua${}", n)
    }

    // ---- program / blocks ----

    pub fn parse_program(&mut self) -> Result<Program> {
        let start = self.cur_span().start;
        let statements = self.block()?;
        if !self.at_eof() {
            return Err(self.unexpected("end of input"));
        }
        let end = self.prev_span().end;
        Ok(Program {
            statements,
            span: Span::new(start, end),
            type_aliases: Vec::new(),
            class_brands: Vec::new(),
            language: crate::ast::SourceLanguage::Lua,
        })
    }

    /// A block runs until a block terminator (`end`, `else`, `elseif`,
    /// `until`) or EOF. A `return` may only appear as the last statement.
    fn block(&mut self) -> Result<Vec<Stmt>> {
        let mut out = Vec::new();
        loop {
            if self.is_block_end() {
                break;
            }
            if self.check(&Tok::Return) {
                out.push(self.return_stmt()?);
                // `return` is a block terminator in Lua.
                break;
            }
            let s = self.statement()?;
            // skip pure Empty (from `;`)
            if !matches!(s, Stmt::Empty { .. }) {
                out.push(s);
            }
        }
        Ok(out)
    }

    fn is_block_end(&self) -> bool {
        matches!(
            self.cur(),
            Tok::End | Tok::Else | Tok::Elseif | Tok::Until | Tok::Eof
        )
    }

    fn block_as_stmt(&mut self) -> Result<Box<Stmt>> {
        let start = self.cur_span().start;
        let body = self.block()?;
        let end = self.prev_span().end;
        Ok(Box::new(Stmt::Block {
            body,
            span: Span::new(start, end),
        }))
    }

    // ---- statements ----

    fn statement(&mut self) -> Result<Stmt> {
        match self.cur() {
            Tok::Semi => {
                let span = self.cur_span();
                self.advance();
                Ok(Stmt::Empty { span })
            }
            Tok::Local => self.local_stmt(),
            Tok::Function => self.function_stmt(),
            Tok::If => self.if_stmt(),
            Tok::While => self.while_stmt(),
            Tok::Repeat => self.repeat_stmt(),
            Tok::For => self.for_stmt(),
            Tok::Do => {
                let start = self.cur_span().start;
                self.advance();
                let body = self.block()?;
                self.expect(&Tok::End, "'end'")?;
                Ok(Stmt::Block {
                    body,
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Tok::Break => {
                let span = self.cur_span();
                self.advance();
                Ok(Stmt::Break { label: None, span })
            }
            Tok::Return => self.return_stmt(),
            Tok::DColon => Err(self.unsupported("labels / goto are not supported")),
            _ => self.expr_or_assign_stmt(),
        }
    }

    fn return_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.expect(&Tok::Return, "'return'")?;
        // optional expression list
        let argument = if self.is_block_end() || self.check(&Tok::Semi) {
            None
        } else {
            let first = self.expr()?;
            if self.check(&Tok::Comma) {
                return Err(self.unsupported(
                    "multiple return values are not supported; return a single value",
                ));
            }
            Some(first)
        };
        self.eat(&Tok::Semi);
        Ok(Stmt::Return {
            argument,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn local_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // local
        if self.check(&Tok::Function) {
            self.advance();
            let name = self.expect_name("function name")?;
            let (params, body) = self.func_body(false)?;
            return Ok(Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation: None,
                return_type_ast: None,
                span: Span::new(start, self.prev_span().end),
            });
        }
        // local namelist [= exprlist]
        let mut names = vec![self.expect_name("variable name")?];
        while self.eat(&Tok::Comma) {
            names.push(self.expect_name("variable name")?);
        }
        let inits = if self.eat(&Tok::Assign) {
            Some(self.expr_list()?)
        } else {
            None
        };
        self.make_var_decls(
            VarKind::Let,
            names,
            inits,
            Span::new(start, self.prev_span().end),
        )
    }

    fn make_var_decls(
        &self,
        kind: VarKind,
        names: Vec<String>,
        inits: Option<Vec<Expr>>,
        span: Span,
    ) -> Result<Stmt> {
        let declarations = match inits {
            None => names
                .into_iter()
                .map(|name| VarDeclarator {
                    name,
                    init: None,
                    type_annotation: None,
                    type_ast: None,
                    kind,
                    span,
                })
                .collect(),
            Some(exprs) => {
                if exprs.len() != names.len() {
                    return Err(ParseError::Unsupported {
                        feature: "multiple-value binding (the name and value counts must match; \
                                  multi-return / nil-padding is not supported)"
                            .to_string(),
                        span,
                    }
                    .into());
                }
                names
                    .into_iter()
                    .zip(exprs)
                    .map(|(name, e)| VarDeclarator {
                        name,
                        init: Some(e),
                        type_annotation: None,
                        type_ast: None,
                        kind,
                        span,
                    })
                    .collect()
            }
        };
        Ok(Stmt::Var {
            kind,
            declarations,
            span,
        })
    }

    fn function_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // function
                        // funcname: Name {'.' Name} [':' Name]
        let first = self.expect_name("function name")?;
        let name_span = self.prev_span();
        let mut target = Expr::Ident {
            name: first.clone(),
            span: name_span,
        };
        let mut dotted = false;
        let mut is_method = false;
        loop {
            if self.eat(&Tok::Dot) {
                let prop = self.expect_name("field name")?;
                target = Expr::Member {
                    object: Box::new(target),
                    property: prop,
                    span: Span::new(start, self.prev_span().end),
                };
                dotted = true;
            } else if self.eat(&Tok::Colon) {
                let prop = self.expect_name("method name")?;
                target = Expr::Member {
                    object: Box::new(target),
                    property: prop,
                    span: Span::new(start, self.prev_span().end),
                };
                is_method = true;
                break;
            } else {
                break;
            }
        }
        let (params, body) = self.func_body(is_method)?;
        let span = Span::new(start, self.prev_span().end);
        if !dotted && !is_method {
            return Ok(Stmt::FunctionDecl {
                name: first,
                params,
                body,
                type_annotation: None,
                return_type_ast: None,
                span,
            });
        }
        // `function t.k(...)` / `function t:m(...)` desugar to assignment.
        let func = Expr::Function {
            name: None,
            params,
            body,
            type_annotation: None,
            span,
        };
        Ok(Stmt::Expr {
            expression: Expr::Assign {
                op: AssignOp::Assign,
                left: Box::new(target),
                right: Box::new(func),
                span,
            },
            span,
        })
    }

    /// Parse `(params) block end`. When `is_method`, a leading `self`
    /// parameter is injected (Lua's `:` sugar).
    fn func_body(&mut self, is_method: bool) -> Result<(Vec<Param>, Box<Stmt>)> {
        self.expect(&Tok::LParen, "'('")?;
        let mut params = Vec::new();
        if is_method {
            params.push(Param::new("self", self.cur_span()));
        }
        if !self.check(&Tok::RParen) {
            loop {
                if self.check(&Tok::Ellipsis) {
                    return Err(self.unsupported("varargs ('...') are not supported"));
                }
                let span = self.cur_span();
                let name = self.expect_name("parameter name")?;
                params.push(Param::new(name, span));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        let body = self.block_as_stmt()?;
        self.expect(&Tok::End, "'end'")?;
        Ok((params, body))
    }

    fn if_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // if
        let test = self.expr()?;
        self.expect(&Tok::Then, "'then'")?;
        let consequent = self.block_as_stmt()?;
        let alternate = self.if_tail(start)?;
        self.expect(&Tok::End, "'end'")?;
        Ok(Stmt::If {
            test,
            consequent,
            alternate,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse the `elseif`/`else` tail of an `if`, building nested `If`s.
    /// Does not consume the closing `end`.
    fn if_tail(&mut self, start: usize) -> Result<Option<Box<Stmt>>> {
        if self.eat(&Tok::Elseif) {
            let test = self.expr()?;
            self.expect(&Tok::Then, "'then'")?;
            let consequent = self.block_as_stmt()?;
            let alternate = self.if_tail(start)?;
            Ok(Some(Box::new(Stmt::If {
                test,
                consequent,
                alternate,
                span: Span::new(start, self.prev_span().end),
            })))
        } else if self.eat(&Tok::Else) {
            Ok(Some(self.block_as_stmt()?))
        } else {
            Ok(None)
        }
    }

    fn while_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance();
        let test = self.expr()?;
        self.expect(&Tok::Do, "'do'")?;
        let body = self.block_as_stmt()?;
        self.expect(&Tok::End, "'end'")?;
        Ok(Stmt::While {
            test,
            body,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn repeat_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance();
        let body = self.block_as_stmt()?;
        self.expect(&Tok::Until, "'until'")?;
        let cond = self.expr()?;
        // `repeat B until c` ≡ do B while (not c)
        let span = Span::new(start, self.prev_span().end);
        let test = Expr::Unary {
            op: UnaryOp::Not,
            argument: Box::new(cond),
            span,
        };
        Ok(Stmt::DoWhile { body, test, span })
    }

    fn for_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        self.advance(); // for
        let name = self.expect_name("loop variable")?;
        if !self.check(&Tok::Assign) {
            // generic for (`for k,v in ...`) — not expressible cleanly.
            return Err(self.unsupported(
                "generic 'for ... in' is not supported; use a numeric 'for' or a 'while' loop",
            ));
        }
        self.advance(); // =
        let from = self.expr()?;
        self.expect(&Tok::Comma, "',' in numeric for")?;
        let to = self.expr()?;
        let step = if self.eat(&Tok::Comma) {
            Some(self.expr()?)
        } else {
            None
        };
        self.expect(&Tok::Do, "'do'")?;
        let body = self.block_as_stmt()?;
        self.expect(&Tok::End, "'end'")?;
        let span = Span::new(start, self.prev_span().end);

        // Desugar `for i = a, b[, s] do body end` to a C-style for.
        let descending = matches!(
            &step,
            Some(Expr::Unary {
                op: UnaryOp::Neg,
                ..
            })
        );
        let cmp = if descending { BinOp::GtEq } else { BinOp::LtEq };
        let var = Expr::Ident {
            name: name.clone(),
            span,
        };
        let test = Expr::Binary {
            op: cmp,
            left: Box::new(var.clone()),
            right: Box::new(to),
            span,
        };
        let step_expr = step.unwrap_or(Expr::Lit {
            value: Literal::Number(1.0),
            span,
        });
        let update = Expr::Assign {
            op: AssignOp::AddAssign,
            left: Box::new(var),
            right: Box::new(step_expr),
            span,
        };
        let init = ForInit::VarDecl(vec![VarDeclarator {
            name,
            init: Some(from),
            type_annotation: None,
            type_ast: None,
            kind: VarKind::Let,
            span,
        }]);
        Ok(Stmt::For {
            init: Some(init),
            test: Some(test),
            update: Some(update),
            body,
            span,
        })
    }

    fn expr_or_assign_stmt(&mut self) -> Result<Stmt> {
        let start = self.cur_span().start;
        let first = self.suffixed_expr()?;
        if !self.check(&Tok::Assign) && !self.check(&Tok::Comma) {
            // must be a call to be a valid statement
            if !matches!(first, Expr::Call { .. }) {
                return Err(ParseError::Unsupported {
                    feature: "expression statements must be function calls".to_string(),
                    span: first.span(),
                }
                .into());
            }
            let span = first.span();
            return Ok(Stmt::Expr {
                expression: first,
                span,
            });
        }
        // assignment: collect targets
        let mut targets = vec![first];
        while self.eat(&Tok::Comma) {
            targets.push(self.suffixed_expr()?);
        }
        self.expect(&Tok::Assign, "'='")?;
        let values = self.expr_list()?;
        let span = Span::new(start, self.prev_span().end);
        for t in &targets {
            if !t.is_valid_assignment_target() {
                return Err(ParseError::InvalidAssignmentTarget { span: t.span() }.into());
            }
        }
        self.lower_assignment(targets, values, span)
    }

    fn lower_assignment(
        &mut self,
        targets: Vec<Expr>,
        values: Vec<Expr>,
        span: Span,
    ) -> Result<Stmt> {
        if targets.len() == 1 && values.len() == 1 {
            let mut values = values;
            let mut targets = targets;
            return Ok(Stmt::Expr {
                expression: Expr::Assign {
                    op: AssignOp::Assign,
                    left: Box::new(targets.pop().unwrap()),
                    right: Box::new(values.pop().unwrap()),
                    span,
                },
                span,
            });
        }
        if targets.len() != values.len() {
            return Err(ParseError::Unsupported {
                feature: "multiple assignment requires equal numbers of targets and values"
                    .to_string(),
                span,
            }
            .into());
        }
        // Evaluate all RHS into temps first (Lua semantics), then assign.
        let mut body = Vec::new();
        let mut temps = Vec::new();
        for v in values {
            let t = self.fresh_temp();
            body.push(Stmt::Var {
                kind: VarKind::Let,
                declarations: vec![VarDeclarator {
                    name: t.clone(),
                    init: Some(v),
                    type_annotation: None,
                    type_ast: None,
                    kind: VarKind::Let,
                    span,
                }],
                span,
            });
            temps.push(t);
        }
        for (target, t) in targets.into_iter().zip(temps) {
            body.push(Stmt::Expr {
                expression: Expr::Assign {
                    op: AssignOp::Assign,
                    left: Box::new(target),
                    right: Box::new(Expr::Ident { name: t, span }),
                    span,
                },
                span,
            });
        }
        Ok(Stmt::Block { body, span })
    }

    fn expr_list(&mut self) -> Result<Vec<Expr>> {
        let mut out = vec![self.expr()?];
        while self.eat(&Tok::Comma) {
            out.push(self.expr()?);
        }
        Ok(out)
    }

    // ---- expressions (precedence climbing) ----

    fn expr(&mut self) -> Result<Expr> {
        self.binary(1)
    }

    /// Returns `(BinOp, left_bp, right_bp)` for a binary operator token.
    fn binop_info(t: &Tok) -> Option<(BinOp, u8, u8)> {
        Some(match t {
            Tok::Or => (BinOp::Or, 1, 2),
            Tok::And => (BinOp::And, 2, 3),
            Tok::Lt => (BinOp::Lt, 3, 4),
            Tok::Gt => (BinOp::Gt, 3, 4),
            Tok::Le => (BinOp::LtEq, 3, 4),
            Tok::Ge => (BinOp::GtEq, 3, 4),
            Tok::Ne => (BinOp::NotEqEq, 3, 4),
            Tok::Eq => (BinOp::EqEqEq, 3, 4),
            Tok::Pipe => (BinOp::BitOr, 4, 5),
            Tok::Tilde => (BinOp::BitXor, 5, 6),
            Tok::Amp => (BinOp::BitAnd, 6, 7),
            Tok::Shl => (BinOp::LShift, 7, 8),
            Tok::Shr => (BinOp::RShift, 7, 8),
            // `..` is right-associative; mapped to `+` (string concat via Plus).
            Tok::Concat => (BinOp::Add, 8, 8),
            Tok::Plus => (BinOp::Add, 9, 10),
            Tok::Minus => (BinOp::Sub, 9, 10),
            Tok::Star => (BinOp::Mul, 10, 11),
            Tok::Slash => (BinOp::Div, 10, 11),
            // floor division collapses to `/` in this subset.
            Tok::DSlash => (BinOp::Div, 10, 11),
            Tok::Percent => (BinOp::Mod, 10, 11),
            _ => return None,
        })
    }

    fn binary(&mut self, min_bp: u8) -> Result<Expr> {
        let start = self.cur_span().start;
        let mut left = self.unary()?;
        while let Some((op, lbp, rbp)) = Self::binop_info(self.cur()) {
            if lbp < min_bp {
                break;
            }
            self.advance();
            let right = self.binary(rbp)?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
                span: Span::new(start, self.prev_span().end),
            };
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        // `#x` (length) lowers to a `.length` member read.
        if self.check(&Tok::Hash) {
            self.advance();
            let argument = Box::new(self.unary()?);
            return Ok(Expr::Member {
                object: argument,
                property: "length".to_string(),
                span: Span::new(start, self.prev_span().end),
            });
        }
        let op = match self.cur() {
            Tok::Not => Some(UnaryOp::Not),
            Tok::Minus => Some(UnaryOp::Neg),
            Tok::Tilde => Some(UnaryOp::BitNot),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let argument = Box::new(self.unary()?);
            let span = Span::new(start, self.prev_span().end);
            return Ok(Expr::Unary { op, argument, span });
        }
        self.pow()
    }

    fn pow(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let base = self.suffixed_expr()?;
        if self.check(&Tok::Caret) {
            self.advance();
            // right operand may itself carry a unary; right-associative.
            let exp = self.unary()?;
            return Ok(Expr::Binary {
                op: BinOp::Pow,
                left: Box::new(base),
                right: Box::new(exp),
                span: Span::new(start, self.prev_span().end),
            });
        }
        Ok(base)
    }

    /// Primary expression followed by any number of suffixes:
    /// `.name`, `[expr]`, `(args)`, `:name args`, string/table call sugar.
    fn suffixed_expr(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        let mut e = self.primary()?;
        loop {
            match self.cur() {
                Tok::Dot => {
                    self.advance();
                    let property = self.expect_name("field name")?;
                    e = Expr::Member {
                        object: Box::new(e),
                        property,
                        span: Span::new(start, self.prev_span().end),
                    };
                }
                Tok::LBracket => {
                    self.advance();
                    let index = self.expr()?;
                    self.expect(&Tok::RBracket, "']'")?;
                    let span = Span::new(start, self.prev_span().end);
                    // A string-literal key (`t["name"]`) is a field access,
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
                Tok::Colon => {
                    self.advance();
                    let method = self.expect_name("method name")?;
                    let callee = Expr::Member {
                        object: Box::new(e),
                        property: method,
                        span: Span::new(start, self.prev_span().end),
                    };
                    let arguments = self.call_args()?;
                    e = Expr::Call {
                        callee: Box::new(callee),
                        arguments,
                        keywords: vec![],
                        span: Span::new(start, self.prev_span().end),
                    };
                }
                Tok::LParen | Tok::LBrace | Tok::Str(_) => {
                    let arguments = self.call_args()?;
                    e = Expr::Call {
                        callee: Box::new(e),
                        arguments,
                        keywords: vec![],
                        span: Span::new(start, self.prev_span().end),
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    /// Call arguments: `(exprlist)`, a single table `{...}`, or a single
    /// string literal (Lua's `f"x"` / `f{...}` sugar).
    fn call_args(&mut self) -> Result<Vec<Expr>> {
        match self.cur().clone() {
            Tok::LParen => {
                self.advance();
                if self.eat(&Tok::RParen) {
                    return Ok(Vec::new());
                }
                let args = self.expr_list()?;
                self.expect(&Tok::RParen, "')'")?;
                Ok(args)
            }
            Tok::LBrace => Ok(vec![self.table()?]),
            Tok::Str(s) => {
                let span = self.cur_span();
                self.advance();
                Ok(vec![Expr::Lit {
                    value: Literal::String(s),
                    span,
                }])
            }
            _ => Err(self.unexpected("call arguments")),
        }
    }

    fn primary(&mut self) -> Result<Expr> {
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
            Tok::Nil => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Null,
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
            Tok::Name(name) => {
                self.advance();
                Ok(Expr::Ident { name, span })
            }
            Tok::LParen => {
                self.advance();
                let inner = self.expr()?;
                self.expect(&Tok::RParen, "')'")?;
                Ok(inner)
            }
            Tok::LBrace => self.table(),
            Tok::Function => {
                let start = span.start;
                self.advance();
                let (params, body) = self.func_body(false)?;
                Ok(Expr::Function {
                    name: None,
                    params,
                    body,
                    type_annotation: None,
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Tok::Ellipsis => Err(self.unsupported("varargs ('...') are not supported")),
            _ => Err(self.unexpected("an expression")),
        }
    }

    /// Table constructor. A table is either an array (all positional
    /// fields), a record/map (all keyed fields), or empty — mixing the two
    /// is rejected, matching the no-mixing discipline the type system
    /// needs.
    fn table(&mut self) -> Result<Expr> {
        let start = self.cur_span().start;
        self.expect(&Tok::LBrace, "'{'")?;
        let mut elements: Vec<Option<Expr>> = Vec::new();
        let mut props: Vec<PropDef> = Vec::new();
        while !self.check(&Tok::RBrace) {
            let field_span = self.cur_span();
            if self.check(&Tok::LBracket) {
                // [key] = value
                self.advance();
                let key_expr = self.expr()?;
                self.expect(&Tok::RBracket, "']'")?;
                self.expect(&Tok::Assign, "'=' in table field")?;
                let value = self.expr()?;
                let key = match key_expr {
                    Expr::Lit {
                        value: Literal::String(s),
                        ..
                    } => PropKey::String(s),
                    Expr::Lit {
                        value: Literal::Number(n),
                        ..
                    } => PropKey::Number(n),
                    _ => {
                        return Err(ParseError::Unsupported {
                            feature: "computed table keys must be string or number literals"
                                .to_string(),
                            span: field_span,
                        }
                        .into())
                    }
                };
                props.push(PropDef::Property {
                    key,
                    value,
                    type_annotation: None,
                    span: field_span,
                });
            } else if matches!(self.cur(), Tok::Name(_)) && self.peek_is_assign() {
                // name = value
                let key = self.expect_name("field name")?;
                self.expect(&Tok::Assign, "'='")?;
                let value = self.expr()?;
                props.push(PropDef::Property {
                    key: PropKey::Ident(key),
                    value,
                    type_annotation: None,
                    span: field_span,
                });
            } else {
                // positional element
                let value = self.expr()?;
                elements.push(Some(value));
            }
            if !self.eat(&Tok::Comma) && !self.eat(&Tok::Semi) {
                break;
            }
        }
        self.expect(&Tok::RBrace, "'}'")?;
        let span = Span::new(start, self.prev_span().end);
        match (elements.is_empty(), props.is_empty()) {
            (true, true) => Ok(Expr::Object {
                properties: Vec::new(),
                span,
            }),
            (false, true) => Ok(Expr::Array { elements, span }),
            (true, false) => Ok(Expr::Object {
                properties: props,
                span,
            }),
            (false, false) => Err(ParseError::Unsupported {
                feature: "tables that mix array entries and named fields are not supported; \
                          use one shape per table"
                    .to_string(),
                span,
            }
            .into()),
        }
    }

    fn peek_is_assign(&self) -> bool {
        matches!(
            self.toks.get(self.pos + 1).map(|s| &s.value),
            Some(Tok::Assign)
        )
    }
}
