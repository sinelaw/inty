//! Indentation-aware lexer for the Python subset.
//!
//! Produces a flat token stream with explicit `Newline`, `Indent` and
//! `Dedent` tokens (the off-side rule), plus implicit line-joining inside
//! brackets. Tabs for indentation are rejected to keep column arithmetic
//! unambiguous.

use crate::error::{ParseError, Result};
use crate::span::{Span, Spanned};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Number(f64),
    Str(String),
    Name(String),
    // keywords we handle
    And,
    Or,
    Not,
    If,
    Elif,
    Else,
    While,
    For,
    In,
    Def,
    Return,
    Pass,
    Break,
    Continue,
    True,
    False,
    None,
    Lambda,
    Is,
    /// A reserved word we recognise but deliberately don't support; the
    /// parser turns it into a clear `Unsupported` diagnostic.
    Reserved(String),
    // operators
    Plus,
    Minus,
    Star,
    Slash,
    DSlash,
    Percent,
    DStar,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Assign,
    AugAssign(AugOp),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Dot,
    Semi,
    Arrow,
    // layout
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AugOp {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

impl Tok {
    pub fn describe(&self) -> String {
        match self {
            Tok::Number(n) => format!("number {}", n),
            Tok::Str(_) => "string".to_string(),
            Tok::Name(n) => format!("name '{}'", n),
            Tok::Newline => "newline".to_string(),
            Tok::Indent => "indent".to_string(),
            Tok::Dedent => "dedent".to_string(),
            Tok::Eof => "end of input".to_string(),
            other => format!("{:?}", other),
        }
    }

    fn keyword(s: &str) -> Option<Tok> {
        Some(match s {
            "and" => Tok::And,
            "or" => Tok::Or,
            "not" => Tok::Not,
            "if" => Tok::If,
            "elif" => Tok::Elif,
            "else" => Tok::Else,
            "while" => Tok::While,
            "for" => Tok::For,
            "in" => Tok::In,
            "def" => Tok::Def,
            "return" => Tok::Return,
            "pass" => Tok::Pass,
            "break" => Tok::Break,
            "continue" => Tok::Continue,
            "True" => Tok::True,
            "False" => Tok::False,
            "None" => Tok::None,
            "lambda" => Tok::Lambda,
            "is" => Tok::Is,
            "class" | "import" | "from" | "as" | "with" | "try" | "except" | "finally"
            | "raise" | "global" | "nonlocal" | "del" | "assert" | "yield" | "async"
            | "await" => Tok::Reserved(s.to_string()),
            _ => return None,
        })
    }
}

struct Lexer {
    chars: Vec<(usize, char)>,
    len: usize,
    pos: usize,
    indents: Vec<usize>,
    bracket_depth: usize,
    out: Vec<Spanned<Tok>>,
}

impl Lexer {
    fn new(source: &str) -> Self {
        Lexer {
            chars: source.char_indices().collect(),
            len: source.len(),
            pos: 0,
            indents: vec![0],
            bracket_depth: 0,
            out: Vec::new(),
        }
    }

    fn byte_at(&self, idx: usize) -> usize {
        self.chars.get(idx).map(|(b, _)| *b).unwrap_or(self.len)
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).map(|(_, c)| *c)
    }

    fn peek2(&self) -> Option<char> {
        self.chars.get(self.pos + 1).map(|(_, c)| *c)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn emit(&mut self, tok: Tok, start: usize) {
        let span = Span::new(self.byte_at(start), self.byte_at(self.pos));
        self.out.push(Spanned::new(tok, span));
    }

    fn emit_here(&mut self, tok: Tok) {
        let b = self.byte_at(self.pos);
        self.out.push(Spanned::new(tok, Span::new(b, b)));
    }

    fn tokenize(mut self) -> Result<Vec<Spanned<Tok>>> {
        let mut at_line_start = true;
        loop {
            if at_line_start && self.bracket_depth == 0 {
                if self.handle_line_start()? {
                    // blank / comment-only line consumed; stay at line start
                    continue;
                }
                at_line_start = false;
            }

            match self.peek() {
                None => break,
                Some(' ') | Some('\t') => {
                    self.bump();
                }
                Some('#') => {
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                Some('\\') if self.peek2() == Some('\n') => {
                    self.bump();
                    self.bump();
                }
                Some('\n') => {
                    self.bump();
                    if self.bracket_depth == 0 {
                        self.emit_here(Tok::Newline);
                        at_line_start = true;
                    }
                }
                Some(_) => self.lex_token()?,
            }
        }

        // end of file: close the last logical line and all open blocks.
        if !matches!(self.out.last().map(|s| &s.value), Some(Tok::Newline) | None) {
            self.emit_here(Tok::Newline);
        }
        while self.indents.len() > 1 {
            self.indents.pop();
            self.emit_here(Tok::Dedent);
        }
        self.emit_here(Tok::Eof);
        Ok(self.out)
    }

    /// At the physical start of a line (outside brackets): skip blank and
    /// comment-only lines, otherwise measure indentation and emit
    /// `Indent`/`Dedent`. Returns `true` if the line was blank/comment and
    /// fully consumed.
    fn handle_line_start(&mut self) -> Result<bool> {
        let mut col = 0usize;
        let probe_start = self.pos;
        loop {
            match self.peek() {
                Some(' ') => {
                    col += 1;
                    self.bump();
                }
                Some('\t') => {
                    return Err(ParseError::Unsupported {
                        feature: "tabs for indentation are not supported; use spaces".to_string(),
                        span: Span::new(self.byte_at(self.pos), self.byte_at(self.pos + 1)),
                    }
                    .into())
                }
                _ => break,
            }
        }
        match self.peek() {
            None => {
                // end of input: let the main loop observe EOF and stop.
                // (Returning `true` here would spin, since there's nothing
                // left to consume.)
                return Ok(false);
            }
            Some('\n') => {
                // blank line: consume the newline
                self.bump();
                return Ok(true);
            }
            Some('#') => {
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        break;
                    }
                    self.bump();
                }
                return Ok(true);
            }
            _ => {}
        }
        let top = *self.indents.last().unwrap();
        if col > top {
            self.indents.push(col);
            self.emit(Tok::Indent, probe_start);
        } else if col < top {
            while col < *self.indents.last().unwrap() {
                self.indents.pop();
                self.emit_here(Tok::Dedent);
            }
            if col != *self.indents.last().unwrap() {
                return Err(ParseError::Unsupported {
                    feature: "inconsistent indentation".to_string(),
                    span: Span::new(self.byte_at(probe_start), self.byte_at(self.pos)),
                }
                .into());
            }
        }
        Ok(false)
    }

    fn lex_token(&mut self) -> Result<()> {
        let start = self.pos;
        let c = self.peek().unwrap();
        match c {
            '0'..='9' => self.number(start)?,
            'a'..='z' | 'A'..='Z' | '_' => self.name(start),
            '"' | '\'' => self.string(start)?,
            _ => self.operator(start)?,
        }
        Ok(())
    }

    fn number(&mut self, start: usize) -> Result<()> {
        if self.peek() == Some('0') && matches!(self.peek2(), Some('x') | Some('X')) {
            self.bump();
            self.bump();
            let s = self.pos;
            while matches!(self.peek(), Some(ch) if ch.is_ascii_hexdigit() || ch == '_') {
                self.bump();
            }
            let text: String = self.chars[s..self.pos]
                .iter()
                .map(|(_, c)| *c)
                .filter(|c| *c != '_')
                .collect();
            let v = i64::from_str_radix(&text, 16)
                .map_err(|_| self.err("malformed number", start))?;
            self.emit(Tok::Number(v as f64), start);
            return Ok(());
        }
        while matches!(self.peek(), Some(ch) if ch.is_ascii_digit() || ch == '_') {
            self.bump();
        }
        if self.peek() == Some('.') {
            self.bump();
            while matches!(self.peek(), Some(ch) if ch.is_ascii_digit() || ch == '_') {
                self.bump();
            }
        }
        if matches!(self.peek(), Some('e') | Some('E')) {
            self.bump();
            if matches!(self.peek(), Some('+') | Some('-')) {
                self.bump();
            }
            while matches!(self.peek(), Some(ch) if ch.is_ascii_digit()) {
                self.bump();
            }
        }
        let text: String = self.chars[start..self.pos]
            .iter()
            .map(|(_, c)| *c)
            .filter(|c| *c != '_')
            .collect();
        let v: f64 = text.parse().map_err(|_| self.err("malformed number", start))?;
        self.emit(Tok::Number(v), start);
        Ok(())
    }

    fn name(&mut self, start: usize) {
        while matches!(self.peek(), Some(ch) if ch.is_alphanumeric() || ch == '_') {
            self.bump();
        }
        let text: String = self.chars[start..self.pos].iter().map(|(_, c)| *c).collect();
        // string prefixes like f"..." / r"..." / b"...": only the plain
        // string forms are supported; f-strings are rejected at the prefix.
        let tok = Tok::keyword(&text).unwrap_or(Tok::Name(text));
        self.emit(tok, start);
    }

    fn string(&mut self, start: usize) -> Result<()> {
        let quote = self.bump().unwrap();
        // triple-quoted?
        let triple = self.peek() == Some(quote) && self.peek2() == Some(quote);
        if triple {
            self.bump();
            self.bump();
        }
        let mut s = String::new();
        loop {
            match self.bump() {
                Some('\\') => {
                    let e = self.bump().ok_or_else(|| self.err("unterminated string", start))?;
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '\\' => '\\',
                        '\'' => '\'',
                        '"' => '"',
                        '0' => '\0',
                        other => other,
                    });
                }
                Some(c) if c == quote => {
                    if triple {
                        if self.peek() == Some(quote) && self.peek2() == Some(quote) {
                            self.bump();
                            self.bump();
                            break;
                        }
                        s.push(c);
                    } else {
                        break;
                    }
                }
                Some('\n') if !triple => return Err(self.err("unterminated string", start)),
                Some(c) => s.push(c),
                None => return Err(self.err("unterminated string", start)),
            }
        }
        self.emit(Tok::Str(s), start);
        Ok(())
    }

    fn operator(&mut self, start: usize) -> Result<()> {
        let c = self.bump().unwrap();
        let tok = match c {
            '+' => self.maybe_aug(Tok::Plus, AugOp::Add),
            '-' => {
                if self.peek() == Some('>') {
                    self.bump();
                    Tok::Arrow
                } else {
                    self.maybe_aug(Tok::Minus, AugOp::Sub)
                }
            }
            '*' => {
                if self.peek() == Some('*') {
                    self.bump();
                    self.maybe_aug(Tok::DStar, AugOp::Pow)
                } else {
                    self.maybe_aug(Tok::Star, AugOp::Mul)
                }
            }
            '/' => {
                if self.peek() == Some('/') {
                    self.bump();
                    self.maybe_aug(Tok::DSlash, AugOp::FloorDiv)
                } else {
                    self.maybe_aug(Tok::Slash, AugOp::Div)
                }
            }
            '%' => self.maybe_aug(Tok::Percent, AugOp::Mod),
            '&' => self.maybe_aug(Tok::Amp, AugOp::BitAnd),
            '|' => self.maybe_aug(Tok::Pipe, AugOp::BitOr),
            '^' => self.maybe_aug(Tok::Caret, AugOp::BitXor),
            '~' => Tok::Tilde,
            '<' => match self.peek() {
                Some('<') => {
                    self.bump();
                    self.maybe_aug(Tok::Shl, AugOp::Shl)
                }
                Some('=') => {
                    self.bump();
                    Tok::Le
                }
                _ => Tok::Lt,
            },
            '>' => match self.peek() {
                Some('>') => {
                    self.bump();
                    self.maybe_aug(Tok::Shr, AugOp::Shr)
                }
                Some('=') => {
                    self.bump();
                    Tok::Ge
                }
                _ => Tok::Gt,
            },
            '=' => {
                if self.peek() == Some('=') {
                    self.bump();
                    Tok::Eq
                } else {
                    Tok::Assign
                }
            }
            '!' => {
                if self.peek() == Some('=') {
                    self.bump();
                    Tok::Ne
                } else {
                    return Err(self.err("unexpected '!'", start));
                }
            }
            '(' => {
                self.bracket_depth += 1;
                Tok::LParen
            }
            ')' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                Tok::RParen
            }
            '[' => {
                self.bracket_depth += 1;
                Tok::LBracket
            }
            ']' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                Tok::RBracket
            }
            '{' => {
                self.bracket_depth += 1;
                Tok::LBrace
            }
            '}' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                Tok::RBrace
            }
            ',' => Tok::Comma,
            ':' => Tok::Colon,
            '.' => Tok::Dot,
            ';' => Tok::Semi,
            other => return Err(self.err(&format!("unexpected character '{}'", other), start)),
        };
        self.emit(tok, start);
        Ok(())
    }

    fn maybe_aug(&mut self, plain: Tok, aug: AugOp) -> Tok {
        if self.peek() == Some('=') {
            self.bump();
            Tok::AugAssign(aug)
        } else {
            plain
        }
    }

    fn err(&self, msg: &str, start: usize) -> crate::error::IntyError {
        ParseError::Unsupported {
            feature: msg.to_string(),
            span: Span::new(self.byte_at(start), self.byte_at(self.pos)),
        }
        .into()
    }
}

pub fn tokenize(source: &str) -> Result<Vec<Spanned<Tok>>> {
    Lexer::new(source).tokenize()
}
