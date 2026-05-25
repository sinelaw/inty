//! Hand-written lexer for the Lua subset.

use crate::error::{ParseError, Result};
use crate::span::{Span, Spanned};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    // literals
    Number(f64),
    Str(String),
    Name(String),
    // keywords
    And,
    Break,
    Do,
    Else,
    Elseif,
    End,
    False,
    For,
    Function,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,
    // symbols
    Plus,
    Minus,
    Star,
    Slash,
    DSlash,
    Percent,
    Caret,
    Hash,
    Amp,
    Tilde,
    Pipe,
    Shl,
    Shr,
    Eq,
    Ne,
    Le,
    Ge,
    Lt,
    Gt,
    Assign,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Semi,
    Colon,
    DColon,
    Comma,
    Dot,
    Concat,
    Ellipsis,
    Eof,
}

impl Tok {
    /// Human-readable description for diagnostics.
    pub fn describe(&self) -> String {
        match self {
            Tok::Number(n) => format!("number {}", n),
            Tok::Str(_) => "string".to_string(),
            Tok::Name(n) => format!("name '{}'", n),
            Tok::Eof => "end of input".to_string(),
            other => format!("{:?}", other),
        }
    }

    fn keyword(s: &str) -> Option<Tok> {
        Some(match s {
            "and" => Tok::And,
            "break" => Tok::Break,
            "do" => Tok::Do,
            "else" => Tok::Else,
            "elseif" => Tok::Elseif,
            "end" => Tok::End,
            "false" => Tok::False,
            "for" => Tok::For,
            "function" => Tok::Function,
            "if" => Tok::If,
            "in" => Tok::In,
            "local" => Tok::Local,
            "nil" => Tok::Nil,
            "not" => Tok::Not,
            "or" => Tok::Or,
            "repeat" => Tok::Repeat,
            "return" => Tok::Return,
            "then" => Tok::Then,
            "true" => Tok::True,
            "until" => Tok::Until,
            "while" => Tok::While,
            _ => return None,
        })
    }
}

struct Lexer {
    chars: Vec<(usize, char)>,
    len: usize,
    pos: usize,
}

impl Lexer {
    fn new(source: &str) -> Self {
        Lexer {
            chars: source.char_indices().collect(),
            len: source.len(),
            pos: 0,
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

    fn span_from(&self, start_idx: usize) -> Span {
        Span::new(self.byte_at(start_idx), self.byte_at(self.pos))
    }

    fn tokenize(mut self) -> Result<Vec<Spanned<Tok>>> {
        let mut out = Vec::new();
        loop {
            self.skip_trivia()?;
            let start = self.pos;
            let Some(c) = self.peek() else {
                out.push(Spanned::new(Tok::Eof, Span::new(self.len, self.len)));
                break;
            };
            let tok = match c {
                '0'..='9' => self.number()?,
                'a'..='z' | 'A'..='Z' | '_' => self.name(),
                '"' | '\'' => self.short_string()?,
                '[' if matches!(self.peek2(), Some('[')) => self.long_string()?,
                _ => self.symbol()?,
            };
            out.push(Spanned::new(tok, self.span_from(start)));
        }
        Ok(out)
    }

    fn skip_trivia(&mut self) -> Result<()> {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some('-') if matches!(self.peek2(), Some('-')) => {
                    self.bump();
                    self.bump();
                    // long comment --[[ ... ]] ?
                    if self.peek() == Some('[') && self.peek2() == Some('[') {
                        self.bump();
                        self.bump();
                        self.consume_until_long_close()?;
                    } else {
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            self.bump();
                        }
                    }
                }
                _ => return Ok(()),
            }
        }
    }

    fn consume_until_long_close(&mut self) -> Result<()> {
        loop {
            match self.bump() {
                Some(']') if self.peek() == Some(']') => {
                    self.bump();
                    return Ok(());
                }
                Some(_) => {}
                None => {
                    return Err(ParseError::Unsupported {
                        feature: "unterminated long bracket".to_string(),
                        span: Span::new(self.len, self.len),
                    }
                    .into())
                }
            }
        }
    }

    fn number(&mut self) -> Result<Tok> {
        let start = self.pos;
        // hex
        if self.peek() == Some('0') && matches!(self.peek2(), Some('x') | Some('X')) {
            self.bump();
            self.bump();
            let s = self.pos;
            while matches!(self.peek(), Some(c) if c.is_ascii_hexdigit()) {
                self.bump();
            }
            let text: String = self.chars[s..self.pos].iter().map(|(_, c)| *c).collect();
            let v = i64::from_str_radix(&text, 16).map_err(|_| self.num_err(start))?;
            return Ok(Tok::Number(v as f64));
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.bump();
        }
        if self.peek() == Some('.') {
            self.bump();
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.bump();
            }
        }
        if matches!(self.peek(), Some('e') | Some('E')) {
            self.bump();
            if matches!(self.peek(), Some('+') | Some('-')) {
                self.bump();
            }
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.bump();
            }
        }
        let text: String = self.chars[start..self.pos].iter().map(|(_, c)| *c).collect();
        let v: f64 = text.parse().map_err(|_| self.num_err(start))?;
        Ok(Tok::Number(v))
    }

    fn num_err(&self, start: usize) -> crate::error::IntyError {
        ParseError::Unsupported {
            feature: "malformed number literal".to_string(),
            span: self.span_from(start),
        }
        .into()
    }

    fn name(&mut self) -> Tok {
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.bump();
        }
        let text: String = self.chars[start..self.pos].iter().map(|(_, c)| *c).collect();
        Tok::keyword(&text).unwrap_or(Tok::Name(text))
    }

    fn short_string(&mut self) -> Result<Tok> {
        let start = self.pos;
        let quote = self.bump().unwrap();
        let mut s = String::new();
        loop {
            match self.bump() {
                Some('\\') => {
                    let e = self.bump().ok_or_else(|| self.str_err(start))?;
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '\\' => '\\',
                        '"' => '"',
                        '\'' => '\'',
                        '0' => '\0',
                        other => other,
                    });
                }
                Some(c) if c == quote => return Ok(Tok::Str(s)),
                Some('\n') | None => return Err(self.str_err(start)),
                Some(c) => s.push(c),
            }
        }
    }

    fn long_string(&mut self) -> Result<Tok> {
        // already know next two are '[' '['
        self.bump();
        self.bump();
        let mut s = String::new();
        loop {
            match self.bump() {
                Some(']') if self.peek() == Some(']') => {
                    self.bump();
                    return Ok(Tok::Str(s));
                }
                Some(c) => s.push(c),
                None => {
                    return Err(ParseError::Unsupported {
                        feature: "unterminated long string".to_string(),
                        span: Span::new(self.len, self.len),
                    }
                    .into())
                }
            }
        }
    }

    fn str_err(&self, start: usize) -> crate::error::IntyError {
        ParseError::Unsupported {
            feature: "unterminated string literal".to_string(),
            span: self.span_from(start),
        }
        .into()
    }

    fn symbol(&mut self) -> Result<Tok> {
        let start = self.pos;
        let c = self.bump().unwrap();
        let tok = match c {
            '+' => Tok::Plus,
            '-' => Tok::Minus,
            '*' => Tok::Star,
            '/' => {
                if self.peek() == Some('/') {
                    self.bump();
                    Tok::DSlash
                } else {
                    Tok::Slash
                }
            }
            '%' => Tok::Percent,
            '^' => Tok::Caret,
            '#' => Tok::Hash,
            '&' => Tok::Amp,
            '~' => {
                if self.peek() == Some('=') {
                    self.bump();
                    Tok::Ne
                } else {
                    Tok::Tilde
                }
            }
            '|' => Tok::Pipe,
            '<' => match self.peek() {
                Some('<') => {
                    self.bump();
                    Tok::Shl
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
                    Tok::Shr
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
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '{' => Tok::LBrace,
            '}' => Tok::RBrace,
            '[' => Tok::LBracket,
            ']' => Tok::RBracket,
            ';' => Tok::Semi,
            ':' => {
                if self.peek() == Some(':') {
                    self.bump();
                    Tok::DColon
                } else {
                    Tok::Colon
                }
            }
            ',' => Tok::Comma,
            '.' => {
                if self.peek() == Some('.') {
                    self.bump();
                    if self.peek() == Some('.') {
                        self.bump();
                        Tok::Ellipsis
                    } else {
                        Tok::Concat
                    }
                } else {
                    Tok::Dot
                }
            }
            other => {
                return Err(ParseError::Unsupported {
                    feature: format!("unexpected character '{}'", other),
                    span: self.span_from(start),
                }
                .into())
            }
        };
        Ok(tok)
    }
}

pub fn tokenize(source: &str) -> Result<Vec<Spanned<Tok>>> {
    Lexer::new(source).tokenize()
}
