//! Token definitions for the mquickjs lexer.

use std::fmt;

/// Source location information
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// A token with its span
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }
}

/// Token types for mquickjs
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Keywords
    Var,
    Let,
    Const,
    Function,
    Class,
    Extends,
    Super,
    Async,
    Await,
    If,
    Else,
    While,
    Do,
    For,
    In,
    Of,
    Return,
    Throw,
    Try,
    Catch,
    Finally,
    Switch,
    Case,
    Default,
    Break,
    Continue,
    New,
    Delete,
    Typeof,
    Void,
    Instanceof,
    This,
    Null,
    True,
    False,
    Import,
    Export,
    From,
    As,

    // Literals
    Number(f64),
    String(std::string::String),
    Regex {
        pattern: std::string::String,
        flags: std::string::String,
    },
    /// Template literal head: `text${
    TemplateHead(std::string::String),
    /// Template literal middle: }text${
    TemplateMiddle(std::string::String),
    /// Template literal tail: }text`
    TemplateTail(std::string::String),
    /// Template literal with no substitutions: `text`
    TemplateNoSub(std::string::String),

    // Identifier
    Ident(std::string::String),

    // Type annotation comment /*: ... */
    TypeAnnotation(std::string::String),

    // Operators
    // Arithmetic
    Plus,     // +
    Minus,    // -
    Star,     // *
    StarStar, // **
    Slash,    // /
    Percent,  // %

    // Comparison
    Lt,      // <
    Gt,      // >
    LtEq,    // <=
    GtEq,    // >=
    EqEq,    // ==
    NotEq,   // !=
    EqEqEq,  // ===
    NotEqEq, // !==

    // Logical
    And, // &&
    Or,  // ||
    Not, // !

    // Bitwise
    BitAnd,  // &
    BitOr,   // |
    BitXor,  // ^
    BitNot,  // ~
    LShift,  // <<
    RShift,  // >>
    URShift, // >>>

    // Assignment
    Eq,         // =
    PlusEq,     // +=
    MinusEq,    // -=
    StarEq,     // *=
    StarStarEq, // **=
    SlashEq,    // /=
    PercentEq,  // %=
    LShiftEq,   // <<=
    RShiftEq,   // >>=
    URShiftEq,  // >>>=
    BitAndEq,   // &=
    BitOrEq,    // |=
    BitXorEq,   // ^=

    // Increment/Decrement
    PlusPlus,   // ++
    MinusMinus, // --

    // Punctuation
    LParen,    // (
    RParen,    // )
    LBrace,    // {
    RBrace,    // }
    LBracket,  // [
    RBracket,  // ]
    Comma,     // ,
    Dot,       // .
    Semicolon, // ;
    Colon,     // :
    Question,  // ?
    FatArrow,  // =>

    // Special
    Eof,
}

impl Token {
    /// Check if this token is a keyword that can be used as an identifier in some contexts
    pub fn is_keyword(&self) -> bool {
        matches!(
            self,
            Token::Var
                | Token::Let
                | Token::Const
                | Token::Function
                | Token::Class
                | Token::Extends
                | Token::Super
                | Token::Async
                | Token::Await
                | Token::If
                | Token::Else
                | Token::While
                | Token::Do
                | Token::For
                | Token::In
                | Token::Of
                | Token::Return
                | Token::Throw
                | Token::Try
                | Token::Catch
                | Token::Finally
                | Token::Switch
                | Token::Case
                | Token::Default
                | Token::Break
                | Token::Continue
                | Token::New
                | Token::Delete
                | Token::Typeof
                | Token::Void
                | Token::Instanceof
                | Token::This
                | Token::Null
                | Token::True
                | Token::False
                | Token::Import
                | Token::Export
                | Token::From
                | Token::As
        )
    }

    /// Get the keyword for an identifier string, if any
    pub fn keyword(s: &str) -> Option<Token> {
        match s {
            "var" => Some(Token::Var),
            "let" => Some(Token::Let),
            "const" => Some(Token::Const),
            "class" => Some(Token::Class),
            "extends" => Some(Token::Extends),
            "super" => Some(Token::Super),
            "async" => Some(Token::Async),
            "await" => Some(Token::Await),
            "function" => Some(Token::Function),
            "if" => Some(Token::If),
            "else" => Some(Token::Else),
            "while" => Some(Token::While),
            "do" => Some(Token::Do),
            "for" => Some(Token::For),
            "in" => Some(Token::In),
            "of" => Some(Token::Of),
            "return" => Some(Token::Return),
            "throw" => Some(Token::Throw),
            "try" => Some(Token::Try),
            "catch" => Some(Token::Catch),
            "finally" => Some(Token::Finally),
            "switch" => Some(Token::Switch),
            "case" => Some(Token::Case),
            "default" => Some(Token::Default),
            "break" => Some(Token::Break),
            "continue" => Some(Token::Continue),
            "new" => Some(Token::New),
            "delete" => Some(Token::Delete),
            "typeof" => Some(Token::Typeof),
            "void" => Some(Token::Void),
            "instanceof" => Some(Token::Instanceof),
            "this" => Some(Token::This),
            "null" => Some(Token::Null),
            "true" => Some(Token::True),
            "false" => Some(Token::False),
            "import" => Some(Token::Import),
            "export" => Some(Token::Export),
            "from" => Some(Token::From),
            "as" => Some(Token::As),
            _ => None,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Var => write!(f, "var"),
            Token::Let => write!(f, "let"),
            Token::Const => write!(f, "const"),
            Token::Class => write!(f, "class"),
            Token::Extends => write!(f, "extends"),
            Token::Super => write!(f, "super"),
            Token::Async => write!(f, "async"),
            Token::Await => write!(f, "await"),
            Token::Function => write!(f, "function"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::Do => write!(f, "do"),
            Token::For => write!(f, "for"),
            Token::In => write!(f, "in"),
            Token::Of => write!(f, "of"),
            Token::Return => write!(f, "return"),
            Token::Throw => write!(f, "throw"),
            Token::Try => write!(f, "try"),
            Token::Catch => write!(f, "catch"),
            Token::Finally => write!(f, "finally"),
            Token::Switch => write!(f, "switch"),
            Token::Case => write!(f, "case"),
            Token::Default => write!(f, "default"),
            Token::Break => write!(f, "break"),
            Token::Continue => write!(f, "continue"),
            Token::New => write!(f, "new"),
            Token::Delete => write!(f, "delete"),
            Token::Typeof => write!(f, "typeof"),
            Token::Void => write!(f, "void"),
            Token::Instanceof => write!(f, "instanceof"),
            Token::This => write!(f, "this"),
            Token::Null => write!(f, "null"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Import => write!(f, "import"),
            Token::Export => write!(f, "export"),
            Token::From => write!(f, "from"),
            Token::As => write!(f, "as"),
            Token::Number(n) => write!(f, "{}", n),
            Token::String(s) => write!(f, "\"{}\"", s),
            Token::Regex { pattern, flags } => write!(f, "/{}/{}", pattern, flags),
            Token::TemplateHead(s) => write!(f, "`{}${{", s),
            Token::TemplateMiddle(s) => write!(f, "}}{}${{", s),
            Token::TemplateTail(s) => write!(f, "}}{}`", s),
            Token::TemplateNoSub(s) => write!(f, "`{}`", s),
            Token::Ident(s) => write!(f, "{}", s),
            Token::TypeAnnotation(s) => write!(f, "/*: {} */", s),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::StarStar => write!(f, "**"),
            Token::Slash => write!(f, "/"),
            Token::Percent => write!(f, "%"),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::LtEq => write!(f, "<="),
            Token::GtEq => write!(f, ">="),
            Token::EqEq => write!(f, "=="),
            Token::NotEq => write!(f, "!="),
            Token::EqEqEq => write!(f, "==="),
            Token::NotEqEq => write!(f, "!=="),
            Token::And => write!(f, "&&"),
            Token::Or => write!(f, "||"),
            Token::Not => write!(f, "!"),
            Token::BitAnd => write!(f, "&"),
            Token::BitOr => write!(f, "|"),
            Token::BitXor => write!(f, "^"),
            Token::BitNot => write!(f, "~"),
            Token::LShift => write!(f, "<<"),
            Token::RShift => write!(f, ">>"),
            Token::URShift => write!(f, ">>>"),
            Token::Eq => write!(f, "="),
            Token::PlusEq => write!(f, "+="),
            Token::MinusEq => write!(f, "-="),
            Token::StarEq => write!(f, "*="),
            Token::StarStarEq => write!(f, "**="),
            Token::SlashEq => write!(f, "/="),
            Token::PercentEq => write!(f, "%="),
            Token::LShiftEq => write!(f, "<<="),
            Token::RShiftEq => write!(f, ">>="),
            Token::URShiftEq => write!(f, ">>>="),
            Token::BitAndEq => write!(f, "&="),
            Token::BitOrEq => write!(f, "|="),
            Token::BitXorEq => write!(f, "^="),
            Token::PlusPlus => write!(f, "++"),
            Token::MinusMinus => write!(f, "--"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::Semicolon => write!(f, ";"),
            Token::Colon => write!(f, ":"),
            Token::Question => write!(f, "?"),
            Token::FatArrow => write!(f, "=>"),
            Token::Eof => write!(f, "<eof>"),
        }
    }
}
