//! Character-level scanner for tokenizing JavaScript source.

use super::token::{Span, Spanned, Token};
use crate::error::{LexError, Result};
use crate::parser::ast::TypeAnnotation;

/// The lexer/scanner for mquickjs source code.
pub struct Scanner<'a> {
    source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    current_pos: usize,
    /// Collected type annotations for later retrieval
    type_annotations: Vec<TypeAnnotation>,
    /// Whether the last token allows a regex to follow (for disambiguation)
    last_token_allows_regex: bool,
    /// Stack of template literal depth (for nested templates)
    /// When > 0, a `}` should be scanned as template continuation
    template_depth: usize,
    /// Most recently emitted identifier and its end position, used to
    /// attach inline `/*: T */` annotations to the name that precedes them.
    last_ident: Option<(String, usize)>,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
            current_pos: 0,
            type_annotations: Vec::new(),
            last_token_allows_regex: true, // At start of file, / is regex
            template_depth: 0,
            last_ident: None,
        }
    }

    /// Tokenize the entire source and return all tokens along with type annotations.
    pub fn tokenize(mut self) -> Result<(Vec<Spanned<Token>>, Vec<TypeAnnotation>)> {
        let mut tokens = Vec::new();

        loop {
            let token = self.next_token()?;
            let is_eof = token.value == Token::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
        }

        Ok((tokens, self.type_annotations))
    }

    /// Update regex context based on the token we just produced
    fn update_regex_context(&mut self, token: &Token) {
        // After these tokens, / is division (not regex):
        // - identifiers, numbers, strings, regex, template literals
        // - ), ], }
        // - ++, --
        // - this, true, false, null
        self.last_token_allows_regex = !matches!(
            token,
            Token::Ident(_)
                | Token::Number(_)
                | Token::String(_)
                | Token::Regex { .. }
                | Token::TemplateNoSub(_)
                | Token::TemplateTail(_)
                | Token::RParen
                | Token::RBracket
                | Token::RBrace
                | Token::PlusPlus
                | Token::MinusMinus
                | Token::This
                | Token::True
                | Token::False
                | Token::Null
        );
    }

    /// Get the next token from the source.
    pub fn next_token(&mut self) -> Result<Spanned<Token>> {
        self.skip_whitespace_and_comments()?;

        let start = self.current_pos;

        let Some((pos, ch)) = self.peek() else {
            return Ok(Spanned::new(Token::Eof, Span::new(start, start)));
        };

        let token = match ch {
            // Single-character tokens
            '(' => {
                self.advance();
                Token::LParen
            }
            ')' => {
                self.advance();
                Token::RParen
            }
            '{' => {
                self.advance();
                Token::LBrace
            }
            '}' => {
                if self.template_depth > 0 {
                    // We're inside a template literal, scan the continuation
                    self.advance(); // consume the }
                    self.scan_template_continuation()?
                } else {
                    self.advance();
                    Token::RBrace
                }
            }
            '[' => {
                self.advance();
                Token::LBracket
            }
            ']' => {
                self.advance();
                Token::RBracket
            }
            ',' => {
                self.advance();
                Token::Comma
            }
            ';' => {
                self.advance();
                Token::Semicolon
            }
            ':' => {
                self.advance();
                Token::Colon
            }
            '?' => {
                self.advance();
                Token::Question
            }
            '~' => {
                self.advance();
                Token::BitNot
            }

            // Multi-character operators
            '+' => self.scan_plus(),
            '-' => self.scan_minus(),
            '*' => self.scan_star(),
            '/' => self.scan_slash_or_regex()?,
            '%' => self.scan_percent(),
            '<' => self.scan_less_than(),
            '>' => self.scan_greater_than(),
            '=' => self.scan_equals(),
            '!' => self.scan_exclamation(),
            '&' => self.scan_ampersand(),
            '|' => self.scan_pipe(),
            '^' => self.scan_caret(),
            '.' => {
                self.advance();
                // Check for number starting with .
                if self
                    .peek()
                    .map(|(_, c)| c.is_ascii_digit())
                    .unwrap_or(false)
                {
                    let token = self.scan_number_after_dot(start)?;
                    return Ok(Spanned::new(token, Span::new(start, self.current_pos)));
                }
                Token::Dot
            }

            // Strings
            '"' | '\'' => self.scan_string()?,

            // Template literals
            '`' => self.scan_template_literal()?,

            // Numbers
            '0'..='9' => self.scan_number()?,

            // Identifiers and keywords (ASCII or Unicode)
            'a'..='z' | 'A'..='Z' | '_' | '$' => self.scan_identifier(),

            // Unicode identifier start
            _ if ch.is_alphabetic() => self.scan_identifier(),

            _ => {
                self.advance();
                return Err(LexError::UnexpectedCharacter {
                    ch,
                    span: Span::new(pos, self.current_pos),
                }
                .into());
            }
        };

        self.update_regex_context(&token);
        // Remember the last identifier so a following inline `/*: T */`
        // annotation can be attached to it.
        if let Token::Ident(name) = &token {
            self.last_ident = Some((name.clone(), self.current_pos));
        }
        Ok(Spanned::new(token, Span::new(start, self.current_pos)))
    }

    fn peek(&mut self) -> Option<(usize, char)> {
        self.chars.peek().copied()
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        let result = self.chars.next();
        if let Some((pos, ch)) = result {
            self.current_pos = pos + ch.len_utf8();
        }
        result
    }

    fn peek_next(&self) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next().map(|(_, c)| c)
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<()> {
        loop {
            match self.peek() {
                Some((_, ' ' | '\t' | '\n' | '\r' | '\x0B' | '\x0C')) => {
                    self.advance();
                }
                Some((_, '/')) => {
                    match self.peek_next() {
                        Some('/') => {
                            // Single-line comment
                            self.advance(); // /
                            self.advance(); // /
                            while let Some((_, ch)) = self.peek() {
                                if ch == '\n' {
                                    break;
                                }
                                self.advance();
                            }
                        }
                        Some('*') => {
                            // Multi-line comment - check for type annotation
                            let start = self.current_pos;
                            self.advance(); // /
                            self.advance(); // *

                            // Inline `/*: T */` annotation: attaches to the
                            // most recently emitted identifier.
                            if self.peek().map(|(_, c)| c == ':').unwrap_or(false) {
                                self.advance(); // consume ':'
                                self.skip_whitespace();
                                let content = self.read_until_comment_end();
                                self.consume_comment_end();
                                if let Some((name, _)) = self.last_ident.clone() {
                                    self.type_annotations.push(TypeAnnotation {
                                        name,
                                        content: content.trim().to_string(),
                                        span: Span::new(start, self.current_pos),
                                    });
                                }
                                continue;
                            }

                            // Check if this is a doc comment /**
                            if self.peek().map(|(_, c)| c == '*').unwrap_or(false) {
                                self.advance(); // consume third *
                                self.skip_whitespace();

                                // Try to read keyword
                                let keyword = self.peek_keyword();

                                match keyword.as_deref() {
                                    Some("var") | Some("const") | Some("let") => {
                                        let kw = keyword.unwrap();
                                        self.advance_keyword(&kw);
                                        self.parse_var_annotations(start);
                                        continue;
                                    }
                                    Some("function") => {
                                        self.advance_keyword("function");
                                        self.parse_function_annotation(start);
                                        continue;
                                    }
                                    Some("export") => {
                                        self.advance_keyword("export");
                                        self.skip_whitespace();
                                        // Check for "export var" or "export function"
                                        let next_kw = self.peek_keyword();
                                        match next_kw.as_deref() {
                                            Some("var") | Some("const") | Some("let") => {
                                                let kw = next_kw.unwrap();
                                                self.advance_keyword(&kw);
                                                self.parse_var_annotations(start);
                                                continue;
                                            }
                                            Some("function") => {
                                                self.advance_keyword("function");
                                                self.parse_function_annotation(start);
                                                continue;
                                            }
                                            _ => {} // fall through to regular comment
                                        }
                                    }
                                    _ => {} // fall through to regular comment
                                }
                            }

                            // Regular comment - skip until */
                            loop {
                                match self.peek() {
                                    Some((_, '*')) => {
                                        self.advance();
                                        if self.peek().map(|(_, c)| c == '/').unwrap_or(false) {
                                            self.advance();
                                            break;
                                        }
                                    }
                                    Some(_) => {
                                        self.advance();
                                    }
                                    None => {
                                        return Err(LexError::UnterminatedComment {
                                            span: Span::new(start, self.current_pos),
                                        }
                                        .into());
                                    }
                                }
                            }
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn scan_plus(&mut self) -> Token {
        self.advance(); // +
        match self.peek() {
            Some((_, '+')) => {
                self.advance();
                Token::PlusPlus
            }
            Some((_, '=')) => {
                self.advance();
                Token::PlusEq
            }
            _ => Token::Plus,
        }
    }

    fn scan_minus(&mut self) -> Token {
        self.advance(); // -
        match self.peek() {
            Some((_, '-')) => {
                self.advance();
                Token::MinusMinus
            }
            Some((_, '=')) => {
                self.advance();
                Token::MinusEq
            }
            _ => Token::Minus,
        }
    }

    fn scan_star(&mut self) -> Token {
        self.advance(); // *
        match self.peek() {
            Some((_, '*')) => {
                self.advance();
                match self.peek() {
                    Some((_, '=')) => {
                        self.advance();
                        Token::StarStarEq
                    }
                    _ => Token::StarStar,
                }
            }
            Some((_, '=')) => {
                self.advance();
                Token::StarEq
            }
            _ => Token::Star,
        }
    }

    fn scan_slash_or_regex(&mut self) -> Result<Token> {
        let start = self.current_pos;
        self.advance(); // /

        // Check if this should be a regex based on context
        if self.last_token_allows_regex {
            // This is a regex literal
            return self.scan_regex_literal(start);
        }

        // Otherwise it's division or /=
        match self.peek() {
            Some((_, '=')) => {
                self.advance();
                Ok(Token::SlashEq)
            }
            _ => Ok(Token::Slash),
        }
    }

    fn scan_regex_literal(&mut self, start: usize) -> Result<Token> {
        let mut pattern = String::new();
        let mut in_class = false; // Inside [...] character class

        loop {
            match self.peek() {
                Some((_, '/')) if !in_class => {
                    self.advance();
                    break;
                }
                Some((_, '[')) => {
                    in_class = true;
                    pattern.push('[');
                    self.advance();
                }
                Some((_, ']')) if in_class => {
                    in_class = false;
                    pattern.push(']');
                    self.advance();
                }
                Some((_, '\\')) => {
                    pattern.push('\\');
                    self.advance();
                    // Include the next character as-is
                    if let Some((_, ch)) = self.peek() {
                        pattern.push(ch);
                        self.advance();
                    }
                }
                Some((_, '\n')) | None => {
                    return Err(LexError::UnterminatedRegex {
                        span: Span::new(start, self.current_pos),
                    }
                    .into());
                }
                Some((_, ch)) => {
                    pattern.push(ch);
                    self.advance();
                }
            }
        }

        // Scan flags (gimsuvy)
        let mut flags = String::new();
        while let Some((_, ch)) = self.peek() {
            if ch.is_ascii_alphabetic() {
                flags.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        Ok(Token::Regex { pattern, flags })
    }

    fn scan_percent(&mut self) -> Token {
        self.advance(); // %
        match self.peek() {
            Some((_, '=')) => {
                self.advance();
                Token::PercentEq
            }
            _ => Token::Percent,
        }
    }

    fn scan_less_than(&mut self) -> Token {
        self.advance(); // <
        match self.peek() {
            Some((_, '<')) => {
                self.advance();
                match self.peek() {
                    Some((_, '=')) => {
                        self.advance();
                        Token::LShiftEq
                    }
                    _ => Token::LShift,
                }
            }
            Some((_, '=')) => {
                self.advance();
                Token::LtEq
            }
            _ => Token::Lt,
        }
    }

    fn scan_greater_than(&mut self) -> Token {
        self.advance(); // >
        match self.peek() {
            Some((_, '>')) => {
                self.advance();
                match self.peek() {
                    Some((_, '>')) => {
                        self.advance();
                        match self.peek() {
                            Some((_, '=')) => {
                                self.advance();
                                Token::URShiftEq
                            }
                            _ => Token::URShift,
                        }
                    }
                    Some((_, '=')) => {
                        self.advance();
                        Token::RShiftEq
                    }
                    _ => Token::RShift,
                }
            }
            Some((_, '=')) => {
                self.advance();
                Token::GtEq
            }
            _ => Token::Gt,
        }
    }

    fn scan_equals(&mut self) -> Token {
        self.advance(); // =
        match self.peek() {
            Some((_, '=')) => {
                self.advance();
                match self.peek() {
                    Some((_, '=')) => {
                        self.advance();
                        Token::EqEqEq
                    }
                    _ => Token::EqEq,
                }
            }
            Some((_, '>')) => {
                self.advance();
                Token::FatArrow
            }
            _ => Token::Eq,
        }
    }

    fn scan_exclamation(&mut self) -> Token {
        self.advance(); // !
        match self.peek() {
            Some((_, '=')) => {
                self.advance();
                match self.peek() {
                    Some((_, '=')) => {
                        self.advance();
                        Token::NotEqEq
                    }
                    _ => Token::NotEq,
                }
            }
            _ => Token::Not,
        }
    }

    fn scan_ampersand(&mut self) -> Token {
        self.advance(); // &
        match self.peek() {
            Some((_, '&')) => {
                self.advance();
                Token::And
            }
            Some((_, '=')) => {
                self.advance();
                Token::BitAndEq
            }
            _ => Token::BitAnd,
        }
    }

    fn scan_pipe(&mut self) -> Token {
        self.advance(); // |
        match self.peek() {
            Some((_, '|')) => {
                self.advance();
                Token::Or
            }
            Some((_, '=')) => {
                self.advance();
                Token::BitOrEq
            }
            _ => Token::BitOr,
        }
    }

    fn scan_caret(&mut self) -> Token {
        self.advance(); // ^
        match self.peek() {
            Some((_, '=')) => {
                self.advance();
                Token::BitXorEq
            }
            _ => Token::BitXor,
        }
    }

    fn scan_string(&mut self) -> Result<Token> {
        let (start_pos, quote) = self.advance().unwrap();
        let mut value = String::new();

        loop {
            match self.peek() {
                Some((_, ch)) if ch == quote => {
                    self.advance();
                    break;
                }
                Some((_, '\\')) => {
                    self.advance();
                    match self.peek() {
                        Some((_, 'n')) => {
                            self.advance();
                            value.push('\n');
                        }
                        Some((_, 't')) => {
                            self.advance();
                            value.push('\t');
                        }
                        Some((_, 'r')) => {
                            self.advance();
                            value.push('\r');
                        }
                        Some((_, '\\')) => {
                            self.advance();
                            value.push('\\');
                        }
                        Some((_, '\'')) => {
                            self.advance();
                            value.push('\'');
                        }
                        Some((_, '"')) => {
                            self.advance();
                            value.push('"');
                        }
                        Some((_, '0')) => {
                            self.advance();
                            value.push('\0');
                        }
                        Some((_, 'x')) => {
                            self.advance();
                            let hex = self.scan_hex_digits(2)?;
                            if let Some(ch) = char::from_u32(hex) {
                                value.push(ch);
                            }
                        }
                        Some((_, 'u')) => {
                            self.advance();
                            if self.peek().map(|(_, c)| c == '{').unwrap_or(false) {
                                // \u{HHHHHH}
                                self.advance();
                                let mut hex_str = String::new();
                                while let Some((_, ch)) = self.peek() {
                                    if ch == '}' {
                                        self.advance();
                                        break;
                                    }
                                    hex_str.push(ch);
                                    self.advance();
                                }
                                if let Ok(code) = u32::from_str_radix(&hex_str, 16) {
                                    if let Some(ch) = char::from_u32(code) {
                                        value.push(ch);
                                    }
                                }
                            } else {
                                // \uHHHH
                                let hex = self.scan_hex_digits(4)?;
                                if let Some(ch) = char::from_u32(hex) {
                                    value.push(ch);
                                }
                            }
                        }
                        Some((_, ch)) => {
                            self.advance();
                            value.push(ch);
                        }
                        None => {
                            return Err(LexError::UnterminatedString {
                                span: Span::new(start_pos, self.current_pos),
                            }
                            .into());
                        }
                    }
                }
                Some((_, '\n')) | None => {
                    return Err(LexError::UnterminatedString {
                        span: Span::new(start_pos, self.current_pos),
                    }
                    .into());
                }
                Some((_, ch)) => {
                    self.advance();
                    value.push(ch);
                }
            }
        }

        Ok(Token::String(value))
    }

    /// Scan a template literal starting from the opening backtick.
    /// Returns TemplateNoSub if no substitutions, or TemplateHead if there's a ${.
    fn scan_template_literal(&mut self) -> Result<Token> {
        let start_pos = self.current_pos;
        self.advance(); // consume the `

        let (value, has_substitution) = self.scan_template_chars(start_pos)?;

        if has_substitution {
            self.template_depth += 1;
            Ok(Token::TemplateHead(value))
        } else {
            Ok(Token::TemplateNoSub(value))
        }
    }

    /// Scan template continuation after a }.
    /// Returns TemplateMiddle if there's another ${, or TemplateTail if it ends with `.
    fn scan_template_continuation(&mut self) -> Result<Token> {
        let start_pos = self.current_pos;
        let (value, has_substitution) = self.scan_template_chars(start_pos)?;

        if has_substitution {
            Ok(Token::TemplateMiddle(value))
        } else {
            self.template_depth -= 1;
            Ok(Token::TemplateTail(value))
        }
    }

    /// Scan the content of a template literal until either ${ or `.
    /// Returns (content, has_substitution) where has_substitution is true if ended with ${.
    fn scan_template_chars(&mut self, start_pos: usize) -> Result<(String, bool)> {
        let mut value = String::new();

        loop {
            match self.peek() {
                Some((_, '`')) => {
                    self.advance();
                    return Ok((value, false));
                }
                Some((_, '$')) => {
                    if self.peek_next() == Some('{') {
                        self.advance(); // consume $
                        self.advance(); // consume {
                        return Ok((value, true));
                    }
                    value.push('$');
                    self.advance();
                }
                Some((_, '\\')) => {
                    self.advance();
                    match self.peek() {
                        Some((_, 'n')) => {
                            self.advance();
                            value.push('\n');
                        }
                        Some((_, 't')) => {
                            self.advance();
                            value.push('\t');
                        }
                        Some((_, 'r')) => {
                            self.advance();
                            value.push('\r');
                        }
                        Some((_, '\\')) => {
                            self.advance();
                            value.push('\\');
                        }
                        Some((_, '`')) => {
                            self.advance();
                            value.push('`');
                        }
                        Some((_, '$')) => {
                            self.advance();
                            value.push('$');
                        }
                        Some((_, '{')) => {
                            self.advance();
                            value.push('{');
                        }
                        Some((_, '0')) => {
                            self.advance();
                            value.push('\0');
                        }
                        Some((_, 'x')) => {
                            self.advance();
                            let hex = self.scan_hex_digits(2)?;
                            if let Some(ch) = char::from_u32(hex) {
                                value.push(ch);
                            }
                        }
                        Some((_, 'u')) => {
                            self.advance();
                            if self.peek().map(|(_, c)| c == '{').unwrap_or(false) {
                                // \u{HHHHHH}
                                self.advance();
                                let mut hex_str = String::new();
                                while let Some((_, ch)) = self.peek() {
                                    if ch == '}' {
                                        self.advance();
                                        break;
                                    }
                                    hex_str.push(ch);
                                    self.advance();
                                }
                                if let Ok(code) = u32::from_str_radix(&hex_str, 16) {
                                    if let Some(ch) = char::from_u32(code) {
                                        value.push(ch);
                                    }
                                }
                            } else {
                                // \uHHHH
                                let hex = self.scan_hex_digits(4)?;
                                if let Some(ch) = char::from_u32(hex) {
                                    value.push(ch);
                                }
                            }
                        }
                        Some((_, '\n')) => {
                            // Line continuation - consume newline but don't add to string
                            self.advance();
                        }
                        Some((_, ch)) => {
                            // Unknown escape - just include the character
                            self.advance();
                            value.push(ch);
                        }
                        None => {
                            return Err(LexError::UnterminatedString {
                                span: Span::new(start_pos, self.current_pos),
                            }
                            .into());
                        }
                    }
                }
                Some((_, ch)) => {
                    value.push(ch);
                    self.advance();
                }
                None => {
                    return Err(LexError::UnterminatedString {
                        span: Span::new(start_pos, self.current_pos),
                    }
                    .into());
                }
            }
        }
    }

    fn scan_hex_digits(&mut self, count: usize) -> Result<u32> {
        let mut hex_str = String::new();
        for _ in 0..count {
            match self.peek() {
                Some((_, ch)) if ch.is_ascii_hexdigit() => {
                    hex_str.push(ch);
                    self.advance();
                }
                _ => break,
            }
        }
        u32::from_str_radix(&hex_str, 16).map_err(|_| {
            LexError::InvalidEscapeSequence {
                span: Span::new(self.current_pos - hex_str.len(), self.current_pos),
            }
            .into()
        })
    }

    fn scan_number(&mut self) -> Result<Token> {
        let start = self.current_pos;

        // Check for hex, binary, or octal
        if self.peek().map(|(_, c)| c == '0').unwrap_or(false) {
            self.advance();
            match self.peek() {
                Some((_, 'x')) | Some((_, 'X')) => {
                    self.advance();
                    return self.scan_hex_number(start);
                }
                Some((_, 'b')) | Some((_, 'B')) => {
                    self.advance();
                    return self.scan_binary_number(start);
                }
                Some((_, 'o')) | Some((_, 'O')) => {
                    self.advance();
                    return self.scan_octal_number(start);
                }
                Some((_, '.')) => {
                    self.advance();
                    return self.scan_number_after_dot(start);
                }
                Some((_, ch)) if ch.is_ascii_digit() => {
                    // Continue with decimal
                }
                _ => return Ok(Token::Number(0.0)),
            }
        }

        // Decimal number
        self.scan_decimal_digits();

        // Fractional part
        if self.peek().map(|(_, c)| c == '.').unwrap_or(false) {
            self.advance();
            self.scan_decimal_digits();
        }

        // Exponent
        if let Some((_, 'e' | 'E')) = self.peek() {
            self.advance();
            if let Some((_, '+' | '-')) = self.peek() {
                self.advance();
            }
            self.scan_decimal_digits();
        }

        let num_str: String = self.source[start..self.current_pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();

        let value = num_str
            .parse::<f64>()
            .map_err(|_| LexError::InvalidNumber {
                span: Span::new(start, self.current_pos),
            })?;

        Ok(Token::Number(value))
    }

    fn scan_number_after_dot(&mut self, start: usize) -> Result<Token> {
        self.scan_decimal_digits();

        // Exponent
        if let Some((_, 'e' | 'E')) = self.peek() {
            self.advance();
            if let Some((_, '+' | '-')) = self.peek() {
                self.advance();
            }
            self.scan_decimal_digits();
        }

        let num_str: String = self.source[start..self.current_pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();

        let value = num_str
            .parse::<f64>()
            .map_err(|_| LexError::InvalidNumber {
                span: Span::new(start, self.current_pos),
            })?;

        Ok(Token::Number(value))
    }

    fn scan_decimal_digits(&mut self) {
        while let Some((_, ch)) = self.peek() {
            if ch.is_ascii_digit() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn scan_hex_number(&mut self, start: usize) -> Result<Token> {
        let hex_start = self.current_pos;
        while let Some((_, ch)) = self.peek() {
            if ch.is_ascii_hexdigit() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let hex_str: String = self.source[hex_start..self.current_pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();

        let value = i64::from_str_radix(&hex_str, 16).map_err(|_| LexError::InvalidNumber {
            span: Span::new(start, self.current_pos),
        })? as f64;

        Ok(Token::Number(value))
    }

    fn scan_binary_number(&mut self, start: usize) -> Result<Token> {
        let bin_start = self.current_pos;
        while let Some((_, ch)) = self.peek() {
            if ch == '0' || ch == '1' || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let bin_str: String = self.source[bin_start..self.current_pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();

        let value = i64::from_str_radix(&bin_str, 2).map_err(|_| LexError::InvalidNumber {
            span: Span::new(start, self.current_pos),
        })? as f64;

        Ok(Token::Number(value))
    }

    fn scan_octal_number(&mut self, start: usize) -> Result<Token> {
        let oct_start = self.current_pos;
        while let Some((_, ch)) = self.peek() {
            if ('0'..='7').contains(&ch) || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let oct_str: String = self.source[oct_start..self.current_pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();

        let value = i64::from_str_radix(&oct_str, 8).map_err(|_| LexError::InvalidNumber {
            span: Span::new(start, self.current_pos),
        })? as f64;

        Ok(Token::Number(value))
    }

    fn skip_whitespace(&mut self) {
        while let Some((_, ch)) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Peek ahead to read identifier without consuming
    fn peek_keyword(&self) -> Option<String> {
        let mut iter = self.chars.clone();
        let mut result = String::new();

        while let Some((_, ch)) = iter.next() {
            if ch.is_alphabetic() || ch == '_' || (!result.is_empty() && ch.is_alphanumeric()) {
                result.push(ch);
            } else {
                break;
            }
        }

        if result.is_empty() {
            None
        } else {
            Some(result)
        }
    }

    /// Advance past the keyword characters
    fn advance_keyword(&mut self, kw: &str) {
        for _ in kw.chars() {
            self.advance();
        }
    }

    /// Read an identifier from current position
    fn read_identifier(&mut self) -> String {
        let mut name = String::new();
        while let Some((_, ch)) = self.peek() {
            if Self::is_ident_char(ch) {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        name
    }

    /// Read content until we hit a comma or end of comment (*/)
    fn read_until_comma_or_end(&mut self) -> String {
        let mut content = String::new();
        let mut paren_depth: i32 = 0;
        let mut brace_depth: i32 = 0;
        let mut angle_depth: i32 = 0;

        while let Some((_, ch)) = self.peek() {
            // Check for end of comment
            if ch == '*' && self.peek_next() == Some('/') {
                break;
            }
            // Comma at top level ends this type annotation. Commas inside
            // parens `(A, B) => C`, braces `{a: T, b: U}` and angle
            // brackets `<T, U>` are part of the current type.
            if ch == ',' && paren_depth == 0 && brace_depth == 0 && angle_depth == 0 {
                break;
            }
            if ch == '(' {
                paren_depth += 1;
            } else if ch == ')' {
                paren_depth = paren_depth.saturating_sub(1);
            } else if ch == '{' {
                brace_depth += 1;
            } else if ch == '}' {
                brace_depth = brace_depth.saturating_sub(1);
            } else if ch == '<' {
                angle_depth += 1;
            } else if ch == '>' && angle_depth > 0 {
                // Only treat `>` as closing if we opened one. Otherwise it's
                // part of `=>`, which shouldn't affect nesting.
                angle_depth -= 1;
            }
            content.push(ch);
            self.advance();
        }
        content
    }

    /// Read content until end of comment
    fn read_until_comment_end(&mut self) -> String {
        let mut content = String::new();
        while let Some((_, ch)) = self.peek() {
            if ch == '*' && self.peek_next() == Some('/') {
                break;
            }
            content.push(ch);
            self.advance();
        }
        content
    }

    /// Consume closing */
    fn consume_comment_end(&mut self) {
        if self.peek().map(|(_, c)| c == '*').unwrap_or(false) {
            self.advance(); // *
        }
        if self.peek().map(|(_, c)| c == '/').unwrap_or(false) {
            self.advance(); // /
        }
    }

    /// Parse variable annotations: name: Type [, name: Type]*
    fn parse_var_annotations(&mut self, start: usize) {
        self.skip_whitespace();

        loop {
            // Read name
            let name = self.read_identifier();
            if name.is_empty() {
                break;
            }

            self.skip_whitespace();

            // Expect ':'
            if !self.peek().map(|(_, c)| c == ':').unwrap_or(false) {
                break;
            }
            self.advance(); // consume ':'
            self.skip_whitespace();

            // Read type until ',' or '*/'
            let content = self.read_until_comma_or_end();

            self.type_annotations.push(TypeAnnotation {
                name: name.trim().to_string(),
                content: content.trim().to_string(),
                span: Span::new(start, self.current_pos + 2),
            });

            self.skip_whitespace();

            // Check for comma to continue
            if self.peek().map(|(_, c)| c == ',').unwrap_or(false) {
                self.advance(); // consume ','
                self.skip_whitespace();
                continue;
            }
            break;
        }

        // Consume closing */
        self.consume_comment_end();
    }

    /// Parse function annotation: name(params): ReturnType
    fn parse_function_annotation(&mut self, start: usize) {
        self.skip_whitespace();

        let name = self.read_identifier();
        if name.is_empty() {
            // Fall back to consuming as regular comment
            self.consume_comment_end();
            return;
        }

        self.skip_whitespace();

        // Read everything from current position to */ as content
        let content = self.read_until_comment_end();

        self.type_annotations.push(TypeAnnotation {
            name: name.trim().to_string(),
            content: content.trim().to_string(),
            span: Span::new(start, self.current_pos + 2),
        });

        self.consume_comment_end();
    }

    fn is_ident_char(ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_' || ch == '$'
    }

    fn scan_identifier(&mut self) -> Token {
        let start = self.current_pos;

        while let Some((_, ch)) = self.peek() {
            // Accept ASCII alphanumeric, _, $, or any Unicode alphanumeric
            if ch.is_alphanumeric() || ch == '_' || ch == '$' {
                self.advance();
            } else {
                break;
            }
        }

        let ident = &self.source[start..self.current_pos];

        // Check if it's a keyword (keywords are ASCII-only)
        Token::keyword(ident).unwrap_or_else(|| Token::Ident(ident.to_string()))
    }

    /// Get collected type annotations
    pub fn type_annotations(&self) -> &[TypeAnnotation] {
        &self.type_annotations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(source: &str) -> Vec<Token> {
        Scanner::new(source)
            .tokenize()
            .unwrap()
            .0
            .into_iter()
            .map(|s| s.value)
            .collect()
    }

    #[test]
    fn test_keywords() {
        assert_eq!(tokenize("var"), vec![Token::Var, Token::Eof]);
        assert_eq!(tokenize("function"), vec![Token::Function, Token::Eof]);
        assert_eq!(
            tokenize("if else"),
            vec![Token::If, Token::Else, Token::Eof]
        );
    }

    #[test]
    fn test_numbers() {
        assert_eq!(tokenize("42"), vec![Token::Number(42.0), Token::Eof]);
        assert_eq!(tokenize("3.14"), vec![Token::Number(3.14), Token::Eof]);
        assert_eq!(tokenize("1e5"), vec![Token::Number(100000.0), Token::Eof]);
        assert_eq!(tokenize("0xFF"), vec![Token::Number(255.0), Token::Eof]);
        assert_eq!(tokenize("0b101"), vec![Token::Number(5.0), Token::Eof]);
        assert_eq!(tokenize("0o755"), vec![Token::Number(493.0), Token::Eof]);
        assert_eq!(tokenize("1_000"), vec![Token::Number(1000.0), Token::Eof]);
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            tokenize("\"hello\""),
            vec![Token::String("hello".to_string()), Token::Eof]
        );
        assert_eq!(
            tokenize("'world'"),
            vec![Token::String("world".to_string()), Token::Eof]
        );
        assert_eq!(
            tokenize("\"hello\\nworld\""),
            vec![Token::String("hello\nworld".to_string()), Token::Eof]
        );
    }

    #[test]
    fn test_operators() {
        // Use valid expression context - after number, / is division
        assert_eq!(
            tokenize("1 + 2 - 3 * 4 / 5"),
            vec![
                Token::Number(1.0),
                Token::Plus,
                Token::Number(2.0),
                Token::Minus,
                Token::Number(3.0),
                Token::Star,
                Token::Number(4.0),
                Token::Slash,
                Token::Number(5.0),
                Token::Eof
            ]
        );
        assert_eq!(
            tokenize("=== !== == !="),
            vec![
                Token::EqEqEq,
                Token::NotEqEq,
                Token::EqEq,
                Token::NotEq,
                Token::Eof
            ]
        );
        assert_eq!(
            tokenize("&& || !"),
            vec![Token::And, Token::Or, Token::Not, Token::Eof]
        );
        assert_eq!(
            tokenize("++ --"),
            vec![Token::PlusPlus, Token::MinusMinus, Token::Eof]
        );
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            tokenize("// comment\n42"),
            vec![Token::Number(42.0), Token::Eof]
        );
        assert_eq!(
            tokenize("/* comment */ 42"),
            vec![Token::Number(42.0), Token::Eof]
        );
    }

    #[test]
    fn test_type_annotation() {
        let scanner = Scanner::new("/** var x: Number */ var x = 42;");
        let (tokens, annotations) = scanner.tokenize().unwrap();
        assert!(tokens.iter().any(|t| t.value == Token::Var));
        assert!(tokens
            .iter()
            .any(|t| matches!(&t.value, Token::Ident(s) if s == "x")));
        assert_eq!(annotations.len(), 1);
        assert_eq!(annotations[0].name, "x");
        assert_eq!(annotations[0].content, "Number");
    }

    #[test]
    fn test_template_literal_no_substitution() {
        assert_eq!(
            tokenize("`hello world`"),
            vec![Token::TemplateNoSub("hello world".to_string()), Token::Eof]
        );
    }

    #[test]
    fn test_template_literal_with_substitution() {
        let tokens = tokenize("`hello ${name}!`");
        assert_eq!(
            tokens,
            vec![
                Token::TemplateHead("hello ".to_string()),
                Token::Ident("name".to_string()),
                Token::TemplateTail("!".to_string()),
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_template_literal_multiple_substitutions() {
        let tokens = tokenize("`${a} + ${b} = ${c}`");
        assert_eq!(
            tokens,
            vec![
                Token::TemplateHead("".to_string()),
                Token::Ident("a".to_string()),
                Token::TemplateMiddle(" + ".to_string()),
                Token::Ident("b".to_string()),
                Token::TemplateMiddle(" = ".to_string()),
                Token::Ident("c".to_string()),
                Token::TemplateTail("".to_string()),
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_template_literal_escape_sequences() {
        assert_eq!(
            tokenize("`line1\\nline2`"),
            vec![Token::TemplateNoSub("line1\nline2".to_string()), Token::Eof]
        );
        assert_eq!(
            tokenize("`escaped \\` backtick`"),
            vec![
                Token::TemplateNoSub("escaped ` backtick".to_string()),
                Token::Eof
            ]
        );
        assert_eq!(
            tokenize("`escaped \\${not interpolated}`"),
            vec![
                Token::TemplateNoSub("escaped ${not interpolated}".to_string()),
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_template_literal_multiline() {
        assert_eq!(
            tokenize("`line1\nline2`"),
            vec![Token::TemplateNoSub("line1\nline2".to_string()), Token::Eof]
        );
    }
}
