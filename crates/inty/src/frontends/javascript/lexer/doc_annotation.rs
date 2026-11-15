//! Statement annotations in `/** … */` doc comments: `/** const c: T */`,
//! `/** function f(…) => R */`, `/** class C … */` and
//! `/** [nominal] type Name<P> = Body */`, each optionally after `export`.
//!
//! A long annotation can be written across lines, JSDoc style:
//!
//! ```text
//! /** type ScoreView = {
//!  *   id: String,
//!  *   fitWidth: Number,  // the width the page is laid out for
//!  * } */
//! ```
//!
//! Before an annotation is read, the comment's body is *cleaned*
//! ([`clean_doc_body`]): each continuation line's leading `*` margin and
//! each `//` comment become spaces. Cleaning keeps every byte where it
//! was, so an offset into the cleaned body is the same offset into the
//! source, and an error found inside an annotation points at the field
//! it is about rather than at the comment's first line.

use super::token::Span;
use crate::ast::{AnnotationKind, TypeAlias, TypeAnnotation};

/// What a doc comment declares, when it is a statement annotation.
#[derive(Debug, Default)]
pub(crate) struct DocAnnotation {
    pub annotations: Vec<TypeAnnotation>,
    pub aliases: Vec<TypeAlias>,
}

/// The body of a doc comment (the text between `/**` and `*/`) with its
/// JSDoc decoration blanked out, byte for byte:
///
/// * On every line but the first, a leading margin — optional spaces or
///   tabs, then a `*` — has its `*` replaced by a space. (The one space
///   JSDoc puts after the `*` is whitespace already.) A `*` anywhere else
///   is left alone.
/// * A `//` comment, outside a `"…"` string literal type, is blanked up
///   to the end of its line.
///
/// The result has the same length as `raw`, with the same newlines in
/// the same places, so offsets into it are offsets into `raw`.
pub(crate) fn clean_doc_body(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut at_line_start = false; // the first line has no margin
    let mut in_comment = false;
    let mut in_string = false;
    let mut chars = raw.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\n' {
            out.push('\n');
            at_line_start = true;
            in_comment = false;
            in_string = false;
            continue;
        }
        if in_comment {
            blank(&mut out, c);
            continue;
        }
        if at_line_start {
            match c {
                ' ' | '\t' | '\r' => {
                    out.push(c);
                    continue;
                }
                '*' => {
                    out.push(' ');
                    at_line_start = false;
                    continue;
                }
                _ => at_line_start = false,
            }
        }
        if in_string {
            out.push(c);
            match c {
                '\\' => {
                    if let Some(&next) = chars.peek() {
                        if next != '\n' {
                            chars.next();
                            out.push(next);
                        }
                    }
                }
                '"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => {
                in_string = true;
                out.push(c);
            }
            '/' if chars.peek() == Some(&'/') => {
                in_comment = true;
                blank(&mut out, c);
            }
            _ => out.push(c),
        }
    }
    debug_assert_eq!(out.len(), raw.len());
    out
}

/// Push as many spaces as `c` takes bytes.
fn blank(out: &mut String, c: char) {
    for _ in 0..c.len_utf8() {
        out.push(' ');
    }
}

/// Read the statement annotation in a doc comment, if it is one.
///
/// `raw` is the comment's body as written and `cleaned` the same body
/// through [`clean_doc_body`]; `body_start` is the source offset of the
/// body's first byte and `comment_start` that of the opening `/**`.
///
/// Returns `None` when the comment isn't a statement annotation, so the
/// caller reads it as an ordinary doc comment (which may carry a JSDoc
/// `@type` tag). With the keyword after a `*` margin rather than on the
/// `/**` line, the comment must be an annotation in shape and in syntax:
/// one whose type doesn't parse is taken for prose.
pub(crate) fn read_doc_annotation(
    raw: &str,
    cleaned: &str,
    body_start: usize,
    comment_start: usize,
) -> Option<DocAnnotation> {
    let mut c = Cursor {
        text: cleaned,
        pos: 0,
        base: body_start,
    };
    c.skip_whitespace();
    // A margin stripped before the keyword (`/**\n * type X = …`) is
    // also how a prose doc comment looks (`/**\n * function that …`),
    // so that form must have an annotation's shape to be read as one.
    let after_margin = raw[..c.pos].contains('*');
    let comment_end = body_start + cleaned.len() + 2;
    let mut out = DocAnnotation::default();
    let mut keyword = c.peek_keyword()?;
    let mut exported = false;
    if keyword == "export" {
        c.advance(keyword.len());
        c.skip_whitespace();
        keyword = c.peek_keyword()?;
        exported = true;
    }
    match keyword {
        "var" | "const" | "let" => {
            c.advance(keyword.len());
            c.read_var_annotations(comment_start, &mut out.annotations);
            if out.annotations.is_empty() && after_margin {
                return None;
            }
        }
        "function" => {
            c.advance(keyword.len());
            c.skip_whitespace();
            let name = c.read_identifier();
            if name.is_empty() {
                return if after_margin { None } else { Some(out) };
            }
            c.skip_whitespace();
            if after_margin && !matches!(c.peek(), Some('(' | '<')) {
                return None;
            }
            let (content, content_start) = c.read_to_end();
            out.annotations.push(TypeAnnotation {
                name,
                content,
                span: Span::new(comment_start, comment_end),
                kind: AnnotationKind::Inline,
                content_start: Some(content_start),
            });
        }
        "class" if !exported => {
            c.advance(keyword.len());
            c.skip_whitespace();
            let name = c.read_identifier();
            if name.is_empty() {
                return if after_margin { None } else { Some(out) };
            }
            c.skip_whitespace();
            let rest = c.rest();
            if after_margin
                && !(rest.starts_with(['{', '(', '<'])
                    || rest.starts_with("extends")
                    || rest.is_empty())
            {
                return None;
            }
            let (content, _) = c.read_to_end();
            out.annotations.push(TypeAnnotation {
                name,
                // The class reader reassembles its parts, so offsets
                // into this text aren't kept.
                content: collapse_lines(&content),
                span: Span::new(comment_start, comment_end),
                kind: AnnotationKind::Class,
                content_start: None,
            });
        }
        "type" | "nominal" if !exported => {
            let nominal = keyword == "nominal";
            c.advance(keyword.len());
            if nominal {
                c.skip_whitespace();
                if c.peek_keyword() != Some("type") {
                    return if after_margin { None } else { Some(out) };
                }
                c.advance("type".len());
            }
            match c.read_type_alias(nominal, Span::new(comment_start, comment_end)) {
                Some(alias) => out.aliases.push(alias),
                None if after_margin => return None,
                None => {}
            }
        }
        _ => return None,
    }
    // The margin-led form is also how prose looks (`/**\n * function
    // foo(bar) is deprecated`), so it is an annotation only when its
    // types read as types. (A class declaration is checked by its shape
    // above.)
    if after_margin {
        let types = out
            .annotations
            .iter()
            .filter(|a| a.kind != AnnotationKind::Class)
            .map(|a| &a.content)
            .chain(out.aliases.iter().map(|a| &a.body));
        for ty in types {
            if crate::infer::type_parser::parse_type_syntax(ty).is_err() {
                return None;
            }
        }
    }
    Some(out)
}

/// The text of a multi-line annotation on one line: each line trimmed,
/// joined by single spaces.
fn collapse_lines(s: &str) -> String {
    s.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// A position in a cleaned doc-comment body.
struct Cursor<'b> {
    text: &'b str,
    pos: usize,
    /// Source offset of `text[0]`.
    base: usize,
}

impl<'b> Cursor<'b> {
    fn peek(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }

    fn rest(&self) -> &'b str {
        &self.text[self.pos..]
    }

    fn advance(&mut self, bytes: usize) {
        self.pos = (self.pos + bytes).min(self.text.len());
    }

    fn bump(&mut self) {
        if let Some(c) = self.peek() {
            self.pos += c.len_utf8();
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if !c.is_whitespace() {
                break;
            }
            self.bump();
        }
    }

    /// The word at the cursor, without consuming it.
    fn peek_keyword(&self) -> Option<&'b str> {
        let rest = self.rest();
        let len = rest
            .char_indices()
            .take_while(|&(i, c)| c.is_alphabetic() || c == '_' || (i > 0 && c.is_alphanumeric()))
            .map(|(i, c)| i + c.len_utf8())
            .last()?;
        Some(&rest[..len])
    }

    fn read_identifier(&mut self) -> String {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if !is_id_continue(c) {
                break;
            }
            self.bump();
        }
        self.text[start..self.pos].to_string()
    }

    /// The rest of the body, trimmed, and the source offset it starts at.
    fn read_to_end(&mut self) -> (String, usize) {
        let start = self.pos;
        self.pos = self.text.len();
        trimmed_at(self.text, start, self.pos, self.base)
    }

    /// `name: Type [, name: Type]*`, as after `/** var`.
    fn read_var_annotations(&mut self, comment_start: usize, out: &mut Vec<TypeAnnotation>) {
        self.skip_whitespace();
        loop {
            let name = self.read_identifier();
            if name.is_empty() {
                break;
            }
            self.skip_whitespace();
            if self.peek() != Some(':') {
                break;
            }
            self.bump();
            self.skip_whitespace();
            let start = self.pos;
            self.read_until_top_level_comma();
            let (content, content_start) = trimmed_at(self.text, start, self.pos, self.base);
            out.push(TypeAnnotation {
                name,
                content,
                // As before multi-line annotations: from the comment's
                // start to two past this declarator's type.
                span: Span::new(comment_start, self.base + self.pos + 2),
                kind: AnnotationKind::Inline,
                content_start: Some(content_start),
            });
            self.skip_whitespace();
            if self.peek() == Some(',') {
                self.bump();
                self.skip_whitespace();
                continue;
            }
            break;
        }
    }

    /// Advance to the end of one declarator's type: the next comma
    /// outside brackets (and outside a scheme's `where C, … =>` clause,
    /// whose commas separate constraints), or the end of the body.
    fn read_until_top_level_comma(&mut self) {
        let start = self.pos;
        let mut paren: i32 = 0;
        let mut brace: i32 = 0;
        let mut angle: i32 = 0;
        let mut bracket: i32 = 0;
        let mut in_where = false;
        let mut in_string = false;
        while let Some(ch) = self.peek() {
            // A string literal type's commas and brackets are its own.
            if in_string || ch == '"' {
                if ch == '\\' && in_string {
                    self.bump();
                } else if ch == '"' {
                    in_string = !in_string;
                }
                self.bump();
                continue;
            }
            let top = paren == 0 && brace == 0 && angle == 0 && bracket == 0;
            let so_far = &self.text[start..self.pos];
            if top && !in_where && ch.is_whitespace() && so_far.ends_with("where") {
                let before = so_far[..so_far.len() - 5].chars().last();
                if before.is_some_and(|c| c.is_whitespace() || c == '>') {
                    in_where = true;
                }
            }
            if top && in_where && ch == '>' && so_far.ends_with('=') {
                in_where = false;
                self.bump();
                continue;
            }
            if ch == ',' && top && !in_where {
                break;
            }
            match ch {
                '(' => paren += 1,
                ')' => paren = (paren - 1).max(0),
                '{' => brace += 1,
                '}' => brace = (brace - 1).max(0),
                '[' => bracket += 1,
                ']' => bracket = (bracket - 1).max(0),
                '<' => angle += 1,
                // A `>` closes only an opened `<`, and never an arrow's.
                '>' if angle > 0 && !so_far.ends_with('=') => angle -= 1,
                _ => {}
            }
            self.bump();
        }
    }

    /// `Name<P1, P2> = Body` after `type`. The parameter list may end in
    /// a trailing comma.
    fn read_type_alias(&mut self, nominal: bool, span: Span) -> Option<TypeAlias> {
        self.skip_whitespace();
        let name = self.read_identifier();
        if name.is_empty() {
            return None;
        }
        self.skip_whitespace();
        let mut params = Vec::new();
        if self.peek() == Some('<') {
            self.bump();
            loop {
                self.skip_whitespace();
                if self.peek() == Some('>') && !params.is_empty() {
                    self.bump();
                    break;
                }
                let p = self.read_identifier();
                if p.is_empty() {
                    return None;
                }
                params.push(p);
                self.skip_whitespace();
                match self.peek() {
                    Some(',') => self.bump(),
                    Some('>') => {
                        self.bump();
                        break;
                    }
                    _ => return None,
                }
            }
            self.skip_whitespace();
        }
        if self.peek() != Some('=') {
            return None;
        }
        self.bump();
        let (body, body_start) = self.read_to_end();
        Some(TypeAlias {
            name,
            params,
            body,
            body_ast: None,
            span,
            nominal,
            content_start: Some(body_start),
        })
    }
}

/// `text[start..end]` trimmed, and the source offset of its first byte.
fn trimmed_at(text: &str, start: usize, end: usize, base: usize) -> (String, usize) {
    let slice = &text[start..end];
    let lead = slice.len() - slice.trim_start().len();
    (slice.trim().to_string(), base + start + lead)
}

/// ECMAScript `IdentifierPart`, as the scanner reads names.
fn is_id_continue(ch: char) -> bool {
    ch == '$' || ch == '\u{200C}' || ch == '\u{200D}' || unicode_ident::is_xid_continue(ch)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cleaning_keeps_every_offset() {
        let raw = " type A = {\n   *   a: Number, // why é\n   * }\n ";
        let cleaned = clean_doc_body(raw);
        assert_eq!(cleaned.len(), raw.len());
        assert_eq!(
            cleaned,
            " type A = {\n       a: Number,          \n     }\n "
        );
    }

    #[test]
    fn only_a_margin_star_is_blanked() {
        // On the first line, and after other text on a line, a `*` stays.
        let cleaned = clean_doc_body(" * a\n  b * c\n * d");
        assert_eq!(cleaned, " * a\n  b * c\n   d");
    }

    #[test]
    fn a_comment_inside_a_string_literal_type_stays() {
        let raw = " const u: \"http://x\" | \"a\\\"//\" // note\n";
        let cleaned = clean_doc_body(raw);
        assert_eq!(cleaned, " const u: \"http://x\" | \"a\\\"//\"        \n");
    }

    #[test]
    fn blank_lines_between_margins() {
        let raw = "\n * type A = {\n *\n\n *   a: Number,\n *\n * }\n ";
        let cleaned = clean_doc_body(raw);
        assert_eq!(
            cleaned,
            "\n   type A = {\n  \n\n     a: Number,\n  \n   }\n "
        );
    }
}
