//! Conversions between minfern's byte spans and LSP positions, plus
//! `MinfernError` → LSP `Diagnostic` mapping.

use minfern::error::{LexError, MinfernError, ParseError, TypeError};
use minfern::lexer::Span;
use serde_json::{json, Value};

/// LSP position: zero-based line, character (UTF-16 code units).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

/// Convert a byte offset in `text` to an LSP `Position` (UTF-16 units).
///
/// Offsets past the end of the text saturate to the position just past
/// the last character. Offsets that land inside a multi-byte UTF-8
/// sequence round down to the start of that sequence.
pub fn byte_to_position(text: &str, byte_offset: usize) -> Position {
    let clamped = byte_offset.min(text.len());
    let mut line: u32 = 0;
    let mut character: u32 = 0;
    let mut bytes_seen = 0usize;

    for ch in text.chars() {
        if bytes_seen >= clamped {
            break;
        }
        let ch_len = ch.len_utf8();
        if ch == '\n' {
            line += 1;
            character = 0;
        } else {
            character += ch.len_utf16() as u32;
        }
        bytes_seen += ch_len;
    }
    Position { line, character }
}

/// Convert an LSP `Position` to a byte offset in `text`. Returns `None`
/// if the line doesn't exist; clamps over-long character offsets to the
/// end of the line.
pub fn position_to_byte(text: &str, pos: Position) -> Option<usize> {
    let mut line: u32 = 0;
    let mut byte_offset = 0usize;

    for ch in text.chars() {
        if line == pos.line {
            break;
        }
        byte_offset += ch.len_utf8();
        if ch == '\n' {
            line += 1;
        }
    }
    if line != pos.line {
        return None;
    }

    let mut character: u32 = 0;
    let mut iter = text[byte_offset..].chars();
    while character < pos.character {
        match iter.next() {
            Some('\n') | None => break,
            Some(ch) => {
                byte_offset += ch.len_utf8();
                character += ch.len_utf16() as u32;
            }
        }
    }
    Some(byte_offset)
}

/// Convert a span to an LSP-shaped `{start, end}` range as JSON.
pub fn span_to_range(text: &str, span: Span) -> Value {
    let start = byte_to_position(text, span.start);
    let end = byte_to_position(text, span.end);
    json!({
        "start": {"line": start.line, "character": start.character},
        "end":   {"line": end.line,   "character": end.character},
    })
}

/// Stable code string for an error variant. Editors can filter by this.
fn error_code(err: &MinfernError) -> &'static str {
    match err {
        MinfernError::Lex(e) => match e {
            LexError::UnexpectedCharacter { .. } => "UnexpectedCharacter",
            LexError::UnterminatedString { .. } => "UnterminatedString",
            LexError::UnterminatedComment { .. } => "UnterminatedComment",
            LexError::InvalidNumber { .. } => "InvalidNumber",
            LexError::InvalidEscapeSequence { .. } => "InvalidEscapeSequence",
            LexError::UnterminatedRegex { .. } => "UnterminatedRegex",
        },
        MinfernError::Parse(e) => match e {
            ParseError::UnexpectedToken { .. } => "UnexpectedToken",
            ParseError::UnexpectedEof { .. } => "UnexpectedEof",
            ParseError::InvalidAssignmentTarget { .. } => "InvalidAssignmentTarget",
            ParseError::InvalidForInTarget { .. } => "InvalidForInTarget",
            ParseError::DuplicateProperty { .. } => "DuplicateProperty",
            ParseError::BreakOutsideLoop { .. } => "BreakOutsideLoop",
            ParseError::ContinueOutsideLoop { .. } => "ContinueOutsideLoop",
            ParseError::ReturnOutsideFunction { .. } => "ReturnOutsideFunction",
        },
        MinfernError::Type(e) => match e {
            TypeError::UnificationError { .. } => "UnificationError",
            TypeError::OccursCheck { .. } => "OccursCheck",
            TypeError::UndefinedVariable { .. } => "UndefinedVariable",
            TypeError::PropertyNotFound { .. } => "PropertyNotFound",
            TypeError::NotAFunction { .. } => "NotAFunction",
            TypeError::ArityMismatch { .. } => "ArityMismatch",
            TypeError::TypeAnnotationParse { .. } => "TypeAnnotationParse",
            TypeError::Rank1Restriction { .. } => "Rank1Restriction",
            TypeError::ConstraintNotSatisfied { .. } => "ConstraintNotSatisfied",
            TypeError::EscapedSkolem { .. } => "EscapedSkolem",
            TypeError::AmbiguousType { .. } => "AmbiguousType",
            TypeError::AssignmentToConstant { .. } => "AssignmentToConstant",
            TypeError::AssignmentToPolymorphicProperty { .. } => "AssignmentToPolymorphicProperty",
            TypeError::Module { .. } => "Module",
        },
    }
}

fn error_span(err: &MinfernError) -> Span {
    match err {
        MinfernError::Lex(e) => e.span(),
        MinfernError::Parse(e) => e.span(),
        MinfernError::Type(e) => e.span(),
    }
}

/// Convert a single `MinfernError` into an LSP `Diagnostic` JSON object.
pub fn error_to_diagnostic(text: &str, err: &MinfernError) -> Value {
    json!({
        "range": span_to_range(text, error_span(err)),
        "severity": 1, // Error
        "source": "minfern",
        "code": error_code(err),
        "message": err.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn position_at_start() {
        let p = byte_to_position("hello", 0);
        assert_eq!(p, Position { line: 0, character: 0 });
    }

    #[test]
    fn position_after_newline() {
        let text = "ab\ncd";
        // offset of 'c' is 3
        let p = byte_to_position(text, 3);
        assert_eq!(p, Position { line: 1, character: 0 });
        let p = byte_to_position(text, 4);
        assert_eq!(p, Position { line: 1, character: 1 });
    }

    #[test]
    fn position_counts_utf16_units() {
        // U+1F600 (😀) is 4 bytes UTF-8 and 2 UTF-16 code units.
        let text = "a😀b";
        let p = byte_to_position(text, text.find('b').unwrap());
        assert_eq!(p, Position { line: 0, character: 3 });
    }

    #[test]
    fn position_to_byte_roundtrip() {
        let text = "var x = 1;\nvar y = 2;\n";
        for (i, _) in text.char_indices() {
            let pos = byte_to_position(text, i);
            assert_eq!(position_to_byte(text, pos), Some(i), "mismatch at {}", i);
        }
    }

    #[test]
    fn position_to_byte_clamps_past_line_end() {
        let text = "ab\ncd";
        // character 99 on line 0 → end of line 0 (offset of '\n')
        let pos = Position { line: 0, character: 99 };
        assert_eq!(position_to_byte(text, pos), Some(2));
    }

    #[test]
    fn position_to_byte_unknown_line() {
        let text = "ab";
        let pos = Position { line: 5, character: 0 };
        assert_eq!(position_to_byte(text, pos), None);
    }
}
