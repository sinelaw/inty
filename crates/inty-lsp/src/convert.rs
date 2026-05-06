//! Conversions between inty's byte spans and LSP positions, plus
//! `IntyError` → `lsp_types::Diagnostic` mapping.

use lsp_types::{Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range};
use inty::error::{LexError, IntyError, ParseError, TypeError};
use inty::infer::InferWarning;
use inty::lexer::Span;

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

/// Convert a span to an LSP `Range`.
pub fn span_to_range(text: &str, span: Span) -> Range {
    Range {
        start: byte_to_position(text, span.start),
        end: byte_to_position(text, span.end),
    }
}

/// Stable code string for an error variant. Editors can filter by this.
fn error_code(err: &IntyError) -> &'static str {
    match err {
        IntyError::Lex(e) => match e {
            LexError::UnexpectedCharacter { .. } => "UnexpectedCharacter",
            LexError::UnterminatedString { .. } => "UnterminatedString",
            LexError::UnterminatedComment { .. } => "UnterminatedComment",
            LexError::InvalidNumber { .. } => "InvalidNumber",
            LexError::InvalidEscapeSequence { .. } => "InvalidEscapeSequence",
            LexError::UnterminatedRegex { .. } => "UnterminatedRegex",
        },
        IntyError::Parse(e) => match e {
            ParseError::UnexpectedToken { .. } => "UnexpectedToken",
            ParseError::UnexpectedEof { .. } => "UnexpectedEof",
            ParseError::InvalidAssignmentTarget { .. } => "InvalidAssignmentTarget",
            ParseError::InvalidForInTarget { .. } => "InvalidForInTarget",
            ParseError::DuplicateProperty { .. } => "DuplicateProperty",
            ParseError::BreakOutsideLoop { .. } => "BreakOutsideLoop",
            ParseError::ContinueOutsideLoop { .. } => "ContinueOutsideLoop",
            ParseError::ReturnOutsideFunction { .. } => "ReturnOutsideFunction",
        },
        IntyError::Type(e) => match e {
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
            TypeError::InvalidSyntax { .. } => "InvalidSyntax",
            TypeError::TypeMismatch { .. } => "TypeMismatch",
        },
    }
}

fn error_span(err: &IntyError) -> Span {
    match err {
        IntyError::Lex(e) => e.span(),
        IntyError::Parse(e) => e.span(),
        IntyError::Type(e) => e.span(),
    }
}

/// Convert a single `IntyError` into an LSP `Diagnostic`.
pub fn error_to_diagnostic(text: &str, err: &IntyError) -> Diagnostic {
    Diagnostic {
        range: span_to_range(text, error_span(err)),
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String(error_code(err).to_string())),
        code_description: None,
        source: Some("inty".to_string()),
        message: err.to_string(),
        related_information: None,
        tags: None,
        data: None,
    }
}

/// Convert a non-fatal inference warning into an LSP `Diagnostic`.
pub fn warning_to_diagnostic(text: &str, warning: &InferWarning) -> Diagnostic {
    Diagnostic {
        range: span_to_range(text, warning.span),
        severity: Some(DiagnosticSeverity::WARNING),
        code: Some(NumberOrString::String("InferWarning".to_string())),
        code_description: None,
        source: Some("inty".to_string()),
        message: warning.message.clone(),
        related_information: None,
        tags: None,
        data: None,
    }
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
