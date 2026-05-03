//! Diagnostic printing for minfern errors.

use std::io::Write;

use ariadne::{Color, ColorGenerator, Config, Fmt, Label, Report, ReportKind, Source};

use crate::error::{LexError, MinfernError, ParseError, TypeError};
use crate::lexer::Span;

/// Ariadne interprets label offsets as character (Unicode scalar) indices,
/// not byte offsets. Minfern's lexer tracks positions in bytes, so every
/// span destined for ariadne must be converted first. If this conversion is
/// skipped, any multi-byte character (including non-ASCII letters, emoji,
/// and typographic symbols) earlier in the source shifts the underline to
/// the right by the extra bytes those characters occupy.
///
/// The conversion also rounds a byte offset that lands inside a multi-byte
/// sequence down to the preceding character boundary, so we never split a
/// grapheme in the middle.
fn byte_to_char_offset(source: &str, byte_offset: usize) -> usize {
    if byte_offset >= source.len() {
        return source.chars().count();
    }
    let mut boundary = byte_offset;
    while boundary > 0 && !source.is_char_boundary(boundary) {
        boundary -= 1;
    }
    source[..boundary].chars().count()
}

/// Convert a minfern byte-offset span to the character-offset range that
/// ariadne expects.
fn char_range(source: &str, span: Span) -> std::ops::Range<usize> {
    let start = byte_to_char_offset(source, span.start);
    let end = byte_to_char_offset(source, span.end);
    start..end
}

/// Print a minfern error with colored diagnostics to stderr.
pub fn print_error(filename: &str, source: &str, error: &MinfernError) {
    let _ = write_error(std::io::stderr(), filename, source, error, true);
}

/// Print a minfern error to stderr without ANSI color escapes.
pub fn print_error_plain(filename: &str, source: &str, error: &MinfernError) {
    let _ = write_error(std::io::stderr(), filename, source, error, false);
}

/// Render a minfern error into `writer`.
///
/// Extracted from [`print_error`] so tests (and future consumers that
/// pipe diagnostics) can inspect the rendered output without spawning
/// the binary or capturing a global stderr. Set `color = false` to
/// suppress ANSI escape sequences — the CLI uses this for `--no-color`
/// and tests use it to assert on plain text directly.
pub fn write_error<W: Write>(
    mut writer: W,
    filename: &str,
    source: &str,
    error: &MinfernError,
    color: bool,
) -> std::io::Result<()> {
    let config = Config::new().with_color(color);
    // `Fmt::fg` always emits ANSI escapes, independent of ariadne's Config.
    // Wrap it so message strings stay plain when `color` is false.
    let tint = |s: &str, c: Color| -> String {
        if color {
            s.fg(c).to_string()
        } else {
            s.to_string()
        }
    };
    // Handle UnificationError specially since it has multiple labels
    if let MinfernError::Type(TypeError::UnificationError {
        expected,
        found,
        span,
        context,
        expected_origin,
        found_origin,
    }) = error
    {
        let mut colors = ColorGenerator::new();
        let expected_color = colors.next();
        let found_color = colors.next();
        let error_color = Color::Red;

        let msg = format!(
            "Type mismatch: {} '{}', {} '{}'",
            tint("expected", expected_color),
            expected,
            tint("found", found_color),
            found
        );

        let main_range = char_range(source, *span);
        let mut report = Report::build(ReportKind::Error, (filename, main_range.clone()))
            .with_config(config)
            .with_message(&msg)
            .with_label(
                Label::new((filename, main_range))
                    .with_message(&msg)
                    .with_color(error_color),
            );

        if let Some(ctx) = context {
            report.add_help(ctx.clone());
        }

        if let Some(origin) = expected_origin {
            let origin_range = char_range(source, origin.span());
            report = report.with_label(
                Label::new((filename, origin_range))
                    .with_message(format!(
                        "{} type: from {}",
                        tint("Expected", expected_color),
                        origin.description()
                    ))
                    .with_color(expected_color),
            );
        }

        if let Some(origin) = found_origin {
            let origin_range = char_range(source, origin.span());
            report = report.with_label(
                Label::new((filename, origin_range))
                    .with_message(format!(
                        "{} type: from {}",
                        tint("Found", found_color),
                        origin.description()
                    ))
                    .with_color(found_color),
            );
        }

        // Add footer note explaining why this is an error
        report.add_note(format!(
            "Cannot unify {} '{}' with {} '{}'",
            tint("expected", expected_color),
            expected,
            tint("found", found_color),
            found
        ));

        writeln!(writer)?;
        report
            .finish()
            .write((filename, Source::from(source)), &mut writer)?;
        writeln!(writer)?;
        return Ok(());
    }

    // Handle all other errors with single note
    let (message, span, note) = match error {
        MinfernError::Lex(e) => match e {
            LexError::UnexpectedCharacter { ch, span } => {
                (format!("Unexpected character: '{}'", ch), *span, None)
            }
            LexError::UnterminatedString { span } => {
                ("Unterminated string literal".to_string(), *span, None)
            }
            LexError::UnterminatedRegex { span } => {
                ("Unterminated regex literal".to_string(), *span, None)
            }
            LexError::InvalidEscapeSequence { span } => {
                ("Invalid escape sequence".to_string(), *span, None)
            }
            LexError::UnterminatedComment { span } => {
                ("Unterminated comment".to_string(), *span, None)
            }
            LexError::InvalidNumber { span } => ("Invalid number literal".to_string(), *span, None),
        },

        MinfernError::Parse(e) => match e {
            ParseError::UnexpectedToken {
                found,
                expected,
                span,
            } => (
                format!("Unexpected token: found '{}', expected {}", found, expected),
                *span,
                None,
            ),
            ParseError::UnexpectedEof { span } => {
                ("Unexpected end of file".to_string(), *span, None)
            }
            ParseError::InvalidAssignmentTarget { span } => {
                ("Invalid assignment target".to_string(), *span, None)
            }
            ParseError::DuplicateProperty { name, span } => {
                (format!("Duplicate property: '{}'", name), *span, None)
            }
            ParseError::InvalidForInTarget { span } => (
                "Invalid left-hand side in for-in/of loop".to_string(),
                *span,
                None,
            ),
            ParseError::BreakOutsideLoop { span } => {
                ("'break' outside of loop or switch".to_string(), *span, None)
            }
            ParseError::ContinueOutsideLoop { span } => {
                ("'continue' outside of loop".to_string(), *span, None)
            }
            ParseError::ReturnOutsideFunction { span } => {
                ("'return' outside of function".to_string(), *span, None)
            }
        },

        MinfernError::Type(e) => match e {
            TypeError::UnificationError { .. } => {
                unreachable!("UnificationError is handled above")
            }
            TypeError::OccursCheck { var, ty, span } => (
                format!("Infinite type: {} occurs in {}", var, ty),
                *span,
                Some("This would create an infinite type".to_string()),
            ),
            TypeError::UndefinedVariable { name, span } => {
                (format!("Undefined variable: '{}'", name), *span, None)
            }
            TypeError::PropertyNotFound {
                prop,
                obj_type,
                span,
            } => (
                format!("Property '{}' not found in type {}", prop, obj_type),
                *span,
                None,
            ),
            TypeError::NotAFunction { ty, span } => {
                (format!("Type '{}' is not a function", ty), *span, None)
            }
            TypeError::ArityMismatch {
                expected,
                found,
                span,
            } => (
                format!(
                    "Arity mismatch: expected {} arguments, found {}",
                    expected, found
                ),
                *span,
                None,
            ),
            TypeError::ConstraintNotSatisfied { class, ty, span } => (
                format!("Type '{}' is not an instance of {}", ty, class),
                *span,
                None,
            ),
            TypeError::TypeAnnotationParse { message, span } => (
                format!("Failed to parse type annotation: {}", message),
                *span,
                None,
            ),
            TypeError::Rank1Restriction { span } => (
                "Rank-1 restriction: type parameters not allowed in nested position".to_string(),
                *span,
                Some(
                    "Type parameters (<T>) can only appear at the outermost level of a type. \
                    Nested type parameters would require Rank-2 or higher polymorphism."
                        .to_string(),
                ),
            ),
            TypeError::EscapedSkolem { span } => (
                "Escaped skolem variable: type is not polymorphic enough".to_string(),
                *span,
                None,
            ),
            TypeError::AmbiguousType { span } => (
                "Ambiguous type: multiple valid instantiations".to_string(),
                *span,
                None,
            ),
            TypeError::AssignmentToConstant { name, span } => (
                format!("Cannot assign to constant '{}'", name),
                *span,
                Some("This binding is immutable and cannot be reassigned".to_string()),
            ),
            TypeError::AssignmentToPolymorphicProperty {
                object,
                property,
                span,
            } => (
                format!(
                    "Cannot assign to polymorphic property '{}' of immutable binding '{}'",
                    property, object
                ),
                *span,
                Some(
                    "Assigning to a polymorphic property would violate type safety. \
                    The property type uses type parameters that could be instantiated differently."
                        .to_string(),
                ),
            ),
            TypeError::Module { message, span } => (message.clone(), *span, None),
        },
    };

    let range = char_range(source, span);
    let mut report = Report::build(ReportKind::Error, (filename, range.clone()))
        .with_config(config)
        .with_message(&message)
        .with_label(
            Label::new((filename, range))
                .with_message(&message)
                .with_color(Color::Red),
        );

    if let Some(note_text) = note {
        report.add_help(note_text);
    }

    report
        .finish()
        .write((filename, Source::from(source)), &mut writer)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TypeError;
    use crate::lexer::Span;

    #[test]
    fn byte_to_char_offset_handles_multi_byte_chars() {
        // Em dash (—) is 3 bytes, 1 char.
        let s = "a—b";
        assert_eq!(byte_to_char_offset(s, 0), 0); // before 'a'
        assert_eq!(byte_to_char_offset(s, 1), 1); // after 'a', before '—'
        assert_eq!(byte_to_char_offset(s, 4), 2); // after '—', before 'b'
        assert_eq!(byte_to_char_offset(s, 5), 3); // after 'b'
    }

    #[test]
    fn byte_to_char_offset_rounds_down_inside_multi_byte() {
        // If a byte offset lands inside a multi-byte sequence we must round
        // down rather than panic. (`source[..offset]` would otherwise panic.)
        let s = "a—b"; // 'a' + em-dash (3 bytes) + 'b'
        assert_eq!(byte_to_char_offset(s, 2), 1); // inside em-dash
        assert_eq!(byte_to_char_offset(s, 3), 1);
    }

    fn render_error(source: &str, error: &MinfernError) -> String {
        let mut buf = Vec::new();
        // color=false keeps tests asserting on plain text without having
        // to strip ANSI escapes after the fact.
        write_error(&mut buf, "test.js", source, error, false).unwrap();
        String::from_utf8(buf).unwrap()
    }

    /// Column (in chars) of the first non-space, non-gutter marker on the
    /// line after the source line. Ariadne uses `─` for wide spans and
    /// `┬` for single-char spans, so accept either.
    fn underline_marker_col(underline_content: &str) -> usize {
        underline_content
            .chars()
            .position(|c| c == '─' || c == '┬')
            .expect("underline marker (─ or ┬) in underline line")
    }

    /// Column (in chars) of the first occurrence of `needle` in
    /// `src_content`. We count chars, not bytes, because ariadne also
    /// lays out the display in chars.
    fn source_col(src_content: &str, needle: &str) -> usize {
        let byte_idx = src_content
            .find(needle)
            .unwrap_or_else(|| panic!("{:?} present in source line", needle));
        src_content[..byte_idx].chars().count()
    }

    /// Regression test for highlighting offset when multi-byte Unicode
    /// characters appear earlier in the source.
    ///
    /// Minfern stores spans in bytes. Ariadne interprets span offsets as
    /// character indices. Before the fix, the em-dash below would shift the
    /// underline 2 columns to the right of `x`, because the span's byte
    /// start landed past the dash but ariadne counted it as characters.
    #[test]
    fn unification_underline_aligned_after_multi_byte_char() {
        // Prefix contains an em-dash (3 bytes, 1 char). The error span is
        // for the literal `x` on the second line.
        let source = "// —\nvar x = 1;\n";
        // Byte offset of `x`:
        //   "// " = 3 bytes, "—" = 3 bytes, "\n" = 1 byte, "var " = 4 bytes
        //   -> 3 + 3 + 1 + 4 = 11
        let x_start = source.find("x").unwrap();
        assert_eq!(x_start, 11, "fixture math");
        let span = Span::new(x_start, x_start + 1);

        let error = MinfernError::Type(TypeError::UnificationError {
            expected: "String".to_string(),
            found: "Number".to_string(),
            span,
            context: None,
            expected_origin: None,
            found_origin: None,
        });

        let rendered = render_error(source, &error);

        // Find the source-display line that contains `var x = 1;` and the
        // underline line that follows it.
        let lines: Vec<&str> = rendered.lines().collect();
        let src_idx = lines
            .iter()
            .position(|l| l.contains("var x = 1;"))
            .expect("source line in rendered output");
        let underline = lines
            .get(src_idx + 1)
            .expect("underline line in rendered output");

        // Split on `│` so we only compare the content side of the gutter.
        let src_content = lines[src_idx].split('│').nth(1).unwrap();
        let under_content = underline.split('│').nth(1).unwrap();

        let x_col = source_col(src_content, "x");
        let under_col = underline_marker_col(under_content);

        assert_eq!(
            x_col, under_col,
            "underline offset does not match `x` column\n\
             rendered:\n{}",
            rendered
        );
    }

    /// Non-unification errors take a different code path — make sure they
    /// also honour multi-byte offsets.
    #[test]
    fn undefined_variable_underline_aligned_after_multi_byte_char() {
        let source = "// ✓ ×\nfoo;\n";
        let foo_start = source.find("foo").unwrap();
        let span = Span::new(foo_start, foo_start + 3);

        let error = MinfernError::Type(TypeError::UndefinedVariable {
            name: "foo".to_string(),
            span,
        });

        let rendered = render_error(source, &error);
        let lines: Vec<&str> = rendered.lines().collect();
        let src_idx = lines
            .iter()
            .position(|l| l.contains("foo;"))
            .expect("source line in rendered output");
        let src_content = lines[src_idx].split('│').nth(1).unwrap();
        let under_content = lines[src_idx + 1].split('│').nth(1).unwrap();

        let foo_col = source_col(src_content, "foo");
        let under_col = underline_marker_col(under_content);

        assert_eq!(
            foo_col, under_col,
            "underline offset does not match `foo` column\n\
             rendered:\n{}",
            rendered
        );
    }

    /// Baseline: ASCII-only sources must still underline the right span.
    #[test]
    fn underline_aligned_ascii_only() {
        let source = "var x = 1;\n";
        let x_start = source.find("x").unwrap();
        let span = Span::new(x_start, x_start + 1);

        let error = MinfernError::Type(TypeError::UndefinedVariable {
            name: "x".to_string(),
            span,
        });

        let rendered = render_error(source, &error);
        let lines: Vec<&str> = rendered.lines().collect();
        let src_idx = lines
            .iter()
            .position(|l| l.contains("var x = 1;"))
            .expect("source line");
        let src_content = lines[src_idx].split('│').nth(1).unwrap();
        let under_content = lines[src_idx + 1].split('│').nth(1).unwrap();

        let x_col = source_col(src_content, "x");
        let under_col = underline_marker_col(under_content);
        assert_eq!(x_col, under_col);
    }
}
