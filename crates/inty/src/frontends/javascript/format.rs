//! `inty fmt`: lay out long statement annotations across lines.
//!
//! A one-line `/** type … */`, `/** function … */` or `/** const … */`
//! annotation longer than the width is rewritten one field, parameter or
//! union member per line, with a `*` margin and a trailing comma:
//!
//! ```text
//! /** type ScoreView = {
//!  *   id: String,
//!  *   size: Number,
//!  * } */
//! ```
//!
//! Nothing else changes: short annotations, annotations already written
//! across lines, annotations with a `//` comment, `class` declarations and
//! annotations of several declarators (`/** var a: A, b: B */`) are left
//! as they are, as is all code. A multi-line annotation is never touched,
//! so formatting twice gives what formatting once gave.
//!
//! The rewritten annotation reads to the same type: before it replaces
//! the original, its text (read back the way the checker reads it, less
//! whitespace, trailing commas and a leading `|`) is compared with the
//! original's, and an annotation that would differ is left alone.

use super::lexer::{Scanner, Token};
use crate::error::Result;

/// The width `inty fmt` wraps at unless told otherwise.
pub const DEFAULT_WIDTH: usize = 100;

/// `source` with each statement annotation whose line runs past `width`
/// columns laid out across lines. Fails only when `source` doesn't lex.
pub fn format_annotations(source: &str, width: usize) -> Result<String> {
    let mut scanner = Scanner::new(source);
    while scanner.next_token()?.value != Token::Eof {}
    let mut out = source.to_string();
    // Back to front, so earlier spans stay valid.
    for span in scanner.annotation_comments().iter().rev() {
        let comment = &source[span.start..span.end];
        if let Some(new) = format_comment(source, span.start, comment, width) {
            out.replace_range(span.start..span.end, &new);
        }
    }
    Ok(out)
}

/// The comment at `start`, laid out across lines, or `None` to keep it.
fn format_comment(source: &str, start: usize, comment: &str, width: usize) -> Option<String> {
    if comment.contains('\n') {
        return None;
    }
    let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
    let before = &source[line_start..start];
    let col = before.chars().count();
    if col + comment.chars().count() <= width {
        return None;
    }
    let inner = comment.strip_prefix("/**")?.strip_suffix("*/")?;
    let text = inner.trim();
    if has_line_comment(text) {
        return None;
    }
    // Continuation lines line their `*` up under the opening `/**`'s
    // first `*`, indented as the comment's line is.
    let indent: String = if before.chars().all(char::is_whitespace) {
        before.to_string()
    } else {
        " ".repeat(col)
    };
    let margin = format!("{indent} * ");
    let fit = Fit {
        width,
        margin: col + 3,
    };
    let laid = lay_out_annotation(text, &fit)?;
    let mut new = format!("/** {}", laid.lines[0]);
    for line in &laid.lines[1..] {
        new.push('\n');
        if line.is_empty() {
            new.push_str(margin.trim_end());
        } else {
            new.push_str(&margin);
            new.push_str(line);
        }
    }
    if laid.close_on_own_line {
        new.push('\n');
        new.push_str(&indent);
        new.push_str(" */");
    } else {
        new.push_str(" */");
    }
    // The new annotation must read as the old one did.
    let body = new.strip_prefix("/**")?.strip_suffix("*/")?;
    let cleaned = super::lexer::clean_doc_body(body);
    if normalize(&cleaned) != normalize(text) {
        return None;
    }
    Some(new)
}

/// The lines of a laid-out annotation: the first follows `/** `, the
/// rest follow the `*` margin, indented relative to it.
struct Laid {
    lines: Vec<String>,
    /// `*/` goes on a line of its own (after a union's members), rather
    /// than after the last line (`} */`).
    close_on_own_line: bool,
}

/// How much fits on a line.
struct Fit {
    width: usize,
    /// Columns before a continuation line's text: the indentation and `* `.
    margin: usize,
}

impl Fit {
    fn fits(&self, indent: usize, text: &str) -> bool {
        self.margin + indent + text.chars().count() <= self.width
    }
}

/// Lay out the annotation `text` (its body, `type X = …`, without the
/// comment's delimiters).
fn lay_out_annotation(text: &str, fit: &Fit) -> Option<Laid> {
    let rest = text.strip_prefix("export ").map_or(text, str::trim_start);
    let keyword = rest.split(|c: char| !c.is_alphanumeric()).next()?;
    // The text up to where the annotation's type starts, when a union
    // there is to be laid out one member per line.
    let head_end = match keyword {
        "type" | "nominal" => Some(top_level_find(text, |t, i| {
            t[i..].starts_with('=') && !t[i..].starts_with("=>")
        })?),
        "const" | "let" | "var" => {
            let colon = top_level_find(text, |t, i| t[i..].starts_with(':'))?;
            // Several declarators: left as they are.
            if split_top(&text[colon + 1..], ',').len() > 1 {
                return None;
            }
            Some(colon)
        }
        "function" => None,
        _ => return None,
    };
    if let Some(at) = head_end {
        let (head, ty) = (text[..=at].trim_end(), text[at + 1..].trim());
        let members = split_top(ty, '|');
        if members.len() > 1 && members.iter().all(|m| !m.is_empty()) {
            let mut lines = vec![head.to_string()];
            for m in members {
                let sub = lay_out(m, 4, fit);
                lines.push(format!("  | {}", sub[0]));
                lines.extend(sub[1..].iter().cloned());
            }
            return Some(Laid {
                lines,
                close_on_own_line: true,
            });
        }
    }
    let lines = break_group(text, 0, fit)?;
    Some(Laid {
        lines,
        close_on_own_line: false,
    })
}

/// `text` laid out at `indent` columns past the margin: as is when it
/// fits, else with its largest bracketed group one item per line. The
/// first line carries no indentation (it continues a line); the others
/// carry theirs.
fn lay_out(text: &str, indent: usize, fit: &Fit) -> Vec<String> {
    if fit.fits(indent, text) {
        return vec![text.to_string()];
    }
    break_group(text, indent, fit).unwrap_or_else(|| vec![text.to_string()])
}

/// `text` with its largest top-level `{…}`, `(…)` or `[…]` group broken
/// one item per line, each followed by a comma. `None` when it has none.
fn break_group(text: &str, indent: usize, fit: &Fit) -> Option<Vec<String>> {
    let (open, close) = top_level_groups(text)
        .into_iter()
        .max_by_key(|&(open, close)| (close - open, std::cmp::Reverse(open)))?;
    let items = split_top(&text[open + 1..close], ',');
    let items: Vec<&str> = items.into_iter().filter(|i| !i.is_empty()).collect();
    if items.is_empty() {
        return None;
    }
    let pad = " ".repeat(indent + 2);
    let mut lines = vec![text[..=open].trim_end().to_string()];
    for item in items {
        let mut sub = lay_out(item, indent + 2, fit);
        sub.last_mut()?.push(',');
        lines.push(format!("{pad}{}", sub[0]));
        lines.extend(sub.into_iter().skip(1));
    }
    lines.push(format!("{}{}", " ".repeat(indent), text[close..].trim()));
    Some(lines)
}

/// Bracket structure of an annotation's text, outside string literals.
/// Calls `visit(index, char, depth_before)` for each character not in a
/// string; a `>` closes only an open `<`, so `=>` doesn't.
fn walk(text: &str, mut visit: impl FnMut(usize, char, usize) -> bool) {
    let mut depth = 0usize;
    let mut angle = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut prev = '\0';
    for (i, c) in text.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            prev = c;
            continue;
        }
        if !visit(i, c, depth) {
            return;
        }
        match c {
            '"' => in_string = true,
            '{' | '(' | '[' => depth += 1,
            '<' => {
                depth += 1;
                angle += 1;
            }
            '}' | ')' | ']' => depth = depth.saturating_sub(1),
            '>' if angle > 0 && prev != '=' => {
                depth = depth.saturating_sub(1);
                angle -= 1;
            }
            _ => {}
        }
        prev = c;
    }
}

/// The first index outside brackets and strings where `at` holds.
fn top_level_find(text: &str, at: impl Fn(&str, usize) -> bool) -> Option<usize> {
    let mut found = None;
    walk(text, |i, _, depth| {
        if depth == 0 && at(text, i) {
            found = Some(i);
            return false;
        }
        true
    });
    found
}

/// The `{`, `(` and `[` groups outside any bracket: `(open, close)`.
fn top_level_groups(text: &str) -> Vec<(usize, usize)> {
    let mut groups = Vec::new();
    let mut open: Option<usize> = None;
    walk(text, |i, c, depth| {
        match (depth, c) {
            (0, '{' | '(' | '[') => open = Some(i),
            (1, '}' | ')' | ']') => {
                if let Some(o) = open.take() {
                    groups.push((o, i));
                }
            }
            _ => {}
        }
        true
    });
    groups
}

/// `text` split at `sep` outside brackets and strings, each part trimmed.
fn split_top(text: &str, sep: char) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut from = 0;
    walk(text, |i, c, depth| {
        // `||` isn't a separator (nor in the type grammar).
        if depth == 0 && c == sep && !(sep == '|' && text[i + 1..].starts_with('|')) {
            parts.push(text[from..i].trim());
            from = i + 1;
        }
        true
    });
    parts.push(text[from..].trim());
    // A leading `|` leaves an empty first member.
    if sep == '|' && parts.first() == Some(&"") && parts.len() > 1 {
        parts.remove(0);
    }
    parts
}

/// Whether `text` holds a `//` comment (outside a string literal type).
fn has_line_comment(text: &str) -> bool {
    let mut found = false;
    walk(text, |i, c, _| {
        if c == '/' && text[i + 1..].starts_with('/') {
            found = true;
            return false;
        }
        true
    });
    found
}

/// An annotation's text as far as its meaning goes: without whitespace
/// (outside strings), trailing commas, or a union's leading `|`.
fn normalize(text: &str) -> String {
    let mut out = String::new();
    let mut in_string = false;
    let mut escaped = false;
    for c in text.chars() {
        if in_string {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        if c.is_whitespace() {
            continue;
        }
        if matches!(c, '}' | ')' | ']' | '>') && out.ends_with(',') {
            out.pop();
        }
        if c == '|' && (out.ends_with('=') || out.ends_with(':')) {
            continue;
        }
        if c == '"' {
            in_string = true;
        }
        out.push(c);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(src: &str, width: usize) -> String {
        let out = format_annotations(src, width).unwrap();
        // Idempotent.
        assert_eq!(format_annotations(&out, width).unwrap(), out);
        out
    }

    #[test]
    fn a_long_record_type_is_laid_out_one_field_per_line() {
        let src =
            "/** type ScoreView = { id: String, scope: String, size: Number, zoom: Number } */\n";
        assert_eq!(
            fmt(src, 60),
            "/** type ScoreView = {\n *   id: String,\n *   scope: String,\n *   size: Number,\n *   zoom: Number,\n * } */\n"
        );
    }

    #[test]
    fn a_short_annotation_stays_on_one_line() {
        let src = "/** type P = { x: Number, y: Number } */\n/** const p: P */\nconst p = { x: 1, y: 2 };\n";
        assert_eq!(fmt(src, 100), src);
    }

    #[test]
    fn a_long_signature_is_laid_out_one_parameter_per_line() {
        let src = "/** function sideView(b: Builder, v: ScoreView, c: Cached) => Undefined */\nfunction sideView(b, v, c) {}\n";
        assert_eq!(
            fmt(src, 40),
            "/** function sideView(\n *   b: Builder,\n *   v: ScoreView,\n *   c: Cached,\n * ) => Undefined */\nfunction sideView(b, v, c) {}\n"
        );
    }

    #[test]
    fn a_long_union_is_laid_out_one_member_per_line() {
        let src = "/** type Shape = { kind: \"circle\", r: Number } | { kind: \"rect\", w: Number, h: Number } */\n";
        assert_eq!(
            fmt(src, 60),
            "/** type Shape =\n *   | { kind: \"circle\", r: Number }\n *   | { kind: \"rect\", w: Number, h: Number }\n */\n"
        );
    }

    #[test]
    fn nested_records_break_only_where_they_are_too_long() {
        let src = "/** const layout: { width: Number, page: { n: Number, top: Number, left: Number, bottom: Number }, z: Number } */\n";
        assert_eq!(
            fmt(src, 50),
            "/** const layout: {\n *   width: Number,\n *   page: {\n *     n: Number,\n *     top: Number,\n *     left: Number,\n *     bottom: Number,\n *   },\n *   z: Number,\n * } */\n"
        );
    }

    #[test]
    fn indentation_is_kept() {
        let src = "function f() {\n    /** const v: { a: Number, b: String, c: Boolean } */\n    const v = { a: 1, b: \"\", c: true };\n}\n";
        assert_eq!(
            fmt(src, 40),
            "function f() {\n    /** const v: {\n     *   a: Number,\n     *   b: String,\n     *   c: Boolean,\n     * } */\n    const v = { a: 1, b: \"\", c: true };\n}\n"
        );
    }

    #[test]
    fn the_largest_group_is_the_one_broken() {
        let src =
            "/** function f(a: Number) => { x: Number, y: Number, z: Number, w: Number } */\n";
        assert_eq!(
            fmt(src, 50),
            "/** function f(a: Number) => {\n *   x: Number,\n *   y: Number,\n *   z: Number,\n *   w: Number,\n * } */\n"
        );
    }

    #[test]
    fn what_it_leaves_alone() {
        let long = "x".repeat(120);
        for src in [
            // Several declarators.
            format!("/** var a: {{ k: {long} }}, b: Number */\n"),
            // A comment inside.
            format!("/** const a: {{ k: Number, m: Number }} // {long} */\n"),
            // A class declaration.
            format!("/** class C {{ k: Number, m: {long} }} */\nclass C {{}}\n"),
            // Not an annotation.
            format!("/** {long}, {long} */\n"),
            // Already across lines.
            format!("/** type A = {{\n *   k: {long},\n * }} */\n"),
            // Nothing to break.
            format!("/** type A = {long} */\n"),
        ] {
            assert_eq!(fmt(&src, 40), src);
        }
    }

    #[test]
    fn strings_keep_their_commas_and_brackets() {
        let src = "/** type T = { a: \"x, {y}\" | \"(z]\", b: Number, c: String } */\n";
        assert_eq!(
            fmt(src, 30),
            "/** type T = {\n *   a: \"x, {y}\" | \"(z]\",\n *   b: Number,\n *   c: String,\n * } */\n"
        );
    }

    #[test]
    fn normalize_ignores_layout_only() {
        assert_eq!(normalize("{ a: A, b: B, }"), normalize("{a: A, b: B}"));
        assert_eq!(normalize("=\n | A\n | B"), normalize("= A | B"));
        assert_ne!(normalize("\"a b\""), normalize("\"ab\""));
    }
}
