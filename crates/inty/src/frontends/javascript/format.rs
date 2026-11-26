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
//! the original, both are read the way the checker reads them and each
//! type's syntax is parsed ([`parse_type_syntax`]); an annotation whose
//! rewrite declares anything different, or doesn't parse, is left alone,
//! as is one that didn't parse to begin with.

use super::lexer::{clean_doc_body, read_doc_annotation, Scanner, Token};
use crate::error::Result;
use crate::infer::type_parser::parse_type_syntax;
use crate::types::Type;

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
    // The file's own line ending, as the comment's line ends.
    let line_end = source[start..]
        .find('\n')
        .filter(|&i| source[..start + i].ends_with('\r'))
        .map_or("\n", |_| "\r\n");
    let fit = Fit {
        width,
        margin: col + 3,
    };
    let laid = lay_out_annotation(text, &fit)?;
    let mut new = format!("/** {}", laid.lines[0]);
    for line in &laid.lines[1..] {
        new.push_str(line_end);
        if line.is_empty() {
            new.push_str(margin.trim_end());
        } else {
            new.push_str(&margin);
            new.push_str(line);
        }
    }
    if laid.close_on_own_line {
        new.push_str(line_end);
        new.push_str(&indent);
        new.push_str(" */");
    } else {
        new.push_str(" */");
    }
    // The new annotation must read as the old one did: the same
    // declarations, each type parsing to the same type.
    if read_types(comment)? != read_types(&new)? {
        return None;
    }
    Some(new)
}

/// What a statement-annotation comment declares, as the checker reads
/// it: each annotation's name and kind with its type's syntax, each
/// alias's name and parameters with its body's. `None` when it isn't an
/// annotation or a type in it doesn't parse.
fn read_types(comment: &str) -> Option<Vec<(String, std::result::Result<Type, String>)>> {
    let raw = comment.strip_prefix("/**")?.strip_suffix("*/")?;
    let cleaned = clean_doc_body(raw);
    let doc = read_doc_annotation(raw, &cleaned, 3, 0)?;
    let mut out = Vec::new();
    for a in &doc.annotations {
        out.push((
            format!("{} {:?}", a.name, a.kind),
            parse_type_syntax(&a.content),
        ));
    }
    for a in &doc.aliases {
        let head = format!("type {}<{}> {}", a.name, a.params.join(","), a.nominal);
        out.push((head, parse_type_syntax(&a.body)));
    }
    if out.iter().any(|(_, t)| t.is_err()) {
        return None;
    }
    Some(out)
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
            // Several declarators: left as they are. Counted as the
            // annotation reader counts them, as a scheme's `where`
            // constraints are also separated by top-level commas.
            if read_types(&format!("/** {text} */"))?.len() > 1 {
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
        // A function type's result takes in the rest of a union
        // (`(A) => B | C` returns `B | C`), and a quantified type starts
        // with `<`: laid out one member per line, either would read
        // wrong, so such a union is broken some other way.
        let one_per_line = members.len() > 1
            && members.iter().all(|m| !m.is_empty() && !m.starts_with('<'))
            && members[..members.len() - 1]
                .iter()
                .all(|m| top_level_find(m, |t, i| t[i..].starts_with("=>")).is_none());
        if one_per_line {
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
        .filter(|&(open, close)| breakable(text, open, close))
        .max_by_key(|&(open, close)| (close - open, std::cmp::Reverse(open)))?;
    let inner = &text[open + 1..close];
    // A record's fields may be separated by `;` as well as `,`.
    let items = if text[open..].starts_with('{') {
        split_top(inner, ',')
            .into_iter()
            .flat_map(|i| split_top(i, ';'))
            .collect()
    } else {
        split_top(inner, ',')
    };
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

/// Whether the group `open..=close` is a list a trailing comma may end:
/// a record, a function's parameters (`(…) =>`), or a tuple. Not a
/// parenthesised type (`(A | B)[]`) or an index key (`[String]: V`,
/// `[Symbol.iterator]: T`).
fn breakable(text: &str, open: usize, close: usize) -> bool {
    let after = text[close + 1..].trim_start();
    match &text[open..open + 1] {
        "{" => true,
        "(" => after.starts_with("=>"),
        "[" => !after.starts_with(':'),
        _ => false,
    }
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
    fn a_constrained_scheme_is_laid_out_one_parameter_per_line() {
        // The `where` constraints' commas are not declarators'.
        let src = "/** const f: <a, b> where a has {length: b} => (a, (a) => b, Number) => b */\nconst f;\n";
        assert_eq!(
            fmt(src, 60),
            "/** const f: <a, b> where a has {length: b} => (\n *   a,\n *   (a) => b,\n *   Number,\n * ) => b */\nconst f;\n"
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
    fn a_parenthesised_type_or_index_key_is_not_broken() {
        // Not lists: a trailing comma would make them unparseable.
        let src = "/** type T = (Number | String | Boolean | Undefined | Null)[] */\n";
        assert_eq!(fmt(src, 30), src);
        let src = "/** type Bag = { [Symbol.iterator]: () => Number, size: Number } */\n";
        assert_eq!(
            fmt(src, 34),
            "/** type Bag = {\n *   [Symbol.iterator]: () => Number,\n *   size: Number,\n * } */\n"
        );
        let src = "/** type D = { [keyyyyyyyyyyyyyyyyyyyyyyyyy: String]: Number } */\n";
        assert_eq!(
            fmt(src, 34),
            "/** type D = {\n *   [keyyyyyyyyyyyyyyyyyyyyyyyyy: String]: Number,\n * } */\n"
        );
    }

    #[test]
    fn a_union_after_a_function_type_is_not_split() {
        // `(A) => B | C` returns `B | C`, and `<T>…` can't follow `|`.
        let src = "/** const g: (aaaaaaaaaaaaaaaaaaaa: Number) => Number | String */\n";
        assert_eq!(
            fmt(src, 40),
            "/** const g: (\n *   aaaaaaaaaaaaaaaaaaaa: Number,\n * ) => Number | String */\n"
        );
        let src = "/** const id: <T>(xxxxxxxxxxxxxxxx: T, yyyyyyyyyyyyyy: T) => T | Null */\n";
        assert_eq!(
            fmt(src, 40),
            "/** const id: <T>(\n *   xxxxxxxxxxxxxxxx: T,\n *   yyyyyyyyyyyyyy: T,\n * ) => T | Null */\n"
        );
    }

    #[test]
    fn semicolon_separated_fields_are_split() {
        let src = "/** const o: { aaaaaaaaaa: Number; bbbbbbbbbbbb: String; c: Boolean } */\n";
        assert_eq!(
            fmt(src, 40),
            "/** const o: {\n *   aaaaaaaaaa: Number,\n *   bbbbbbbbbbbb: String,\n *   c: Boolean,\n * } */\n"
        );
    }

    #[test]
    fn annotations_naming_generic_aliases_are_laid_out() {
        // Names declared elsewhere, with type arguments, still read.
        let src = "/** const p: { a: Pair<Number>, b: Map<String, Number,>, c: Number } */\n";
        assert_eq!(
            fmt(src, 30),
            "/** const p: {\n *   a: Pair<Number>,\n *   b: Map<String, Number,>,\n *   c: Number,\n * } */\n"
        );
    }

    #[test]
    fn crlf_files_keep_crlf() {
        let src = "/** type A = { aaaaaaaaaa: Number, bbbbbbbbbb: String } */\r\nconst x = 1;\r\n";
        let out = fmt(src, 30);
        assert_eq!(
            out,
            "/** type A = {\r\n *   aaaaaaaaaa: Number,\r\n *   bbbbbbbbbb: String,\r\n * } */\r\nconst x = 1;\r\n"
        );
    }

    #[test]
    fn a_rewrite_must_parse_to_the_same_type() {
        let same = read_types("/** type T = { a: Number, b: String } */");
        assert!(same.is_some());
        assert_eq!(
            read_types("/** type T = {\n *   a: Number,\n *   b: String,\n * } */"),
            same
        );
        // A trailing comma inside a parenthesised type doesn't parse.
        assert_eq!(read_types("/** type T = (\n *   A | B,\n * )[] */"), None);
        // A union whose first member is quantified doesn't parse either.
        assert_eq!(
            read_types("/** const f:\n *   | <T>(x: T) => T\n *   | Null\n */"),
            None
        );
        // Different meaning, same characters but for layout.
        assert_ne!(
            read_types("/** const f: (a: A) => B | C */"),
            read_types("/** const f: ((a: A) => B) | C */")
        );
    }
}

/// Property tests of the layout, both ways round:
///
/// * parse → generate → parse: an annotation, laid out at any width,
///   reads to the same types, and laying it out again changes nothing;
/// * generate → parse → generate: a type printed and laid out, read back
///   by the checker's parser and printed and laid out again, gives the
///   same type and the same layout.
#[cfg(test)]
mod props {
    use super::*;
    use crate::infer::type_parser::parse_type_annotation;
    use crate::span::Span;
    use proptest::prelude::*;

    /// What a source's annotations say: each annotation's name and kind
    /// and each alias's head, with its type's syntax.
    fn types_in(src: &str) -> Vec<(String, std::result::Result<Type, String>)> {
        let mut scanner = Scanner::new(src);
        while scanner.next_token().unwrap().value != Token::Eof {}
        let mut out: Vec<_> = scanner
            .type_annotations()
            .iter()
            .map(|a| {
                (
                    format!("{} {:?}", a.name, a.kind),
                    parse_type_syntax(&a.content),
                )
            })
            .collect();
        out.extend(scanner.type_aliases().iter().map(|a| {
            (
                format!("type {}<{}>", a.name, a.params.join(",")),
                parse_type_syntax(&a.body),
            )
        }));
        out
    }

    fn name() -> impl Strategy<Value = String> {
        "[a-z][a-z0-9]{0,11}"
    }

    /// `ty`, parenthesised when it is a function type or a union that
    /// would otherwise take in what follows it.
    fn atom(ty: String) -> String {
        if ty.contains("=>") || ty.contains(" | ") {
            format!("({ty})")
        } else {
            ty
        }
    }

    /// Annotation type text over the grammar's layout-relevant shapes:
    /// records (with optional fields, `;` separators, index keys),
    /// function types (named, optional and anonymous parameters), unions,
    /// tuples, arrays, grouped types, type arguments, and string literal
    /// types holding commas, brackets and `//`.
    fn type_text() -> impl Strategy<Value = String> {
        let leaf = prop_oneof![
            Just("Number".to_string()),
            Just("String".to_string()),
            Just("Boolean".to_string()),
            Just("Null".to_string()),
            Just("Undefined".to_string()),
            Just("Foo".to_string()),
            Just("42".to_string()),
            Just("\"a, b\"".to_string()),
            Just("\"(x] {y}\"".to_string()),
            Just("\"http://x\"".to_string()),
            Just("\"q\\\"//\"".to_string()),
        ];
        leaf.prop_recursive(4, 48, 5, |inner| {
            prop_oneof![
                // record
                (
                    prop::collection::vec((name(), any::<bool>(), inner.clone()), 1..5),
                    any::<bool>(),
                    prop::option::of(inner.clone()),
                    any::<bool>(),
                )
                    .prop_map(|(fields, semi, index, symbol)| {
                        let sep = if semi { "; " } else { ", " };
                        let mut parts: Vec<String> = fields
                            .into_iter()
                            .map(|(n, opt, t)| format!("{n}{}: {t}", if opt { "?" } else { "" }))
                            .collect();
                        // An index key is a record's only member (`Dict`).
                        if let Some(t) = index {
                            return format!("{{ [String]: {t} }}");
                        }
                        if symbol {
                            parts.push("[Symbol.iterator]: Number".to_string());
                        }
                        format!("{{ {} }}", parts.join(sep))
                    }),
                // function type
                (
                    prop::collection::vec((prop::option::of(name()), inner.clone()), 0..5),
                    inner.clone(),
                )
                    .prop_map(|(params, ret)| {
                        let ps: Vec<String> = params
                            .into_iter()
                            .map(|(n, t)| match n {
                                Some(n) => format!("{n}: {t}"),
                                None => t,
                            })
                            .collect();
                        format!("({}) => {ret}", ps.join(", "))
                    }),
                // union
                prop::collection::vec(inner.clone(), 2..4).prop_map(|ms| ms
                    .into_iter()
                    .map(atom)
                    .collect::<Vec<_>>()
                    .join(" | ")),
                // tuple
                prop::collection::vec(inner.clone(), 1..4)
                    .prop_map(|es| format!("[{}]", es.join(", "))),
                // array, of a grouped type when need be
                inner.clone().prop_map(|t| format!("{}[]", atom(t))),
                // type arguments
                (prop::collection::vec(inner.clone(), 1..3), 0..3usize).prop_map(|(args, k)| {
                    match k {
                        0 => format!("Pair<{}>", args.join(", ")),
                        1 => format!("Dict<{}>", args[0]),
                        _ => format!("Promise<{}>", args[0]),
                    }
                }),
            ]
        })
    }

    /// A one-line statement annotation (without `/** */`).
    fn annotation() -> impl Strategy<Value = String> {
        prop_oneof![
            type_text().prop_map(|t| format!("type A = {t}")),
            type_text().prop_map(|t| format!("const c: {t}")),
            (
                any::<bool>(),
                prop::collection::vec((name(), type_text()), 0..5),
                type_text()
            )
                .prop_map(|(generic, params, ret)| {
                    let ps: Vec<String> = params
                        .into_iter()
                        .map(|(n, t)| format!("{n}: {t}"))
                        .collect();
                    let q = if generic { "<T, U>" } else { "" };
                    format!("function f{q}({}) => {ret}", ps.join(", "))
                }),
        ]
    }

    /// Types the printer writes and the parser reads back.
    fn arb_type() -> impl Strategy<Value = Type> {
        let leaf = prop_oneof![
            Just(Type::Number),
            Just(Type::String),
            Just(Type::Boolean),
            Just(Type::Undefined),
            Just(Type::Null),
        ];
        leaf.prop_recursive(4, 64, 6, |inner| {
            prop_oneof![
                inner.clone().prop_map(Type::array),
                (prop::collection::vec(inner.clone(), 0..5), inner.clone())
                    .prop_map(|(params, ret)| Type::simple_func(params, ret)),
                prop::collection::vec(("[a-z]{1,10}", inner.clone()), 0..6).prop_map(Type::object),
            ]
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]

        /// parse → generate → parse.
        #[test]
        fn layout_keeps_what_an_annotation_says(
            ann in annotation(),
            width in 10usize..140,
            indent in prop_oneof![Just(""), Just("    "), Just("\t")],
            crlf in any::<bool>(),
        ) {
            let nl = if crlf { "\r\n" } else { "\n" };
            let src = format!("{indent}/** {ann} */{nl}const z = 1;{nl}");
            let before = types_in(&src);
            prop_assert!(before.iter().all(|(_, t)| t.is_ok()), "generated {src:?}: {before:?}");
            let out = format_annotations(&src, width).unwrap();
            prop_assert_eq!(&types_in(&out), &before, "width {}:\n{}", width, out);
            prop_assert_eq!(&format_annotations(&out, width).unwrap(), &out);
            // The layout touches the comment only, and keeps the line ending.
            prop_assert!(out.ends_with(&format!("*/{nl}const z = 1;{nl}")), "{:?}", out);
            if crlf {
                prop_assert!(!out.replace("\r\n", "").contains('\n'), "{:?}", out);
            }
            // Not vacuous: whenever the annotation is too long and the
            // layout breaks it, the rewrite is taken (the guard that
            // keeps the original never has to).
            let line = src.lines().next().unwrap().trim_end_matches('\r');
            let fit = Fit { width, margin: indent.chars().count() + 3 };
            if line.chars().count() > width && lay_out_annotation(&ann, &fit).is_some() {
                prop_assert_ne!(&out, &src, "width {}", width);
            }
            // A wide enough line is left as it was.
            if width >= src.lines().next().unwrap().chars().count() {
                prop_assert_eq!(&out, &src);
            }
        }

        /// generate → parse → generate.
        #[test]
        fn layout_of_a_printed_type_round_trips(ty in arb_type(), width in 10usize..140) {
            let lay_out = |ty: &Type| {
                format_annotations(&format!("/** type A = {ty} */\n"), width).unwrap()
            };
            let first = lay_out(&ty);
            // Read the laid-out annotation back as the checker does.
            let mut scanner = Scanner::new(&first);
            while scanner.next_token().unwrap().value != Token::Eof {}
            let body = &scanner.type_aliases()[0].body;
            let (parsed, _) = parse_type_annotation(body, Span::default(), 1000)
                .map_err(|e| TestCaseError::fail(format!("{e}\n{first}")))?;
            prop_assert_eq!(parsed.to_string(), ty.to_string(), "{}", first);
            prop_assert_eq!(lay_out(&parsed), first);
        }
    }
}
