//! Annotations written across lines.
//!
//! A long `/** type … */`, `/** function … */` or `/** const … */`
//! annotation may be laid out one field or parameter per line, JSDoc
//! style, and means exactly what the one-line form means:
//!
//! ```js
//! /** type ScoreView = {
//!  *   id: String,
//!  *   fitWidth: Number,  // the width the page is laid out for
//!  * } */
//! ```
//!
//! * every line after the first may start with a `*` margin (optional
//!   whitespace, `*`, optional space), which is ignored;
//! * the last field, parameter, tuple element or type argument may be
//!   followed by a comma, and a union may start with `|`;
//! * `// …` to the end of a line is a comment;
//! * an error inside the annotation is reported where it is.
//!
//! Each test checks a multi-line program against the one-line program it
//! stands for: both must give the same types, or the same error.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// The type of the program's last expression (`({a, b, …})` gathers the
/// bindings a test is about), or the error, with its line and column.
fn check(src: &str) -> Result<String, String> {
    let program = parse(src).map_err(|e| format!("parse error: {e:?}"))?;
    let (env, mut state) = initial_env_with_stdlib().map_err(|e| format!("stdlib: {e:?}"))?;
    let (ty, _) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| located(src, &e))?;
    state.resolve_constraints().map_err(|e| located(src, &e))?;
    let resolved = state.apply_subst(&ty);
    Ok(inty::types::PrettyContext::new().format_type(&resolved))
}

/// The error and where it is.
fn located(src: &str, e: &inty::error::IntyError) -> String {
    match e.as_type() {
        Some(t) => format!("{} at {}", e, line_col(src, t.span().start)),
        None => format!("{e}"),
    }
}

/// `line:column`, both from 1, of a byte offset.
fn line_col(src: &str, offset: usize) -> String {
    let before = &src[..offset];
    let line = before.matches('\n').count() + 1;
    let col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
    format!("{line}:{col}")
}

/// Both programs check to the same result, which is `Ok`.
fn same(multi: &str, one: &str) -> String {
    let m = check(multi);
    let o = check(one);
    assert_eq!(m, o, "multi-line:\n{multi}\none-line:\n{one}");
    m.unwrap_or_else(|e| panic!("expected the programs to check, got {e}"))
}

const ONE_LINE_VIEW: &str = r#"
/** type ScoreView = { id: String, size: Number, zoom: Number, fitWidth: Number, cache: String[], film: Boolean } */
/** const v: ScoreView */
const v = { id: "a", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
"#;

#[test]
fn star_margin_after_the_keyword_line() {
    let multi = r#"
/** type ScoreView = {
 *   id: String,
 *   size: Number,
 *   zoom: Number,
 *   fitWidth: Number,
 *   cache: String[],
 *   film: Boolean
 * } */
/** const v: ScoreView */
const v = { id: "a", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
"#;
    let ty = same(multi, ONE_LINE_VIEW);
    assert!(ty.contains("fitWidth: Number"), "{ty}");
}

#[test]
fn star_margin_with_the_keyword_on_its_own_line() {
    let multi = r#"
/**
 * type ScoreView = {
 *   id: String,
 *   size: Number,
 *   zoom: Number,
 *   fitWidth: Number,
 *   cache: String[],
 *   film: Boolean,
 * }
 */
/** const v: ScoreView */
const v = { id: "a", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
"#;
    same(multi, ONE_LINE_VIEW);
}

#[test]
fn star_margin_mixed_with_blank_lines() {
    // Lines with only a `*`, empty lines, a margin indented with a tab,
    // and a line with no margin at all.
    let multi = "
/** type ScoreView = {
 *   id: String,
 *
 *   size: Number,

 *   zoom: Number,
\t*   fitWidth: Number,
     cache: String[],
 *
 *   film: Boolean,
 *
 * } */
/** const v: ScoreView */
const v = { id: \"a\", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
";
    same(multi, ONE_LINE_VIEW);
}

#[test]
fn no_margin_still_works() {
    let multi = r#"
/** type ScoreView = {
  id: String,
  size: Number,
  zoom: Number,
  fitWidth: Number,
  cache: String[],
  film: Boolean,
} */
/** const v: ScoreView */
const v = { id: "a", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
"#;
    same(multi, ONE_LINE_VIEW);
}

#[test]
fn comments_on_fields() {
    // Commas, brackets, quotes and `*/`-free punctuation inside a comment
    // are not the annotation's.
    let multi = r#"
/** type ScoreView = {
 *   id: String,         // the score's id, e.g. "bach-1" (or "x, y")
 *   size: Number,       // in pt { not a brace
 *   zoom: Number,       // 1 = 100% <- not a type argument
 *   fitWidth: Number,   // the width the page is laid out for (follows `width` less often while resizing)
 *   cache: String[],    // [ not a bracket
 *   film: Boolean,      // | not a union
 * } */
/** const v: ScoreView */  // a comment after the annotation is JavaScript's
const v = { id: "a", size: 1, zoom: 2, fitWidth: 3, cache: [], film: false };
({ v })
"#;
    same(multi, ONE_LINE_VIEW);
}

#[test]
fn a_comment_on_a_one_line_annotation() {
    let multi = r#"
/** const n: Number // how many */
const n = 1;
({ n })
"#;
    let one = r#"
/** const n: Number */
const n = 1;
({ n })
"#;
    same(multi, one);
}

#[test]
fn slashes_in_a_string_literal_type_are_not_a_comment() {
    let multi = r#"
/** type Url = {
 *   scheme: "http://" | "https://", // the two we fetch
 * } */
/** const u: Url */
const u = { scheme: "https://" };
({ u })
"#;
    let one = r#"
/** type Url = { scheme: "http://" | "https://" } */
/** const u: Url */
const u = { scheme: "https://" };
({ u })
"#;
    let ty = same(multi, one);
    assert!(ty.contains("http://"), "{ty}");
}

#[test]
fn function_signature_one_parameter_per_line() {
    let multi = r#"
/** type Builder = { out: String[] } */
/** type Cached = { id: String } */
/** function sideView(
 *   b: Builder,        // where the view is written
 *   n: Number,
 *   c: Cached,
 * ) => Number */
function sideView(b, n, c) { b.out.push(c.id); return n; }
({ sideView })
"#;
    let one = r#"
/** type Builder = { out: String[] } */
/** type Cached = { id: String } */
/** function sideView(b: Builder, n: Number, c: Cached) => Number */
function sideView(b, n, c) { b.out.push(c.id); return n; }
({ sideView })
"#;
    same(multi, one);
}

#[test]
fn generic_function_signature_across_lines() {
    let multi = r#"
/**
 * function pick<
 *   K,
 *   V,
 * >(
 *   m: Map<K, V,>,
 *   k: K,
 *   fallback: V,
 * ) => V
 */
function pick(m, k, fallback) { return m.get(k) ?? fallback; }
({ pick })
"#;
    let one = r#"
/** function pick<K, V>(m: Map<K, V>, k: K, fallback: V) => V */
function pick(m, k, fallback) { return m.get(k) ?? fallback; }
({ pick })
"#;
    same(multi, one);
}

#[test]
fn const_annotation_across_lines() {
    let multi = r#"
/** const layout: {
 *   width: Number,
 *   pages: { n: Number, top: Number }[], // laid out so far
 *   scale: (Number,) => Number,
 * } */
const layout = { width: 1, pages: [], scale: (x) => x * 2 };
({ layout })
"#;
    let one = r#"
/** const layout: { width: Number, pages: { n: Number, top: Number }[], scale: (Number) => Number } */
const layout = { width: 1, pages: [], scale: (x) => x * 2 };
({ layout })
"#;
    same(multi, one);
}

#[test]
fn several_declarators_across_lines() {
    let multi = r#"
/** var a: {
 *   x: Number, // (one, two
 * },
 *   b: String
 */
var a = { x: 1 }, b = "s";
({ a, b })
"#;
    let one = r#"
/** var a: { x: Number }, b: String */
var a = { x: 1 }, b = "s";
({ a, b })
"#;
    same(multi, one);
}

#[test]
fn union_one_member_per_line() {
    let multi = r#"
/**
 * type Shape =
 *   | { kind: "circle", r: Number }   // a disc
 *   | { kind: "rect", w: Number, h: Number }
 */
/** function area(s: Shape) => Number */
function area(s) { return s.kind === "circle" ? s.r * s.r : s.w * s.h; }
({ area })
"#;
    let one = r#"
/** type Shape = { kind: "circle", r: Number } | { kind: "rect", w: Number, h: Number } */
/** function area(s: Shape) => Number */
function area(s) { return s.kind === "circle" ? s.r * s.r : s.w * s.h; }
({ area })
"#;
    same(multi, one);
}

#[test]
fn trailing_commas() {
    let multi = r#"
/** type Pair<A, B,> = { first: A, second: B, } */
/** type Row = [Number, String,] */
/** const f: (a: Number, b: Pair<String, Number,>,) => Row */
const f = (a, b) => [a + b.second, b.first];
/** const g: <T,>(T,) => T[] */
const g = (x) => [x];
/** const d: Dict<Number,> */
const d = {};
({ f, g, d })
"#;
    let one = r#"
/** type Pair<A, B> = { first: A, second: B } */
/** type Row = [Number, String] */
/** const f: (a: Number, b: Pair<String, Number>) => Row */
const f = (a, b) => [a + b.second, b.first];
/** const g: <T>(T) => T[] */
const g = (x) => [x];
/** const d: Dict<Number> */
const d = {};
({ f, g, d })
"#;
    same(multi, one);
}

#[test]
fn exported_function_across_lines() {
    let multi = r#"
/** export function scale(
 *   x: Number,
 *   by: Number,
 * ) => Number */
export function scale(x, by) { return x * by; }
"#;
    let one = r#"
/** export function scale(x: Number, by: Number) => Number */
export function scale(x, by) { return x * by; }
"#;
    assert_eq!(check(multi), check(one));
    assert!(check(multi).is_ok(), "{:?}", check(multi));
}

#[test]
fn a_mismatch_is_rejected_alike() {
    // The annotation is enforced the same way in both layouts.
    let multi = r#"
/** const v: {
 *   id: String,
 *   n: Number,
 * } */
const v = { id: "a", n: "not a number" };
"#;
    let one = r#"
/** const v: { id: String, n: Number } */
const v = { id: "a", n: "not a number" };
"#;
    let m = check(multi).unwrap_err();
    let o = check(one).unwrap_err();
    // The same error, at the same place in the code (the initialiser,
    // on line 6 here and line 3 there).
    assert_eq!(m.replace("6:", "L:"), o.replace("3:", "L:"));
}

#[test]
fn an_error_in_a_field_is_reported_at_the_field() {
    let src = r#"
/** type ScoreView = {
 *   id: String,
 *   size: Number,
 *   zoom: Number,
 *   width: Number,
 *   fitWidth: Numbr,  // line 7
 *   film: Boolean,
 * } */
"#;
    let err = check(src).unwrap_err();
    assert!(err.contains("unknown type 'Numbr'"), "{err}");
    assert!(err.ends_with(" at 7:16"), "{err}");
}

#[test]
fn an_error_in_a_parameter_is_reported_at_the_parameter() {
    let src = r#"
/** type Box<T> = { v: T } */
/**
 * function f(
 *   a: Number,
 *   b: Box,
 * ) => Number
 */
function f(a, b) { return a; }
"#;
    let err = check(src).unwrap_err();
    assert!(err.contains("type 'Box' takes 1 type argument"), "{err}");
    assert!(err.ends_with(" at 6:9"), "{err}");
}

#[test]
fn a_syntax_error_is_reported_where_it_is() {
    // A missing comma between two fields: reported at the second field,
    // on its own line.
    let src = r#"
/** const v: {
 *   id: String
 *   n: Number,
 * } */
const v = { id: "a", n: 1 };
"#;
    let err = check(src).unwrap_err();
    assert!(err.ends_with(" at 4:6"), "{err}");
}

#[test]
fn an_error_in_a_one_line_annotation_points_inside_it() {
    let src = "/** function first(o: T) => Number */\nfunction first(o) { return 1; }\n";
    let err = check(src).unwrap_err();
    assert!(err.contains("unknown type 'T'"), "{err}");
    assert!(err.ends_with(" at 1:23"), "{err}");
}

#[test]
fn prose_that_looks_like_an_annotation_is_still_prose() {
    // After a `*` margin, a keyword followed by something of an
    // annotation's shape is still prose when its "type" doesn't parse.
    let src = r#"
/**
 * function foo(bar) is deprecated; use baz instead.
 */
function foo(bar) { return bar; }
/**
 * type Foo = the kind of foo we accept.
 */
const Foo = 1;
/**
 * const total: the running total, in cents
 */
const total = 0;
({ foo, Foo, total })
"#;
    let ty = check(src).unwrap();
    assert!(ty.contains("total: Number"), "{ty}");
}

#[test]
fn prose_doc_comments_are_not_annotations() {
    // A JSDoc block whose text happens to start with a keyword, after a
    // `*` margin, is documentation, not an annotation: it doesn't have
    // an annotation's shape.
    let src = r#"
/**
 * function inc adds one to its argument (see below).
 */
function inc(x) { return x + 1; }
/**
 * class names are listed here
 */
const names = ["a"];
/**
 * type of the thing
 */
const t = 1;
/**
 * const values below
 */
const k = inc(t);
({ inc, names, k })
"#;
    let ty = check(src).unwrap();
    assert!(ty.contains("inc: (Number) => Number"), "{ty}");
}

// ---------------------------------------------------------------------
// `inty fmt`: the formatter's output reads to the same annotations, and
// checks to the same result, on every JavaScript file in the repository.
// ---------------------------------------------------------------------

use inty::frontends::javascript::format::format_annotations;
use inty::frontends::javascript::lexer::{Scanner, Token};
use inty::infer::parse_type_syntax;
use std::path::{Path, PathBuf};

/// The repository's JavaScript sources and declaration files.
fn corpus() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for dir in [
        root.join("stdlib"),
        root.join("tests"),
        root.join("../inty-cli/tests"),
        root.join("../inty-go/tests"),
        root.join("../../examples"),
    ] {
        collect_js(&dir, &mut files);
    }
    files.sort();
    assert!(files.len() > 50, "found only {} files", files.len());
    files
}

fn collect_js(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n != "node_modules") {
                collect_js(&p, out);
            }
        } else if p.extension().is_some_and(|x| x == "js") {
            out.push(p);
        }
    }
}

/// What the scanner reads from a source's annotations, as far as their
/// meaning goes: each annotation's name and kind, each alias's name and
/// parameters, with its type's syntax parsed (unknown names standing for
/// type variables), so two layouts of one annotation compare equal and
/// any change to what it says, or a rewrite that doesn't parse, doesn't.
fn annotations_of(src: &str) -> Option<Vec<String>> {
    let mut scanner = Scanner::new(src);
    loop {
        match scanner.next_token() {
            Ok(t) if t.value == Token::Eof => break,
            Ok(_) => {}
            Err(_) => return None,
        }
    }
    let mut out: Vec<String> = scanner
        .type_annotations()
        .iter()
        .map(|a| {
            // A class declaration isn't a type expression; the formatter
            // leaves those alone, so their text is compared as is.
            let ty = if format!("{:?}", a.kind) == "Class" {
                a.content.clone()
            } else {
                format!("{:?}", parse_type_syntax(&a.content))
            };
            format!("{} {:?} {ty}", a.name, a.kind)
        })
        .collect();
    out.extend(scanner.type_aliases().iter().map(|a| {
        format!(
            "type {}<{}> {} {:?}",
            a.name,
            a.params.join(","),
            a.nominal,
            parse_type_syntax(&a.body)
        )
    }));
    Some(out)
}

/// The check result without its position (formatting moves code down).
fn without_position(r: Result<String, String>) -> Result<String, String> {
    r.map_err(|e| match e.rfind(" at ") {
        Some(i) if e[i + 4..].chars().all(|c| c.is_ascii_digit() || c == ':') => e[..i].to_string(),
        _ => e,
    })
}

#[test]
fn formatting_the_corpus_keeps_every_annotation() {
    let mut wrapped = 0;
    for path in corpus() {
        let src = std::fs::read_to_string(&path).unwrap();
        let Some(before) = annotations_of(&src) else {
            continue; // doesn't lex: nothing to format
        };
        for width in [40, 100] {
            let out = format_annotations(&src, width).unwrap();
            if out != src {
                wrapped += 1;
            }
            assert_eq!(
                format_annotations(&out, width).unwrap(),
                out,
                "{}: formatting at {width} isn't idempotent",
                path.display()
            );
            assert_eq!(
                annotations_of(&out).as_ref(),
                Some(&before),
                "{}: formatting at {width} changed an annotation",
                path.display()
            );
        }
    }
    assert!(
        wrapped > 10,
        "only {wrapped} files had an annotation to wrap"
    );
}

#[test]
fn formatted_programs_check_the_same() {
    for path in corpus() {
        if path.to_string_lossy().ends_with(".d.js") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let Ok(out) = format_annotations(&src, 40) else {
            continue;
        };
        if out == src {
            continue;
        }
        assert_eq!(
            without_position(check(&out)),
            without_position(check(&src)),
            "{}: the formatted program checks differently",
            path.display()
        );
    }
}
