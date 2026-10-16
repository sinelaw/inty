//! Inlay hints as the editor and the web playground render them.
//!
//! Each test writes the source with every hint spliced in at its
//! anchor as `⟨label⟩`, so a hint in the wrong place (inside a name,
//! after a `:`) or with the wrong type shows up in the expected text.

use inty::frontends::Language;
use inty_lsp::Analysis;

fn annotate(src: &str, lang: Language) -> String {
    let analysis = Analysis::check_lang(src, lang);
    assert!(
        analysis.errors.is_empty(),
        "expected a clean check, got {:?}",
        analysis.errors
    );
    let mut hints = analysis.inlay_hints_in(0, src.len(), src);
    hints.sort_by_key(|h| h.after_byte);
    let mut out = String::new();
    let mut last = 0;
    for h in &hints {
        out.push_str(&src[last..h.after_byte]);
        out.push_str(&format!("⟨{}⟩", h.label.trim()));
        last = h.after_byte;
    }
    out.push_str(&src[last..]);
    out
}

fn py(src: &str) -> String {
    annotate(src, Language::Python)
}

fn js(src: &str) -> String {
    annotate(src, Language::JavaScript)
}

#[test]
fn python_def_type_does_not_land_on_its_first_param() {
    // `def pair(` is 9 bytes, the length of `function `: the function's
    // type used to be keyed at the first parameter.
    let out = py("def pair(a, b):\n    return [a, b]\n");
    assert_eq!(
        out,
        "def pair(a⟨: a⟩, b⟨: a⟩)⟨-> a[]⟩:\n    return [a, b]\n"
    );
}

#[test]
fn python_tuple_targets_get_their_own_hints() {
    let out = py("def two(n, s):\n    return (n, s + \"!\")\n\ncount, tag = two(3, \"x\")\n");
    assert!(
        out.ends_with("count⟨: Number⟩, tag⟨: String⟩ = two(3, \"x\")\n"),
        "{out}"
    );
}

#[test]
fn python_loop_variable_hint_sits_on_the_name() {
    let out = py("for v in [1, 2]:\n    pass\n");
    assert_eq!(out, "for v⟨: Number⟩ in [1, 2]:\n    pass\n");
    let out = py("for k, v in [(1, \"a\")]:\n    pass\n");
    assert_eq!(
        out,
        "for k⟨: Number⟩, v⟨: String⟩ in [(1, \"a\")]:\n    pass\n"
    );
}

#[test]
fn python_annotations_are_not_repeated_as_hints() {
    let out = py("def add_one(x: int) -> int:\n    return x + 1\n\ncount: int = 5\n");
    assert_eq!(
        out,
        "def add_one(x: int) -> int:\n    return x + 1\n\ncount: int = 5\n"
    );
}

#[test]
fn python_lambda_params_still_get_hints() {
    // `lambda x:` — the colon ends the parameter list, it isn't an
    // annotation.
    let out = py("f = lambda x: x + 1\n");
    assert!(out.contains("lambda x⟨: Number⟩:"), "{out}");
}

#[test]
fn python_class_shows_its_name() {
    let out = py("class Counter:\n    def __init__(self):\n        self.v = 0\n\nc = Counter()\n");
    assert!(out.contains("c⟨: Counter⟩ = Counter()"), "{out}");
}

#[test]
fn js_function_hints_unchanged() {
    let out = js("function square(x) { return x * x; }\nvar n = square(3);\n");
    assert_eq!(
        out,
        "function square(x⟨: Number⟩)⟨-> Number⟩ { return x * x; }\nvar n⟨: Number⟩ = square(3);\n"
    );
}

#[test]
fn self_reference_reads_as_self() {
    let out = js(concat!(
        "var b = {\n",
        "    url: \"\",\n",
        "    setUrl: function(u) { this.url = u; return this; },\n",
        "    send: function() { return this.url; }\n",
        "};\n",
        "var r = b.setUrl(\"/x\").send();\n",
    ));
    assert!(
        out.contains("var b⟨: {send: (this: Self) => String, setUrl: (this: Self, String) => Self, url: String}⟩"),
        "{out}"
    );
    assert!(!out.contains('μ'), "{out}");
}

#[test]
fn js_class_hides_its_private_fields() {
    let out = js("class C {\n    #n = 0;\n    get() { return this.#n; }\n}\nvar c = new C();\n");
    assert!(out.contains("var c⟨: C⟩ = new C();"), "{out}");
}

#[test]
fn nullable_return_has_no_vacuous_where_clause() {
    let out = js(concat!(
        "/** function find<a>(xs: a[], v: a) => a | Null */\n",
        "function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }\n",
    ));
    assert!(out.contains("⟨-> Null | a⟩"), "{out}");
}

/// Prints every playground example with its hints, for eyeballing:
/// `cargo test -p inty-lsp --test inlay_hints -- --ignored --nocapture`
#[test]
#[ignore]
fn dump_playground() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/playground");
    let mut paths: Vec<_> = ["features", "ts-misses", "py-features", "py-misses"]
        .iter()
        .flat_map(|d| std::fs::read_dir(format!("{root}/{d}")).unwrap())
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    for path in paths {
        let src = std::fs::read_to_string(&path).unwrap();
        let lang = if path.extension().is_some_and(|e| e == "py") {
            Language::Python
        } else {
            Language::JavaScript
        };
        let analysis = Analysis::check_lang(&src, lang);
        let mut hints = analysis.inlay_hints_in(0, src.len(), &src);
        hints.sort_by_key(|h| h.after_byte);
        let mut out = String::new();
        let mut last = 0;
        for h in &hints {
            out.push_str(&src[last..h.after_byte]);
            out.push_str(&format!("⟨{}⟩", h.label.trim()));
            last = h.after_byte;
        }
        out.push_str(&src[last..]);
        println!("==== {}", path.display());
        for (i, line) in out.lines().enumerate() {
            println!("{:3} {line}", i + 1);
        }
        for e in &analysis.errors {
            println!("  -> error: {e:?}");
        }
    }
}
