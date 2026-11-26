//! The language server checks a saved document as the CLI checks the
//! file: its imports resolve relative to it.

use std::path::{Path, PathBuf};

use inty::frontends::Language;
use inty_lsp::Analysis;

/// A directory of files under the system temp dir, removed on drop.
struct Project(PathBuf);

impl Project {
    fn new(files: &[(&str, &str)]) -> Self {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("inty-lsp-imports-{}-{nanos}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        for (name, text) in files {
            std::fs::write(dir.join(name), text).unwrap();
        }
        Project(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn check(text: &str, path: &Path) -> Analysis {
    Analysis::check_document(text, Language::JavaScript, Some(path))
}

fn errors(analysis: &Analysis) -> Vec<String> {
    analysis.errors.iter().map(|e| e.to_string()).collect()
}

fn hover(analysis: &Analysis, text: &str, needle: &str) -> String {
    let at = text
        .rfind(needle)
        .unwrap_or_else(|| panic!("`{needle}` in the text"));
    analysis
        .hover_at(at)
        .unwrap_or_else(|| panic!("hover on `{needle}`"))
        .type_str
}

#[test]
fn an_imported_name_has_its_type() {
    let project = Project::new(&[("lib.js", "export function double(n) { return n * 2; }\n")]);
    let main = "import { double } from \"./lib.js\";\nconst x = double(2);\n";
    let analysis = check(main, &project.path("main.js"));
    assert!(errors(&analysis).is_empty(), "{:?}", errors(&analysis));
    assert_eq!(hover(&analysis, main, "double(2)"), "(Number) => Number");
    assert_eq!(hover(&analysis, main, "x ="), "Number");
}

#[test]
fn an_imported_module_s_errors_are_its_own() {
    let project = Project::new(&[(
        "lib.js",
        "export const one = 1;\nconst broken = one - {};\n",
    )]);
    let main = "import { one } from \"./lib.js\";\nconst n = one;\n";
    let analysis = check(main, &project.path("main.js"));
    assert!(errors(&analysis).is_empty(), "{:?}", errors(&analysis));
    // What the module typed despite its error, its importers see.
    assert_eq!(hover(&analysis, main, "n ="), "Number");
}

#[test]
fn a_failed_import_is_reported_and_the_rest_checked() {
    let project = Project::new(&[("lib.js", "export const one = 1;\n")]);
    let main = "import { a } from \"./missing.js\";\n\
                import { nope } from \"./lib.js\";\n\
                const n = 1;\n";
    let analysis = check(main, &project.path("main.js"));
    let shown = errors(&analysis);
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert!(shown[0].contains("cannot resolve import"), "{shown:?}");
    assert!(shown[1].contains("no export named"), "{shown:?}");
    assert_eq!(hover(&analysis, main, "n ="), "Number");
}

#[test]
fn a_document_with_no_file_leaves_its_imports_unresolved() {
    let main = "import { one } from \"./lib.js\";\nconst n = 1;\n";
    let analysis = Analysis::check_document(main, Language::JavaScript, None);
    assert_eq!(hover(&analysis, main, "n ="), "Number");
}

#[test]
fn the_project_s_libs_declare_what_annotations_name() {
    let project = Project::new(&[
        (
            "app.d.js",
            "/** type Item = {label: String} */\n/** const none: Item[] */ const none;\n",
        ),
        ("inty.json", r#"{ "libs": ["./app.d.js"] }"#),
    ]);
    let main = "/** function matching(items: Item[], q: String) => Item[] */\n\
                function matching(items, q) { return items.filter(it => it.label === q); }\n\
                const hits = matching(none, \"x\");\n";
    let analysis = check(main, &project.path("main.js"));
    assert!(errors(&analysis).is_empty(), "{:?}", errors(&analysis));
    assert_eq!(hover(&analysis, main, "q) {"), "String");
    assert_eq!(hover(&analysis, main, "hits ="), "Item[]");
}
