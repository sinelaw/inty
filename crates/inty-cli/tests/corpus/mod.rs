//! The programs `tests/soundness.rs` and `tests/output_snapshots.rs` run
//! inty on: the JavaScript programs under `examples/` and in the test
//! directories below (not declaration files or a test harness's own
//! script), and the soundness probes in `tests/soundness/`. A new program
//! in one of these directories joins both checks.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The workspace root, which paths in the corpus are relative to.
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace root")
        .to_path_buf()
}

/// Directories whose `.js` files are in the corpus; `true` to include
/// their subdirectories.
const DIRS: &[(&str, bool)] = &[
    ("examples", true),
    ("crates/inty/tests", false),
    ("crates/inty/tests/fixtures", false),
    ("crates/inty-go/tests/programs", false),
    ("crates/inty-go/tests/io", false),
    ("crates/inty-cli/tests/soundness", false),
];

fn collect(dir: &Path, recurse: bool, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if path.is_dir() {
            if recurse && name != "node_modules" && !name.starts_with('.') {
                collect(&path, recurse, out);
            }
        } else if name.ends_with(".js") && !name.ends_with(".d.js") {
            out.push(path);
        }
    }
}

/// The corpus, as paths relative to [`root`] with `/` separators, sorted.
pub fn programs() -> Vec<String> {
    let root = root();
    let mut paths = Vec::new();
    for (dir, recurse) in DIRS {
        collect(&root.join(dir), *recurse, &mut paths);
    }
    let mut programs: Vec<String> = paths
        .iter()
        .map(|p| {
            let rel = p.strip_prefix(&root).expect("under the root");
            rel.components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/")
        })
        .collect();
    programs.sort();
    programs.dedup();
    assert!(programs.len() > 50, "the corpus is too small: {programs:?}");
    programs
}

/// Run the `inty` binary from the workspace root, colour off (the option
/// goes last: a subcommand, `declarations` say, comes first).
pub fn inty(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_inty"))
        .current_dir(root())
        .args(args)
        .arg("--no-color")
        .output()
        .expect("run inty")
}

/// Map `f` over `items` on a few threads, keeping their order.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results = std::sync::Mutex::new(Vec::with_capacity(items.len()));
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(item) = items.get(i) else { break };
                let r = f(item);
                results.lock().unwrap().push((i, r));
            });
        }
    });
    let mut results = results.into_inner().unwrap();
    results.sort_by_key(|(i, _)| *i);
    results.into_iter().map(|(_, r)| r).collect()
}
