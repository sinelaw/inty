//! Module graph: every reachable module from the entry, keyed by
//! canonical path. Holds the parsed AST, original source text, and
//! resolved import targets for each module so the emitter can do
//! its work without re-touching the disk.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use inty::ast::Program;

#[derive(Debug)]
pub struct Module {
    /// Canonical path of this module on disk.
    pub path: PathBuf,
    /// Original source text — needed for the source map's "sources
    /// content" field and for re-using span ranges in diagnostics.
    pub source: String,
    /// Parsed AST. Re-used by the emitter; not re-typechecked.
    pub program: Program,
    /// Canonical paths of every module this one imports or
    /// re-exports from. Used for cycle detection and topological
    /// ordering.
    pub import_targets: Vec<PathBuf>,
    /// Map from the literal specifier string (`"./foo.js"`) as
    /// written in source to its canonical resolved path. Both
    /// `import` and `export … from` specifiers go in here so the
    /// emitter can look up the target module by exactly what the
    /// user wrote.
    pub specifier_resolution: HashMap<String, PathBuf>,
}

#[derive(Default, Debug)]
pub struct ModuleGraph {
    pub modules: HashMap<PathBuf, Module>,
}

impl ModuleGraph {
    pub fn contains(&self, path: &Path) -> bool {
        self.modules.contains_key(path)
    }

    pub fn insert(&mut self, m: Module) {
        self.modules.insert(m.path.clone(), m);
    }

    pub fn get(&self, path: &Path) -> Option<&Module> {
        self.modules.get(path)
    }

    /// Topological order over `modules`, dependencies first. Cycles
    /// are guarded against in the loader; if one slips through the
    /// ordering still terminates because we mark visited nodes
    /// before recursing.
    pub fn dependency_order(&self, entry: &Path) -> Vec<PathBuf> {
        let mut order: Vec<PathBuf> = Vec::new();
        let mut visited: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
        self.visit(entry, &mut visited, &mut order);
        order
    }

    fn visit(
        &self,
        node: &Path,
        visited: &mut std::collections::HashSet<PathBuf>,
        order: &mut Vec<PathBuf>,
    ) {
        if !visited.insert(node.to_path_buf()) {
            return;
        }
        if let Some(m) = self.modules.get(node) {
            for dep in &m.import_targets {
                self.visit(dep, visited, order);
            }
        }
        order.push(node.to_path_buf());
    }
}
