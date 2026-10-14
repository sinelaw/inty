//! inty's programs in the Lean model's wire format (`lean/Inty/Wire.lean`),
//! so the model runs on inty's own programs (ground rule 4 of
//! `lean/ROADMAP.md`), not only on the differential test's generated ones.
//!
//! [`lower_program`] writes a parsed JavaScript program as one wire line,
//! and [`lower_entry`] a program of several modules, or says why it
//! can't: the program uses something the model doesn't have (a bitwise
//! operator, a comparison of strings, a class, a builtin, …), or
//! something whose lowering would change its meaning (a name used before
//! its declaration). The lowering is the inverse of the
//! differential test's printer (`tests/differential.rs`): a statement list
//! is a sequence whose value is its last statement's, a declaration binds
//! the rest of its block, a function's body ends in what it returns, and a
//! test of a binding for nothing, of its `typeof` or of its tag field takes
//! the binding apart (`unwrap`, `typetest`, `casetag`), shadowing it in
//! each branch with the binding the model's form makes.

use crate::ast::{
    AssignOp, BinOp, ChainSegment, ExportDecl, ExportFromKind, Expr, ForInit, ImportSpecifier,
    Literal, Param, Program, PropDef, PropKey, Stmt, UnaryOp, VarDeclarator, VarKind,
};
use crate::span::Span;
use crate::types::{LitValue, Nothing, Presence, RowTail, TVarName, Type};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Why a program isn't in the model's fragment.
pub type Unsupported = String;

type Lowered = Result<String, Unsupported>;

fn unsupported<T>(what: impl Into<String>) -> Result<T, Unsupported> {
    Err(what.into())
}

/// The program in the wire format, or what keeps it out of the model.
pub fn lower_program(program: &Program) -> Lowered {
    let module = read_module(program, &mut |source| {
        unsupported(format!("an import of `{source}`"))
    })?;
    lower_modules(vec![module])
}

/// The program whose entry module is the file `path`, with the modules it
/// imports, in the wire format; or what keeps it out of the model.
///
/// The modules run in the order JavaScript runs them, each once: those an
/// importer imports first, in the order it imports them. Each module's
/// declarations bind the modules after it, which see only what they
/// import: an import is the exporting module's binding itself, so a use
/// takes a new instance of its scheme, and an exported `let` is live.
pub fn lower_entry(path: &Path) -> Lowered {
    let mut loader = Loader {
        modules: Vec::new(),
        index: HashMap::new(),
    };
    loader.load(path)?;
    lower_modules(loader.modules)
}

/// The modules of a program, in the order they run.
struct Loader {
    modules: Vec<Module>,
    /// Each file's module, or `None` while its imports load.
    index: HashMap<PathBuf, Option<usize>>,
}

impl Loader {
    fn load(&mut self, path: &Path) -> Result<usize, Unsupported> {
        let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        match self.index.get(&path) {
            Some(Some(k)) => return Ok(*k),
            Some(None) => return unsupported("a cycle of imports"),
            None => {}
        }
        self.index.insert(path.clone(), None);
        let Ok(text) = std::fs::read_to_string(&path) else {
            return unsupported(format!("a module that can't be read ({})", path.display()));
        };
        let Ok(program) = crate::frontends::javascript::parse_source(&text) else {
            return unsupported(format!("a module that doesn't parse ({})", path.display()));
        };
        let dir = path.parent().map(Path::to_path_buf).unwrap_or_default();
        let module = read_module(&program, &mut |source| {
            let target = match crate::modules::resolve_path(&dir, source) {
                Ok(t) => t,
                Err(_) => return unsupported(format!("an import of `{source}`, not found")),
            };
            let name = target.to_string_lossy();
            if name.starts_with(crate::stdlib::BUILTIN_MODULE_PREFIX) || name.ends_with(".d.js") {
                return unsupported(format!("an import of `{source}`, a declared module"));
            }
            self.load(&target)
        })?;
        self.modules.push(module);
        let k = self.modules.len() - 1;
        self.index.insert(path, Some(k));
        Ok(k)
    }
}

/// A module of the program: its statements, its imports and exports read
/// off them.
struct Module {
    stmts: Vec<Stmt>,
    /// Each local name an import binds, and what to.
    imports: Vec<(String, Imported)>,
    /// Each name it exports, and what.
    exports: Vec<(String, Exported)>,
    /// What each name it exports is, once its declarations are lowered.
    table: HashMap<String, Target>,
}

enum Imported {
    /// The export of that name of the module.
    Name(usize, String),
    /// `import * as ns`: the module's namespace.
    Namespace(usize),
}

enum Exported {
    /// A binding of the module's own.
    Local(String),
    /// `export { x } from "…"`: the export of that name of the module.
    From(usize, String),
    /// `export * from "…"`: the module's exports but its default.
    All(usize),
    /// `export * as ns from "…"`: the module's namespace.
    Namespace(usize),
}

#[derive(Clone, Copy)]
enum Target {
    /// A binder, by its id.
    Binder(usize),
    /// A module's namespace, whose members are its exports.
    Namespace(usize),
}

/// The methods of strings and arrays the model has, natives, by their name
/// and number of arguments (`dynamics`' `BUILTIN_METHODS`).
const NATIVE_METHODS: &[(&str, usize)] = &[
    ("slice", 0),
    ("slice", 1),
    ("slice", 2),
    ("toUpperCase", 0),
    ("charCodeAt", 1),
    ("indexOf", 1),
];

/// The name an `export default` of what isn't a named function binds.
const DEFAULT: &str = "*default*";

/// A module's statements, without its imports and with its exports'
/// declarations; `resolve` gives the module an import names.
fn read_module(
    program: &Program,
    resolve: &mut dyn FnMut(&str) -> Result<usize, Unsupported>,
) -> Result<Module, Unsupported> {
    if !program.type_aliases.is_empty() {
        return unsupported("a type alias");
    }
    // The parser lowers a class to a factory function.
    if !program.class_brands.is_empty() {
        return unsupported("a class");
    }
    let mut module = Module {
        stmts: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        table: HashMap::new(),
    };
    for s in &program.statements {
        match s {
            Stmt::Import {
                specifiers, source, ..
            } => {
                let m = resolve(source)?;
                for spec in specifiers {
                    module.imports.push(match spec {
                        ImportSpecifier::Named {
                            imported, local, ..
                        } => (local.clone(), Imported::Name(m, imported.clone())),
                        ImportSpecifier::Default { local, .. } => {
                            (local.clone(), Imported::Name(m, "default".to_string()))
                        }
                        ImportSpecifier::Namespace { local, .. } => {
                            (local.clone(), Imported::Namespace(m))
                        }
                    });
                }
            }
            Stmt::Export { declaration, .. } => match declaration {
                ExportDecl::Var {
                    kind,
                    declarations,
                    span,
                } => {
                    for d in declarations {
                        module
                            .exports
                            .push((d.name.clone(), Exported::Local(d.name.clone())));
                    }
                    module.stmts.push(Stmt::Var {
                        kind: *kind,
                        declarations: declarations.clone(),
                        span: *span,
                    });
                }
                ExportDecl::Function {
                    name,
                    params,
                    body,
                    type_annotation,
                    span,
                } => {
                    module
                        .exports
                        .push((name.clone(), Exported::Local(name.clone())));
                    module.stmts.push(Stmt::FunctionDecl {
                        name: name.clone(),
                        params: params.clone(),
                        body: body.clone(),
                        type_annotation: type_annotation.clone(),
                        return_type_ast: None,
                        span: *span,
                    });
                }
                // `export default function f() {}` declares `f`.
                ExportDecl::Default {
                    value:
                        Expr::Function {
                            name: Some(name),
                            params,
                            body,
                            type_annotation,
                            arrow: false,
                            ..
                        },
                    span,
                } => {
                    module
                        .exports
                        .push(("default".to_string(), Exported::Local(name.clone())));
                    module.stmts.push(Stmt::FunctionDecl {
                        name: name.clone(),
                        params: params.clone(),
                        body: body.clone(),
                        type_annotation: type_annotation.clone(),
                        return_type_ast: None,
                        span: *span,
                    });
                }
                ExportDecl::Default { value, span } => {
                    module
                        .exports
                        .push(("default".to_string(), Exported::Local(DEFAULT.to_string())));
                    module.stmts.push(Stmt::Var {
                        kind: VarKind::Const,
                        declarations: vec![VarDeclarator {
                            name: DEFAULT.to_string(),
                            init: Some(value.clone()),
                            type_annotation: None,
                            type_ast: None,
                            kind: VarKind::Const,
                            span: *span,
                        }],
                        span: *span,
                    });
                }
                ExportDecl::List { specifiers, .. } => {
                    for sp in specifiers {
                        module
                            .exports
                            .push((sp.exported.clone(), Exported::Local(sp.local.clone())));
                    }
                }
                ExportDecl::From { kind, source, .. } => {
                    let m = resolve(source)?;
                    match kind {
                        ExportFromKind::Named(specs) => {
                            for sp in specs {
                                module.exports.push((
                                    sp.exported.clone(),
                                    Exported::From(m, sp.local.clone()),
                                ));
                            }
                        }
                        ExportFromKind::All => {
                            module.exports.push((String::new(), Exported::All(m)))
                        }
                        ExportFromKind::AllAs(ns) => {
                            module.exports.push((ns.clone(), Exported::Namespace(m)))
                        }
                    }
                }
            },
            s => module.stmts.push(s.clone()),
        }
    }
    Ok(module)
}

/// The modules, in the order they run, the last the program's entry.
fn lower_modules(modules: Vec<Module>) -> Lowered {
    // What a module exports of its own it declares, or imports (inty
    // rejects an export of what it doesn't).
    for m in &modules {
        let local: Vec<String> = m
            .stmts
            .iter()
            .flat_map(declared)
            .chain(m.imports.iter().map(|(l, _)| l.clone()))
            .collect();
        for (_, e) in &m.exports {
            if let Exported::Local(l) = e {
                if !local.contains(l) {
                    return unsupported(format!("an export of `{l}`, which isn't declared"));
                }
            }
        }
    }
    let entry = modules.len() - 1;
    let reexports: Vec<(usize, String)> = modules[entry]
        .exports
        .iter()
        .filter_map(|(_, e)| match e {
            Exported::From(m, x) => Some((*m, x.clone())),
            _ => None,
        })
        .collect();
    let mut cx = Cx {
        scope: Vec::new(),
        depth: 0,
        defined: vec!["length".to_string()],
        read: Vec::new(),
        arrow: false,
        new: false,
        next_id: 0,
        tested: Vec::new(),
        assigned: Vec::new(),
        var_ok: true,
        iteration: Vec::new(),
        groups: HashMap::new(),
        modules,
        module: 0,
        this_users: Vec::new(),
        natives: Vec::new(),
    };
    let wire = cx.enter_module(0)?;
    for (m, x) in reexports {
        if !cx.modules[m].table.contains_key(&x) {
            return unsupported(format!("a re-export of `{x}`, which isn't exported"));
        }
    }
    // A property only a builtin has (`xs.map`, `s.slice`): the model's
    // strings and arrays have only `length`.
    if let Some(l) = cx.read.iter().find(|l| !cx.defined.contains(l)) {
        return unsupported(format!(
            "the property `{l}`, which no object of the program has"
        ));
    }
    // A method of the program's objects that a string or an array has
    // too: which a call means depends on the receiver's type.
    if let Some(l) = cx.natives.iter().find(|l| cx.defined.contains(l)) {
        return unsupported(format!(
            "a method `{l}` of the program's, which strings or arrays have too"
        ));
    }
    // An arrow function isn't a constructor; the model's functions are.
    if cx.arrow && cx.new {
        return unsupported("`new` in a program with an arrow function");
    }
    if cx.tested.iter().any(|t| cx.assigned.contains(t)) {
        return unsupported("a `let` or a parameter taken apart by a test and assigned");
    }
    Ok(wire)
}

/// A binder in scope, innermost last.
#[derive(Clone)]
struct Binder {
    name: Option<String>,
    kind: Kind,
    /// Which binder it is, for `tested` and `assigned`.
    id: usize,
    /// The sum its annotation declares, if any: what a test of its tag
    /// field or of its `typeof` can take apart in the model.
    sum: Option<Sum>,
    /// How many functions it is declared inside.
    depth: usize,
    /// The module it is declared in: only that module's code sees it.
    module: usize,
    /// A `for` loop's `let`, which JavaScript binds afresh each iteration:
    /// the model's one binding is the same only where no closure sees it.
    per_iteration: bool,
}

/// A declared sum a test takes apart.
#[derive(Clone, Copy, PartialEq)]
enum Sum {
    /// A variant tagged by a field: `x.l === "t"`.
    Variant,
    /// A sum told apart by `typeof`.
    Typeof,
    /// `T | Null` or `T | Undefined`: a test of its truthiness takes it
    /// apart.
    Maybe,
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    /// A `const`, a function's own name, or what `unwrap`, `typetest` and
    /// `casetag` bind.
    Const,
    /// A `let` or a parameter.
    Mut,
    /// A function's `this`.
    This,
    /// A function declaration's name, which JavaScript lets the program
    /// assign to (the model's is a `const`).
    FnName,
    /// An arrow function's `this`, unused: its `this` is its context's.
    ArrowThis,
    /// What a test of a binding binds in a branch (`unwrap`, `typetest`,
    /// `casetag`), a `const` of the model's: assigning to it would assign
    /// to a copy, so the program is left out.
    Shadow,
    /// A name declared later in an enclosing block, hoisted by JavaScript
    /// (a function) or in its temporal dead zone: a use resolves to it,
    /// which the model's scoping can't say. Not a binder of the model's.
    Later,
    /// A function of a group of mutually recursive ones, inside the group:
    /// the field of that name of what the group's function (the binder of
    /// that id) returns. Not a binder of the model's.
    Member(usize),
    /// An import: the binder of that id, another module's. Not a binder
    /// of the model's.
    Alias(usize),
    /// `import * as ns`: that module's namespace, whose members are its
    /// exports. Not a binder of the model's.
    Namespace(usize),
}

impl Kind {
    /// Whether the model has a binder for it.
    fn bound(self) -> bool {
        !matches!(
            self,
            Kind::Later | Kind::Member(_) | Kind::Alias(_) | Kind::Namespace(_)
        )
    }
}

struct Cx {
    scope: Vec<Binder>,
    /// How many functions the lowering is inside.
    depth: usize,
    /// The labels the program's objects and annotations have.
    defined: Vec<String>,
    /// The labels the program reads or calls.
    read: Vec<String>,
    /// Whether the program has an arrow function, and `new`.
    arrow: bool,
    new: bool,
    /// The last binder's id; the `let`s and parameters a test took apart,
    /// and those assigned.
    next_id: usize,
    tested: Vec<usize>,
    assigned: Vec<usize>,
    /// Whether the block being lowered is a function's body or the
    /// program, where a `var` is a `let` (in a nested block it would be
    /// the function's).
    var_ok: bool,
    /// The names a `for` loop's initialiser is about to declare.
    iteration: Vec<String>,
    /// The groups of mutually recursive function declarations of the
    /// blocks being lowered: each group's first declaration, and how many
    /// it has (`hoist` puts them together).
    groups: HashMap<*const Stmt, usize>,
    /// The program's modules, in the order they run, and the one being
    /// lowered.
    modules: Vec<Module>,
    module: usize,
    /// The function declarations whose body uses `this`, by their binders'
    /// ids.
    this_users: Vec<usize>,
    /// The natives' names the program calls.
    natives: Vec<String>,
}

/// What the end of a statement list is.
#[derive(Clone, Copy, PartialEq)]
enum Tail {
    /// The program's: its value is the last statement's.
    Program,
    /// A module's other than the entry's: the next module follows it.
    Module,
    /// A function body's: it returns what its last statement returns, or
    /// `undefined` when it falls off its end.
    Body,
    /// A statement's, whose value is dropped (a branch of an `if`, a
    /// loop's body, a block).
    Stmt,
}

impl Cx {
    fn push(&mut self, name: Option<&str>, kind: Kind) {
        self.push_sum(name, kind, None);
    }

    fn push_sum(&mut self, name: Option<&str>, kind: Kind, sum: Option<Sum>) {
        self.next_id += 1;
        self.scope.push(Binder {
            name: name.map(str::to_string),
            kind,
            id: self.next_id,
            sum,
            depth: self.depth,
            module: self.module,
            per_iteration: false,
        });
    }

    /// The binder `name` resolves to (an import's, the exporting module's),
    /// and its de Bruijn index.
    fn binder(&self, name: &str) -> Result<(usize, Binder), Unsupported> {
        let (i, _) = self.lookup(name)?;
        let b = self.own(name).expect("looked up");
        let b = match b.kind {
            Kind::Alias(id) => self
                .scope
                .iter()
                .find(|t| t.id == id)
                .expect("an import's binding"),
            _ => b,
        };
        Ok((i, b.clone()))
    }

    /// The binder of the current module `name` names (an import's alias
    /// itself).
    fn own(&self, name: &str) -> Option<&Binder> {
        self.scope
            .iter()
            .rev()
            .find(|b| b.module == self.module && b.name.as_deref() == Some(name))
    }

    /// `name` taken apart by a test, in the branches: a `let` or a
    /// parameter so tested mustn't be assigned anywhere (the branches see
    /// a copy, and a closure may assign the original).
    fn tested(&mut self, b: &Binder) {
        if b.kind == Kind::Mut {
            self.tested.push(b.id);
        }
    }

    fn pop(&mut self, n: usize) {
        self.scope.truncate(self.scope.len() - n);
    }

    /// `name`'s de Bruijn index and kind; a group's member's is its
    /// group's function's index.
    fn lookup(&self, name: &str) -> Result<(usize, Kind), Unsupported> {
        let mut i = 0;
        let mut member = None;
        let mut alias = None;
        for b in self.scope.iter().rev() {
            if let Some(g) = member {
                if b.id == g {
                    return Ok((i, Kind::Member(g)));
                }
            } else if let Some(a) = alias {
                if b.id == a {
                    return Ok((i, b.kind));
                }
            } else if b.module == self.module && b.name.as_deref() == Some(name) {
                match b.kind {
                    Kind::Later => {
                        return unsupported(format!("`{name}` used before its declaration"))
                    }
                    Kind::Member(g) => member = Some(g),
                    Kind::Alias(a) => alias = Some(a),
                    Kind::Namespace(_) => return Ok((0, b.kind)),
                    _ if b.per_iteration && b.depth < self.depth => {
                        return unsupported("a closure seeing a `for` loop's `let`")
                    }
                    k => return Ok((i, k)),
                }
            }
            if b.kind.bound() {
                i += 1;
            }
        }
        unsupported(format!("`{name}` isn't bound in the program (a builtin)"))
    }

    /// The de Bruijn index of the binder of that id.
    fn index_of(&self, id: usize) -> usize {
        self.scope
            .iter()
            .rev()
            .take_while(|b| b.id != id)
            .filter(|b| b.kind.bound())
            .count()
    }

    fn this(&self) -> Lowered {
        let mut i = 0;
        for b in self.scope.iter().rev() {
            match b.kind {
                Kind::This => return Ok(format!("(var {i})")),
                k if !k.bound() => continue,
                _ => i += 1,
            }
        }
        unsupported("`this` outside a function")
    }

    /// A statement list: each declaration binds the rest of the list.
    fn block(&mut self, stmts: &[Stmt], tail: Tail) -> Lowered {
        let (stmts, groups) = hoist(
            stmts
                .iter()
                .filter(|s| !matches!(s, Stmt::Empty { .. }))
                .collect(),
        );
        self.groups.extend(groups);
        // The names the list declares are in scope, as `Later`, until
        // their declarations.
        let mut names: Vec<String> = stmts.iter().flat_map(|s| declared(s)).collect();
        let n = names.len();
        names.sort();
        names.dedup();
        if names.len() != n {
            return unsupported("a name declared twice in a block");
        }
        let mut later = 0;
        for s in &stmts {
            for name in declared(s) {
                self.push(Some(&name), Kind::Later);
                later += 1;
            }
        }
        let falls_off = tail == Tail::Body && !stmts.last().is_some_and(|s| returns(s));
        let r = self.stmts(&stmts, tail, falls_off);
        // Drop what's left of the `Later` markers (all of them, now that
        // each declaration replaced its own).
        let n = self
            .scope
            .iter()
            .rev()
            .take_while(|b| b.kind == Kind::Later)
            .count();
        debug_assert!(n <= later);
        self.pop(n);
        r
    }

    fn stmts(&mut self, stmts: &[&Stmt], tail: Tail, falls_off: bool) -> Lowered {
        let Some((first, rest)) = stmts.split_first() else {
            return self.rest(&[], tail, falls_off);
        };
        let last = rest.is_empty();
        match first {
            Stmt::Var {
                kind, declarations, ..
            } => {
                if *kind == VarKind::Var && !self.var_ok {
                    return unsupported("a `var` in a nested block");
                }
                self.decls(declarations, rest, tail, falls_off)
            }
            Stmt::FunctionDecl { .. } if self.groups.contains_key(&(*first as *const Stmt)) => {
                let k = self
                    .groups
                    .remove(&(*first as *const Stmt))
                    .expect("a group");
                self.group(&stmts[..k], &stmts[k..], tail, falls_off)
            }
            Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                return_type_ast,
                ..
            } => {
                if type_annotation.is_some() || return_type_ast.is_some() {
                    return unsupported("an annotated function");
                }
                // (In a nested block, sloppy JavaScript also assigns it to
                // the function's `var` of that name.)
                if !self.var_ok {
                    return unsupported("a function declaration in a nested block");
                }
                self.unlater(name);
                let f = self.function_named(Some(name), Kind::FnName, params, body, false)?;
                self.push(Some(name), Kind::FnName);
                if crate::ast::free_idents::mentions_this_in_stmt(body) {
                    self.this_users.push(self.next_id);
                }
                let rest = self.rest(rest, tail, falls_off);
                self.pop(1);
                Ok(format!("(let {f} {})", rest?))
            }
            // An early exit, `if (v.kind !== "a") { return …; } rest`: the
            // rest runs only where the test fails, so it is that branch of
            // the test, and sees what the test takes apart (inty narrows
            // what follows an exit by the test's facts).
            Stmt::If {
                test,
                consequent,
                alternate: None,
                ..
            } if !last && pattern(test).is_some() && exits(consequent) => self.test(
                test,
                |cx| {
                    cx.branch(
                        consequent,
                        if tail == Tail::Module {
                            Tail::Stmt
                        } else {
                            tail
                        },
                    )
                },
                |cx| cx.stmts(rest, tail, falls_off),
            ),
            // A program ending in a statement other than an expression
            // has no value inty types (it types it `undefined`).
            s if last && tail == Tail::Program && !matches!(s, Stmt::Expr { .. }) => {
                let s = self.stmt(first, Tail::Stmt)?;
                Ok(format!("(seq {s} (undef))"))
            }
            // A module's last statement, then the next module.
            _ if last && tail == Tail::Module => {
                let s = self.stmt(first, Tail::Stmt)?;
                Ok(format!("(seq {s} {})", self.next_module()?))
            }
            _ => {
                let s = self.stmt(first, if last { tail } else { Tail::Stmt })?;
                if last {
                    if falls_off {
                        Ok(format!("(seq {s} (undef))"))
                    } else {
                        Ok(s)
                    }
                } else {
                    let rest = self.stmts(rest, tail, falls_off)?;
                    Ok(format!("(seq {s} {rest})"))
                }
            }
        }
    }

    /// A group of mutually recursive function declarations, `function f(…)
    /// {… g(…) …} function g(…) {… f(…) …}`: a function returning an object
    /// of them, `const G = function () { return {f: …, g: …}; }`, through
    /// which they reach each other (`g(…)` in `f` is `G().g(…)`), then each
    /// name bound to `function (x₀, …) { return G().f(x₀, …); }`. Inside
    /// the group, its members have one type each, as `G`'s own name has in
    /// its body; `G` is generalised, and so is each name, a function: the
    /// typing of a strongly connected component (`docs/scc-inference.md`).
    fn group(&mut self, members: &[&Stmt], rest: &[&Stmt], tail: Tail, falls_off: bool) -> Lowered {
        let mut fns = Vec::new();
        for s in members {
            let Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                return_type_ast,
                ..
            } = s
            else {
                unreachable!("a group holds function declarations");
            };
            if type_annotation.is_some() || return_type_ast.is_some() {
                return unsupported("an annotated function");
            }
            if !self.var_ok {
                return unsupported("a function declaration in a nested block");
            }
            // (Called through `G().f`, its `this` would be that object.)
            if crate::ast::free_idents::mentions_this_in_stmt(body) {
                return unsupported("a mutually recursive function using `this`");
            }
            for p in params.iter() {
                if p.optional || p.default.is_some() || p.type_ast.is_some() {
                    return unsupported("an optional or annotated parameter");
                }
            }
            fns.push((name.as_str(), params.as_slice(), &**body));
        }
        for (name, ..) in &fns {
            self.unlater(name);
            self.defined.push(name.to_string());
        }
        // `G`: its `this` and itself, then its members.
        self.push(None, Kind::This);
        self.push(None, Kind::Const);
        let g = self.next_id;
        self.depth += 1;
        for (name, ..) in &fns {
            self.push(Some(name), Kind::Member(g));
        }
        let fields: Result<Vec<String>, Unsupported> = fns
            .iter()
            .map(|(name, params, body)| {
                let f = self.function_named(Some(name), Kind::FnName, params, body, false)?;
                Ok(format!("(field s:{} {f})", tok(name)?))
            })
            .collect();
        self.pop(fns.len());
        self.depth -= 1;
        self.pop(2);
        let group = format!("(func 0 (ret (obj {})))", fields?.join(" "));
        self.push(None, Kind::Const);
        let g = self.next_id;
        let mut wrappers = Vec::new();
        for (name, params, _) in &fns {
            let n = params.len();
            // Inside the wrapper, its parameters, itself and its `this`
            // come first.
            let gi = self.index_of(g) + n + 2;
            let args: String = (0..n).map(|i| format!(" (var {i})")).collect();
            wrappers.push(format!(
                "(func {n} (ret (app (get (app (var {gi})) s:{}){args})))",
                tok(name)?
            ));
            self.push(Some(name), Kind::FnName);
        }
        let rest = self.rest(rest, tail, falls_off);
        self.pop(fns.len() + 1);
        let mut out = rest?;
        for w in wrappers.iter().rev() {
            out = format!("(let {w} {out})");
        }
        Ok(format!("(let {group} {out})"))
    }

    /// Module `k`, with its imports, and those after it.
    fn enter_module(&mut self, k: usize) -> Lowered {
        self.module = k;
        let imports = std::mem::take(&mut self.modules[k].imports);
        let mut pushed = 0;
        for (local, imported) in imports {
            let target = match imported {
                Imported::Name(m, x) => match self.modules[m].table.get(&x) {
                    Some(t) => *t,
                    None => {
                        return unsupported(format!("an import of `{x}`, which isn't exported"))
                    }
                },
                Imported::Namespace(m) => Target::Namespace(m),
            };
            self.push(
                Some(&local),
                match target {
                    Target::Binder(id) => Kind::Alias(id),
                    Target::Namespace(m) => Kind::Namespace(m),
                },
            );
            pushed += 1;
        }
        let stmts = std::mem::take(&mut self.modules[k].stmts);
        let tail = if k + 1 == self.modules.len() {
            Tail::Program
        } else {
            Tail::Module
        };
        let r = self.block(&stmts, tail);
        self.pop(pushed);
        r
    }

    /// The end of the current module: its exports, then the next module.
    fn next_module(&mut self) -> Lowered {
        let k = self.module;
        for (name, exported) in std::mem::take(&mut self.modules[k].exports) {
            match exported {
                Exported::Local(l) => {
                    let Some(b) = self
                        .scope
                        .iter()
                        .rev()
                        .find(|b| b.module == k && b.name.as_deref() == Some(&*l))
                    else {
                        return unsupported(format!("an export of `{l}`, which isn't declared"));
                    };
                    let t = match b.kind {
                        Kind::Alias(id) => Target::Binder(id),
                        Kind::Namespace(m) => Target::Namespace(m),
                        k if k.bound() => Target::Binder(b.id),
                        _ => return unsupported(format!("an export of `{l}`")),
                    };
                    self.modules[k].table.insert(name, t);
                }
                Exported::From(m, x) => {
                    let Some(t) = self.modules[m].table.get(&x).copied() else {
                        return unsupported(format!("a re-export of `{x}`, which isn't exported"));
                    };
                    self.modules[k].table.insert(name, t);
                }
                Exported::All(m) => {
                    let all: Vec<(String, Target)> = self.modules[m]
                        .table
                        .iter()
                        .filter(|(x, _)| *x != "default")
                        .map(|(x, t)| (x.clone(), *t))
                        .collect();
                    for (x, t) in all {
                        self.modules[k].table.entry(x).or_insert(t);
                    }
                }
                Exported::Namespace(m) => {
                    self.modules[k].table.insert(name, Target::Namespace(m));
                }
            }
        }
        let r = self.enter_module(k + 1);
        self.module = k;
        r
    }

    /// A module's export, `ns.x`, as the binder it is.
    fn namespace_member(&self, m: usize, x: &str) -> Lowered {
        match self.modules[m].table.get(x) {
            Some(Target::Binder(id)) => Ok(format!("(var {})", self.index_of(*id))),
            Some(Target::Namespace(_)) => {
                unsupported("a namespace in a namespace, used as a value")
            }
            None => unsupported(format!("`{x}`, which the module doesn't export")),
        }
    }

    /// The module whose namespace `e` is, if it is one.
    fn namespace(&self, e: &Expr) -> Option<usize> {
        let Expr::Ident { name, .. } = e else {
            return None;
        };
        match self.lookup(name) {
            Ok((_, Kind::Namespace(m))) => Some(m),
            _ => None,
        }
    }

    /// The rest of a list after a declaration: `undefined` if nothing.
    fn rest(&mut self, rest: &[&Stmt], tail: Tail, falls_off: bool) -> Lowered {
        if rest.is_empty() && tail == Tail::Module {
            self.next_module()
        } else if rest.is_empty() {
            Ok("(undef)".to_string())
        } else {
            self.stmts(rest, tail, falls_off)
        }
    }

    /// Remove `name`'s `Later` marker: its declaration is reached.
    fn unlater(&mut self, name: &str) {
        if let Some(i) = self
            .scope
            .iter()
            .rposition(|b| b.kind == Kind::Later && b.name.as_deref() == Some(name))
        {
            self.scope.remove(i);
        }
    }

    fn decls(
        &mut self,
        decls: &[crate::ast::VarDeclarator],
        rest: &[&Stmt],
        tail: Tail,
        falls_off: bool,
    ) -> Lowered {
        let Some((d, more)) = decls.split_first() else {
            return self.rest(rest, tail, falls_off);
        };
        if d.type_ast.is_some() {
            return unsupported("a declared type in the TypeAst channel");
        }
        let mutable = d.kind != VarKind::Const;
        let init = match &d.init {
            // `const f = (x) => … f(…) …`: the function's own name, which
            // the model's function binds, is `f`, the `const` it is.
            Some(
                e @ Expr::Function {
                    name: None,
                    params,
                    body,
                    type_annotation: None,
                    arrow,
                    ..
                },
            ) if !mutable
                && d.type_annotation.is_none()
                && crate::ast::free_idents::free_identifiers_in_expr(e).contains(&d.name) =>
            {
                self.function_named(Some(&d.name), Kind::FnName, params, body, *arrow)?
            }
            Some(e) => self.expr(e)?,
            // (inty gives `let x;` a type its later assignments decide.)
            None => return unsupported("a declaration without an initialiser"),
        };
        let ann = match &d.type_annotation {
            Some(a) => {
                let ann = annotation(&a.content)?;
                // An annotation's record labels are the program's too.
                let t = match &ann {
                    Ann::Mono(t) | Ann::Poly(_, t) => t,
                };
                for tok in t.split(['(', ')', ' ']) {
                    if let Some(l) = tok.strip_prefix("s:") {
                        self.defined.push(l.to_string());
                    }
                }
                Some(ann)
            }
            None => None,
        };
        // The sum the binding declares, or an alias's (`const w = v`).
        let sum = match &ann {
            Some(Ann::Mono(t)) if t.starts_with("(variant") => Some(Sum::Variant),
            Some(Ann::Mono(t)) if t.starts_with("(sum") => Some(Sum::Typeof),
            Some(Ann::Mono(t)) if t.starts_with("(nullable") || t.starts_with("(optional") => {
                Some(Sum::Maybe)
            }
            Some(_) => None,
            None => match &d.init {
                Some(Expr::Ident { name, .. }) => self.binder(name).ok().and_then(|(_, b)| b.sum),
                _ => None,
            },
        };
        self.unlater(&d.name);
        self.push_sum(
            Some(&d.name),
            if mutable { Kind::Mut } else { Kind::Const },
            sum,
        );
        if let Some(k) = self.iteration.iter().position(|n| *n == d.name) {
            self.iteration.remove(k);
            self.scope.last_mut().expect("pushed").per_iteration = true;
        }
        let body = self.decls(more, rest, tail, falls_off);
        self.pop(1);
        let body = body?;
        Ok(match (ann, mutable) {
            (None, false) => format!("(let {init} {body})"),
            (None, true) => format!("(letmut {init} {body})"),
            (Some(Ann::Mono(t)), false) => format!("(letann {t} {init} {body})"),
            (Some(Ann::Mono(t)), true) => format!("(letmutann {t} {init} {body})"),
            // The model generalises an annotation's scheme over a value only
            // (inty checks the others with flexible variables).
            (Some(Ann::Poly(..)), false)
                if !matches!(d.init, Some(Expr::Function { .. } | Expr::Lit { .. })) =>
            {
                return unsupported("a polymorphic annotation on what isn't a value");
            }
            (Some(Ann::Poly(n, t)), false) => format!("(letpoly {n} {t} {init} {body})"),
            (Some(Ann::Poly(..)), true) => {
                return unsupported("a polymorphic annotation on a `let`");
            }
        })
    }

    fn stmt(&mut self, s: &Stmt, tail: Tail) -> Lowered {
        match s {
            // `x++` and `x--` whose value is dropped: `x = x - -1` (a
            // subtraction, which takes numbers only, as `++` does).
            Stmt::Expr {
                expression:
                    Expr::Unary {
                        op:
                            op @ (UnaryOp::PreInc
                            | UnaryOp::PostInc
                            | UnaryOp::PreDec
                            | UnaryOp::PostDec),
                        argument,
                        ..
                    },
                ..
            } if tail != Tail::Program => {
                let Expr::Ident { name, .. } = &**argument else {
                    return unsupported(format!("the operator {op:?} on what isn't a binding"));
                };
                let one = if matches!(op, UnaryOp::PreInc | UnaryOp::PostInc) {
                    "(neg (num 1 0))"
                } else {
                    "(num 1 0)"
                };
                self.assign(name, |_, i| Ok(format!("(minus (var {i}) {one})")))
            }
            Stmt::Expr { expression, .. } => self.expr(expression),
            Stmt::Block { body, .. } => {
                let var_ok = std::mem::replace(&mut self.var_ok, false);
                let r = self.block(body, tail);
                self.var_ok = var_ok;
                r
            }
            Stmt::Return { .. } if self.depth == 0 => unsupported("`return` outside a function"),
            Stmt::Return { argument, .. } => match argument {
                Some(e) => Ok(format!("(ret {})", self.expr(e)?)),
                None => Ok("(ret (undef))".to_string()),
            },
            Stmt::Throw { argument, .. } => Ok(format!("(throw {})", self.expr(argument)?)),
            Stmt::If {
                test,
                consequent,
                alternate,
                ..
            } => {
                // A function's last `if`: its branches' `return`s are its
                // results (`returns`); anything else's value is dropped.
                self.test(
                    test,
                    |cx| cx.branch(consequent, tail),
                    |cx| match alternate {
                        Some(a) => cx.branch(a, tail),
                        None => Ok("(undef)".to_string()),
                    },
                )
            }
            Stmt::While { test, body, .. } => {
                let c = self.expr(test)?;
                let b = self.branch(body, Tail::Stmt)?;
                Ok(format!("(while {c} {b})"))
            }
            // `for (init; test; update) body` is `{ init; while (test) {
            // body; update } }`, where no `continue` skips the update and
            // no closure sees the `let`s JavaScript binds afresh each
            // iteration.
            Stmt::For {
                init,
                test,
                update,
                body,
                span,
            } => {
                if continues(body) {
                    return unsupported("a `continue` in a `for` loop");
                }
                let test = test.clone().unwrap_or(Expr::Lit {
                    value: Literal::Boolean(true),
                    span: *span,
                });
                let mut each = vec![(**body).clone()];
                if let Some(u) = update {
                    each.push(Stmt::Expr {
                        expression: u.clone(),
                        span: *span,
                    });
                }
                let w = Stmt::While {
                    test,
                    body: Box::new(Stmt::Block {
                        body: each,
                        span: *span,
                    }),
                    span: *span,
                };
                match init {
                    None => self.stmt(&w, Tail::Stmt),
                    Some(ForInit::Expr(e)) => {
                        let e = self.expr(e)?;
                        Ok(format!("(seq {e} {})", self.stmt(&w, Tail::Stmt)?))
                    }
                    Some(ForInit::VarDecl(ds)) => {
                        if ds.iter().any(|d| d.kind == VarKind::Var) {
                            return unsupported("a `var` in a `for` loop");
                        }
                        self.iteration = ds.iter().map(|d| d.name.clone()).collect();
                        let r = self.decls(ds, &[&w], Tail::Stmt, false);
                        self.iteration.clear();
                        r
                    }
                }
            }
            Stmt::Break { label: None, .. } => Ok("(break)".to_string()),
            Stmt::Continue { label: None, .. } => Ok("(continue)".to_string()),
            Stmt::Try {
                block,
                handler,
                finalizer,
                ..
            } => {
                let b = self.branch(block, tail)?;
                let caught = match handler {
                    Some(h) => {
                        self.push(Some(&h.param), Kind::Mut);
                        let body = self.branch(&h.body, tail);
                        self.pop(1);
                        format!("(trycatch {b} {})", body?)
                    }
                    None => b,
                };
                match finalizer {
                    Some(f) => {
                        let f = self.branch(f, Tail::Stmt)?;
                        Ok(format!("(tryfinally {caught} {f})"))
                    }
                    None => Ok(caught),
                }
            }
            Stmt::Var { .. } | Stmt::FunctionDecl { .. } => {
                unsupported("a declaration as a branch")
            }
            _ => unsupported(stmt_name(s)),
        }
    }

    /// A branch of an `if`, a loop's body, a `try` block: a statement,
    /// its declarations scoped to it.
    fn branch(&mut self, s: &Stmt, tail: Tail) -> Lowered {
        let tail = if tail == Tail::Body && !returns(s) {
            Tail::Stmt
        } else {
            tail
        };
        let var_ok = std::mem::replace(&mut self.var_ok, false);
        let r = match s {
            Stmt::Block { body, .. } => self.block(body, tail),
            s => self.block(std::slice::from_ref(s), tail),
        };
        self.var_ok = var_ok;
        r
    }

    /// A test, with what its branches are: a test of a binding for
    /// nothing, of its `typeof` or of its tag takes it apart.
    fn test(
        &mut self,
        test: &Expr,
        yes: impl Fn(&mut Self) -> Lowered,
        no: impl Fn(&mut Self) -> Lowered,
    ) -> Lowered {
        match pattern(test) {
            Some(Pattern::Truthy { name, negated }) => {
                // (A name the program doesn't bind, a builtin's, is tested
                // as any value is.)
                let Ok((i, b)) = self.binder(name) else {
                    return self.plain_test(test, yes, no);
                };
                if b.sum != Some(Sum::Maybe) {
                    return self.plain_test(test, yes, no);
                }
                self.tested(&b);
                // `x ? truthy : falsy` on a sum of nothing is
                // `unwrap x falsy (x' ? truthy : falsy)`: `truthy` sees
                // `x`'s value; `falsy` runs once either way, and sees `x`
                // as it is, as inty's does.
                let (truthy, falsy): (&Branch<Self>, &Branch<Self>) =
                    if negated { (&no, &yes) } else { (&yes, &no) };
                let none = falsy(self)?;
                self.push_sum(Some(name), Kind::Shadow, None);
                let some = truthy(self);
                self.pop(1);
                let some = some?;
                self.push(None, Kind::Const);
                let other = falsy(self);
                self.pop(1);
                Ok(format!(
                    "(unwrap (var {i}) {none} (cond (var 0) {some} {}))",
                    other?
                ))
            }
            Some(Pattern::Nothing { name, negated }) => {
                let (i, b) = self.binder(name)?;
                self.tested(&b);
                // `x != null ? some : none`: `some` sees `x`'s value.
                let (none, some) = if negated {
                    let none = no(self)?;
                    self.push_sum(Some(name), Kind::Shadow, b.sum);
                    let some = yes(self);
                    self.pop(1);
                    (none, some)
                } else {
                    let none = yes(self)?;
                    self.push_sum(Some(name), Kind::Shadow, b.sum);
                    let some = no(self);
                    self.pop(1);
                    (none, some)
                };
                Ok(format!("(unwrap (var {i}) {none} {})", some?))
            }
            Some(Pattern::Typeof { name, tag, negated }) => {
                let (i, b) = self.binder(name)?;
                if b.sum != Some(Sum::Typeof) {
                    // Not a sum: a plain test (`===` on its `typeof`).
                    return self.plain_test(test, yes, no);
                }
                self.tested(&b);
                let (case, rest) = self.split(&b, yes, no, negated)?;
                let tag = tok(tag)?;
                Ok(format!("(typetest (var {i}) s:{tag} {rest} {case})"))
            }
            Some(Pattern::Tag {
                name,
                label,
                tag,
                negated,
            }) => {
                let (i, b) = self.binder(name)?;
                if b.sum != Some(Sum::Variant) {
                    return self.plain_test(test, yes, no);
                }
                self.tested(&b);
                let (label, tag) = (tok(label)?, tok(tag)?);
                let (case, rest) = self.split(&b, yes, no, negated)?;
                Ok(format!(
                    "(casetag (var {i}) s:{label} s:{tag} {rest} {case})"
                ))
            }
            None => self.plain_test(test, yes, no),
        }
    }

    /// A test that takes nothing apart: `?:` on its value.
    fn plain_test(
        &mut self,
        test: &Expr,
        yes: impl FnOnce(&mut Self) -> Lowered,
        no: impl FnOnce(&mut Self) -> Lowered,
    ) -> Lowered {
        let c = self.expr(test)?;
        let t = yes(self)?;
        let e = no(self)?;
        Ok(format!("(cond {c} {t} {e})"))
    }

    /// The branches of a test that takes `name` apart, each seeing it
    /// rebound: the case's, then the rest's.
    fn split(
        &mut self,
        b: &Binder,
        yes: impl FnOnce(&mut Self) -> Lowered,
        no: impl FnOnce(&mut Self) -> Lowered,
        negated: bool,
    ) -> Result<(String, String), Unsupported> {
        self.push_sum(b.name.as_deref(), Kind::Shadow, b.sum);
        let r = (|| {
            let y = yes(self)?;
            let n = no(self)?;
            Ok(if negated { (n, y) } else { (y, n) })
        })();
        self.pop(1);
        r
    }

    fn function(
        &mut self,
        name: Option<&str>,
        params: &[Param],
        body: &Stmt,
        arrow: bool,
    ) -> Lowered {
        self.function_named(name, Kind::Const, params, body, arrow)
    }

    /// A function, its own name bound as `kind`.
    fn function_named(
        &mut self,
        name: Option<&str>,
        kind: Kind,
        params: &[Param],
        body: &Stmt,
        arrow: bool,
    ) -> Lowered {
        self.arrow |= arrow;
        for p in params {
            if p.optional || p.default.is_some() || p.type_ast.is_some() {
                return unsupported("an optional or annotated parameter");
            }
        }
        // `this`, the function itself, then the parameters, the first
        // innermost.
        self.push(None, if arrow { Kind::ArrowThis } else { Kind::This });
        self.push(name, kind);
        self.depth += 1;
        let var_ok = std::mem::replace(&mut self.var_ok, true);
        for p in params.iter().rev() {
            self.push(Some(&p.name), Kind::Mut);
        }
        let b = match body {
            Stmt::Block { body, .. } => self.block(body, Tail::Body),
            // An arrow's expression body.
            Stmt::Return {
                argument: Some(e), ..
            } => self.expr(e),
            s => self.block(std::slice::from_ref(s), Tail::Body),
        };
        self.var_ok = var_ok;
        self.depth -= 1;
        self.pop(params.len() + 2);
        Ok(format!("(func {} {})", params.len(), b?))
    }

    /// An assignment to the binding `name` of `value`, given `name`'s
    /// index.
    fn assign(&mut self, name: &str, value: impl FnOnce(&mut Self, usize) -> Lowered) -> Lowered {
        // (JavaScript's imports are read-only.)
        if self
            .own(name)
            .is_some_and(|b| matches!(b.kind, Kind::Alias(_) | Kind::Namespace(_)))
        {
            return unsupported("an assignment to an import");
        }
        let (i, b) = self.binder(name)?;
        self.assigned.push(b.id);
        if b.kind == Kind::Shadow {
            return unsupported("an assignment to a binding a test took apart");
        }
        if matches!(b.kind, Kind::FnName | Kind::Member(_)) {
            return unsupported("an assignment to a function declaration's name");
        }
        Ok(format!("(assign {i} {})", value(self, i)?))
    }

    fn exprs(&mut self, es: &[Expr]) -> Lowered {
        let mut out = String::new();
        for e in es {
            out.push(' ');
            out.push_str(&self.expr(e)?);
        }
        Ok(out)
    }

    fn expr(&mut self, e: &Expr) -> Lowered {
        match e {
            Expr::Lit { value, .. } => literal(value),
            Expr::Ident { name, .. } => match self.lookup(name) {
                Ok((i, Kind::Member(_))) => Ok(format!("(get (app (var {i})) s:{})", tok(name)?)),
                Ok((_, Kind::Namespace(_))) => unsupported("a module's namespace as a value"),
                Ok((i, _)) => Ok(format!("(var {i})")),
                Err(_) if name == "undefined" => Ok("(undef)".to_string()),
                Err(why) => Err(why),
            },
            Expr::This { .. } => self.this(),
            Expr::Array { elements, .. } => {
                let mut out = String::from("(arr");
                for el in elements {
                    match el {
                        Some(Expr::Spread { .. }) => return unsupported("an array spread"),
                        Some(e) => {
                            out.push(' ');
                            out.push_str(&self.expr(e)?);
                        }
                        None => return unsupported("an array hole"),
                    }
                }
                out.push(')');
                Ok(out)
            }
            Expr::Object { properties, .. } => self.object(properties),
            Expr::Function {
                name,
                params,
                body,
                type_annotation,
                arrow,
                ..
            } => {
                if type_annotation.is_some() {
                    return unsupported("an annotated function");
                }
                self.function(name.as_deref(), params, body, *arrow)
            }
            // `ns.x`, of a module's namespace: its export `x`, a new
            // instance of its scheme at each use.
            Expr::Member {
                object, property, ..
            } if self.namespace(object).is_some() => {
                self.namespace_member(self.namespace(object).expect("a namespace"), property)
            }
            Expr::Member {
                object, property, ..
            } => {
                self.read.push(property.clone());
                let property = tok(property)?;
                Ok(format!("(get {} s:{property})", self.expr(object)?))
            }
            Expr::ComputedMember { property, .. }
                if matches!(
                    **property,
                    Expr::Lit {
                        value: Literal::String(_),
                        ..
                    }
                ) =>
            {
                unsupported("a property read by a string index")
            }
            Expr::ComputedMember {
                object, property, ..
            } => Ok(format!(
                "(index {} {})",
                self.expr(object)?,
                self.expr(property)?
            )),
            Expr::Call {
                callee,
                arguments,
                keywords,
                ..
            } => {
                if !keywords.is_empty() {
                    return unsupported("keyword arguments");
                }
                if arguments.iter().any(|a| matches!(a, Expr::Spread { .. })) {
                    return unsupported("a spread argument");
                }
                match &**callee {
                    // (Its `this` is the namespace, which the model has no
                    // value for: a function using it is left out.)
                    Expr::Member {
                        object, property, ..
                    } if self.namespace(object).is_some() => {
                        let m = self.namespace(object).expect("a namespace");
                        if let Some(Target::Binder(id)) = self.modules[m].table.get(property) {
                            if self.this_users.contains(id) {
                                return unsupported(
                                    "a call through a namespace of a function using `this`",
                                );
                            }
                        }
                        Ok(format!(
                            "(app {}{})",
                            self.namespace_member(m, property)?,
                            self.exprs(arguments)?
                        ))
                    }
                    // A string's or an array's method: the model's native of
                    // that name and number of arguments (`lean/Inty/Classes.lean`,
                    // `stringMethod`, `arrayMethod`).
                    Expr::Member {
                        object, property, ..
                    } if NATIVE_METHODS.iter().any(|(m, _)| m == property) => {
                        let n = arguments.len();
                        if !NATIVE_METHODS.contains(&(property.as_str(), n)) {
                            return unsupported(format!("`{property}` with {n} arguments"));
                        }
                        self.natives.push(property.clone());
                        Ok(format!(
                            "(mcall {} s:{}/{n}{})",
                            self.expr(object)?,
                            tok(property)?,
                            self.exprs(arguments)?
                        ))
                    }
                    Expr::Member {
                        object, property, ..
                    } => {
                        self.read.push(property.clone());
                        let property = tok(property)?;
                        Ok(format!(
                            "(mcall {} s:{property}{})",
                            self.expr(object)?,
                            self.exprs(arguments)?
                        ))
                    }
                    Expr::ComputedMember { .. } => unsupported("a call of a computed member"),
                    f => Ok(format!("(app {}{})", self.expr(f)?, self.exprs(arguments)?)),
                }
            }
            Expr::New {
                callee, arguments, ..
            } => {
                self.new = true;
                Ok(format!(
                    "(new {}{})",
                    self.expr(callee)?,
                    self.exprs(arguments)?
                ))
            }
            Expr::Unary { op, argument, .. } => match op {
                UnaryOp::Neg => Ok(format!("(neg {})", self.expr(argument)?)),
                UnaryOp::Not => Ok(format!("(not {})", self.expr(argument)?)),
                UnaryOp::Typeof => Ok(format!("(typeof {})", self.expr(argument)?)),
                UnaryOp::Void => match &**argument {
                    Expr::Lit { .. } => Ok("(undef)".to_string()),
                    a => Ok(format!("(seq {} (undef))", self.expr(a)?)),
                },
                op => unsupported(format!("the operator {op:?}")),
            },
            Expr::Binary {
                op, left, right, ..
            } => match op {
                BinOp::Add => Ok(format!("(plus {} {})", self.expr(left)?, self.expr(right)?)),
                BinOp::Sub => Ok(format!(
                    "(minus {} {})",
                    self.expr(left)?,
                    self.expr(right)?
                )),
                BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::Lt
                | BinOp::LtEq
                | BinOp::Gt
                | BinOp::GtEq
                | BinOp::EqEqEq
                | BinOp::NotEqEq => {
                    let form = match op {
                        BinOp::Mul => "times",
                        BinOp::Div => "div",
                        BinOp::Mod => "mod",
                        BinOp::Lt => "lt",
                        BinOp::LtEq => "le",
                        BinOp::Gt => "gt",
                        BinOp::GtEq => "ge",
                        BinOp::EqEqEq => "eq",
                        _ => "ne",
                    };
                    Ok(format!(
                        "({form} {} {})",
                        self.expr(left)?,
                        self.expr(right)?
                    ))
                }
                // A test on the left (a boolean): `a && b` is `a ? b : false`,
                // so `b` sees what `a` takes apart.
                BinOp::And | BinOp::Or
                    if matches!(pattern(left), Some(p) if !matches!(p, Pattern::Truthy { .. }))
                        && boolean(right) =>
                {
                    if *op == BinOp::And {
                        self.test(left, |cx| cx.expr(right), |_| Ok("(bool false)".into()))
                    } else {
                        self.test(left, |_| Ok("(bool true)".into()), |cx| cx.expr(right))
                    }
                }
                // Otherwise `const t = a; t ? b : t` (`t ? t : b` for `||`),
                // whose branches have one type, or an expected type pushed
                // into each; inty's union of two known types (`c && obj`)
                // is a join the model leaves out on purpose (lean/GAPS.md).
                BinOp::And | BinOp::Or => {
                    let a = self.expr(left)?;
                    self.push(None, Kind::Const);
                    let b = self.expr(right);
                    self.pop(1);
                    let b = b?;
                    Ok(if *op == BinOp::And {
                        format!("(let {a} (cond (var 0) {b} (var 0)))")
                    } else {
                        format!("(let {a} (cond (var 0) (var 0) {b}))")
                    })
                }
                op => unsupported(format!("the operator {op:?}")),
            },
            // `x += e` is `x = x + e`, and so on, for a binding.
            Expr::Assign {
                op, left, right, ..
            } if *op != AssignOp::Assign => {
                let form = match op {
                    AssignOp::AddAssign => "plus",
                    AssignOp::SubAssign => "minus",
                    AssignOp::MulAssign => "times",
                    AssignOp::DivAssign => "div",
                    AssignOp::ModAssign => "mod",
                    op => return unsupported(format!("the assignment {op:?}")),
                };
                let Expr::Ident { name, .. } = &**left else {
                    return unsupported(format!("the assignment {op:?} to what isn't a binding"));
                };
                self.assign(name, |cx, i| {
                    Ok(format!("({form} (var {i}) {})", cx.expr(right)?))
                })
            }
            Expr::Assign { left, right, .. } => match &**left {
                Expr::Ident { name, .. } => self.assign(name, |cx, _| cx.expr(right)),
                Expr::Member {
                    object, property, ..
                } => {
                    self.defined.push(property.clone());
                    let property = tok(property)?;
                    Ok(format!(
                        "(set {} s:{property} {})",
                        self.expr(object)?,
                        self.expr(right)?
                    ))
                }
                Expr::ComputedMember {
                    object, property, ..
                } => Ok(format!(
                    "(setindex {} {} {})",
                    self.expr(object)?,
                    self.expr(property)?,
                    self.expr(right)?
                )),
                _ => unsupported("a destructuring assignment"),
            },
            Expr::Conditional {
                test,
                consequent,
                alternate,
                ..
            } => self.test(test, |cx| cx.expr(consequent), |cx| cx.expr(alternate)),
            Expr::Sequence { expressions, .. } => {
                let (last, init) = expressions
                    .split_last()
                    .ok_or_else(|| "an empty sequence".to_string())?;
                let mut out = self.expr(last)?;
                for e in init.iter().rev() {
                    out = format!("(seq {} {out})", self.expr(e)?);
                }
                Ok(out)
            }
            Expr::OptionalChain { segments, .. } => {
                if segments.iter().any(|s| match s {
                    ChainSegment::Member { optional, .. }
                    | ChainSegment::Computed { optional, .. }
                    | ChainSegment::Call { optional, .. } => *optional,
                }) {
                    unsupported("`?.`")
                } else {
                    unsupported("a call chain")
                }
            }
            Expr::Tuple { .. } => unsupported("a tuple"),
            Expr::NewTarget { .. } => unsupported("`new.target`"),
            // `a ?? b` is `unwrap a b x`: `a`'s value if it isn't nothing,
            // else `b`'s.
            Expr::NullishCoalesce { left, right, .. } => {
                let a = self.expr(left)?;
                let b = self.expr(right)?;
                Ok(format!("(unwrap {a} {b} (var 0))"))
            }
            Expr::Spread { .. } => unsupported("a spread"),
            Expr::RestArray { .. } | Expr::RestRow { .. } => unsupported("destructuring"),
            Expr::TemplateLiteral { .. } => unsupported("a template literal"),
        }
    }

    /// An object literal: its runs of fields between spreads are literals,
    /// spread left to right (`{a: 1, ...o}` is `{...{a: 1}, ...o}`).
    fn object(&mut self, props: &[PropDef]) -> Lowered {
        // A getter or a method beside a spread would be lowered into an
        // operand of the spread: a getter would run there, with the
        // operand as `this`, and a method's `this` would be the operand's
        // type.
        if props.iter().any(|p| matches!(p, PropDef::Spread { .. }))
            && props
                .iter()
                .any(|p| matches!(p, PropDef::Getter { .. } | PropDef::Method { .. }))
        {
            return unsupported("a getter or a method in a literal with a spread");
        }
        let mut parts: Vec<String> = Vec::new();
        let mut run: Vec<String> = Vec::new();
        let mut labels: Vec<String> = Vec::new();
        let mut spread = false;
        for p in props {
            match p {
                PropDef::Property {
                    key,
                    value,
                    type_annotation,
                    type_ast,
                    ..
                } => {
                    if type_annotation.is_some() || type_ast.is_some() {
                        return unsupported("an annotated field");
                    }
                    let l = key_label(key)?;
                    labels.push(l.clone());
                    run.push(format!(" (field s:{l} {})", self.expr(value)?));
                }
                PropDef::Method {
                    key,
                    params,
                    body,
                    return_type_ast,
                    proto: false,
                    ..
                } => {
                    if return_type_ast.is_some() {
                        return unsupported("an annotated method");
                    }
                    let l = key_label(key)?;
                    labels.push(l.clone());
                    let f = self.function(None, params, body, false)?;
                    run.push(format!(" (method s:{l} {f})"));
                }
                PropDef::Getter {
                    key,
                    body,
                    proto: false,
                    ..
                } => {
                    let l = key_label(key)?;
                    labels.push(l.clone());
                    let f = self.function(None, &[], body, false)?;
                    run.push(format!(" (getter s:{l} {f})"));
                }
                PropDef::Spread { argument, .. } => {
                    spread = true;
                    if !run.is_empty() {
                        parts.push(format!("(obj{})", run.concat()));
                        run.clear();
                    }
                    parts.push(self.expr(argument)?);
                }
                PropDef::Setter { .. } => return unsupported("a setter"),
                PropDef::Method { .. } | PropDef::Getter { .. } => {
                    return unsupported("a class member");
                }
            }
        }
        self.defined.extend(labels.iter().cloned());
        let mut sorted = labels.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != labels.len() {
            return unsupported("a label written twice in a literal");
        }
        if !spread {
            return Ok(format!("(obj{})", run.concat()));
        }
        if !run.is_empty() {
            parts.push(format!("(obj{})", run.concat()));
        }
        let mut parts = parts.into_iter();
        let first = parts.next().expect("a spread");
        let mut out = match parts.next() {
            Some(second) => format!("(spread {first} {second})"),
            None => format!("(spread {first} (obj))"),
        };
        for p in parts {
            out = format!("(spread {out} {p})");
        }
        Ok(out)
    }
}

/// A block with its function declarations moved up, as JavaScript hoists
/// them, each after the declarations it refers to: the model has no
/// forward reference. The other statements keep their order (a function's
/// declaration has no effect, so it can move). Functions calling each
/// other are a group, moved as one, and returned beside the block; a
/// block refusing every order is left as it is (and the program is left
/// out by `Later`).
fn hoist(stmts: Vec<&Stmt>) -> (Vec<&Stmt>, Vec<(*const Stmt, usize)>) {
    let n = stmts.len();
    let is_fn = |s: &Stmt| matches!(s, Stmt::FunctionDecl { .. });
    let declares: Vec<Vec<String>> = stmts.iter().map(|s| declared(s)).collect();
    // `after[j]`: the statements `j` must follow.
    let mut after: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (j, s) in stmts.iter().enumerate() {
        let free = crate::ast::free_idents::free_identifiers_in_stmt(s);
        for (i, names) in declares.iter().enumerate() {
            if i != j && names.iter().any(|d| free.contains(d)) {
                after[j].push(i);
            }
        }
        // Statements other than functions keep their order.
        if !is_fn(s) {
            if let Some(i) = (0..j).rev().find(|&i| !is_fn(stmts[i])) {
                after[j].push(i);
            }
        }
    }
    // Functions that reach each other through the functions they call are
    // one group, placed as one: `unit[j]` is the first of `j`'s.
    let fns: Vec<usize> = (0..n).filter(|&j| is_fn(stmts[j])).collect();
    let mut reach = vec![vec![false; n]; n];
    for &j in &fns {
        for &i in &after[j] {
            reach[j][i] = is_fn(stmts[i]);
        }
    }
    for &k in &fns {
        for &a in &fns {
            if reach[a][k] {
                for &b in &fns {
                    reach[a][b] |= reach[k][b];
                }
            }
        }
    }
    let unit: Vec<usize> = (0..n)
        .map(|j| {
            if is_fn(stmts[j]) {
                fns.iter()
                    .copied()
                    .find(|&i| i == j || (reach[i][j] && reach[j][i]))
                    .expect("j itself")
            } else {
                j
            }
        })
        .collect();
    let members = |u: usize| -> Vec<usize> { (0..n).filter(|&j| unit[j] == u).collect() };
    let mut out = Vec::with_capacity(n);
    let mut groups = Vec::new();
    let mut placed = vec![false; n];
    while out.len() < n {
        // The first unit whose predecessors are all placed.
        let Some(u) = (0..n).find(|&u| {
            unit[u] == u
                && !placed[u]
                && members(u)
                    .iter()
                    .all(|&j| after[j].iter().all(|&i| unit[i] == u || placed[i]))
        }) else {
            return (stmts, Vec::new());
        };
        let ms = members(u);
        if ms.len() > 1 {
            groups.push((stmts[u] as *const Stmt, ms.len()));
        }
        for j in ms {
            placed[j] = true;
            out.push(stmts[j]);
        }
    }
    (out, groups)
}

/// Whether `e` is a boolean whatever its operands: a test, a comparison,
/// `!`, a boolean literal, or `&&`/`||` of those.
fn boolean(e: &Expr) -> bool {
    match e {
        Expr::Lit {
            value: Literal::Boolean(_),
            ..
        } => true,
        Expr::Unary {
            op: UnaryOp::Not, ..
        } => true,
        Expr::Binary {
            op, left, right, ..
        } => match op {
            BinOp::Lt
            | BinOp::LtEq
            | BinOp::Gt
            | BinOp::GtEq
            | BinOp::EqEq
            | BinOp::NotEq
            | BinOp::EqEqEq
            | BinOp::NotEqEq => true,
            BinOp::And | BinOp::Or => boolean(left) && boolean(right),
            _ => false,
        },
        _ => false,
    }
}

/// Whether a statement always leaves the statements after it: it
/// returns, throws, breaks or continues on every path (as inty's
/// `always_exits` reads it).
fn exits(s: &Stmt) -> bool {
    match s {
        Stmt::Return { .. } | Stmt::Throw { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {
            true
        }
        Stmt::Block { body, .. } => body.iter().any(exits),
        Stmt::If {
            consequent,
            alternate: Some(alt),
            ..
        } => exits(consequent) && exits(alt),
        _ => false,
    }
}

/// Whether a loop's body has a `continue` of that loop.
fn continues(s: &Stmt) -> bool {
    match s {
        Stmt::Continue { .. } => true,
        Stmt::Block { body, .. } => body.iter().any(continues),
        Stmt::If {
            consequent,
            alternate,
            ..
        } => continues(consequent) || alternate.as_deref().is_some_and(continues),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            continues(block)
                || handler.as_ref().is_some_and(|h| continues(&h.body))
                || finalizer.as_deref().is_some_and(continues)
        }
        Stmt::Switch { cases, .. } => cases.iter().any(|c| c.consequent.iter().any(continues)),
        Stmt::Labeled { body, .. } => continues(body),
        _ => false,
    }
}

/// The names a statement declares in its block.
fn declared(s: &Stmt) -> Vec<String> {
    match s {
        Stmt::Var { declarations, .. } => declarations.iter().map(|d| d.name.clone()).collect(),
        Stmt::FunctionDecl { name, .. } => vec![name.clone()],
        _ => Vec::new(),
    }
}

/// Whether every path through `s` returns or throws: a function's body
/// ending in it doesn't fall off its end.
fn returns(s: &Stmt) -> bool {
    match s {
        Stmt::Return { .. } | Stmt::Throw { .. } => true,
        Stmt::Block { body, .. } => body
            .iter()
            .rfind(|s| !matches!(s, Stmt::Empty { .. }))
            .is_some_and(returns),
        Stmt::If {
            consequent,
            alternate: Some(a),
            ..
        } => returns(consequent) && returns(a),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            finalizer.as_deref().is_some_and(returns)
                || (returns(block) && handler.as_ref().is_none_or(|h| returns(&h.body)))
        }
        _ => false,
    }
}

fn stmt_name(s: &Stmt) -> String {
    match s {
        Stmt::DoWhile { .. } => "`do … while`",
        Stmt::For { .. } => "`for`",
        Stmt::ForIn { .. } => "`for … in`",
        Stmt::ForOf { .. } => "`for … of`",
        Stmt::Switch { .. } => "`switch`",
        Stmt::Labeled { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => "a label",
        Stmt::Import { .. } | Stmt::Export { .. } => "a module",
        _ => "a statement",
    }
    .to_string()
}

/// A test the model has a form for.
enum Pattern<'a> {
    /// `x != null` (`negated`, the value's branch first) or `x == null`.
    Nothing { name: &'a str, negated: bool },
    /// `typeof x === "t"`, or `!==` (`negated`).
    Typeof {
        name: &'a str,
        tag: &'a str,
        negated: bool,
    },
    /// `x.l === "t"`, or `!==` (`negated`).
    Tag {
        name: &'a str,
        label: &'a str,
        tag: &'a str,
        negated: bool,
    },
    /// `x` as a test, or `!x` (`negated`): truthy only if not nothing.
    Truthy { name: &'a str, negated: bool },
}

/// One branch of a test, lowered in the scope it sees.
type Branch<'a, S> = dyn Fn(&mut S) -> Lowered + 'a;

fn pattern(test: &Expr) -> Option<Pattern<'_>> {
    match test {
        Expr::Ident { name, .. } => {
            return Some(Pattern::Truthy {
                name,
                negated: false,
            })
        }
        Expr::Unary {
            op: UnaryOp::Not,
            argument,
            ..
        } => {
            if let Expr::Ident { name, .. } = &**argument {
                return Some(Pattern::Truthy {
                    name,
                    negated: true,
                });
            }
        }
        _ => {}
    }
    let Expr::Binary {
        op, left, right, ..
    } = test
    else {
        return None;
    };
    fn ident(e: &Expr) -> Option<&str> {
        match e {
            Expr::Ident { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }
    fn string(e: &Expr) -> Option<&str> {
        match e {
            Expr::Lit {
                value: Literal::String(s),
                ..
            } => Some(s.as_str()),
            _ => None,
        }
    }
    match op {
        BinOp::NotEq | BinOp::EqEq => {
            let negated = *op == BinOp::NotEq;
            let null = |e: &Expr| {
                matches!(
                    e,
                    Expr::Lit {
                        value: Literal::Null,
                        ..
                    }
                )
            };
            if null(right) {
                ident(left).map(|name| Pattern::Nothing { name, negated })
            } else {
                None
            }
        }
        BinOp::EqEqEq | BinOp::NotEqEq => {
            let negated = *op == BinOp::NotEqEq;
            let tag = string(right)?;
            match &**left {
                Expr::Unary {
                    op: UnaryOp::Typeof,
                    argument,
                    ..
                } => ident(argument).map(|name| Pattern::Typeof { name, tag, negated }),
                Expr::Member {
                    object, property, ..
                } => ident(object).map(|name| Pattern::Tag {
                    name,
                    label: property,
                    tag,
                    negated,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A label's or a string's text as one wire token: `%XX` for a character
/// of hex code `XX` a token can't hold (`unescape` in `Wire.lean`).
fn tok(l: &str) -> Lowered {
    if l.contains('\x01') {
        return unsupported("a label or string holding \\x01, inty's call signature's key");
    }
    Ok(l.chars()
        .map(|c| {
            if c.is_ascii_whitespace() || c.is_ascii_control() || "()%".contains(c) {
                format!("%{:02X}", c as u32)
            } else {
                c.to_string()
            }
        })
        .collect())
}

fn key_label(k: &PropKey) -> Result<String, Unsupported> {
    match k {
        PropKey::Ident(l) | PropKey::String(l) => tok(l),
        PropKey::Number(_) => unsupported("a numeric key"),
    }
}

fn literal(v: &Literal) -> Lowered {
    match v {
        Literal::Null => Ok("(null)".to_string()),
        Literal::Undefined => Ok("(undef)".to_string()),
        Literal::Boolean(b) => Ok(format!("(bool {b})")),
        Literal::Number(n) => number(*n),
        Literal::String(s) => Ok(format!("(str s:{})", tok(s)?)),
        Literal::Regex { .. } => unsupported("a regular expression"),
    }
}

/// A number literal as `(num M E)`, `M × 10^-E`: its shortest decimal.
fn number(n: f64) -> Lowered {
    if !n.is_finite() || n.is_sign_negative() {
        return unsupported("a number literal that isn't finite and non-negative");
    }
    let s = format!("{n}");
    let (int, frac) = s.split_once('.').unwrap_or((&s, ""));
    let digits = format!("{int}{frac}");
    let digits = digits.trim_start_matches('0');
    let digits = if digits.is_empty() { "0" } else { digits };
    Ok(format!("(num {digits} {})", frac.len()))
}

/// An annotation's type: monomorphic, or quantifying some variables.
enum Ann {
    Mono(String),
    Poly(usize, String),
}

fn annotation(content: &str) -> Result<Ann, Unsupported> {
    let (ty, vars) = crate::infer::type_parser::parse_type_annotation(content, Span::default(), 0)
        .map_err(|_| format!("an annotation inty's parser rejects: {content}"))?;
    // The quantified variables, in the order of their ids.
    let mut ids: Vec<u32> = vars.values().copied().collect();
    ids.sort();
    let index: HashMap<u32, usize> = ids.iter().enumerate().map(|(i, &id)| (id, i)).collect();
    let t = wire_ty(&ty, &index)?;
    Ok(if index.is_empty() {
        Ann::Mono(t)
    } else {
        Ann::Poly(index.len(), t)
    })
}

/// A type in the wire format.
fn wire_ty(t: &Type, vars: &HashMap<u32, usize>) -> Lowered {
    let go = |t: &Type| wire_ty(t, vars);
    match t {
        Type::Number => Ok("number".into()),
        Type::String => Ok("string".into()),
        Type::Boolean => Ok("boolean".into()),
        Type::Undefined => Ok("undefined".into()),
        Type::Null => Ok("null".into()),
        Type::Literal(LitValue::String(s)) => Ok(format!("(strlit s:{})", tok(s)?)),
        Type::Array(t) => Ok(format!("(arr {})", go(t)?)),
        Type::Maybe(Nothing::Null, t) => Ok(format!("(nullable {})", go(t)?)),
        Type::Maybe(Nothing::Undefined, t) => Ok(format!("(optional {})", go(t)?)),
        Type::Var(TVarName::Skolem(id) | TVarName::Flex(id)) => match vars.get(id) {
            Some(i) => Ok(format!("(tv {i})")),
            None => unsupported("a type variable that isn't quantified"),
        },
        Type::Union(members) => {
            if members.len() == 2 {
                for (a, b) in [(&members[0], &members[1]), (&members[1], &members[0])] {
                    match b {
                        Type::Null => return Ok(format!("(nullable {})", go(a)?)),
                        Type::Undefined => return Ok(format!("(optional {})", go(a)?)),
                        _ => {}
                    }
                }
            }
            if t.is_typeof_sum() {
                let mut out = String::from("(sum");
                for m in members {
                    out.push(' ');
                    out.push_str(&go(m)?);
                }
                out.push(')');
                return Ok(out);
            }
            variant(members, vars)
        }
        _ if t.as_callable().is_some() => {
            let Some((this, params, ret)) = t.as_callable() else {
                unreachable!()
            };
            if this.is_some_and(|t| *t != Type::Undefined) {
                return unsupported("a function type with a `this`");
            }
            if let Type::Row(row) = t {
                if row.props.len() != 1 || !matches!(row.tail, RowTail::Closed) {
                    return unsupported("a callable row with fields");
                }
            }
            let mut out = format!("(fn {}", go(ret)?);
            for p in params {
                if p.presence != Presence::Pre {
                    return unsupported("an optional parameter's type");
                }
                out.push(' ');
                out.push_str(&go(&p.ty)?);
            }
            out.push(')');
            Ok(out)
        }
        Type::Row(row) => {
            if !matches!(row.tail, RowTail::Closed) {
                return unsupported("an open record type");
            }
            let mut out = String::from("(rec");
            for (l, f) in &row.props {
                if f.presence != Presence::Pre {
                    return unsupported("an optional field");
                }
                out.push_str(&format!(" (s:{} {})", tok(&l.0)?, go(&f.ty)?));
            }
            out.push(')');
            Ok(out)
        }
        _ => unsupported(format!("the type {t}")),
    }
}

/// A union of records told apart by a field holding a different string
/// literal type in each: a variant tagged by that field.
fn variant(members: &[Type], vars: &HashMap<u32, usize>) -> Lowered {
    let rows: Vec<&crate::types::RowType> = members
        .iter()
        .map(|m| match m {
            Type::Row(r) if !m.is_func() => Some(r),
            _ => None,
        })
        .collect::<Option<_>>()
        .ok_or_else(|| "a union the model has no sum for".to_string())?;
    let tag_of = |r: &crate::types::RowType, l: &crate::types::PropName| match r.props.get(l) {
        Some(f) => match &f.ty {
            Type::Literal(LitValue::String(s)) => Some(s.clone()),
            _ => None,
        },
        None => None,
    };
    let label = rows[0]
        .props
        .keys()
        .find(|l| {
            let tags: Option<Vec<String>> = rows.iter().map(|r| tag_of(r, l)).collect();
            tags.is_some_and(|mut ts| {
                let n = ts.len();
                ts.sort();
                ts.dedup();
                ts.len() == n
            })
        })
        .ok_or_else(|| "a union of records with no tag field".to_string())?;
    let mut out = format!("(variant s:{}", tok(&label.0)?);
    for m in members {
        out.push(' ');
        out.push_str(&wire_ty(m, vars)?);
    }
    out.push(')');
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lower(src: &str) -> Lowered {
        lower_program(&crate::frontends::javascript::parse_source(src).unwrap())
    }

    #[test]
    fn lowers_the_differential_tests_forms() {
        assert_eq!(
            lower("const x = 1; x + 2;").unwrap(),
            "(let (num 1 0) (plus (var 0) (num 2 0)))"
        );
        assert_eq!(
            lower("function f(a, b) { return a; } f(1, 2);").unwrap(),
            "(let (func 2 (ret (var 0))) (app (var 0) (num 1 0) (num 2 0)))"
        );
        assert_eq!(
            lower("/** const v: Number | String */ const v = 1; typeof v === \"number\" ? v - 1 : 0;")
                .unwrap(),
            "(letann (sum number string) (num 1 0) (typetest (var 0) s:number (num 0 0) (minus (var 0) (num 1 0))))"
        );
        assert_eq!(
            lower("let x = 1.5; x = 2;").unwrap(),
            "(letmut (num 15 1) (assign 0 (num 2 0)))"
        );
        // A body that falls off its end returns `undefined`.
        assert_eq!(
            lower("(function () { 1; });").unwrap(),
            "(func 0 (seq (num 1 0) (undef)))"
        );
    }

    #[test]
    fn leaves_out_what_the_model_lacks() {
        assert!(lower("x => x++;").is_err());
        assert!(lower("Math.abs(1);").is_err());
        // Used before its declaration (hoisted).
        assert!(lower("const y = f(); function f() { return x; } const x = 1;").is_err());
        assert!(lower("function f() { return x; } f(); const x = 1;").is_err());
        // A function declaration moves up after what it reads.
        assert_eq!(
            lower("const x = 1; f(); function f() { return x; }").unwrap(),
            "(let (num 1 0) (let (func 0 (ret (var 2))) (app (var 0))))"
        );
        assert!(lower("(() => this);").is_err());
        // A tested `let` assigned elsewhere: the branch sees a copy.
        assert!(lower(
            "/** let x: Number | Null */ let x = 1; let f = function () { return 0; }; \
             if (x != null) { f = function () { return x - 1; }; } x = null; f();"
        )
        .is_err());
        // A getter beside a spread.
        assert!(
            lower("const o = {x: 1}; const p = {...o, get g() { return this.x; }}; p.g;").is_err()
        );
        // A test of `typeof` or of a tag on what isn't a declared sum is a
        // plain one.
        assert_eq!(
            lower("const n = 1; typeof n === \"number\" ? n - 1 : 0;").unwrap(),
            "(let (num 1 0) (cond (eq (typeof (var 0)) (str s:number)) (minus (var 0) (num 1 0)) (num 0 0)))"
        );
        assert_eq!(
            lower("const a = 1; const b = 2; a < b && b < a;").unwrap(),
            "(let (num 1 0) (let (num 2 0) (let (lt (var 1) (var 0)) (cond (var 0) (lt (var 1) (var 2)) (var 0)))))"
        );
        // `a && b` of anything: `const t = a; t ? b : t`.
        assert_eq!(
            lower("const a = 1; const b = 2; a && b;").unwrap(),
            "(let (num 1 0) (let (num 2 0) (let (var 1) (cond (var 0) (var 1) (var 0)))))"
        );
        // `??`, and a test of a sum's truthiness.
        assert_eq!(
            lower("/** const x: Number | Null */ const x = 1; x ?? 0;").unwrap(),
            "(letann (nullable number) (num 1 0) (unwrap (var 0) (num 0 0) (var 0)))"
        );
        assert_eq!(
            lower("/** const x: Number | Null */ const x = 1; x ? x - 1 : 0;").unwrap(),
            "(letann (nullable number) (num 1 0) (unwrap (var 0) (num 0 0) \
             (cond (var 0) (minus (var 0) (num 1 0)) (num 0 0))))"
        );
        // An early exit: what follows is the branch the test doesn't take.
        assert_eq!(
            lower(
                "/** const x: Number | Null */ const x = 1; \
                 function f() { if (x == null) { return 0; } return x - 1; } f();"
            )
            .unwrap(),
            "(letann (nullable number) (num 1 0) (let (func 0 (unwrap (var 2) (ret (num 0 0)) \
             (ret (minus (var 0) (num 1 0))))) (app (var 0))))"
        );
        assert!(lower("\"a\" < \"b\";").is_err());
    }

    #[test]
    fn lowers_for_loops_and_updates() {
        assert_eq!(lower("7 % 2;").unwrap(), "(mod (num 7 0) (num 2 0))");
        // `for (init; test; update) body` is `{ init; while (test) { body;
        // update } }`; `i++` whose value is dropped is `i = i - -1`.
        assert_eq!(
            lower("let s = 0; for (let i = 0; i < 3; i++) { s += i; }").unwrap(),
            "(letmut (num 0 0) (seq (letmut (num 0 0) (while (lt (var 0) (num 3 0)) \
             (seq (assign 1 (plus (var 1) (var 0))) (assign 0 (minus (var 0) (neg (num 1 0))))))) \
             (undef)))"
        );
        assert_eq!(
            lower("let i = 0; for (i = 1; ; i--) { break; }").unwrap(),
            "(letmut (num 0 0) (seq (seq (assign 0 (num 1 0)) (while (bool true) \
             (seq (break) (assign 0 (minus (var 0) (num 1 0)))))) (undef)))"
        );
        // A `continue` would skip the update.
        assert!(lower("for (let i = 0; i < 3; i++) { continue; }").is_err());
        // A `continue` of a nested loop doesn't.
        assert!(lower("for (let i = 0; i < 3; i++) { while (false) { continue; } }").is_ok());
        // A closure would see one binding where JavaScript makes one each
        // iteration.
        assert!(lower("for (let i = 0; i < 3; i++) { const f = () => i; }").is_err());
        assert!(lower("for (var i = 0; i < 3; i++) {}").is_err());
        // The value of `i++` is the old `i`'s.
        assert!(lower("let i = 0; i++;").is_err());
        assert!(lower("let i = 0; const j = i++;").is_err());
    }

    #[test]
    fn lowers_mutual_recursion_as_a_group() {
        // `G = function () { return {f: …, g: …}; }`, `g` in `f` is
        // `G().g`, and each name a function calling through `G`.
        assert_eq!(
            lower("function f(n) { return g(n); } function g(n) { return f(n); } f(1);").unwrap(),
            "(let (func 0 (ret (obj (field s:f (func 1 (ret (app (get (app (var 3)) s:g) (var 0))))) \
             (field s:g (func 1 (ret (app (get (app (var 3)) s:f) (var 0)))))))) \
             (let (func 1 (ret (app (get (app (var 3)) s:f) (var 0)))) \
             (let (func 1 (ret (app (get (app (var 4)) s:g) (var 0)))) (app (var 1) (num 1 0)))))"
        );
        // A group moves up as one, after what it reads.
        assert!(lower(
            "const a = f(1); function f(n) { return n > 0 ? g(n - 1) : k; } \
             function g(n) { return f(n); } const k = 0;"
        )
        .is_err());
        assert!(lower(
            "const k = 0; const a = f(1); function f(n) { return n > 0 ? g(n - 1) : k; } \
             function g(n) { return f(n); }"
        )
        .is_ok());
        // Through `G().f`, `this` would be the group's object.
        assert!(
            lower("function f() { g; return this; } function g() { return f(); } g();").is_err()
        );
        assert!(lower("function f() { return g(); } function g() { return f(); } f = 1;").is_err());
        // A `const` function calling itself: the function's own name.
        assert_eq!(
            lower("const f = (n) => n > 0 ? f(n - 1) : 0; f(3);").unwrap(),
            "(let (func 1 (ret (cond (gt (var 0) (num 0 0)) (app (var 1) (minus (var 0) (num 1 0))) \
             (num 0 0)))) (app (var 0) (num 3 0)))"
        );
        assert!(lower("let f = (n) => n > 0 ? f(n - 1) : 0; f(3);").is_err());
    }

    #[test]
    fn lowers_native_methods_by_their_arguments() {
        // `s.slice(1)` is the native `slice/1` (no optional parameters).
        assert_eq!(
            lower("\"abc\".slice(1).toUpperCase();").unwrap(),
            "(mcall (mcall (str s:abc) s:slice/1 (num 1 0)) s:toUpperCase/0)"
        );
        assert_eq!(
            lower("[1, 2].indexOf(2);").unwrap(),
            "(mcall (arr (num 1 0) (num 2 0)) s:indexOf/1 (num 2 0))"
        );
        assert!(lower("\"abc\".indexOf(\"b\", 1);").is_err());
        assert!(lower("\"abc\".map(1);").is_err());
        // A program whose objects have such a method too.
        assert!(lower("const o = {slice: function (a) { return a; }}; o.slice(1);").is_err());
    }

    #[test]
    fn lowers_a_module() {
        // Its exports' declarations; the program's value is its last
        // statement's.
        assert_eq!(
            lower("export function f(x) { return x; } export default 1; f(2);").unwrap(),
            "(let (func 1 (ret (var 0))) (let (num 1 0) (app (var 1) (num 2 0))))"
        );
        assert!(lower("export { ghost };").is_err());
        assert!(lower("import { f } from \"./f.js\"; f(1);").is_err());
    }
}
