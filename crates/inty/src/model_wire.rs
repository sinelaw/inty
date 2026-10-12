//! inty's programs in the Lean model's wire format (`lean/Inty/Wire.lean`),
//! so the model runs on inty's own programs (ground rule 4 of
//! `lean/ROADMAP.md`), not only on the differential test's generated ones.
//!
//! [`lower_program`] writes a parsed JavaScript program as one wire line,
//! or says why it can't: the program uses something the model doesn't
//! have (an operator other than `+` and `-`, a `for` loop, a class, a
//! builtin, …), or something whose lowering would change its meaning (a
//! name used before its declaration). The lowering is the inverse of the
//! differential test's printer (`tests/differential.rs`): a statement list
//! is a sequence whose value is its last statement's, a declaration binds
//! the rest of its block, a function's body ends in what it returns, and a
//! test of a binding for nothing, of its `typeof` or of its tag field takes
//! the binding apart (`unwrap`, `typetest`, `casetag`), shadowing it in
//! each branch with the binding the model's form makes.

use crate::ast::{
    BinOp, ChainSegment, Expr, Literal, Param, Program, PropDef, PropKey, Stmt, UnaryOp, VarKind,
};
use crate::span::Span;
use crate::types::{LitValue, Nothing, Presence, RowTail, TVarName, Type};
use std::collections::HashMap;

/// Why a program isn't in the model's fragment.
pub type Unsupported = String;

type Lowered = Result<String, Unsupported>;

fn unsupported<T>(what: impl Into<String>) -> Result<T, Unsupported> {
    Err(what.into())
}

/// The program in the wire format, or what keeps it out of the model.
pub fn lower_program(program: &Program) -> Lowered {
    if !program.type_aliases.is_empty() {
        return unsupported("a type alias");
    }
    // The parser lowers a class to a factory function.
    if !program.class_brands.is_empty() {
        return unsupported("a class");
    }
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
    };
    let wire = cx.block(&program.statements, Tail::Program)?;
    // A property only a builtin has (`xs.map`, `s.slice`): the model's
    // strings and arrays have only `length`.
    if let Some(l) = cx.read.iter().find(|l| !cx.defined.contains(l)) {
        return unsupported(format!(
            "the property `{l}`, which no object of the program has"
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
}

/// A declared sum a test takes apart.
#[derive(Clone, Copy, PartialEq)]
enum Sum {
    /// A variant tagged by a field: `x.l === "t"`.
    Variant,
    /// A sum told apart by `typeof`.
    Typeof,
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
}

/// What the end of a statement list is.
#[derive(Clone, Copy, PartialEq)]
enum Tail {
    /// The program's: its value is the last statement's.
    Program,
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
        });
    }

    /// The binder `name` resolves to, and its de Bruijn index.
    fn binder(&self, name: &str) -> Result<(usize, Binder), Unsupported> {
        let (i, _) = self.lookup(name)?;
        let b = self
            .scope
            .iter()
            .rev()
            .find(|b| b.name.as_deref() == Some(name))
            .expect("looked up");
        Ok((i, b.clone()))
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

    /// `name`'s de Bruijn index and kind.
    fn lookup(&self, name: &str) -> Result<(usize, Kind), Unsupported> {
        let mut i = 0;
        for b in self.scope.iter().rev() {
            if b.name.as_deref() == Some(name) {
                return match b.kind {
                    Kind::Later => unsupported(format!("`{name}` used before its declaration")),
                    k => Ok((i, k)),
                };
            }
            if b.kind != Kind::Later {
                i += 1;
            }
        }
        unsupported(format!("`{name}` isn't bound in the program (a builtin)"))
    }

    fn this(&self) -> Lowered {
        let mut i = 0;
        for b in self.scope.iter().rev() {
            match b.kind {
                Kind::This => return Ok(format!("(var {i})")),
                Kind::Later => continue,
                _ => i += 1,
            }
        }
        unsupported("`this` outside a function")
    }

    /// A statement list: each declaration binds the rest of the list.
    fn block(&mut self, stmts: &[Stmt], tail: Tail) -> Lowered {
        let stmts = hoist(
            stmts
                .iter()
                .filter(|s| !matches!(s, Stmt::Empty { .. }))
                .collect(),
        );
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
            return Ok("(undef)".to_string());
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
                let rest = self.rest(rest, tail, falls_off);
                self.pop(1);
                Ok(format!("(let {f} {})", rest?))
            }
            // A program ending in a statement other than an expression
            // has no value inty types (it types it `undefined`).
            s if last && tail == Tail::Program && !matches!(s, Stmt::Expr { .. }) => {
                let s = self.stmt(first, Tail::Stmt)?;
                Ok(format!("(seq {s} (undef))"))
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

    /// The rest of a list after a declaration: `undefined` if nothing.
    fn rest(&mut self, rest: &[&Stmt], tail: Tail, falls_off: bool) -> Lowered {
        if rest.is_empty() {
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
        yes: impl FnOnce(&mut Self) -> Lowered,
        no: impl FnOnce(&mut Self) -> Lowered,
    ) -> Lowered {
        match pattern(test) {
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
                    return unsupported("a test of `typeof` on what isn't a declared sum");
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
                    return unsupported("a test of a tag on what isn't a declared variant");
                }
                self.tested(&b);
                let (label, tag) = (tok(label)?, tok(tag)?);
                let (case, rest) = self.split(&b, yes, no, negated)?;
                Ok(format!(
                    "(casetag (var {i}) s:{label} s:{tag} {rest} {case})"
                ))
            }
            None => {
                let c = self.expr(test)?;
                let t = yes(self)?;
                let e = no(self)?;
                Ok(format!("(cond {c} {t} {e})"))
            }
        }
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
                op => unsupported(format!("the operator {op:?}")),
            },
            Expr::Assign {
                op, left, right, ..
            } => {
                if *op != crate::ast::AssignOp::Assign {
                    return unsupported(format!("the assignment {op:?}"));
                }
                match &**left {
                    Expr::Ident { name, .. } => {
                        let (i, b) = self.binder(name)?;
                        let k = b.kind;
                        self.assigned.push(b.id);
                        if k == Kind::Shadow {
                            return unsupported("an assignment to a binding a test took apart");
                        }
                        if k == Kind::FnName {
                            return unsupported("an assignment to a function declaration's name");
                        }
                        Ok(format!("(assign {i} {})", self.expr(right)?))
                    }
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
                }
            }
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
            Expr::NullishCoalesce { .. } => unsupported("`??`"),
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
/// other, or one refusing every order, leave the block as it is (and the
/// program is left out by `Later`).
fn hoist(stmts: Vec<&Stmt>) -> Vec<&Stmt> {
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
    let mut out = Vec::with_capacity(n);
    let mut placed = vec![false; n];
    while out.len() < n {
        // The first statement whose predecessors are all placed.
        let Some(j) = (0..n).find(|&j| !placed[j] && after[j].iter().all(|&i| placed[i])) else {
            return stmts;
        };
        placed[j] = true;
        out.push(stmts[j]);
    }
    out
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
}

fn pattern(test: &Expr) -> Option<Pattern<'_>> {
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
        assert!(lower("1 * 2;").is_err());
        assert!(lower("for (;;) {}").is_err());
        assert!(lower("Math.abs(1);").is_err());
        // Used before its declaration (hoisted).
        assert!(lower("function f() { return g(); } function g() { return f(); }").is_err());
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
        // A test of `typeof` or of a tag on what isn't a declared sum.
        assert!(lower("const n = 1; typeof n === \"number\" ? n - 1 : 0;").is_err());
        assert!(lower("const o = {name: \"bob\"}; o.name === \"bob\" ? 1 : 2;").is_err());
    }
}
