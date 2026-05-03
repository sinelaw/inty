//! AST construction + analysis helpers used across the metamorphic
//! tests. Nothing here touches proptest or the type checker — it's all
//! pure AST manipulation.

use std::collections::HashSet;

use minfern::lexer::Span;
use minfern::parser::ast::*;

// -------------------------------------------------------------------------
// Small constructors — cut down on boilerplate when building expected ASTs
// or synthesising statements inside transformations.
// -------------------------------------------------------------------------

pub fn span() -> Span {
    Span::new(0, 0)
}

pub fn empty_stmt() -> Stmt {
    Stmt::Empty { span: span() }
}

pub fn var_stmt(kind: VarKind, name: &str, init: Option<Expr>) -> Stmt {
    Stmt::Var {
        kind,
        declarations: vec![VarDeclarator {
            name: name.to_string(),
            init,
            type_annotation: None,
            kind,
            span: span(),
        }],
        span: span(),
    }
}

#[allow(dead_code)]
pub fn ident_expr(name: &str) -> Expr {
    Expr::Ident {
        name: name.to_string(),
        span: span(),
    }
}

pub fn num_lit(n: f64) -> Expr {
    Expr::Lit {
        value: Literal::Number(n),
        span: span(),
    }
}

// -------------------------------------------------------------------------
// Name collection.
//
// `names_in` returns every identifier that appears as either a binder or
// a reference anywhere in the program. We use it for two separate jobs:
//   1. Freshness: picking a name that doesn't collide with anything in p.
//   2. Independence checks for the swap transformation.
//
// Property keys inside object literals are deliberately *not* collected —
// `obj.x` uses the string "x" as a label, not as a variable reference,
// so renaming a variable `x` must not touch it.
// -------------------------------------------------------------------------

pub fn names_in(program: &Program) -> HashSet<String> {
    let mut names = HashSet::new();
    for stmt in &program.statements {
        names_in_stmt(stmt, &mut names);
    }
    names
}

pub fn names_in_stmt(stmt: &Stmt, out: &mut HashSet<String>) {
    match stmt {
        Stmt::Block { body, .. } => {
            for s in body {
                names_in_stmt(s, out);
            }
        }
        Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
        Stmt::Expr { expression, .. } => names_in_expr(expression, out),
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                out.insert(d.name.clone());
                if let Some(e) = &d.init {
                    names_in_expr(e, out);
                }
            }
        }
        Stmt::FunctionDecl {
            name, params, body, ..
        } => {
            out.insert(name.clone());
            for p in params {
                out.insert(p.clone());
            }
            names_in_stmt(body, out);
        }
        Stmt::Return { argument, .. } => {
            if let Some(e) = argument {
                names_in_expr(e, out);
            }
        }
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            names_in_expr(test, out);
            names_in_stmt(consequent, out);
            if let Some(a) = alternate {
                names_in_stmt(a, out);
            }
        }
        Stmt::While { test, body, .. } | Stmt::DoWhile { body, test, .. } => {
            names_in_expr(test, out);
            names_in_stmt(body, out);
        }
        Stmt::Throw { argument, .. } => names_in_expr(argument, out),
        _ => {}
    }
}

pub fn names_in_expr(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
        Expr::Ident { name, .. } => {
            out.insert(name.clone());
        }
        Expr::Array { elements, .. } => {
            for e in elements.iter().flatten() {
                names_in_expr(e, out);
            }
        }
        Expr::Object { properties, .. } => {
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => names_in_expr(value, out),
                    PropDef::Method { params, body, .. } => {
                        for param in params {
                            out.insert(param.clone());
                        }
                        names_in_stmt(body, out);
                    }
                    PropDef::Getter { body, .. } => names_in_stmt(body, out),
                    PropDef::Setter { param, body, .. } => {
                        out.insert(param.clone());
                        names_in_stmt(body, out);
                    }
                }
            }
        }
        Expr::Function {
            name, params, body, ..
        } => {
            if let Some(n) = name {
                out.insert(n.clone());
            }
            for p in params {
                out.insert(p.clone());
            }
            names_in_stmt(body, out);
        }
        Expr::Member { object, .. } => names_in_expr(object, out),
        Expr::ComputedMember {
            object, property, ..
        } => {
            names_in_expr(object, out);
            names_in_expr(property, out);
        }
        Expr::Call {
            callee, arguments, ..
        }
        | Expr::New {
            callee, arguments, ..
        } => {
            names_in_expr(callee, out);
            for a in arguments {
                names_in_expr(a, out);
            }
        }
        Expr::Unary { argument, .. } => names_in_expr(argument, out),
        Expr::Binary { left, right, .. } | Expr::Assign { left, right, .. } => {
            names_in_expr(left, out);
            names_in_expr(right, out);
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            names_in_expr(test, out);
            names_in_expr(consequent, out);
            names_in_expr(alternate, out);
        }
        Expr::Sequence { expressions, .. } => {
            for e in expressions {
                names_in_expr(e, out);
            }
        }
        Expr::TemplateLiteral { expressions, .. } => {
            for e in expressions {
                names_in_expr(e, out);
            }
        }
    }
}

// -------------------------------------------------------------------------
// Bindings vs references — used by the swap-independence check.
//
// `bound_names_in_stmt` returns *only* the names a statement introduces
// into its enclosing scope. `referenced_names_in_stmt` returns the
// identifiers the statement reads, approximated by "all identifiers
// minus the ones it binds at top level". Inner scopes get over-counted,
// which means the swap check is conservative (may refuse safe swaps),
// never unsound (won't accept unsafe ones).
// -------------------------------------------------------------------------

pub fn bound_names_in_stmt(stmt: &Stmt) -> HashSet<String> {
    let mut out = HashSet::new();
    match stmt {
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                out.insert(d.name.clone());
            }
        }
        Stmt::FunctionDecl { name, .. } => {
            out.insert(name.clone());
        }
        _ => {}
    }
    out
}

pub fn referenced_names_in_stmt(stmt: &Stmt) -> HashSet<String> {
    let mut all = HashSet::new();
    names_in_stmt(stmt, &mut all);
    let bound = bound_names_in_stmt(stmt);
    all.difference(&bound).cloned().collect()
}

// -------------------------------------------------------------------------
// Fresh-name picker. Used to avoid accidental collisions when injecting
// test-only bindings. The prefix keeps the generated name visually
// distinct from user code so a failure dump is easy to read.
// -------------------------------------------------------------------------

pub fn fresh_name(prefix: &str, taken: &HashSet<String>) -> String {
    let mut i = 0;
    loop {
        let candidate = format!("{}{}", prefix, i);
        if !taken.contains(&candidate) {
            return candidate;
        }
        i += 1;
    }
}

// -------------------------------------------------------------------------
// Capture-avoiding rename: `rename_all(p, from, to)` replaces every
// identifier occurrence equal to `from` with `to`.
//
// Safety note: this is only alpha-equivalent if `to` does not appear
// anywhere in `p` (as a binder or a reference). Callers must pass a
// globally fresh target name — `fresh_name("...", &names_in(p))`
// is the intended usage.
//
// Object property *labels* and template-literal quasis are left alone:
// they're strings, not identifier binders/references.
// -------------------------------------------------------------------------

pub fn rename_all(program: &Program, from: &str, to: &str) -> Program {
    let stmts = program
        .statements
        .iter()
        .map(|s| rename_stmt(s, from, to))
        .collect();
    Program {
        statements: stmts,
        span: program.span,
    }
}

fn rename_stmt(stmt: &Stmt, from: &str, to: &str) -> Stmt {
    match stmt {
        Stmt::Block { body, span } => Stmt::Block {
            body: body.iter().map(|s| rename_stmt(s, from, to)).collect(),
            span: *span,
        },
        Stmt::Var {
            kind,
            declarations,
            span,
        } => Stmt::Var {
            kind: *kind,
            declarations: declarations
                .iter()
                .map(|d| VarDeclarator {
                    name: if d.name == from { to.to_string() } else { d.name.clone() },
                    init: d.init.as_ref().map(|e| rename_expr(e, from, to)),
                    type_annotation: d.type_annotation.clone(),
                    kind: d.kind,
                    span: d.span,
                })
                .collect(),
            span: *span,
        },
        Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            span,
        } => Stmt::FunctionDecl {
            name: if name == from { to.to_string() } else { name.clone() },
            params: params
                .iter()
                .map(|p| if p == from { to.to_string() } else { p.clone() })
                .collect(),
            body: Box::new(rename_stmt(body, from, to)),
            type_annotation: type_annotation.clone(),
            span: *span,
        },
        Stmt::Expr { expression, span } => Stmt::Expr {
            expression: rename_expr(expression, from, to),
            span: *span,
        },
        Stmt::Return { argument, span } => Stmt::Return {
            argument: argument.as_ref().map(|e| rename_expr(e, from, to)),
            span: *span,
        },
        Stmt::If {
            test,
            consequent,
            alternate,
            span,
        } => Stmt::If {
            test: rename_expr(test, from, to),
            consequent: Box::new(rename_stmt(consequent, from, to)),
            alternate: alternate
                .as_ref()
                .map(|s| Box::new(rename_stmt(s, from, to))),
            span: *span,
        },
        Stmt::While { test, body, span } => Stmt::While {
            test: rename_expr(test, from, to),
            body: Box::new(rename_stmt(body, from, to)),
            span: *span,
        },
        Stmt::DoWhile { body, test, span } => Stmt::DoWhile {
            body: Box::new(rename_stmt(body, from, to)),
            test: rename_expr(test, from, to),
            span: *span,
        },
        Stmt::Throw { argument, span } => Stmt::Throw {
            argument: rename_expr(argument, from, to),
            span: *span,
        },
        // Other statement kinds aren't produced by our strategies, so a
        // structural clone is fine.
        other => other.clone(),
    }
}

fn rename_expr(expr: &Expr, from: &str, to: &str) -> Expr {
    match expr {
        Expr::Ident { name, span } => Expr::Ident {
            name: if name == from { to.to_string() } else { name.clone() },
            span: *span,
        },
        Expr::Array { elements, span } => Expr::Array {
            elements: elements
                .iter()
                .map(|e| e.as_ref().map(|x| rename_expr(x, from, to)))
                .collect(),
            span: *span,
        },
        Expr::Object { properties, span } => Expr::Object {
            properties: properties.iter().map(|p| rename_prop(p, from, to)).collect(),
            span: *span,
        },
        Expr::Function {
            name,
            params,
            body,
            type_annotation,
            span,
        } => Expr::Function {
            name: name
                .as_ref()
                .map(|n| if n == from { to.to_string() } else { n.clone() }),
            params: params
                .iter()
                .map(|p| if p == from { to.to_string() } else { p.clone() })
                .collect(),
            body: Box::new(rename_stmt(body, from, to)),
            type_annotation: type_annotation.clone(),
            span: *span,
        },
        Expr::Member {
            object,
            property,
            span,
        } => Expr::Member {
            object: Box::new(rename_expr(object, from, to)),
            // Member property names are labels, not variable references.
            property: property.clone(),
            span: *span,
        },
        Expr::ComputedMember {
            object,
            property,
            span,
        } => Expr::ComputedMember {
            object: Box::new(rename_expr(object, from, to)),
            property: Box::new(rename_expr(property, from, to)),
            span: *span,
        },
        Expr::Call {
            callee,
            arguments,
            span,
        } => Expr::Call {
            callee: Box::new(rename_expr(callee, from, to)),
            arguments: arguments.iter().map(|a| rename_expr(a, from, to)).collect(),
            span: *span,
        },
        Expr::New {
            callee,
            arguments,
            span,
        } => Expr::New {
            callee: Box::new(rename_expr(callee, from, to)),
            arguments: arguments.iter().map(|a| rename_expr(a, from, to)).collect(),
            span: *span,
        },
        Expr::Unary { op, argument, span } => Expr::Unary {
            op: *op,
            argument: Box::new(rename_expr(argument, from, to)),
            span: *span,
        },
        Expr::Binary {
            op,
            left,
            right,
            span,
        } => Expr::Binary {
            op: *op,
            left: Box::new(rename_expr(left, from, to)),
            right: Box::new(rename_expr(right, from, to)),
            span: *span,
        },
        Expr::Assign {
            op,
            left,
            right,
            span,
        } => Expr::Assign {
            op: *op,
            left: Box::new(rename_expr(left, from, to)),
            right: Box::new(rename_expr(right, from, to)),
            span: *span,
        },
        Expr::Conditional {
            test,
            consequent,
            alternate,
            span,
        } => Expr::Conditional {
            test: Box::new(rename_expr(test, from, to)),
            consequent: Box::new(rename_expr(consequent, from, to)),
            alternate: Box::new(rename_expr(alternate, from, to)),
            span: *span,
        },
        Expr::Sequence { expressions, span } => Expr::Sequence {
            expressions: expressions.iter().map(|e| rename_expr(e, from, to)).collect(),
            span: *span,
        },
        Expr::TemplateLiteral {
            quasis,
            expressions,
            span,
        } => Expr::TemplateLiteral {
            quasis: quasis.clone(),
            expressions: expressions.iter().map(|e| rename_expr(e, from, to)).collect(),
            span: *span,
        },
        other => other.clone(),
    }
}

fn rename_prop(prop: &PropDef, from: &str, to: &str) -> PropDef {
    match prop {
        // Property keys are labels, not variable references. Leave the
        // key alone; only rename inside the value.
        PropDef::Property {
            key,
            value,
            type_annotation,
            span,
        } => PropDef::Property {
            key: key.clone(),
            value: rename_expr(value, from, to),
            type_annotation: type_annotation.clone(),
            span: *span,
        },
        PropDef::Method {
            key,
            params,
            body,
            span,
        } => PropDef::Method {
            key: key.clone(),
            params: params
                .iter()
                .map(|p| if p == from { to.to_string() } else { p.clone() })
                .collect(),
            body: Box::new(rename_stmt(body, from, to)),
            span: *span,
        },
        PropDef::Getter { key, body, span } => PropDef::Getter {
            key: key.clone(),
            body: Box::new(rename_stmt(body, from, to)),
            span: *span,
        },
        PropDef::Setter {
            key,
            param,
            body,
            span,
        } => PropDef::Setter {
            key: key.clone(),
            param: if param == from { to.to_string() } else { param.clone() },
            body: Box::new(rename_stmt(body, from, to)),
            span: *span,
        },
    }
}
