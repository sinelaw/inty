//! `this` in a class's field initialisers and constructor.
//!
//! A class lowers to a factory returning an object literal, so its fields
//! are set before the instance exists. JavaScript sets them one by one on
//! the instance, and an initialiser can see the instance through `this`:
//! a field set later still reads `undefined`, and a method called there
//! may read such a field. So inty takes `this` in an initialiser (or in
//! the value of a constructor's `this.f = …`) only as `this.f`, a read of
//! a field set before it, and reads the value that field was set to,
//! which the lowering keeps in a local. An initialiser that is a whole
//! arrow function (`f = () => this.n`) runs later, on the finished
//! instance, so it is lowered to a method whose `this` is the instance.

use std::collections::HashMap;

use crate::ast::*;
use crate::error::{ParseError, Result};
use crate::span::Span;

/// A field already set while a class's fields are set.
pub(super) enum SetField {
    /// Set to a value, kept in this local.
    Value(String),
    /// Set to an arrow function (a method of the instance). Reading it
    /// would be calling it with the instance as `this` or passing it on
    /// before the instance is complete, so it isn't read.
    Arrow,
}

fn unsupported(class: &str, what: &str, span: Span) -> crate::error::IntyError {
    ParseError::Unsupported {
        feature: format!(
            "{} in a field initialiser or constructor of class `{}` (there `this` may \
             only read a field set before, as `this.field`; JavaScript would run it on \
             an instance whose later fields aren't set yet)",
            what, class
        ),
        span,
    }
    .into()
}

fn is_this(e: &Expr) -> bool {
    matches!(e, Expr::This { .. })
}

/// Whether `e` stores to or deletes a property of `this` (`this.f = …`,
/// `this.f++`, `delete this[k]`).
fn is_this_place(e: &Expr) -> bool {
    match e {
        Expr::Member { object, .. } | Expr::ComputedMember { object, .. } => is_this(object),
        _ => false,
    }
}

/// Rewrite every `this.f` in `expr` to the local holding `f`'s value,
/// rejecting any other use of `this`.
pub(super) fn rewrite(
    expr: &mut Expr,
    fields: &HashMap<String, SetField>,
    class: &str,
) -> Result<()> {
    let span = expr.span();
    match expr {
        Expr::This { span } => Err(unsupported(class, "`this` other than `this.field`", *span)),
        Expr::Member {
            object, property, ..
        } if is_this(object) => match fields.get(property.as_str()) {
            Some(SetField::Value(local)) => {
                *expr = Expr::Ident {
                    name: local.clone(),
                    span,
                };
                Ok(())
            }
            Some(SetField::Arrow) => Err(unsupported(
                class,
                &format!("reading the arrow-function field `this.{}`", property),
                span,
            )),
            None => Err(unsupported(
                class,
                &format!(
                    "reading `this.{}`, which isn't a field set before (a later field, a \
                     method or a getter)",
                    property
                ),
                span,
            )),
        },
        Expr::Lit { .. } | Expr::Ident { .. } | Expr::NewTarget { .. } => Ok(()),
        Expr::Array { elements, .. } => {
            for e in elements.iter_mut().flatten() {
                rewrite(e, fields, class)?;
            }
            Ok(())
        }
        Expr::Tuple { elements, .. }
        | Expr::Sequence {
            expressions: elements,
            ..
        }
        | Expr::TemplateLiteral {
            expressions: elements,
            ..
        } => {
            for e in elements {
                rewrite(e, fields, class)?;
            }
            Ok(())
        }
        Expr::Object { properties, .. } => {
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => rewrite(value, fields, class)?,
                    PropDef::Spread { argument, .. } => rewrite(argument, fields, class)?,
                    // An object literal's method or accessor has the
                    // literal as its `this`.
                    PropDef::Method { .. } | PropDef::Getter { .. } | PropDef::Setter { .. } => {}
                }
            }
            Ok(())
        }
        Expr::Function { .. } => {
            // An arrow function's `this` is the instance, and it may run
            // after the instance is complete: inty doesn't tell arrows
            // from `function`s here, so neither may mention `this`.
            if crate::ast::free_idents::mentions_this(expr) {
                Err(unsupported(class, "`this` inside a function", span))
            } else {
                Ok(())
            }
        }
        Expr::Member { object, .. } => rewrite(object, fields, class),
        Expr::ComputedMember {
            object, property, ..
        } => {
            if is_this(object) {
                return Err(unsupported(class, "`this[…]`", span));
            }
            rewrite(object, fields, class)?;
            rewrite(property, fields, class)
        }
        Expr::Call {
            callee,
            arguments,
            keywords,
            ..
        } => {
            if is_this_place(callee) {
                return Err(unsupported(class, "calling a method of `this`", span));
            }
            rewrite(callee, fields, class)?;
            for a in arguments {
                rewrite(a, fields, class)?;
            }
            for (_, a) in keywords {
                rewrite(a, fields, class)?;
            }
            Ok(())
        }
        Expr::New {
            callee, arguments, ..
        } => {
            rewrite(callee, fields, class)?;
            for a in arguments {
                rewrite(a, fields, class)?;
            }
            Ok(())
        }
        Expr::Unary { op, argument, .. } => {
            let writes = matches!(
                op,
                UnaryOp::PreInc
                    | UnaryOp::PreDec
                    | UnaryOp::PostInc
                    | UnaryOp::PostDec
                    | UnaryOp::Delete
            );
            if writes && is_this_place(argument) {
                return Err(unsupported(class, "changing a field of `this`", span));
            }
            rewrite(argument, fields, class)
        }
        Expr::Assign { left, right, .. } => {
            if is_this_place(left) {
                return Err(unsupported(
                    class,
                    "storing to a field of `this` inside an expression",
                    span,
                ));
            }
            rewrite(left, fields, class)?;
            rewrite(right, fields, class)
        }
        Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
            rewrite(left, fields, class)?;
            rewrite(right, fields, class)
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            rewrite(test, fields, class)?;
            rewrite(consequent, fields, class)?;
            rewrite(alternate, fields, class)
        }
        Expr::OptionalChain { head, segments, .. } => {
            if is_this_place(head) && matches!(segments.first(), Some(ChainSegment::Call { .. })) {
                return Err(unsupported(class, "calling a method of `this`", span));
            }
            rewrite(head, fields, class)?;
            for seg in segments {
                match seg {
                    ChainSegment::Member { .. } => {}
                    ChainSegment::Computed { property, .. } => rewrite(property, fields, class)?,
                    ChainSegment::Call { arguments, .. } => {
                        for a in arguments {
                            rewrite(a, fields, class)?;
                        }
                    }
                }
            }
            Ok(())
        }
        Expr::Spread { argument, .. } => rewrite(argument, fields, class),
        Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => {
            rewrite(source, fields, class)
        }
    }
}

/// Rewrite every `this.f` in a constructor statement, as [`rewrite`] does
/// for an expression. The statement runs between the fields set before it
/// and those set after: it may read the first (as `this.f`) but not set a
/// field itself (only a `this.f = …` line of its own does), and it may
/// not `return`, which would leave the instance unbuilt.
pub(super) fn rewrite_stmt(
    stmt: &mut Stmt,
    fields: &HashMap<String, SetField>,
    class: &str,
) -> Result<()> {
    let each = |stmts: &mut [Stmt]| -> Result<()> {
        for s in stmts {
            rewrite_stmt(s, fields, class)?;
        }
        Ok(())
    };
    match stmt {
        Stmt::Block { body, .. } => each(body),
        Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => Ok(()),
        Stmt::Expr { expression, .. }
        | Stmt::Throw {
            argument: expression,
            ..
        } => rewrite(expression, fields, class),
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                if let Some(init) = &mut d.init {
                    rewrite(init, fields, class)?;
                }
            }
            Ok(())
        }
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            rewrite(test, fields, class)?;
            rewrite_stmt(consequent, fields, class)?;
            match alternate {
                Some(a) => rewrite_stmt(a, fields, class),
                None => Ok(()),
            }
        }
        Stmt::While { test, body, .. } | Stmt::DoWhile { body, test, .. } => {
            rewrite(test, fields, class)?;
            rewrite_stmt(body, fields, class)
        }
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            match init {
                Some(ForInit::VarDecl(decls)) => {
                    for d in decls {
                        if let Some(init) = &mut d.init {
                            rewrite(init, fields, class)?;
                        }
                    }
                }
                Some(ForInit::Expr(e)) => rewrite(e, fields, class)?,
                None => {}
            }
            for e in [test, update].into_iter().flatten() {
                rewrite(e, fields, class)?;
            }
            rewrite_stmt(body, fields, class)
        }
        Stmt::ForIn {
            left, right, body, ..
        }
        | Stmt::ForOf {
            left, right, body, ..
        } => {
            if let ForInLhs::Expr(e) = left {
                rewrite(e, fields, class)?;
            }
            rewrite(right, fields, class)?;
            rewrite_stmt(body, fields, class)
        }
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            rewrite_stmt(block, fields, class)?;
            if let Some(h) = handler {
                rewrite_stmt(&mut h.body, fields, class)?;
            }
            match finalizer {
                Some(f) => rewrite_stmt(f, fields, class),
                None => Ok(()),
            }
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            rewrite(discriminant, fields, class)?;
            for c in cases {
                if let Some(t) = &mut c.test {
                    rewrite(t, fields, class)?;
                }
                each(&mut c.consequent)?;
            }
            Ok(())
        }
        Stmt::Labeled { body, .. } => rewrite_stmt(body, fields, class),
        Stmt::FunctionDecl { .. } => {
            if crate::ast::free_idents::mentions_this_in_stmt(stmt) {
                Err(unsupported(class, "`this` inside a function", stmt.span()))
            } else {
                Ok(())
            }
        }
        Stmt::Return { span, .. } => Err(ParseError::Unsupported {
            feature: format!(
                "`return` in the constructor of class `{}` (the instance is built from \
                 the fields its constructor sets, so it has to run to its end)",
                class
            ),
            span: *span,
        }
        .into()),
        Stmt::Import { span, .. } | Stmt::Export { span, .. } => {
            Err(unsupported(class, "an import or export", *span))
        }
    }
}

/// The names a constructor statement declares in the constructor's own
/// scope (its `var`/`let`/`const` and `function` declarations).
pub(super) fn declared_names(stmt: &Stmt) -> Vec<String> {
    match stmt {
        Stmt::Var { declarations, .. } => declarations.iter().map(|d| d.name.clone()).collect(),
        Stmt::FunctionDecl { name, .. } => vec![name.clone()],
        _ => Vec::new(),
    }
}
