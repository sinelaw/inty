//! A walk over every expression of a program.
//!
//! Every variant is matched by name, with no catch-all, so a node added to
//! the AST doesn't compile until the walk visits what it holds.

use super::{
    ChainSegment, ExportDecl, Expr, ForInLhs, ForInit, Param, PropDef, Stmt, VarDeclarator,
};

/// Call `f` on every expression in `stmts`, outer before inner, in
/// source order.
pub fn each_expr<'a>(stmts: &'a [Stmt], f: &mut impl FnMut(&'a Expr)) {
    for stmt in stmts {
        stmt_exprs(stmt, f);
    }
}

fn stmt_exprs<'a>(stmt: &'a Stmt, f: &mut impl FnMut(&'a Expr)) {
    match stmt {
        Stmt::Block { body, .. } => each_expr(body, f),
        Stmt::Expr { expression, .. } => expr(expression, f),
        Stmt::Var { declarations, .. } => declarators(declarations, f),
        Stmt::Export { declaration, .. } => match declaration {
            ExportDecl::Var { declarations, .. } => declarators(declarations, f),
            ExportDecl::Function { params, body, .. } => function(params, body, f),
            ExportDecl::Default { value, .. } => expr(value, f),
            ExportDecl::List { .. } | ExportDecl::From { .. } => {}
        },
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            expr(test, f);
            stmt_exprs(consequent, f);
            if let Some(alternate) = alternate {
                stmt_exprs(alternate, f);
            }
        }
        Stmt::While { test, body, .. } => {
            expr(test, f);
            stmt_exprs(body, f);
        }
        Stmt::DoWhile { body, test, .. } => {
            stmt_exprs(body, f);
            expr(test, f);
        }
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            match init {
                Some(ForInit::VarDecl(decls)) => declarators(decls, f),
                Some(ForInit::Expr(e)) => expr(e, f),
                None => {}
            }
            test.iter().chain(update).for_each(|e| expr(e, f));
            stmt_exprs(body, f);
        }
        Stmt::ForIn {
            left, right, body, ..
        }
        | Stmt::ForOf {
            left, right, body, ..
        } => {
            match left {
                ForInLhs::Expr(e) => expr(e, f),
                ForInLhs::VarDecl(..) => {}
            }
            expr(right, f);
            stmt_exprs(body, f);
        }
        Stmt::Return { argument, .. } => argument.iter().for_each(|e| expr(e, f)),
        Stmt::Throw { argument, .. } => expr(argument, f),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            stmt_exprs(block, f);
            if let Some(handler) = handler {
                stmt_exprs(&handler.body, f);
            }
            if let Some(finalizer) = finalizer {
                stmt_exprs(finalizer, f);
            }
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            expr(discriminant, f);
            for case in cases {
                case.test.iter().for_each(|e| expr(e, f));
                each_expr(&case.consequent, f);
            }
        }
        Stmt::Labeled { body, .. } => stmt_exprs(body, f),
        Stmt::FunctionDecl { params, body, .. } => function(params, body, f),
        Stmt::Import { .. } | Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
    }
}

fn declarators<'a>(decls: &'a [VarDeclarator], f: &mut impl FnMut(&'a Expr)) {
    for d in decls {
        d.init.iter().for_each(|e| expr(e, f));
    }
}

fn function<'a>(params: &'a [Param], body: &'a Stmt, f: &mut impl FnMut(&'a Expr)) {
    for p in params {
        p.default.iter().for_each(|e| expr(e, f));
    }
    stmt_exprs(body, f);
}

fn expr<'a>(e: &'a Expr, f: &mut impl FnMut(&'a Expr)) {
    f(e);
    match e {
        Expr::Lit { .. } | Expr::Ident { .. } | Expr::This { .. } | Expr::NewTarget { .. } => {}
        Expr::Array { elements, .. } => elements.iter().flatten().for_each(|e| expr(e, f)),
        Expr::Tuple { elements, .. } => elements.iter().for_each(|e| expr(e, f)),
        Expr::Object { properties, .. } => {
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => expr(value, f),
                    PropDef::Getter { body, .. } | PropDef::Setter { body, .. } => {
                        stmt_exprs(body, f)
                    }
                    PropDef::Method { params, body, .. } => function(params, body, f),
                    PropDef::Spread { argument, .. } => expr(argument, f),
                }
            }
        }
        Expr::Function { params, body, .. } => function(params, body, f),
        Expr::Member { object, .. } => expr(object, f),
        Expr::ComputedMember {
            object, property, ..
        } => {
            expr(object, f);
            expr(property, f);
        }
        Expr::Call {
            callee,
            arguments,
            keywords,
            ..
        } => {
            expr(callee, f);
            arguments.iter().for_each(|e| expr(e, f));
            keywords.iter().for_each(|(_, e)| expr(e, f));
        }
        Expr::New {
            callee, arguments, ..
        } => {
            expr(callee, f);
            arguments.iter().for_each(|e| expr(e, f));
        }
        Expr::Unary { argument, .. }
        | Expr::Spread { argument, .. }
        | Expr::RestArray {
            source: argument, ..
        }
        | Expr::RestRow {
            source: argument, ..
        } => expr(argument, f),
        Expr::Binary { left, right, .. }
        | Expr::Assign { left, right, .. }
        | Expr::NullishCoalesce { left, right, .. } => {
            expr(left, f);
            expr(right, f);
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            expr(test, f);
            expr(consequent, f);
            expr(alternate, f);
        }
        Expr::OptionalChain { head, segments, .. } => {
            expr(head, f);
            for segment in segments {
                match segment {
                    ChainSegment::Computed { property, .. } => expr(property, f),
                    ChainSegment::Call { arguments, .. } => {
                        arguments.iter().for_each(|e| expr(e, f))
                    }
                    ChainSegment::Member { .. } => {}
                }
            }
        }
        Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
            expressions.iter().for_each(|e| expr(e, f))
        }
    }
}
