//! Surface-form predicate (phase 7c).
//!
//! The well-typed-term generator in `crate::meta::soundness` may only
//! emit *surface* expressions: nodes the parser actually produces, with
//! no runtime-only forms (closure values, heap locations, etc.) leaking
//! back into the AST. `is_surface_expr` formalises that contract.
//!
//! Today every `Expr` variant is surface — the runtime forms
//! (`Value::Closure`, `Value::Array(Loc)`, …) live in `crate::dynamics::value`
//! and never appear in `Expr`. The predicate exists so that future
//! AST extensions (e.g. quoted closure-thunks, runtime markers) can
//! be added with one match arm here, and the generator/property test
//! gates on the predicate to refuse to feed them in.

use crate::ast::{Expr, Stmt};

/// True if `expr` is built entirely from parser-surface AST forms. Use
/// this to gate inputs to the well-typed-term generator and the blame
/// prober: those tools must only consider expressions a programmer
/// could write in source.
pub fn is_surface_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Lit { .. } | Expr::Ident { .. } | Expr::This { .. } | Expr::NewTarget { .. } => true,
        Expr::Array { elements, .. } => elements.iter().all(|e| match e {
            Some(e) => is_surface_expr(e),
            None => true,
        }),
        Expr::Tuple { elements, .. } => elements.iter().all(is_surface_expr),
        Expr::Object { properties, .. } => properties.iter().all(|p| match p {
            crate::ast::PropDef::Property { value, .. } => is_surface_expr(value),
            crate::ast::PropDef::Method { body, .. } => is_surface_stmt(body),
            crate::ast::PropDef::Getter { body, .. } => is_surface_stmt(body),
            crate::ast::PropDef::Setter { body, .. } => is_surface_stmt(body),
            crate::ast::PropDef::Spread { argument, .. } => is_surface_expr(argument),
        }),
        Expr::Function { body, .. } => is_surface_stmt(body),
        Expr::Member { object, .. } => is_surface_expr(object),
        Expr::ComputedMember {
            object, property, ..
        } => is_surface_expr(object) && is_surface_expr(property),
        Expr::Call {
            callee, arguments, ..
        }
        | Expr::New {
            callee, arguments, ..
        } => is_surface_expr(callee) && arguments.iter().all(is_surface_expr),
        Expr::Unary { argument, .. } => is_surface_expr(argument),
        Expr::Binary { left, right, .. } | Expr::Assign { left, right, .. } => {
            is_surface_expr(left) && is_surface_expr(right)
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => is_surface_expr(test) && is_surface_expr(consequent) && is_surface_expr(alternate),
        Expr::NullishCoalesce { left, right, .. } => {
            is_surface_expr(left) && is_surface_expr(right)
        }
        Expr::OptionalChain { head, segments, .. } => {
            is_surface_expr(head)
                && segments.iter().all(|s| match s {
                    crate::ast::ChainSegment::Member { .. } => true,
                    crate::ast::ChainSegment::Computed { property, .. } => {
                        is_surface_expr(property)
                    }
                    crate::ast::ChainSegment::Call { arguments, .. } => {
                        arguments.iter().all(is_surface_expr)
                    }
                })
        }
        Expr::Spread { argument, .. } => is_surface_expr(argument),
        // Synthetic destructuring-rest nodes never appear in
        // user-written source — they're emitted by the desugarer in
        // declarator initialisers — so they're not "surface" forms.
        Expr::RestArray { .. } | Expr::RestRow { .. } => false,
        Expr::Sequence { expressions, .. } => expressions.iter().all(is_surface_expr),
        Expr::TemplateLiteral { expressions, .. } => expressions.iter().all(is_surface_expr),
    }
}

/// True if `stmt` is built entirely from parser-surface AST forms.
pub fn is_surface_stmt(stmt: &Stmt) -> bool {
    use crate::ast::{ExportDecl, ForInit};
    match stmt {
        Stmt::Empty { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => true,
        Stmt::Block { body, .. } => body.iter().all(is_surface_stmt),
        Stmt::Expr { expression, .. } => is_surface_expr(expression),
        Stmt::Var { declarations, .. } => declarations
            .iter()
            .all(|d| d.init.as_ref().map_or(true, is_surface_expr)),
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            is_surface_expr(test)
                && is_surface_stmt(consequent)
                && alternate.as_ref().map_or(true, |s| is_surface_stmt(s))
        }
        Stmt::While { test, body, .. } | Stmt::DoWhile { test, body, .. } => {
            is_surface_expr(test) && is_surface_stmt(body)
        }
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            init.as_ref().map_or(true, |i| match i {
                ForInit::VarDecl(decls) => decls
                    .iter()
                    .all(|d| d.init.as_ref().map_or(true, is_surface_expr)),
                ForInit::Expr(e) => is_surface_expr(e),
            }) && test.as_ref().map_or(true, is_surface_expr)
                && update.as_ref().map_or(true, is_surface_expr)
                && is_surface_stmt(body)
        }
        Stmt::ForIn { right, body, .. } | Stmt::ForOf { right, body, .. } => {
            is_surface_expr(right) && is_surface_stmt(body)
        }
        Stmt::Return { argument, .. } => argument.as_ref().map_or(true, is_surface_expr),
        Stmt::Throw { argument, .. } => is_surface_expr(argument),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            is_surface_stmt(block)
                && handler.as_ref().map_or(true, |c| is_surface_stmt(&c.body))
                && finalizer.as_ref().map_or(true, |f| is_surface_stmt(f))
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            is_surface_expr(discriminant)
                && cases.iter().all(|c| {
                    c.test.as_ref().map_or(true, is_surface_expr)
                        && c.consequent.iter().all(is_surface_stmt)
                })
        }
        Stmt::Labeled { body, .. } => is_surface_stmt(body),
        Stmt::FunctionDecl { body, .. } => is_surface_stmt(body),
        Stmt::Import { .. } => true,
        Stmt::Export { declaration, .. } => match declaration {
            ExportDecl::Var { declarations, .. } => declarations
                .iter()
                .all(|d| d.init.as_ref().map_or(true, is_surface_expr)),
            ExportDecl::Function { body, .. } => is_surface_stmt(body),
            ExportDecl::Default { value, .. } => is_surface_expr(value),
            ExportDecl::List { .. } => true,
            ExportDecl::From { .. } => true,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontends::javascript::lexer::{Scanner, Token};
    use crate::frontends::javascript::parser::Parser;

    fn parse(src: &str) -> crate::ast::Program {
        let mut scanner = Scanner::new(src);
        let mut tokens = Vec::new();
        loop {
            let tok = scanner.next_token().unwrap();
            let is_eof = matches!(tok.value, Token::Eof);
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        let type_annotations = scanner.type_annotations().to_vec();
        let mut parser = Parser::new(tokens, type_annotations);
        parser.parse_program().unwrap()
    }

    #[test]
    fn parsed_programs_are_always_surface() {
        // Sanity: anything the parser produces should pass the
        // surface predicate. If a future AST variant is added but
        // forgotten in `is_surface_*`, this test catches it.
        let cases = [
            "var x = 1 + 2;",
            "function f(x) { return x; } f(3);",
            "[1, 2, 3].length;",
            "({a: 1}).a;",
            "if (true) { 1; } else { 2; }",
            "switch (1) { case 1: break; default: break; }",
            "for (var i = 0; i < 5; i = i + 1) { i; }",
            "var s = `hi ${1}`;",
            "try { throw 7; } catch (e) { e; }",
        ];
        for src in cases {
            let prog = parse(src);
            for stmt in &prog.statements {
                assert!(is_surface_stmt(stmt), "non-surface in: {}", src);
            }
        }
    }
}
