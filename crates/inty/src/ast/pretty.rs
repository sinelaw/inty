//! Pretty printer for AST -> JavaScript source code.

use std::fmt::{self, Write};

use super::*;

/// Pretty print an expression to JavaScript source.
pub fn print_expr(expr: &Expr) -> String {
    let mut out = String::new();
    write_expr(&mut out, expr, false).unwrap();
    out
}

/// Pretty print a statement to JavaScript source.
pub fn print_stmt(stmt: &Stmt) -> String {
    let mut out = String::new();
    write_stmt(&mut out, stmt, 0).unwrap();
    out
}

/// Pretty print a program to JavaScript source.
pub fn print_program(program: &Program) -> String {
    print_program_with(program, std::collections::HashMap::new())
}

thread_local! {
    /// Text printed for a declaration in place of its AST, keyed by its
    /// span: a class as written (a `class` is lowered to a function).
    static AS_WRITTEN: std::cell::RefCell<std::collections::HashMap<Span, String>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The declaration at `span` as written, when it is to be printed so.
fn as_written(span: Span) -> Option<String> {
    AS_WRITTEN.with(|m| m.borrow().get(&span).cloned())
}

/// [`print_program`], printing each declaration whose span `as_written`
/// has as the text it gives (each class as written, from
/// [`crate::infer::decorate_with_classes`]).
pub fn print_program_with(
    program: &Program,
    as_written: std::collections::HashMap<Span, String>,
) -> String {
    /// Puts back the texts in place before, however printing ends.
    struct Restore(Option<std::collections::HashMap<Span, String>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let Some(previous) = self.0.take() {
                AS_WRITTEN.with(|m| m.replace(previous));
            }
        }
    }
    let _restore = Restore(Some(AS_WRITTEN.with(|m| m.replace(as_written))));
    print_statements(program)
}

fn print_statements(program: &Program) -> String {
    let mut out = String::new();
    // The program's type aliases, as declared (they are hoisted, so where
    // they stand doesn't matter), for the annotations that name them.
    let mut aliases: Vec<&TypeAlias> = program
        .type_aliases
        .iter()
        .filter(|a| a.body_ast.is_none() && !a.body.trim().is_empty())
        .collect();
    aliases.sort_by_key(|a| a.span.start);
    for alias in aliases {
        let kind = if alias.nominal {
            "nominal type"
        } else {
            "type"
        };
        let params = if alias.params.is_empty() {
            String::new()
        } else {
            format!("<{}>", alias.params.join(", "))
        };
        writeln!(
            out,
            "/** {} {}{} = {} */",
            kind,
            alias.name,
            params,
            alias.body.trim()
        )
        .unwrap();
    }
    for stmt in &program.statements {
        write_stmt(&mut out, stmt, 0).unwrap();
        writeln!(out).unwrap();
    }
    out
}

fn write_expr(w: &mut impl Write, expr: &Expr, needs_parens: bool) -> fmt::Result {
    match expr {
        Expr::Lit { value, .. } => write_literal(w, value),

        Expr::Ident { name, .. } => write!(w, "{}", name),

        Expr::This { .. } => write!(w, "this"),

        Expr::Array { elements, .. } => {
            write!(w, "[")?;
            for (i, elem) in elements.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                if let Some(e) = elem {
                    write_expr(w, e, false)?;
                }
            }
            write!(w, "]")
        }

        Expr::Tuple { elements, .. } => {
            write!(w, "(")?;
            for (i, elem) in elements.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write_expr(w, elem, false)?;
            }
            write!(w, ")")
        }

        Expr::Object { properties, .. } => {
            write!(w, "{{")?;
            for (i, prop) in properties.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write_prop_def(w, prop)?;
            }
            write!(w, "}}")
        }

        Expr::Function {
            name,
            params,
            body,
            type_annotation,
            arrow,
            ..
        } => {
            // In expression contexts that need to start with a token
            // other than `function` (call callees, member targets,
            // etc.), the function expression must be parenthesised —
            // otherwise at statement position `function() {...}()` is
            // parsed as a function *declaration* followed by `()`,
            // which fails with "missing name".
            if needs_parens {
                write!(w, "(")?;
            }
            let (is_async, body) = async_body(body);
            if is_async {
                write!(w, "async ")?;
            }
            // An arrow, as written: it has no `this` of its own.
            if *arrow {
                write!(w, "(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }
                    write!(w, "{}", p.name)?;
                }
                write!(w, ") => ")?;
                write_stmt(w, body, 0)?;
                if needs_parens {
                    write!(w, ")")?;
                }
                return Ok(());
            }
            write!(w, "function")?;
            if let Some(n) = name {
                write!(w, " {}", n)?;
            }
            write!(w, "(")?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", p.name)?;
            }
            write!(w, ")")?;
            if let Some(ann) = type_annotation {
                write!(
                    w,
                    " /** function {}{} */",
                    name.as_deref().unwrap_or(""),
                    ann.content
                )?;
            }
            write!(w, " ")?;
            write_stmt(w, body, 0)?;
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::Member {
            object, property, ..
        } => {
            // Numeric literals need parens for member access: (0).toString()
            let needs_wrap = matches!(
                object.as_ref(),
                Expr::Lit {
                    value: Literal::Number(_),
                    ..
                }
            );
            if needs_wrap {
                write!(w, "(")?;
            }
            write_expr(w, object, true)?;
            if needs_wrap {
                write!(w, ")")?;
            }
            // Render private-field sentinels back to their `#name`
            // source form so the desugared output stays readable.
            if let Some(name) =
                crate::types::private_key_display(&crate::types::PropName(property.clone()))
            {
                write!(w, ".#{}", name)
            } else {
                write!(w, ".{}", property)
            }
        }

        Expr::ComputedMember {
            object, property, ..
        } => {
            write_expr(w, object, true)?;
            write!(w, "[")?;
            write_expr(w, property, false)?;
            write!(w, "]")
        }

        // An `async` body's `return e`, marked (see
        // `crate::types::ASYNC_RETURN`): written as it was, `e`.
        Expr::Call {
            callee, arguments, ..
        } if matches!(callee.as_ref(), Expr::Ident { name, .. } if name == crate::types::ASYNC_RETURN)
            && arguments.len() == 1 =>
        {
            write_expr(w, &arguments[0], needs_parens)
        }

        Expr::Call {
            callee, arguments, ..
        } => {
            write_expr(w, callee, true)?;
            write!(w, "(")?;
            for (i, arg) in arguments.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write_expr(w, arg, false)?;
            }
            write!(w, ")")
        }

        Expr::New {
            callee, arguments, ..
        } => {
            write!(w, "new ")?;
            write_expr(w, callee, true)?;
            write!(w, "(")?;
            for (i, arg) in arguments.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write_expr(w, arg, false)?;
            }
            write!(w, ")")
        }

        Expr::NewTarget { .. } => write!(w, "new.target"),

        Expr::Unary { op, argument, .. } => {
            let (prefix, op_str) = unary_op_str(*op);
            if needs_parens {
                write!(w, "(")?;
            }
            if prefix {
                write!(w, "{}", op_str)?;
                if matches!(
                    op,
                    UnaryOp::Typeof | UnaryOp::Void | UnaryOp::Delete | UnaryOp::Await
                ) {
                    write!(w, " ")?;
                }
                // Wrap negative numbers to avoid --x being parsed as pre-decrement
                let arg_needs_wrap = matches!(
                    argument.as_ref(),
                    Expr::Lit { value: Literal::Number(n), .. } if *n < 0.0
                ) || matches!(
                    argument.as_ref(),
                    Expr::Unary {
                        op: UnaryOp::Neg | UnaryOp::Pos | UnaryOp::PreInc | UnaryOp::PreDec,
                        ..
                    }
                );
                if arg_needs_wrap {
                    write!(w, "(")?;
                    write_expr(w, argument, false)?;
                    write!(w, ")")?;
                } else {
                    write_expr(w, argument, true)?;
                }
            } else {
                write_expr(w, argument, true)?;
                write!(w, "{}", op_str)?;
            }
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::Binary {
            op, left, right, ..
        } => {
            if needs_parens {
                write!(w, "(")?;
            }
            write_expr(w, left, true)?;
            write!(w, " {} ", bin_op_str(*op))?;
            write_expr(w, right, true)?;
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::Assign {
            op, left, right, ..
        } => {
            if needs_parens {
                write!(w, "(")?;
            }
            write_expr(w, left, false)?;
            write!(w, " {} ", assign_op_str(*op))?;
            write_expr(w, right, false)?;
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            if needs_parens {
                write!(w, "(")?;
            }
            write_expr(w, test, true)?;
            write!(w, " ? ")?;
            write_expr(w, consequent, false)?;
            write!(w, " : ")?;
            write_expr(w, alternate, false)?;
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::NullishCoalesce { left, right, .. } => {
            if needs_parens {
                write!(w, "(")?;
            }
            write_expr(w, left, true)?;
            write!(w, " ?? ")?;
            write_expr(w, right, true)?;
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::OptionalChain { head, segments, .. } => {
            use crate::ast::ChainSegment;
            if needs_parens {
                write!(w, "(")?;
            }
            write_expr(w, head, true)?;
            for seg in segments {
                match seg {
                    ChainSegment::Member {
                        property, optional, ..
                    } => {
                        write!(w, "{}{}", if *optional { "?." } else { "." }, property)?;
                    }
                    ChainSegment::Computed {
                        property, optional, ..
                    } => {
                        if *optional {
                            write!(w, "?.[")?;
                        } else {
                            write!(w, "[")?;
                        }
                        write_expr(w, property, false)?;
                        write!(w, "]")?;
                    }
                    ChainSegment::Call {
                        arguments,
                        optional,
                        ..
                    } => {
                        if *optional {
                            write!(w, "?.")?;
                        }
                        write!(w, "(")?;
                        for (i, a) in arguments.iter().enumerate() {
                            if i > 0 {
                                write!(w, ", ")?;
                            }
                            write_expr(w, a, false)?;
                        }
                        write!(w, ")")?;
                    }
                }
            }
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::Spread { argument, .. } => {
            write!(w, "...")?;
            write_expr(w, argument, true)
        }

        // Synthetic destructuring-rest nodes. The source-form
        // round-trip emits something readable rather than the
        // internal shape — these are emitted by the desugarer, not
        // user-written, but `print_program` should still produce
        // valid JavaScript-ish output so decorate-and-reprint works.
        Expr::RestArray { source, skip, .. } => {
            write_expr(w, source, true)?;
            write!(w, ".slice({})", skip)
        }
        Expr::RestRow {
            source, excluded, ..
        } => {
            // No clean inty surface form for object rest; emit a
            // placeholder that round-trips into something the parser
            // could re-accept if reformatted. Used only for decorate
            // output; the underlying typing rule is handled by
            // `Expr::RestRow`'s own arm.
            write!(w, "/* {{...rest excluding [",)?;
            for (i, k) in excluded.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{:?}", k)?;
            }
            write!(w, "]}} */ ")?;
            write_expr(w, source, true)
        }

        Expr::Sequence { expressions, .. } => {
            if needs_parens {
                write!(w, "(")?;
            }
            for (i, e) in expressions.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write_expr(w, e, false)?;
            }
            if needs_parens {
                write!(w, ")")?;
            }
            Ok(())
        }

        Expr::TemplateLiteral {
            quasis,
            expressions,
            ..
        } => {
            write!(w, "`")?;
            for (i, quasi) in quasis.iter().enumerate() {
                write_template_string(w, quasi)?;
                if i < expressions.len() {
                    write!(w, "${{")?;
                    write_expr(w, &expressions[i], false)?;
                    write!(w, "}}")?;
                }
            }
            write!(w, "`")
        }
    }
}

fn write_literal(w: &mut impl Write, lit: &Literal) -> fmt::Result {
    match lit {
        Literal::Null => write!(w, "null"),
        Literal::Undefined => write!(w, "undefined"),
        Literal::Boolean(b) => write!(w, "{}", b),
        Literal::Number(n) => {
            if n.is_nan() {
                write!(w, "NaN")
            } else if n.is_infinite() {
                if *n > 0.0 {
                    write!(w, "Infinity")
                } else {
                    write!(w, "-Infinity")
                }
            } else if *n == 0.0 && n.is_sign_negative() {
                write!(w, "-0")
            } else {
                write!(w, "{}", n)
            }
        }
        Literal::String(s) => write_string(w, s),
        Literal::Regex { pattern, flags } => write!(w, "/{}/{}", pattern, flags),
    }
}

fn write_string(w: &mut impl Write, s: &str) -> fmt::Result {
    write!(w, "\"")?;
    for c in s.chars() {
        match c {
            '"' => write!(w, "\\\"")?,
            '\\' => write!(w, "\\\\")?,
            '\n' => write!(w, "\\n")?,
            '\r' => write!(w, "\\r")?,
            '\t' => write!(w, "\\t")?,
            c if c.is_control() => write!(w, "\\u{:04x}", c as u32)?,
            c => write!(w, "{}", c)?,
        }
    }
    write!(w, "\"")
}

fn write_template_string(w: &mut impl Write, s: &str) -> fmt::Result {
    for c in s.chars() {
        match c {
            '`' => write!(w, "\\`")?,
            '$' => write!(w, "\\$")?,
            '\\' => write!(w, "\\\\")?,
            c => write!(w, "{}", c)?,
        }
    }
    Ok(())
}

fn write_prop_key(w: &mut impl Write, key: &PropKey) -> fmt::Result {
    match key {
        PropKey::Ident(s) => {
            // Render private-field sentinels back to `#name`.
            if let Some(name) =
                crate::types::private_key_display(&crate::types::PropName(s.clone()))
            {
                write!(w, "#{}", name)
            } else {
                write!(w, "{}", s)
            }
        }
        PropKey::String(s) => write_string(w, s),
        PropKey::Number(n) => write!(w, "{}", n),
    }
}

fn write_prop_def(w: &mut impl Write, prop: &PropDef) -> fmt::Result {
    match prop {
        PropDef::Property { key, value, .. } => {
            write_prop_key(w, key)?;
            write!(w, ": ")?;
            write_expr(w, value, false)
        }
        PropDef::Getter { key, body, .. } => {
            write!(w, "get ")?;
            write_prop_key(w, key)?;
            write!(w, "() ")?;
            write_stmt(w, body, 0)
        }
        PropDef::Setter {
            key, param, body, ..
        } => {
            write!(w, "set ")?;
            write_prop_key(w, key)?;
            write!(w, "({}) ", param)?;
            write_stmt(w, body, 0)
        }
        PropDef::Method {
            key,
            params,
            body,
            type_annotation,
            ..
        } => {
            // Its annotation, as written: `/** function m(…) => R */`, or
            // `/** @type {T} */` for one that names its type.
            if let (Some(ann), PropKey::Ident(name)) = (type_annotation, key) {
                if ann.content.trim_start().starts_with('(') {
                    write!(w, "/** function {}{} */ ", name, ann.content.trim())?;
                } else {
                    write!(w, "/** @type {{{}}} */ ", ann.content.trim())?;
                }
            }
            let (is_async, body) = async_body(body);
            if is_async {
                write!(w, "async ")?;
            }
            write_prop_key(w, key)?;
            write!(w, "(")?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", p.name)?;
            }
            write!(w, ") ")?;
            write_stmt(w, body, 0)
        }
        PropDef::Spread { argument, .. } => {
            write!(w, "...")?;
            write_expr(w, argument, false)
        }
    }
}

fn write_stmt(w: &mut impl Write, stmt: &Stmt, indent: usize) -> fmt::Result {
    let ind = "  ".repeat(indent);

    match stmt {
        Stmt::Block { body, .. } => {
            writeln!(w, "{{")?;
            for s in body {
                write!(w, "{}", "  ".repeat(indent + 1))?;
                write_stmt(w, s, indent + 1)?;
                writeln!(w)?;
            }
            write!(w, "{}}}", ind)
        }

        Stmt::Empty { .. } => write!(w, ";"),

        Stmt::Expr { expression, .. } => {
            write_expr(w, expression, false)?;
            write!(w, ";")
        }

        Stmt::Var {
            kind, declarations, ..
        } => {
            let kw = match kind {
                VarKind::Var => "var",
                VarKind::Let => "let",
                VarKind::Const => "const",
            };
            // An external class, `/** class Name … */ class Name;`.
            if let [decl] = declarations.as_slice() {
                if let Some(ann) = decl
                    .type_annotation
                    .as_ref()
                    .filter(|a| a.kind == AnnotationKind::Class)
                {
                    let sep = if ann.content.starts_with(['(', '<']) {
                        ""
                    } else {
                        " "
                    };
                    writeln!(w, "/** class {}{}{} */", decl.name, sep, ann.content)?;
                    return write!(w, "{}class {};", ind, decl.name);
                }
            }
            // Output type annotations before the declaration
            for decl in declarations.iter() {
                if let Some(ann) = &decl.type_annotation {
                    writeln!(w, "/** {} {}: {} */", kw, decl.name, ann.content)?;
                    write!(w, "{}", ind)?;
                }
            }
            write!(w, "{} ", kw)?;
            for (i, decl) in declarations.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", decl.name)?;
                if let Some(init) = &decl.init {
                    write!(w, " = ")?;
                    write_expr(w, init, false)?;
                }
            }
            write!(w, ";")
        }

        Stmt::Import {
            specifiers, source, ..
        } => {
            write!(w, "import ")?;
            if specifiers.is_empty() {
                // Side-effect import
                write!(w, "\"{}\";", source)
            } else {
                let mut first = true;
                let mut has_named = false;

                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Default { local, .. } => {
                            if !first {
                                write!(w, ", ")?;
                            }
                            write!(w, "{}", local)?;
                            first = false;
                        }
                        ImportSpecifier::Namespace { local, .. } => {
                            if !first {
                                write!(w, ", ")?;
                            }
                            write!(w, "* as {}", local)?;
                            first = false;
                        }
                        ImportSpecifier::Named { .. } => {
                            has_named = true;
                        }
                    }
                }

                if has_named {
                    if !first {
                        write!(w, ", ")?;
                    }
                    write!(w, "{{ ")?;
                    let mut named_first = true;
                    for spec in specifiers {
                        if let ImportSpecifier::Named {
                            imported, local, ..
                        } = spec
                        {
                            if !named_first {
                                write!(w, ", ")?;
                            }
                            if imported == local {
                                write!(w, "{}", imported)?;
                            } else {
                                write!(w, "{} as {}", imported, local)?;
                            }
                            named_first = false;
                        }
                    }
                    write!(w, " }}")?;
                }

                write!(w, " from \"{}\";", source)
            }
        }

        Stmt::Export { declaration, .. } => {
            match declaration {
                ExportDecl::Var {
                    kind, declarations, ..
                } => {
                    let kw = match kind {
                        VarKind::Var => "var",
                        VarKind::Let => "let",
                        VarKind::Const => "const",
                    };
                    // Output type annotations before the declaration
                    for decl in declarations.iter() {
                        if let Some(ann) = &decl.type_annotation {
                            writeln!(w, "/** export {} {}: {} */", kw, decl.name, ann.content)?;
                            write!(w, "{}", ind)?;
                        }
                    }
                    write!(w, "export {} ", kw)?;
                    for (i, decl) in declarations.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        write!(w, "{}", decl.name)?;
                        if let Some(init) = &decl.init {
                            write!(w, " = ")?;
                            write_expr(w, init, false)?;
                        }
                    }
                    write!(w, ";")
                }
                ExportDecl::Function {
                    name,
                    params,
                    body,
                    type_annotation,
                    span,
                } => {
                    if let Some(text) = as_written(*span) {
                        return write!(w, "export {}", text);
                    }
                    if let Some(ann) = type_annotation {
                        writeln!(w, "/** export function {}{} */", name, ann.content)?;
                        write!(w, "{}", ind)?;
                    }
                    let (is_async, body) = async_body(body);
                    let prefix = if is_async { "async " } else { "" };
                    write!(w, "export {}function {}(", prefix, name)?;
                    for (i, p) in params.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        write!(w, "{}", p.name)?;
                    }
                    write!(w, ") ")?;
                    write_stmt(w, body, indent)
                }
                ExportDecl::Default { value, .. } => {
                    if let Some(text) = match value {
                        Expr::Function { span, .. } => as_written(*span),
                        _ => None,
                    } {
                        return write!(w, "export default {}", text);
                    }
                    write!(w, "export default ")?;
                    write_expr(w, value, false)?;
                    write!(w, ";")
                }
                ExportDecl::List { specifiers, .. } => {
                    write!(w, "export {{ ")?;
                    for (i, spec) in specifiers.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        if spec.exported == spec.local {
                            write!(w, "{}", spec.local)?;
                        } else {
                            write!(w, "{} as {}", spec.local, spec.exported)?;
                        }
                    }
                    write!(w, " }};")
                }
                ExportDecl::From { kind, source, .. } => {
                    write!(w, "export ")?;
                    match kind {
                        ExportFromKind::Named(specifiers) => {
                            write!(w, "{{ ")?;
                            for (i, spec) in specifiers.iter().enumerate() {
                                if i > 0 {
                                    write!(w, ", ")?;
                                }
                                if spec.exported == spec.local {
                                    write!(w, "{}", spec.local)?;
                                } else {
                                    write!(w, "{} as {}", spec.local, spec.exported)?;
                                }
                            }
                            write!(w, " }}")?;
                        }
                        ExportFromKind::All => write!(w, "*")?,
                        ExportFromKind::AllAs(name) => write!(w, "* as {}", name)?,
                    }
                    write!(w, " from \"{}\";", source)
                }
            }
        }

        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            write!(w, "if (")?;
            write_expr(w, test, false)?;
            write!(w, ") ")?;
            write_stmt(w, consequent, indent)?;
            if let Some(alt) = alternate {
                write!(w, " else ")?;
                write_stmt(w, alt, indent)?;
            }
            Ok(())
        }

        Stmt::While { test, body, .. } => {
            write!(w, "while (")?;
            write_expr(w, test, false)?;
            write!(w, ") ")?;
            write_stmt(w, body, indent)
        }

        Stmt::DoWhile { body, test, .. } => {
            write!(w, "do ")?;
            write_stmt(w, body, indent)?;
            write!(w, " while (")?;
            write_expr(w, test, false)?;
            write!(w, ");")
        }

        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            // Output type annotations before the for loop
            if let Some(ForInit::VarDecl(decls)) = init {
                for decl in decls.iter() {
                    if let Some(ann) = &decl.type_annotation {
                        writeln!(w, "/** var {}: {} */", decl.name, ann.content)?;
                        write!(w, "{}", ind)?;
                    }
                }
            }
            write!(w, "for (")?;
            if let Some(i) = init {
                match i {
                    ForInit::VarDecl(decls) => {
                        for (j, decl) in decls.iter().enumerate() {
                            if j > 0 {
                                write!(w, ", ")?;
                            }
                            if j == 0 {
                                write!(w, "var ")?;
                            }
                            write!(w, "{}", decl.name)?;
                            if let Some(init) = &decl.init {
                                write!(w, " = ")?;
                                write_expr(w, init, false)?;
                            }
                        }
                    }
                    ForInit::Expr(e) => write_expr(w, e, false)?,
                }
            }
            write!(w, "; ")?;
            if let Some(t) = test {
                write_expr(w, t, false)?;
            }
            write!(w, "; ")?;
            if let Some(u) = update {
                write_expr(w, u, false)?;
            }
            write!(w, ") ")?;
            write_stmt(w, body, indent)
        }

        Stmt::ForIn {
            left, right, body, ..
        } => {
            match left {
                ForInLhs::VarDecl(name, annotation, _, _) => {
                    if let Some(ann) = annotation {
                        writeln!(w, "/** var {}: {} */", name, ann.content)?;
                        write!(w, "{}", ind)?;
                    }
                    write!(w, "for (var {}", name)?;
                }
                ForInLhs::Expr(e) => {
                    write!(w, "for (")?;
                    write_expr(w, e, false)?;
                }
            }
            write!(w, " in ")?;
            write_expr(w, right, false)?;
            write!(w, ") ")?;
            write_stmt(w, body, indent)
        }

        Stmt::ForOf {
            left, right, body, ..
        } => {
            match left {
                ForInLhs::VarDecl(name, annotation, _, _) => {
                    if let Some(ann) = annotation {
                        writeln!(w, "/** var {}: {} */", name, ann.content)?;
                        write!(w, "{}", ind)?;
                    }
                    write!(w, "for (var {}", name)?;
                }
                ForInLhs::Expr(e) => {
                    write!(w, "for (")?;
                    write_expr(w, e, false)?;
                }
            }
            write!(w, " of ")?;
            write_expr(w, right, false)?;
            write!(w, ") ")?;
            write_stmt(w, body, indent)
        }

        Stmt::Break { label, .. } => {
            write!(w, "break")?;
            if let Some(l) = label {
                write!(w, " {}", l)?;
            }
            write!(w, ";")
        }

        Stmt::Continue { label, .. } => {
            write!(w, "continue")?;
            if let Some(l) = label {
                write!(w, " {}", l)?;
            }
            write!(w, ";")
        }

        Stmt::Return { argument, .. } => {
            write!(w, "return")?;
            if let Some(arg) = argument {
                write!(w, " ")?;
                write_expr(w, arg, false)?;
            }
            write!(w, ";")
        }

        Stmt::Throw { argument, .. } => {
            write!(w, "throw ")?;
            write_expr(w, argument, false)?;
            write!(w, ";")
        }

        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            write!(w, "try ")?;
            write_stmt(w, block, indent)?;
            if let Some(h) = handler {
                write!(w, " catch ({}) ", h.param)?;
                write_stmt(w, &h.body, indent)?;
            }
            if let Some(f) = finalizer {
                write!(w, " finally ")?;
                write_stmt(w, f, indent)?;
            }
            Ok(())
        }

        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            write!(w, "switch (")?;
            write_expr(w, discriminant, false)?;
            writeln!(w, ") {{")?;
            for case in cases {
                write!(w, "{}", "  ".repeat(indent + 1))?;
                if let Some(test) = &case.test {
                    write!(w, "case ")?;
                    write_expr(w, test, false)?;
                    writeln!(w, ":")?;
                } else {
                    writeln!(w, "default:")?;
                }
                for s in &case.consequent {
                    write!(w, "{}", "  ".repeat(indent + 2))?;
                    write_stmt(w, s, indent + 2)?;
                    writeln!(w)?;
                }
            }
            write!(w, "{}}}", ind)
        }

        Stmt::Labeled { label, body, .. } => {
            write!(w, "{}: ", label)?;
            write_stmt(w, body, indent)
        }

        Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            span,
            ..
        } => {
            if let Some(text) = as_written(*span) {
                return write!(w, "{}", text);
            }
            if let Some(ann) = type_annotation {
                // `(…) => R`, or a type the name can't run into
                // (`new (…) => R`, `this: T => (…) => R`).
                let gap = if ann.content.starts_with(['(', '<']) {
                    ""
                } else {
                    " "
                };
                writeln!(w, "/** function {}{}{} */", name, gap, ann.content)?;
                write!(w, "{}", ind)?;
            }
            let (is_async, body) = async_body(body);
            let prefix = if is_async { "async " } else { "" };
            write!(w, "{}function {}(", prefix, name)?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", p.name)?;
            }
            write!(w, ") ")?;
            write_stmt(w, body, indent)
        }
    }
}

/// An `async` function's body, as written, when `body` is the one the
/// parser lowers it to (`{ return Promise.resolve((() => { … })()); }`),
/// with `true`; else `body`, with `false`. The lowering gives each of
/// those nodes the same span (the function's), which no source text does
/// (in `return Promise.resolve(…)` written out, `Promise` spans less than
/// the call), so a body written that way is printed as written.
fn async_body(body: &Stmt) -> (bool, &Stmt) {
    if let Stmt::Block { body: stmts, .. } = body {
        if let [Stmt::Return {
            argument:
                Some(Expr::Call {
                    callee,
                    arguments,
                    span: call_span,
                    ..
                }),
            span: return_span,
        }] = stmts.as_slice()
        {
            if let (
                Expr::Member {
                    object,
                    property,
                    span: member_span,
                },
                [Expr::Call {
                    callee: iife,
                    arguments: none,
                    span: iife_call_span,
                    ..
                }],
            ) = (&**callee, arguments.as_slice())
            {
                if let (
                    Expr::Ident {
                        name,
                        span: promise_span,
                    },
                    Expr::Function {
                        params,
                        body: inner,
                        arrow: true,
                        span: iife_span,
                        ..
                    },
                ) = (&**object, &**iife)
                {
                    let one_span = [
                        call_span,
                        member_span,
                        promise_span,
                        iife_call_span,
                        iife_span,
                    ]
                    .iter()
                    .all(|s| *s == return_span);
                    if one_span
                        && name == "Promise"
                        && property == "resolve"
                        && none.is_empty()
                        && params.is_empty()
                    {
                        return (true, inner);
                    }
                }
            }
        }
    }
    (false, body)
}

fn unary_op_str(op: UnaryOp) -> (bool, &'static str) {
    match op {
        UnaryOp::Neg => (true, "-"),
        UnaryOp::Pos => (true, "+"),
        UnaryOp::Not => (true, "!"),
        UnaryOp::BitNot => (true, "~"),
        UnaryOp::Typeof => (true, "typeof"),
        UnaryOp::Void => (true, "void"),
        UnaryOp::Delete => (true, "delete"),
        UnaryOp::Await => (true, "await"),
        UnaryOp::PreInc => (true, "++"),
        UnaryOp::PreDec => (true, "--"),
        UnaryOp::PostInc => (false, "++"),
        UnaryOp::PostDec => (false, "--"),
    }
}

fn bin_op_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::FloorDiv => "//",
        BinOp::Pow => "**",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::LtEq => "<=",
        BinOp::GtEq => ">=",
        BinOp::EqEq => "==",
        BinOp::NotEq => "!=",
        BinOp::EqEqEq => "===",
        BinOp::NotEqEq => "!==",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::LShift => "<<",
        BinOp::RShift => ">>",
        BinOp::URShift => ">>>",
        BinOp::In => "in",
        BinOp::Instanceof => "instanceof",
    }
}

fn assign_op_str(op: AssignOp) -> &'static str {
    match op {
        AssignOp::Assign => "=",
        AssignOp::AddAssign => "+=",
        AssignOp::SubAssign => "-=",
        AssignOp::MulAssign => "*=",
        AssignOp::PowAssign => "**=",
        AssignOp::DivAssign => "/=",
        AssignOp::ModAssign => "%=",
        AssignOp::LShiftAssign => "<<=",
        AssignOp::RShiftAssign => ">>=",
        AssignOp::URShiftAssign => ">>>=",
        AssignOp::BitAndAssign => "&=",
        AssignOp::BitOrAssign => "|=",
        AssignOp::BitXorAssign => "^=",
        AssignOp::NullishAssign => "??=",
        AssignOp::LogicalAndAssign => "&&=",
        AssignOp::LogicalOrAssign => "||=",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::Span;

    fn span() -> Span {
        Span::new(0, 0)
    }

    #[test]
    fn test_print_literals() {
        let cases = [
            (Literal::Null, "null"),
            (Literal::Undefined, "undefined"),
            (Literal::Boolean(true), "true"),
            (Literal::Boolean(false), "false"),
            (Literal::Number(42.0), "42"),
            (Literal::Number(2.5), "2.5"),
            (Literal::String("hello".to_string()), "\"hello\""),
            (
                Literal::String("say \"hi\"".to_string()),
                "\"say \\\"hi\\\"\"",
            ),
        ];

        for (lit, expected) in cases {
            let expr = Expr::Lit {
                value: lit,
                span: span(),
            };
            assert_eq!(print_expr(&expr), expected);
        }
    }

    #[test]
    fn test_print_binary() {
        let expr = Expr::Binary {
            op: BinOp::Add,
            left: Box::new(Expr::Lit {
                value: Literal::Number(1.0),
                span: span(),
            }),
            right: Box::new(Expr::Lit {
                value: Literal::Number(2.0),
                span: span(),
            }),
            span: span(),
        };
        assert_eq!(print_expr(&expr), "1 + 2");
    }

    #[test]
    fn test_print_function() {
        let stmt = Stmt::FunctionDecl {
            name: "add".to_string(),
            params: vec![
                Param::new("a", Span::default()),
                Param::new("b", Span::default()),
            ],
            body: Box::new(Stmt::Block {
                body: vec![Stmt::Return {
                    argument: Some(Expr::Binary {
                        op: BinOp::Add,
                        left: Box::new(Expr::Ident {
                            name: "a".to_string(),
                            span: span(),
                        }),
                        right: Box::new(Expr::Ident {
                            name: "b".to_string(),
                            span: span(),
                        }),
                        span: span(),
                    }),
                    span: span(),
                }],
                span: span(),
            }),
            type_annotation: None,
            return_type_ast: None,
            name_span: None,
            span: span(),
        };
        let output = print_stmt(&stmt);
        assert!(output.contains("function add(a, b)"));
        assert!(output.contains("return a + b;"));
    }
}
