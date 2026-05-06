//! Pretty-printing for types.
//!
//! Provides human-readable string representations of types,
//! type schemes, and related structures.

use std::collections::HashMap;
use std::fmt::{self, Display, Write};

use super::ty::{ClassName, LitValue, RowTail, RowType, TVarName, Type, TypePred, TypeScheme};

/// Context for pretty-printing, tracking variable names.
pub struct PrettyContext {
    /// Mapping from type variable IDs to display names.
    var_names: HashMap<u32, String>,
    /// Counter for generating fresh names.
    next_name: usize,
}

impl PrettyContext {
    /// Create a new pretty-printing context.
    pub fn new() -> Self {
        PrettyContext {
            var_names: HashMap::new(),
            next_name: 0,
        }
    }

    /// Get or generate a name for a type variable.
    fn get_var_name(&mut self, id: u32) -> String {
        if let Some(name) = self.var_names.get(&id) {
            return name.clone();
        }

        let name = self.generate_name();
        self.var_names.insert(id, name.clone());
        name
    }

    /// Generate the next fresh variable name.
    fn generate_name(&mut self) -> String {
        let idx = self.next_name;
        self.next_name += 1;

        if idx < 26 {
            // a, b, c, ..., z
            char::from(b'a' + idx as u8).to_string()
        } else {
            // a1, b1, ..., z1, a2, ...
            let letter = char::from(b'a' + (idx % 26) as u8);
            let num = idx / 26;
            format!("{}{}", letter, num)
        }
    }

    /// Format a type to a string.
    pub fn format_type(&mut self, ty: &Type) -> String {
        let mut s = String::new();
        self.write_type(&mut s, ty, false).unwrap();
        s
    }

    /// Format a type using TypeScript-flavour syntax: lowercase
    /// primitives, `;`-separated object properties, `void` instead
    /// of `Undefined` at return positions (we still emit
    /// `undefined` elsewhere). Used by `inty declarations
    /// --format=ts` to emit `.d.ts` output downstream tooling
    /// expects.
    pub fn format_type_ts(&mut self, ty: &Type) -> String {
        let mut s = String::new();
        self.write_type_ts(&mut s, ty, false).unwrap();
        s
    }

    fn write_type_ts<W: Write>(
        &mut self,
        w: &mut W,
        ty: &Type,
        in_func_arg: bool,
    ) -> fmt::Result {
        match ty {
            Type::Number => write!(w, "number"),
            Type::String => write!(w, "string"),
            Type::Boolean => write!(w, "boolean"),
            Type::Undefined => write!(w, "undefined"),
            Type::Null => write!(w, "null"),
            Type::Regex => write!(w, "RegExp"),
            Type::Var(name) => self.write_var(w, name),
            Type::Func {
                this_type: _,
                params,
                ret,
            } => {
                if in_func_arg {
                    write!(w, "(")?;
                }
                write!(w, "(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }
                    write!(w, "_a{}: ", i)?;
                    self.write_type_ts(w, p, false)?;
                }
                write!(w, ") => ")?;
                self.write_type_ts(w, ret, false)?;
                if in_func_arg {
                    write!(w, ")")?;
                }
                Ok(())
            }
            Type::Row(row) => {
                use super::ty::RowTail;
                write!(w, "{{ ")?;
                let mut first = true;
                for (k, v) in &row.props {
                    if !first {
                        write!(w, "; ")?;
                    }
                    first = false;
                    write!(w, "{}: ", k.0)?;
                    self.write_type_ts(w, v, false)?;
                }
                if let RowTail::Open(name) = &row.tail {
                    if !first {
                        write!(w, "; ")?;
                    }
                    write!(w, "[k: string]: ")?;
                    self.write_var(w, name)?;
                }
                write!(w, " }}")
            }
            Type::Array(elem) => {
                let needs_parens = matches!(**elem, Type::Func { .. } | Type::Union(_));
                if needs_parens {
                    write!(w, "(")?;
                }
                self.write_type_ts(w, elem, false)?;
                if needs_parens {
                    write!(w, ")")?;
                }
                write!(w, "[]")
            }
            Type::Map(value) => {
                write!(w, "Record<string, ")?;
                self.write_type_ts(w, value, false)?;
                write!(w, ">")
            }
            Type::Promise(inner) => {
                write!(w, "Promise<")?;
                self.write_type_ts(w, inner, false)?;
                write!(w, ">")
            }
            Type::Named(_, _) => {
                // Named recursive types don't have a clean TS shape;
                // fall back to the inty form.
                self.write_type(w, ty, in_func_arg)
            }
            Type::Literal(lit) => self.write_literal(w, lit),
            Type::Union(members) => {
                if members.is_empty() {
                    return write!(w, "never");
                }
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(w, " | ")?;
                    }
                    self.write_type_ts(w, m, false)?;
                }
                Ok(())
            }
            Type::Module(_) => self.write_type(w, ty, in_func_arg),
        }
    }

    /// Format a type scheme to a string.
    pub fn format_scheme(&mut self, scheme: &TypeScheme) -> String {
        let mut s = String::new();
        self.write_scheme(&mut s, scheme).unwrap();
        s
    }

    /// Write a type to the given writer.
    fn write_type<W: Write>(&mut self, w: &mut W, ty: &Type, in_func_arg: bool) -> fmt::Result {
        match ty {
            Type::Number => write!(w, "Number"),
            Type::String => write!(w, "String"),
            Type::Boolean => write!(w, "Boolean"),
            Type::Undefined => write!(w, "Undefined"),
            Type::Null => write!(w, "Null"),
            Type::Regex => write!(w, "Regex"),

            Type::Var(name) => self.write_var(w, name),

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                // Check if this needs parentheses
                if in_func_arg {
                    write!(w, "(")?;
                }

                // Only show this_type if it's meaningful:
                // - None (static function): don't show
                // - Some(Undefined) or Some(Var(_)): don't show
                // - Some(concrete_type): show "this: T =>"
                let show_this = match this_type {
                    None => false,
                    Some(t) => !matches!(**t, Type::Undefined | Type::Var(_)),
                };
                if show_this {
                    write!(w, "this: ")?;
                    self.write_type(w, this_type.as_ref().unwrap(), false)?;
                    write!(w, " => ")?;
                }

                write!(w, "(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }
                    self.write_type(w, param, false)?;
                }
                write!(w, ") => ")?;
                self.write_type(w, ret, false)?;

                if in_func_arg {
                    write!(w, ")")?;
                }
                Ok(())
            }

            Type::Row(row) => self.write_row(w, row),

            Type::Array(elem) => {
                // Wrap complex types in parentheses for clarity
                let needs_parens = matches!(**elem, Type::Func { .. });
                if needs_parens {
                    write!(w, "(")?;
                }
                self.write_type(w, elem, false)?;
                if needs_parens {
                    write!(w, ")")?;
                }
                write!(w, "[]")
            }

            Type::Promise(inner) => {
                write!(w, "Promise<")?;
                self.write_type(w, inner, false)?;
                write!(w, ">")
            }

            Type::Map(value) => {
                write!(w, "Map<")?;
                self.write_type(w, value, false)?;
                write!(w, ">")
            }

            Type::Named(id, args) => {
                write!(w, "μ{}", id)?;
                if !args.is_empty() {
                    write!(w, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        self.write_type(w, arg, false)?;
                    }
                    write!(w, ">")?;
                }
                Ok(())
            }

            Type::Literal(lit) => self.write_literal(w, lit),

            Type::Module(m) => {
                // Display only the source identity in inline contexts.
                // The full export listing is verbose enough to belong
                // elsewhere (e.g. a `--verbose` mode); here we keep the
                // type readable in error messages and `--annotate` output.
                write!(w, "module {:?}", m.source)
            }

            Type::Union(members) => {
                if members.is_empty() {
                    return write!(w, "never");
                }
                // Unions bind weaker than function arrows; if we're already
                // inside a function-arg context, parenthesise to avoid
                // `A | B => C` reading as `A | (B => C)`.
                if in_func_arg {
                    write!(w, "(")?;
                }
                for (i, m) in members.iter().enumerate() {
                    if i > 0 {
                        write!(w, " | ")?;
                    }
                    // Parenthesise function members so `(A) => B | C` reads
                    // as `((A) => B) | C` rather than `(A) => (B | C)`.
                    let needs_parens = matches!(m, Type::Func { .. });
                    if needs_parens {
                        write!(w, "(")?;
                    }
                    self.write_type(w, m, false)?;
                    if needs_parens {
                        write!(w, ")")?;
                    }
                }
                if in_func_arg {
                    write!(w, ")")?;
                }
                Ok(())
            }
        }
    }

    /// Write a literal-value type.
    fn write_literal<W: Write>(&mut self, w: &mut W, lit: &LitValue) -> fmt::Result {
        match lit {
            LitValue::String(s) => write!(w, "\"{}\"", s),
            LitValue::Number(n) => write!(w, "{}", n),
            LitValue::Bool(b) => write!(w, "{}", b),
        }
    }

    /// Write a type variable.
    fn write_var<W: Write>(&mut self, w: &mut W, name: &TVarName) -> fmt::Result {
        match name {
            TVarName::Flex(id) => {
                let var_name = self.get_var_name(*id);
                write!(w, "{}", var_name)
            }
            TVarName::Skolem(id) => {
                let var_name = self.get_var_name(*id);
                write!(w, "'{}", var_name)
            }
        }
    }

    /// Write a row type.
    fn write_row<W: Write>(&mut self, w: &mut W, row: &RowType) -> fmt::Result {
        write!(w, "{{")?;

        let mut first = true;
        for (prop, ty) in &row.props {
            if !first {
                write!(w, ", ")?;
            }
            first = false;
            write!(w, "{}: ", prop.0)?;
            self.write_type(w, ty, false)?;
        }

        match &row.tail {
            RowTail::Closed => {}
            RowTail::Open(var) => {
                if !row.props.is_empty() {
                    write!(w, " | ")?;
                }
                self.write_var(w, var)?;
            }
            RowTail::Recursive(id, args) => {
                if !row.props.is_empty() {
                    write!(w, " | ")?;
                }
                write!(w, "μ{}", id)?;
                if !args.is_empty() {
                    write!(w, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        self.write_type(w, arg, false)?;
                    }
                    write!(w, ">")?;
                }
            }
        }

        write!(w, "}}")
    }

    /// Write a type scheme.
    fn write_scheme<W: Write>(&mut self, w: &mut W, scheme: &TypeScheme) -> fmt::Result {
        if !scheme.vars.is_empty() {
            write!(w, "<")?;
            for (i, var) in scheme.vars.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                self.write_var(w, var)?;
            }
            write!(w, ">")?;
        }

        if !scheme.body.preds.is_empty() {
            write!(w, " where ")?;
            for (i, pred) in scheme.body.preds.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                self.write_pred(w, pred)?;
            }
            write!(w, " => ")?;
        }

        self.write_type(w, &scheme.body.ty, false)
    }

    /// Write a type predicate.
    fn write_pred<W: Write>(&mut self, w: &mut W, pred: &TypePred) -> fmt::Result {
        match pred.class {
            ClassName::Plus => {
                write!(w, "Plus ")?;
                self.write_type(w, &pred.types[0], true)?;
            }
            ClassName::Indexable => {
                write!(w, "Indexable ")?;
                self.write_type(w, &pred.types[0], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[1], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[2], true)?;
            }
        }
        Ok(())
    }
}

impl Default for PrettyContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Display implementation for types using a fresh context.
impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = PrettyContext::new();
        write!(f, "{}", ctx.format_type(self))
    }
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = PrettyContext::new();
        write!(f, "{}", ctx.format_scheme(self))
    }
}

impl Display for TVarName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TVarName::Flex(id) => write!(f, "t{}", id),
            TVarName::Skolem(id) => write!(f, "'t{}", id),
        }
    }
}

impl Display for ClassName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClassName::Plus => write!(f, "Plus"),
            ClassName::Indexable => write!(f, "Indexable"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_types() {
        assert_eq!(Type::Number.to_string(), "Number");
        assert_eq!(Type::String.to_string(), "String");
        assert_eq!(Type::Boolean.to_string(), "Boolean");
    }

    #[test]
    fn test_type_variable() {
        let ty = Type::flex(0);
        assert_eq!(ty.to_string(), "a");

        let ty2 = Type::flex(1);
        let mut ctx = PrettyContext::new();
        ctx.format_type(&ty);
        let s = ctx.format_type(&ty2);
        assert_eq!(s, "b");
    }

    #[test]
    fn test_function_type() {
        let func = Type::simple_func(vec![Type::Number, Type::String], Type::Boolean);
        assert_eq!(func.to_string(), "(Number, String) => Boolean");
    }

    #[test]
    fn test_array_type() {
        let arr = Type::array(Type::Number);
        assert_eq!(arr.to_string(), "Number[]");
    }

    #[test]
    fn test_row_type() {
        let row = Type::object([("x", Type::Number), ("y", Type::String)]);
        let s = row.to_string();
        assert!(s.contains("x: Number"));
        assert!(s.contains("y: String"));
    }

    #[test]
    fn test_type_scheme() {
        let scheme = TypeScheme::poly(vec![TVarName::Flex(0)], Type::flex(0));
        assert_eq!(scheme.to_string(), "<a>a");
    }

    #[test]
    fn test_qualified_scheme() {
        let scheme = TypeScheme::qualified(
            vec![TVarName::Flex(0)],
            vec![TypePred::plus(Type::flex(0))],
            Type::simple_func(vec![Type::flex(0), Type::flex(0)], Type::flex(0)),
        );
        let s = scheme.to_string();
        assert!(s.contains("Plus"));
        assert!(s.contains("<a>"));
    }
}
