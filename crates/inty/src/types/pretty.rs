//! Pretty-printing for types.
//!
//! Provides human-readable string representations of types,
//! type schemes, and related structures.

use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Write};

use super::ty::{
    ClassName, LitValue, PropName, RowTail, RowType, TVarName, Type, TypePred, TypeScheme,
};
use super::{private_key_display, CALLABLE_KEY};

/// True when this type prints as a bare function `(args) => ret` —
/// either a raw `Type::Func` (only valid as a `<CALL>` field value, but
/// the printer is defensive) or a callable row with no extras (the
/// canonical "function value" shape under the unified design). Used to
/// decide when surrounding parentheses are needed in compound contexts
/// like `T[]` and `T | U`.
fn prints_as_function(ty: &Type) -> bool {
    match ty {
        Type::Func { .. } => true,
        Type::Row(row) => {
            row.props.len() == 1
                && row.props.contains_key(&PropName(CALLABLE_KEY.to_string()))
                && matches!(row.tail, RowTail::Closed)
        }
        _ => false,
    }
}

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

    fn write_type_ts<W: Write>(&mut self, w: &mut W, ty: &Type, in_func_arg: bool) -> fmt::Result {
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
                for (k, e) in &row.props {
                    if !first {
                        write!(w, "; ")?;
                    }
                    first = false;
                    write!(w, "{}: ", k.0)?;
                    self.write_type_ts(w, &e.ty, false)?;
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
                let needs_parens = prints_as_function(elem) || matches!(**elem, Type::Union(_));
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

    /// Format a list of type-class predicates as a comma-separated
    /// string (e.g. `Plus a` or `Plus a, Indexable a b c`), without
    /// any `where` keyword. Returns an empty string when `preds` is
    /// empty.
    pub fn format_preds(&mut self, preds: &[TypePred]) -> String {
        let mut s = String::new();
        for (i, pred) in preds.iter().enumerate() {
            if i > 0 {
                let _ = write!(s, ", ");
            }
            self.write_pred(&mut s, pred).unwrap();
        }
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
                let needs_parens = prints_as_function(elem);
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
                    let needs_parens = prints_as_function(m);
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
        // Callable rows render with the call signature first, without a
        // key, mirroring the keyless `(args) => ret` syntax in `.d.js`
        // type annotations. The CALLABLE_KEY field is reserved and
        // unspeakable in JS source, so it never shows up under its raw
        // name.
        let callable_key = PropName(CALLABLE_KEY.to_string());
        let callable = row.props.get(&callable_key);

        // Special case: if the row has *only* the CALLABLE_KEY field and
        // a closed tail, render as a plain function `(args) => ret`
        // without surrounding braces. Keeps inferred function types
        // readable.
        if let Some(call_entry) = callable {
            if row.props.len() == 1 && matches!(row.tail, RowTail::Closed) {
                return self.write_type(w, &call_entry.ty, false);
            }
        }

        write!(w, "{{")?;

        let mut first = true;
        if let Some(call_entry) = callable {
            self.write_type(w, &call_entry.ty, false)?;
            first = false;
        }
        for (prop, entry) in &row.props {
            if prop == &callable_key {
                continue;
            }
            // Phase 1b will render `Abs` fields as omitted entirely and
            // `Var(theta)` as `prop?: T`. For phase 1a all entries are
            // `Pre`, so this stays equivalent to the old behaviour.
            if matches!(entry.presence, crate::types::ty::Presence::Abs) {
                continue;
            }
            if !first {
                write!(w, ", ")?;
            }
            first = false;
            let optional_marker = matches!(
                entry.presence,
                crate::types::ty::Presence::Var(_)
            );
            // Private-field sentinels render as `#name`, restoring the
            // user-written form. The raw stored key contains control
            // characters that would otherwise look broken in errors.
            if let Some(name) = private_key_display(prop) {
                write!(w, "#{}{}: ", name, if optional_marker { "?" } else { "" })?;
            } else {
                write!(w, "{}{}: ", prop.0, if optional_marker { "?" } else { "" })?;
            }
            self.write_type(w, &entry.ty, false)?;
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
        // The quantifier prefix should only mention vars that actually
        // appear in the printed body or predicates. The body printer
        // hides `this` when it's a bare type variable, so a scheme
        // quantified over that var would otherwise show an orphan
        // letter like `<a, b>(b) => b` for an `id`-style function.
        let displayed_vars = displayed_vars_of_scheme(scheme);
        let visible: Vec<&TVarName> = scheme
            .vars
            .iter()
            .filter(|v| displayed_vars.contains(v))
            .collect();

        if !visible.is_empty() {
            write!(w, "<")?;
            for (i, var) in visible.iter().enumerate() {
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

/// Type variables that the body printer hides — currently just bare
/// `this` parameters on functions, which `write_type` skips unless
/// they're concrete. We need to know about these so that
/// `write_scheme` can drop them from the quantifier prefix instead
/// of printing an orphan letter (`<a, b>(b) => b`).
fn collect_hidden_this_vars(ty: &Type, hidden: &mut HashSet<TVarName>) {
    match ty {
        Type::Func {
            this_type,
            params,
            ret,
        } => {
            if let Some(t) = this_type {
                if let Type::Var(v) = t.as_ref() {
                    hidden.insert(v.clone());
                }
                collect_hidden_this_vars(t, hidden);
            }
            for p in params {
                collect_hidden_this_vars(p, hidden);
            }
            collect_hidden_this_vars(ret, hidden);
        }
        Type::Array(elem) => collect_hidden_this_vars(elem, hidden),
        Type::Promise(inner) => collect_hidden_this_vars(inner, hidden),
        Type::Map(value) => collect_hidden_this_vars(value, hidden),
        Type::Row(row) => {
            for entry in row.props.values() {
                collect_hidden_this_vars(&entry.ty, hidden);
            }
        }
        _ => {}
    }
}

/// Type variables that will actually appear in the printed form of
/// `scheme` — i.e. the free vars of body and predicates, minus the
/// hidden `this` vars. `write_scheme` filters the quantifier list
/// against this set.
fn displayed_vars_of_scheme(scheme: &TypeScheme) -> HashSet<TVarName> {
    let mut used = scheme.body.ty.free_vars();
    for p in &scheme.body.preds {
        used.extend(p.free_vars());
    }
    let mut hidden = HashSet::new();
    collect_hidden_this_vars(&scheme.body.ty, &mut hidden);
    for p in &scheme.body.preds {
        for t in &p.types {
            collect_hidden_this_vars(t, &mut hidden);
        }
    }
    for v in &hidden {
        used.remove(v);
    }
    used
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

    #[test]
    fn scheme_drops_quantifier_for_hidden_this_var() {
        // `function id(x) { return x; }` inferred type:
        //     this: t0, (t1) => t1
        // The body pretty-printer hides `this: t0` (bare tvar), so a
        // scheme that quantifies over BOTH t0 and t1 would print as
        // `<a, b>(b) => b` — an orphan `a` with nowhere to land. The
        // quantifier prefix must skip the hidden-this var and only
        // show `<a>(a) => a`.
        let this_v = TVarName::Flex(0);
        let body_v = TVarName::Flex(1);
        let body = Type::func(
            Type::Var(this_v.clone()),
            vec![Type::Var(body_v.clone())],
            Type::Var(body_v.clone()),
        );
        let scheme = TypeScheme::poly(vec![this_v, body_v], body);
        let s = scheme.to_string();
        assert_eq!(s, "<a>(a) => a", "got: {}", s);
    }

    #[test]
    fn scheme_preserves_class_predicate_in_output() {
        // `function add(x, y) { return x + y; }` → `<a> where Plus a => (a, a) => a`.
        // Regression: the scheme printer must reach the `where` clause
        // and not drop predicates when filtering the quantifier list.
        let a = TVarName::Flex(0);
        let body = Type::simple_func(
            vec![Type::Var(a.clone()), Type::Var(a.clone())],
            Type::Var(a.clone()),
        );
        let scheme = TypeScheme::qualified(
            vec![a.clone()],
            vec![TypePred::plus(Type::Var(a))],
            body,
        );
        let s = scheme.to_string();
        assert!(s.contains("<a>"), "missing <a> in {}", s);
        assert!(s.contains("where Plus"), "missing predicate in {}", s);
        assert!(s.contains("(a, a) => a"), "missing body in {}", s);
    }
}
