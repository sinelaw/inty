//! Pretty-printing for types.
//!
//! Provides human-readable string representations of types,
//! type schemes, and related structures.

use std::collections::HashSet;
use std::fmt::{self, Display, Write};

use super::ty::{
    ClassName, LitValue, Presence, PropName, RowTail, RowType, TVarName, Type, TypePred, TypeScheme,
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

/// Stateless pretty-printer.
///
/// Variable IDs are rendered directly as letters (`0 → a`, `25 → z`,
/// `26 → a0`, …), so the output is a pure function of the input
/// type. Coordination between callers — making sure two formatted
/// fragments use consistent letters for the same tvar — is the job
/// of [`crate::types::TidyEnv`], which runs *before* printing and
/// canonicalises variable IDs into the type itself. The legacy
/// mutable letter map is gone; `PrettyContext` is now effectively
/// a unit type, kept as a zero-sized struct so existing `.format_*`
/// method calls keep working without churn.
pub struct PrettyContext {
    /// Display names for nominal types, keyed by their `TypeId`. When a
    /// `Type::Named(id, _)` is a declared brand, rendering it as the
    /// user's name (`UserId`) rather than the internal `μ<id>` makes
    /// brand-mismatch diagnostics legible. Empty by default; callers
    /// with access to the named-type registry seed it via
    /// [`PrettyContext::with_nominal_names`].
    nominal_names: std::collections::HashMap<crate::types::TypeId, String>,
    /// Diagnostics: a record with more fields than this shows only the
    /// fields in `focus` (or, with none of them, its first few) and
    /// "… and N more" — DOM element rows run to hundreds of fields.
    row_limit: Option<usize>,
    /// Diagnostics: the fields a record always shows (the ones a
    /// mismatch is about).
    focus: HashSet<String>,
    /// Diagnostics: types printed by an alias's name when they are its
    /// body with its parameters (listed) instantiated (`Channel`,
    /// `DomEvent<a>`, rather than their records).
    aliases: Vec<(String, Vec<u32>, Type)>,
}

impl PrettyContext {
    /// Create a pretty-printing context. Stateless apart from the
    /// (usually empty) nominal-name map.
    pub fn new() -> Self {
        Self::with_nominal_names(std::collections::HashMap::new())
    }

    /// Create a context that renders the given nominal `TypeId`s by name.
    pub fn with_nominal_names(
        nominal_names: std::collections::HashMap<crate::types::TypeId, String>,
    ) -> Self {
        PrettyContext {
            nominal_names,
            row_limit: None,
            focus: HashSet::new(),
            aliases: Vec::new(),
        }
    }

    /// Print records of more than `limit` fields trimmed to the `focus`
    /// fields (see the fields' docs).
    pub fn trimming_rows(mut self, limit: usize, focus: HashSet<String>) -> Self {
        self.row_limit = Some(limit);
        self.focus = focus;
        self
    }

    /// Print a type that is one of these aliases' bodies (the body's
    /// parameter variables instantiated) by the alias's name.
    pub fn naming_aliases(mut self, aliases: Vec<(String, Vec<u32>, Type)>) -> Self {
        self.aliases = aliases;
        self
    }

    /// Render a tvar's integer ID as a display letter. After tidy
    /// produces small, traversal-ordered IDs, this is the identity
    /// of the canonical form: `0 → a`, `1 → b`, …, `26 → a0`.
    /// Untidied types with large IDs print as numbered letters
    /// (`b5`, `c12`, …); that's recoverable but ugly, so callers
    /// that care about readability should tidy first.
    fn get_var_name(&mut self, id: u32) -> String {
        let idx = id as usize;
        if idx < 26 {
            char::from(b'a' + idx as u8).to_string()
        } else {
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
            Type::Number | Type::Int => write!(w, "number"),
            Type::String => write!(w, "string"),
            Type::Boolean => write!(w, "boolean"),
            Type::Undefined => write!(w, "undefined"),
            Type::Null => write!(w, "null"),
            Type::Regex => write!(w, "RegExp"),
            Type::TypedArray(k) => write!(w, "{}", k.name()),
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
                    write!(w, "_a{}", i)?;
                    if !matches!(p.presence, Presence::Pre) {
                        write!(w, "?")?;
                    }
                    write!(w, ": ")?;
                    self.write_type_ts(w, &p.ty, false)?;
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
            Type::Tuple(elems) => {
                write!(w, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }
                    self.write_type_ts(w, e, false)?;
                }
                write!(w, "]")
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
            Type::Error => write!(w, "<error>"),
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
        if !self.aliases.is_empty() && matches!(ty, Type::Row(_) | Type::Union(_)) {
            let found = self.aliases.iter().find_map(|(name, params, body)| {
                let mut bound = std::collections::HashMap::new();
                match_alias(body, ty, params, &mut bound).then(|| {
                    let args: Vec<Type> = params
                        .iter()
                        .map(|p| bound.get(p).cloned().unwrap_or(Type::Var(TVarName::Flex(*p))))
                        .collect();
                    (name.clone(), args)
                })
            });
            if let Some((name, args)) = found {
                write!(w, "{}", name)?;
                if !args.is_empty() {
                    write!(w, "<")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ")?;
                        }
                        self.write_type(w, a, false)?;
                    }
                    write!(w, ">")?;
                }
                return Ok(());
            }
        }
        match ty {
            Type::Number => write!(w, "Number"),
            Type::Int => write!(w, "Int"),
            Type::String => write!(w, "String"),
            Type::Boolean => write!(w, "Boolean"),
            Type::Undefined => write!(w, "Undefined"),
            Type::Null => write!(w, "Null"),
            Type::Regex => write!(w, "Regex"),
            Type::TypedArray(k) => write!(w, "{}", k.name()),

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
                    self.write_type(w, &param.ty, false)?;
                    // Surface optionality on the type — `?` follows
                    // the type in inty's source syntax so an
                    // optional `Number` prints as `Number?`. Skip
                    // the suffix for `Presence::Pre` (the common
                    // case) and for `Presence::Abs` (which makes
                    // the param effectively absent — the printer
                    // could omit it entirely but the position is
                    // still part of the signature and surface
                    // syntax doesn't have a representation for
                    // "absent slot in the middle").
                    if !matches!(param.presence, Presence::Pre) {
                        write!(w, "?")?;
                    }
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
                // Wrap complex element types in parentheses so the `[]`
                // binds unambiguously: a union or function element reads as
                // `(A | B)[]` / `((A) => B)[]`, not `A | B[]` (which parses
                // as `A | (B[])`).
                let needs_parens = prints_as_function(elem) || matches!(**elem, Type::Union(_));
                if needs_parens {
                    write!(w, "(")?;
                }
                self.write_type(w, elem, false)?;
                if needs_parens {
                    write!(w, ")")?;
                }
                write!(w, "[]")
            }

            Type::Tuple(elems) => {
                write!(w, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }
                    self.write_type(w, e, false)?;
                }
                write!(w, "]")
            }

            Type::Promise(inner) => {
                write!(w, "Promise<")?;
                self.write_type(w, inner, false)?;
                write!(w, ">")
            }

            Type::Map(value) => {
                write!(w, "Dict<")?;
                self.write_type(w, value, false)?;
                write!(w, ">")
            }

            Type::Named(id, args) => {
                match self.nominal_names.get(id) {
                    Some(name) => write!(w, "{}", name)?,
                    None => write!(w, "μ{}", id)?,
                }
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

            Type::Error => write!(w, "<error>"),
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
        // Diagnostics: a huge record shows the fields that matter.
        let shown = row
            .props
            .iter()
            .filter(|(p, e)| *p != &callable_key && !matches!(e.presence, Presence::Abs))
            .count();
        let trimmed = self.row_limit.is_some_and(|limit| shown > limit);
        let keep = |prop: &PropName, i: usize, focus: &HashSet<String>, limit: usize| -> bool {
            if focus.is_empty() {
                i < limit.min(6)
            } else {
                focus.contains(&prop.0)
            }
        };
        let limit = self.row_limit.unwrap_or(usize::MAX);
        let focus = std::mem::take(&mut self.focus);
        let mut hidden = 0;
        let mut index = 0;
        for (prop, entry) in &row.props {
            if prop == &callable_key {
                continue;
            }
            if trimmed && !matches!(entry.presence, Presence::Abs) {
                index += 1;
                if !keep(prop, index - 1, &focus, limit) {
                    hidden += 1;
                    continue;
                }
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
            let optional_marker = matches!(entry.presence, crate::types::ty::Presence::Var(_));
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
        self.focus = focus;
        if hidden > 0 {
            if !first {
                write!(w, ", ")?;
            }
            write!(w, "… and {} more", hidden)?;
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
            // `HasProp` predicates on the same receiver print together,
            // in first-appearance order: `a has {x: b, y: c}`.
            let mut groups: Vec<(&Type, Vec<(&str, &Type)>)> = Vec::new();
            let mut first = true;
            for pred in &scheme.body.preds {
                if let Some((recv, name, result)) = pred.as_has_prop() {
                    match groups.iter_mut().find(|(r, _)| *r == recv) {
                        Some((_, fields)) => {
                            if !fields.contains(&(name, result)) {
                                fields.push((name, result));
                            }
                        }
                        None => groups.push((recv, vec![(name, result)])),
                    }
                    continue;
                }
                if !first {
                    write!(w, ", ")?;
                }
                first = false;
                self.write_pred(w, pred)?;
            }
            for (recv, fields) in groups {
                if !first {
                    write!(w, ", ")?;
                }
                first = false;
                self.write_has_props(w, recv, &fields)?;
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
            ClassName::Num | ClassName::NumLit => {
                write!(w, "Num ")?;
                self.write_type(w, &pred.types[0], true)?;
            }
            ClassName::Arith => {
                write!(w, "Arith ")?;
                self.write_type(w, &pred.types[0], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[1], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[2], true)?;
            }
            ClassName::Indexable => {
                write!(w, "Indexable ")?;
                self.write_type(w, &pred.types[0], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[1], true)?;
                write!(w, " ")?;
                self.write_type(w, &pred.types[2], true)?;
            }
            ClassName::HasProp => match pred.as_has_prop() {
                Some((recv, name, result)) => self.write_has_props(w, recv, &[(name, result)])?,
                None => {
                    write!(w, "HasProp")?;
                    for t in &pred.types {
                        write!(w, " ")?;
                        self.write_type(w, t, true)?;
                    }
                }
            },
        }
        Ok(())
    }

    /// `recv has {name: T, …}`: the properties a scheme reads from a
    /// value of a quantified type.
    fn write_has_props<W: Write>(
        &mut self,
        w: &mut W,
        recv: &Type,
        fields: &[(&str, &Type)],
    ) -> fmt::Result {
        self.write_type(w, recv, true)?;
        write!(w, " has {{")?;
        for (i, (name, ty)) in fields.iter().enumerate() {
            if i > 0 {
                write!(w, ", ")?;
            }
            write!(w, "{}: ", name)?;
            self.write_type(w, ty, false)?;
        }
        write!(w, "}}")
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
                collect_hidden_this_vars(&p.ty, hidden);
            }
            collect_hidden_this_vars(ret, hidden);
        }
        Type::Array(elem) => collect_hidden_this_vars(elem, hidden),
        Type::Promise(inner) => collect_hidden_this_vars(inner, hidden),
        Type::Map(value) => collect_hidden_this_vars(value, hidden),
        Type::Tuple(elems) => {
            for e in elems {
                collect_hidden_this_vars(e, hidden);
            }
        }
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
    // A `HasProp` receiver is printed (`a has {…}`) even where it's
    // also a method's hidden `this`.
    for p in &scheme.body.preds {
        if let Some((Type::Var(v), _, _)) = p.as_has_prop() {
            hidden.remove(v);
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
        // Tidy before printing so the Display impl produces the
        // canonical letters regardless of the raw IDs the type
        // carries. Callers that already need shared letters across
        // several Display calls should construct a [`TidyEnv`] and
        // run the values through it themselves before calling
        // [`PrettyContext::format_type`].
        let tidied = crate::types::TidyEnv::new().tidy_type(self);
        let mut ctx = PrettyContext::new();
        write!(f, "{}", ctx.format_type(&tidied))
    }
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tidied = crate::types::TidyEnv::new().tidy_scheme(self);
        let mut ctx = PrettyContext::new();
        write!(f, "{}", ctx.format_scheme(&tidied))
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
            ClassName::Num | ClassName::NumLit => write!(f, "Num"),
            ClassName::Arith => write!(f, "Arith"),
            ClassName::Indexable => write!(f, "Indexable"),
            ClassName::HasProp => write!(f, "HasProp"),
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
        let scheme =
            TypeScheme::qualified(vec![a.clone()], vec![TypePred::plus(Type::Var(a))], body);
        let s = scheme.to_string();
        assert!(s.contains("<a>"), "missing <a> in {}", s);
        assert!(s.contains("where Plus"), "missing predicate in {}", s);
        assert!(s.contains("(a, a) => a"), "missing body in {}", s);
    }
}

/// Whether `ty` is `pattern` with its `params` (variable ids) replaced by
/// some types — recorded in `bound`, consistently.
fn match_alias(
    pattern: &Type,
    ty: &Type,
    params: &[u32],
    bound: &mut std::collections::HashMap<u32, Type>,
) -> bool {
    match (pattern, ty) {
        (Type::Var(TVarName::Flex(p)), _) if params.contains(p) => match bound.get(p) {
            Some(b) => b == ty,
            None => {
                bound.insert(*p, ty.clone());
                true
            }
        },
        (Type::Row(a), Type::Row(b)) => {
            a.tail == b.tail
                && a.props.len() == b.props.len()
                && a.props.iter().all(|(k, e)| {
                    b.props
                        .get(k)
                        .is_some_and(|f| e.presence == f.presence && match_alias(&e.ty, &f.ty, params, bound))
                })
        }
        (Type::Union(a), Type::Union(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(x, y)| match_alias(x, y, params, bound))
        }
        (Type::Array(a), Type::Array(b)) | (Type::Promise(a), Type::Promise(b)) => {
            match_alias(a, b, params, bound)
        }
        (
            Type::Func {
                this_type: t1,
                params: p1,
                ret: r1,
            },
            Type::Func {
                this_type: t2,
                params: p2,
                ret: r2,
            },
        ) => {
            p1.len() == p2.len()
                && match (t1, t2) {
                    (None, None) => true,
                    (Some(a), Some(b)) => match_alias(a, b, params, bound),
                    _ => false,
                }
                && p1
                    .iter()
                    .zip(p2)
                    .all(|(x, y)| x.presence == y.presence && match_alias(&x.ty, &y.ty, params, bound))
                && match_alias(r1, r2, params, bound)
        }
        (a, b) => a == b,
    }
}
