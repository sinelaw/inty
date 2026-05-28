//! Parser for TypeScript-style type annotations.
//!
//! Parses type annotation strings like:
//! - `Number`, `String`, `Boolean`
//! - `Number[]`, `String[][]`
//! - `() => Number`, `(a: Number, b: String) => Boolean`
//! - `<T>(x: T) => T`
//! - `{name: String, age: Number}`

use std::collections::HashMap;

use crate::error::TypeError;
use crate::span::Span;
use crate::types::{LitValue, Type};

use super::state::AliasDef;

/// Result type for type annotation parsing.
pub type ParseResult<T> = Result<T, TypeError>;

/// Pre-resolved JSDoc `typeof X` lookup table. The inference caller
/// pre-instantiates each `typeof` reference (so fresh-var allocation
/// happens against the outer counter, in the same range the rest of
/// the annotation will allocate from) and hands the parser a map from
/// the bare identifier `X` to the instantiated type.
///
/// JSDoc's `typeof X` (TypeScript convention) refers to the *value*
/// type of `X`, which is the scheme instantiated to a mono type. We
/// follow that convention — the result of a `typeof` use is always a
/// monomorphic snapshot of the named binding's scheme, not a re-bound
/// polymorphic scheme. Pre-instantiation cleanly bypasses borrow
/// problems with threading `&mut InferState` through the parser.
pub type TypeOfTable = HashMap<String, Type>;

/// Parser for type annotation strings.
pub struct TypeParser<'a> {
    /// The input string.
    input: &'a str,
    /// Current position in the input.
    pos: usize,
    /// Span for error reporting.
    span: Span,
    /// Mapping from type variable names to type variable IDs.
    type_vars: HashMap<String, u32>,
    /// Next fresh type variable ID.
    next_var_id: u32,
    /// Next fresh presence variable ID. Uses an offset to avoid
    /// collision with the caller's pvar source: callers re-seed the
    /// outer pvar source from this after parsing, the same pattern
    /// `next_var_id` uses for type vars.
    next_pvar_id: u32,
    /// Whether we're at the top level (quantifiers allowed).
    /// Set to false when parsing nested types (e.g., inside function parameters).
    allow_quantifiers: bool,
    /// User-defined generic type aliases reachable in this annotation
    /// scope. When `Foo<args>` is parsed and `Foo` is an alias, the
    /// args are substituted into a fresh copy of the alias body.
    aliases: Option<&'a HashMap<String, AliasDef>>,
    /// Pre-built lookup for JSDoc `typeof X`. Built at the call site
    /// (see `rows.rs::infer_object`) by scanning the annotation
    /// content for `typeof IDENT` substrings and pre-instantiating
    /// each one against the outer inference scope. None when no
    /// resolver context is available (alias-body parsing, free-form
    /// type-string parsing in unit tests).
    typeof_table: Option<&'a TypeOfTable>,
}

impl<'a> TypeParser<'a> {
    /// Create a new type parser.
    pub fn new(input: &'a str, span: Span, start_var_id: u32) -> Self {
        TypeParser {
            input,
            pos: 0,
            span,
            type_vars: HashMap::new(),
            next_var_id: start_var_id,
            next_pvar_id: 0,
            allow_quantifiers: true, // Quantifiers allowed at top level
            aliases: None,
            typeof_table: None,
        }
    }

    /// Create a type parser that consults the supplied alias env when
    /// it encounters `Foo<args>` for a user-defined alias `Foo`.
    pub fn with_aliases(
        input: &'a str,
        span: Span,
        start_var_id: u32,
        aliases: &'a HashMap<String, AliasDef>,
    ) -> Self {
        TypeParser {
            input,
            pos: 0,
            span,
            type_vars: HashMap::new(),
            next_var_id: start_var_id,
            next_pvar_id: 0,
            allow_quantifiers: true,
            aliases: Some(aliases),
            typeof_table: None,
        }
    }

    /// Install a [`TypeOfTable`] used to resolve `typeof X` to the
    /// pre-instantiated type of `X` from the calling inference scope.
    /// Must be called before `parse`. The table borrows from the
    /// caller's stack frame; the parser holds it only for the
    /// duration of one annotation parse.
    pub fn with_typeof(mut self, table: &'a TypeOfTable) -> Self {
        self.typeof_table = Some(table);
        self
    }

    /// Allocate a fresh flexible presence variable. Used when an
    /// annotation marks a field optional (`x?: T`).
    fn fresh_pvar(&mut self) -> crate::types::PVarName {
        let id = self.next_pvar_id;
        self.next_pvar_id += 1;
        crate::types::PVarName::Flex(id)
    }

    /// Pre-bind a type-variable name to a specific ID before parsing.
    /// Used when loading a type alias's body so each parameter name
    /// (`T`, `U`, …) maps to the alias-owned ID rather than a fresh
    /// one. Must be called before `parse`.
    pub fn preset_var(&mut self, name: String, id: u32) {
        self.type_vars.insert(name, id);
        if id + 1 > self.next_var_id {
            self.next_var_id = id + 1;
        }
    }

    /// The next free type-variable ID — useful after parsing if the
    /// caller needs to keep its own counter in sync.
    pub fn next_var_id(&self) -> u32 {
        self.next_var_id
    }

    /// The next free presence-variable ID. Mirrors `next_var_id` for
    /// the parallel pvar namespace.
    pub fn next_pvar_id_value(&self) -> u32 {
        self.next_pvar_id
    }

    /// Seed the pvar source so allocations don't collide with the
    /// caller's outer counter. Must be called before `parse`.
    pub fn seed_pvar_id(&mut self, start: u32) {
        self.next_pvar_id = start;
    }

    /// Parse the entire type annotation.
    pub fn parse(&mut self) -> ParseResult<Type> {
        self.skip_whitespace();
        let ty = self.parse_type()?;
        self.skip_whitespace();
        if self.pos < self.input.len() {
            return Err(self.error(format!(
                "unexpected character '{}'",
                self.current_char().unwrap()
            )));
        }
        Ok(ty)
    }

    /// Parse a type, including union postfixes (`A | B | ...`).
    fn parse_type(&mut self) -> ParseResult<Type> {
        self.skip_whitespace();

        // Check for generic type: <T, U>(...)  => ...
        if self.peek_char() == Some('<') {
            // Rank-1 restriction: quantifiers only allowed at top level
            if !self.allow_quantifiers {
                return Err(TypeError::Rank1Restriction { span: self.span });
            }
            return self.parse_generic_type();
        }

        // Parse the leading simple-or-function type, then collect any
        // `| Type` continuations into a union. `|` binds weaker than `=>`,
        // so the function type is parsed first and the union is built
        // around it.
        let first = self.parse_simple_type()?;
        self.skip_whitespace();
        // Intersection types `A & B` are TS-only — reject with a
        // suggested alternative pointing at row merging.
        if self.peek_char() == Some('&') {
            // Don't fire on `&&`; only standalone `&`.
            let after = self.input[self.pos + 1..].chars().next();
            if after != Some('&') {
                return Err(self.error(
                    "intersection types `A & B` are not supported in inty. \
                     Help: merge the rows into a single object type \
                     `{ ...fields of A, ...fields of B }`."
                        .to_string(),
                ));
            }
        }
        if self.peek_char() != Some('|') {
            return Ok(first);
        }
        let mut members = vec![first];
        while self.peek_char() == Some('|') {
            self.pos += 1;
            self.skip_whitespace();
            members.push(self.parse_simple_type()?);
            self.skip_whitespace();
        }
        Ok(Type::union(members))
    }

    /// Parse a generic type like `<T>(x: T) => T` or `<T> {...}`.
    /// Quantifier-then-function is the common form; quantifier-then-row
    /// (`<a> { (a) => T, foo: ... }`) declares a polymorphic callable
    /// row, used by the unified design's primitive-constructor stubs
    /// (`String`, `Number`, `Boolean`) in core.d.js.
    fn parse_generic_type(&mut self) -> ParseResult<Type> {
        self.expect_char('<')?;
        self.skip_whitespace();

        // Parse type parameters
        let mut params = Vec::new();
        loop {
            self.skip_whitespace();
            let name = self.parse_ident()?;
            let var_id = self.next_var_id;
            self.next_var_id += 1;
            self.type_vars.insert(name, var_id);
            params.push(var_id);

            self.skip_whitespace();
            if self.peek_char() == Some('>') {
                break;
            }
            self.expect_char(',')?;
        }
        self.expect_char('>')?;

        // Parse the body — either a function type or a row type. Use
        // `parse_simple_type` so any leaf-shape (and `[]` array
        // suffixes) is acceptable; quantifier-then-arbitrary-shape is
        // the principled extension and only the parser changes.
        self.skip_whitespace();
        self.parse_simple_type()
    }

    /// Parse a function type or a grouped type in parentheses.
    fn parse_func_or_grouped(&mut self) -> ParseResult<Type> {
        // Save position to backtrack if needed
        let start_pos = self.pos;

        // Try to parse as a function type first
        match self.try_parse_func_type() {
            Ok(ty) => Ok(ty),
            Err(e) => {
                // Don't backtrack for errors that committed to the
                // function-type interpretation — Rank-1 is one
                // such case (we identified the function shape but
                // the nested type was Rank-2+); the optional-after-
                // required check is another (we parsed the full
                // signature and rejected it on a semantic ground).
                // Both surface their dedicated variants so
                // backtracking to grouped-type would replace a
                // precise diagnostic with a confusing "unknown
                // type 'a'" from re-parsing the leftover input.
                if matches!(
                    e,
                    TypeError::Rank1Restriction { .. }
                        | TypeError::OptionalParameterFollowedByRequired { .. }
                ) {
                    return Err(e);
                }
                // Backtrack and try as grouped type for syntax errors
                self.pos = start_pos;
                self.parse_grouped_type()
            }
        }
    }

    /// Try to parse a function type, returning error if it's not a function.
    fn try_parse_func_type(&mut self) -> ParseResult<Type> {
        self.parse_func_type()
    }

    /// Parse a grouped type in parentheses: (Type)
    fn parse_grouped_type(&mut self) -> ParseResult<Type> {
        self.expect_char('(')?;
        self.skip_whitespace();
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(ty)
    }

    /// Parse a function type like `(a: Number, b: String) => Boolean`.
    fn parse_func_type(&mut self) -> ParseResult<Type> {
        self.expect_char('(')?;
        self.skip_whitespace();

        let mut params: Vec<crate::types::FuncParam> = Vec::new();

        // Parameters are nested positions, so quantifiers are not allowed
        let old_allow = self.allow_quantifiers;
        self.allow_quantifiers = false;

        if self.peek_char() != Some(')') {
            loop {
                self.skip_whitespace();

                // Parse parameter. Three forms are accepted:
                //   `Type`           — anonymous, required
                //   `name: Type`     — named, required
                //   `name?: Type`    — named, presence-polymorphic
                //   `Type?`          — anonymous, presence-polymorphic
                //
                // The `?` after the parameter name (TypeScript-style)
                // or after a bare type signals an optional positional
                // argument: the formal's presence becomes a fresh
                // presence variable, so a call site that omits the
                // arg unifies presence to `Abs` and a call site that
                // supplies it unifies to `Pre`. This is Garrigue
                // 1994's labeled+optional treatment, ported to
                // inty's row-presence machinery.
                let (param_type, optional) = if self.is_ident_start(self.peek_char()) {
                    let start_pos = self.pos;
                    let _name = self.parse_ident()?;
                    self.skip_whitespace();

                    // `name?:` or `name:` decides optionality on the
                    // named form.
                    let named_optional = self.peek_char() == Some('?');
                    if named_optional {
                        self.pos += 1; // consume '?'
                        self.skip_whitespace();
                    }
                    if self.peek_char() == Some(':') {
                        self.expect_char(':')?;
                        self.skip_whitespace();
                        let ty = self.parse_type()?;
                        (ty, named_optional)
                    } else {
                        // Just an identifier - could be a type name.
                        // Reset and parse as type (which may itself
                        // end in `?` for the anonymous-optional form).
                        self.pos = start_pos;
                        self.parse_param_anon()?
                    }
                } else {
                    self.parse_param_anon()?
                };

                let param = if optional {
                    let pvar = self.fresh_pvar();
                    crate::types::FuncParam::optional(pvar, param_type)
                } else {
                    crate::types::FuncParam::required(param_type)
                };
                params.push(param);

                self.skip_whitespace();
                if self.peek_char() == Some(')') {
                    break;
                }
                self.expect_char(',')?;
            }
        }

        self.expect_char(')')?;
        self.skip_whitespace();

        // Expect '=>'. From this point on we're committed to a
        // function type — any error returned is a function-type
        // diagnostic, not a "this might be a grouped type, try
        // again" backtrackable parse failure. That distinction
        // matters for the ts(1016)-style check below: the wrapper
        // `parse_func_or_grouped` backtracks on any error from
        // `parse_func_type` and falls back to `parse_grouped_type`,
        // which would re-parse our well-formed function-with-bad-
        // optionality as a degenerate grouped expression and
        // surface a confusing "unknown type 'a'" error instead of
        // the real diagnostic. Running the check after `=>` is
        // matched puts it past the backtrack point.
        self.expect_str("=>")?;
        self.skip_whitespace();

        let ret_type = self.parse_type()?;

        // Restore the original setting
        self.allow_quantifiers = old_allow;

        // Reject "required after optional" — `(a?: T, b: U) => V`
        // and `(a: T, b?: U, c: V) => W` are TypeScript ts(1016)
        // errors for good reason: under positional-only calling
        // (which is all JavaScript supports), the trailing
        // required parameter forces every legal call to supply
        // the optional one too, silently neutering the `?`.
        // Garrigue 1994 §3.3 allows this shape only when labeled
        // arguments disambiguate the missing slot; inty has no
        // labels, so the OCaml escape hatch doesn't apply and we
        // follow the TypeScript convention. Surface as the
        // dedicated `OptionalParameterFollowedByRequired` variant
        // so the `parse_func_or_grouped` wrapper recognises the
        // diagnostic as committed-function-type and doesn't
        // backtrack to retry as a grouped expression.
        let mut seen_optional = None;
        for (idx, p) in params.iter().enumerate() {
            match &p.presence {
                crate::types::Presence::Pre => {
                    if let Some(opt_idx) = seen_optional {
                        return Err(TypeError::OptionalParameterFollowedByRequired {
                            optional_idx: opt_idx,
                            required_idx: idx,
                            span: self.span,
                        });
                    }
                }
                crate::types::Presence::Var(_) | crate::types::Presence::Abs => {
                    if seen_optional.is_none() {
                        seen_optional = Some(idx);
                    }
                }
            }
        }

        Ok(Type::wrap_callable(Type::raw_func_with_params(
            None, params, ret_type,
        )))
    }

    /// Parse an anonymous parameter — a type optionally followed by
    /// `?` to mark it presence-polymorphic. Returns the type and a
    /// bool indicating whether the trailing `?` was consumed. Note
    /// that the `?` here is the *parameter optionality* marker, not
    /// the nullable-type postfix that `parse_simple_type` handles:
    /// at the param position the surrounding context disambiguates
    /// (a `?` immediately before a `,` or `)` is parameter
    /// optionality; a `?` deeper in the type stays nullable-type).
    fn parse_param_anon(&mut self) -> ParseResult<(Type, bool)> {
        let ty = self.parse_type()?;
        self.skip_whitespace();
        // The nullable postfix is greedy in `parse_simple_type`, so
        // a trailing `?` here would already have been consumed as
        // part of the type unless it's followed by `,` or `)`. We
        // don't see one in well-formed input; the named form
        // (`name?: T`) is the canonical way to mark a parameter
        // optional.
        Ok((ty, false))
    }

    /// Parse a simple type (primary type with optional [] suffixes).
    fn parse_simple_type(&mut self) -> ParseResult<Type> {
        let mut ty = self.parse_primary_type()?;

        // Parse array suffixes and the nullable postfix in any order.
        // `T?` desugars to `T | Null | Undefined` per the unified
        // design — reuses union narrowing and `?.` / `??` semantics
        // without introducing a new nominal type.
        loop {
            self.skip_whitespace();
            if self.peek_char() == Some('[') && self.peek_char_at(1) == Some(']') {
                self.pos += 2;
                ty = Type::array(ty);
            } else if self.peek_char() == Some('?') {
                // Postfix `T?` desugars to `T | Undefined`, matching
                // TS's optional convention (where `x?: T` adds
                // `undefined`, not `null`). For DOM APIs that return
                // `T | null` specifically (`getElementById` etc.),
                // users write the long form. For the JS-native case
                // (missing fields, `arr.find` returning nothing,
                // `JSON.parse` failures), `?` is the right sugar
                // because narrowing through `=== undefined` and `?.`
                // / `??` works cleanly. Disambiguates from the TS
                // object-property `x?: T` marker, which
                // `parse_object_type` consumes before this loop sees
                // it.
                self.pos += 1;
                ty = Type::union(vec![ty, Type::Undefined]);
            } else {
                break;
            }
        }

        Ok(ty)
    }

    /// Parse a primary type.
    fn parse_primary_type(&mut self) -> ParseResult<Type> {
        self.skip_whitespace();

        match self.peek_char() {
            Some('{') => self.parse_object_type(),
            Some('(') => {
                // Could be grouped type or function type
                self.parse_func_or_grouped()
            }
            Some('"') => self.parse_string_literal_type(),
            Some(c) if c.is_ascii_digit() || c == '-' => self.parse_number_literal_type(),
            Some(c) if self.is_ident_start(Some(c)) => {
                let ident = self.parse_ident()?;
                // JSDoc `typeof X` (TypeScript convention) resolves to
                // the *value* type of the binding `X` from the
                // enclosing scope, instantiated to a mono type. We
                // accept it as a leading-keyword primitive; if no
                // resolver was supplied (alias bodies, type aliases at
                // top-level), `typeof` is rejected with a hint instead
                // of silently degrading to a row property.
                if ident == "typeof" {
                    self.skip_whitespace();
                    let target = self.parse_ident()?;
                    return self.resolve_typeof(&target);
                }
                self.ident_to_type(&ident)
            }
            Some(c) => Err(self.error(format!("unexpected character '{}'", c))),
            None => Err(self.error("unexpected end of type annotation".to_string())),
        }
    }

    /// Resolve `typeof NAME` to the pre-instantiated type from the
    /// enclosing scope. Falls back to a parse error if no table was
    /// installed (alias-body or top-level annotation parsing) or
    /// `NAME` wasn't pre-resolved at the call site.
    fn resolve_typeof(&mut self, name: &str) -> ParseResult<Type> {
        let Some(table) = self.typeof_table else {
            return Err(self.error(
                "`typeof X` requires an enclosing inference scope — this position only supports \
                 alias-body type expressions"
                    .to_string(),
            ));
        };
        match table.get(name) {
            Some(ty) => Ok(ty.clone()),
            None => Err(self.error(format!(
                "`typeof {}`: '{}' is not a value in scope",
                name, name
            ))),
        }
    }

    /// Parse a string-literal type like `"circle"`. Supports basic escape
    /// sequences `\\`, `\"`, `\n`, `\t`. Other backslashed characters
    /// pass through as-is.
    fn parse_string_literal_type(&mut self) -> ParseResult<Type> {
        self.expect_char('"')?;
        let mut s = String::new();
        loop {
            match self.peek_char() {
                None => return Err(self.error("unterminated string literal type".to_string())),
                Some('"') => {
                    self.pos += 1;
                    return Ok(Type::Literal(LitValue::String(s)));
                }
                Some('\\') => {
                    self.pos += 1;
                    match self.peek_char() {
                        Some('"') => {
                            s.push('"');
                            self.pos += 1;
                        }
                        Some('\\') => {
                            s.push('\\');
                            self.pos += 1;
                        }
                        Some('n') => {
                            s.push('\n');
                            self.pos += 1;
                        }
                        Some('t') => {
                            s.push('\t');
                            self.pos += 1;
                        }
                        Some(c) => {
                            s.push(c);
                            self.pos += c.len_utf8();
                        }
                        None => {
                            return Err(self.error("dangling backslash in string literal".into()))
                        }
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
    }

    /// Parse a number-literal type like `42` or `-3.14`.
    fn parse_number_literal_type(&mut self) -> ParseResult<Type> {
        let start = self.pos;
        if self.peek_char() == Some('-') {
            self.pos += 1;
        }
        while matches!(self.peek_char(), Some('0'..='9')) {
            self.pos += 1;
        }
        if self.peek_char() == Some('.') {
            self.pos += 1;
            while matches!(self.peek_char(), Some('0'..='9')) {
                self.pos += 1;
            }
        }
        let text = &self.input[start..self.pos];
        let n: f64 = text
            .parse()
            .map_err(|_| self.error(format!("invalid number literal '{}'", text)))?;
        Ok(Type::Literal(LitValue::Number(n)))
    }

    /// Parse an object type like `{name: String, age: Number}`.
    fn parse_object_type(&mut self) -> ParseResult<Type> {
        self.expect_char('{')?;
        self.skip_whitespace();

        let mut props: Vec<(String, crate::types::FieldEntry)> = Vec::new();

        // Object property types inherit the current allow_quantifiers context:
        // - At top level: { fn: <T>(x: T) => T } is valid Rank-1
        // - Inside function param: (obj: { fn: <T>(x: T) => T }) => X is Rank-2 and rejected

        if self.peek_char() != Some('}') {
            loop {
                self.skip_whitespace();
                // Keyless call signature `(args) => ret` inside a row
                // body is the type-level form for callable rows (TS
                // `interface Foo { (a): R }`). Parse the function type
                // and store the bare `Type::Func` under the reserved
                // CALLABLE_KEY sentinel. `parse_simple_type` returns
                // an auto-wrapped callable row (`Row{<CALL>: Func}`)
                // because top-level `(args) => ret` is a value type;
                // here we need just the inner Func, so we unwrap the
                // single CALLABLE_KEY field. See
                // `examples/fizzy/design.md` § "Callable rows" and
                // `crates/inty/src/types/mod.rs:CALLABLE_KEY`.
                if self.peek_char() == Some('(') {
                    let wrapped = self.parse_simple_type()?;
                    let inner_func = match wrapped {
                        Type::Row(row)
                            if row.props.len() == 1
                                && row.props.contains_key(&crate::types::PropName(
                                    crate::types::CALLABLE_KEY.to_string(),
                                )) =>
                        {
                            row.props
                                .into_iter()
                                .next()
                                .expect("contains_key just asserted")
                                .1
                                .ty
                        }
                        // The constructor invariant says `Type::simple_func`
                        // and friends always produce the wrapped form; if a
                        // future change relaxes that, fall back to using
                        // the type as-is so this arm doesn't silently
                        // misbehave.
                        other => other,
                    };
                    props.push((
                        crate::types::CALLABLE_KEY.to_string(),
                        crate::types::FieldEntry::pre(inner_func),
                    ));
                    self.skip_whitespace();
                    if self.peek_char() == Some('}') {
                        break;
                    }
                    if self.peek_char() == Some(',') || self.peek_char() == Some(';') {
                        self.pos += 1;
                    } else {
                        return Err(self.error(format!(
                            "expected ',' or ';' between object-type properties"
                        )));
                    }
                    self.skip_whitespace();
                    if self.peek_char() == Some('}') {
                        break;
                    }
                    continue;
                }
                // `readonly` is a TS modifier with no semantic effect
                // under inty's structural typing — erase if present.
                if self.input[self.pos..].starts_with("readonly")
                    && !matches!(
                        self.input[self.pos + "readonly".len()..].chars().next(),
                        Some(c) if self.is_ident_cont(Some(c))
                    )
                {
                    self.pos += "readonly".len();
                    self.skip_whitespace();
                }
                let name = self.parse_ident()?;
                self.skip_whitespace();
                // Optional property `x?: T` allocates a fresh presence
                // variable on the field (Remy '94) — the caller may
                // omit it without forcing T | Undefined into the type.
                // See README "Optional row fields" once phase 1d ships.
                let optional = if self.peek_char() == Some('?') {
                    self.pos += 1;
                    self.skip_whitespace();
                    true
                } else {
                    false
                };
                self.expect_char(':')?;
                self.skip_whitespace();
                // Property types inherit the current allow_quantifiers context.
                // At top level, quantifiers are allowed: { fn: <T>(x: T) => T } is valid.
                // Inside function params, they're not: (obj: { fn: <T>(x: T) => T }) => X is Rank-2.
                let ty = self.parse_type()?;
                let entry = if optional {
                    let pvar = self.fresh_pvar();
                    crate::types::FieldEntry::optional(pvar, ty)
                } else {
                    crate::types::FieldEntry::pre(ty)
                };
                props.push((name, entry));

                self.skip_whitespace();
                if self.peek_char() == Some('}') {
                    break;
                }
                // Accept either `,` or `;` as separator — TS uses `;`,
                // inty traditionally uses `,`. Both are equivalent here.
                if self.peek_char() == Some(',') || self.peek_char() == Some(';') {
                    self.pos += 1;
                } else {
                    return Err(self.error(format!(
                        "expected ',' or ';' between object-type properties"
                    )));
                }
                self.skip_whitespace();
                // Trailing separator before `}` is allowed.
                if self.peek_char() == Some('}') {
                    break;
                }
            }
        }

        self.expect_char('}')?;

        Ok(Type::object_entries(props))
    }

    /// Convert an identifier to a type.
    fn ident_to_type(&mut self, ident: &str) -> ParseResult<Type> {
        // Unsupported TS constructs: rejected with a span-anchored
        // diagnostic that names the construct and the inty idiom
        // that replaces it.
        if let Some(suggestion) = unsupported_ts_alternative(ident) {
            return Err(self.error(format!(
                "type '{}' is not supported in inty. {}",
                ident, suggestion
            )));
        }

        match ident {
            "Number" | "number" => Ok(Type::Number),
            "String" | "string" => Ok(Type::String),
            "Boolean" | "boolean" => Ok(Type::Boolean),
            "Undefined" | "undefined" | "void" => Ok(Type::Undefined),
            "Null" | "null" => Ok(Type::Null),
            "Regex" => Ok(Type::Regex),
            "never" => Ok(Type::never()),
            "true" => Ok(Type::lit_bool(true)),
            "false" => Ok(Type::lit_bool(false)),
            "Promise" => {
                // `Promise<T>` — the inner type is required.
                self.skip_whitespace();
                if self.peek_char() != Some('<') {
                    return Err(self.error("expected '<T>' after 'Promise'".to_string()));
                }
                self.expect_char('<')?;
                self.skip_whitespace();
                let inner = self.parse_type()?;
                self.skip_whitespace();
                self.expect_char('>')?;
                Ok(Type::promise(inner))
            }
            _ => {
                // Alias application — `Foo` for a nullary alias or
                // `Foo<arg1, arg2, ...>` for a generic alias. A bare
                // identifier that *is* a registered alias must expand
                // (and arity-check), not silently degrade to a type
                // variable; otherwise a typo'd or unparameterised alias
                // would unify with anything.
                if let Some(aliases) = self.aliases {
                    if let Some(def) = aliases.get(ident).cloned() {
                        let saved_pos = self.pos;
                        self.skip_whitespace();
                        let has_arg_list = self.peek_char() == Some('<');

                        let mut args: Vec<Type> = Vec::new();
                        if has_arg_list {
                            self.expect_char('<')?;
                            self.skip_whitespace();
                            if self.peek_char() != Some('>') {
                                loop {
                                    self.skip_whitespace();
                                    let arg = self.parse_type()?;
                                    args.push(arg);
                                    self.skip_whitespace();
                                    if self.peek_char() == Some(',') {
                                        self.expect_char(',')?;
                                    } else {
                                        break;
                                    }
                                }
                            }
                            self.skip_whitespace();
                            self.expect_char('>')?;
                        } else {
                            // Restore position so the trailing context
                            // (e.g. `|`, `,`, `)`) is left for the
                            // caller's parser to consume.
                            self.pos = saved_pos;
                        }

                        if args.len() != def.params.len() {
                            return Err(self.error(format!(
                                "type alias '{}' expects {} type argument(s), got {}",
                                ident,
                                def.params.len(),
                                args.len()
                            )));
                        }

                        // Nominal alias: produce a branded reference
                        // `Type::Named(id, args)` rather than inlining
                        // the representation, so the type retains its
                        // identity through unification.
                        if let Some(id) = def.nominal_id {
                            return Ok(Type::Named(id, args));
                        }

                        // Structural alias: capture-avoiding
                        // substitution — clone the body and replace each
                        // parameter var with the corresponding argument
                        // type. For a nullary alias the subst is empty
                        // and the body is returned as-is.
                        let mut subst: HashMap<u32, Type> = HashMap::with_capacity(args.len());
                        for (p, a) in def.params.iter().zip(args.iter()) {
                            subst.insert(*p, a.clone());
                        }
                        return Ok(substitute_alias_body(&def.body, &subst));
                    }
                }

                // Check if it's a known type variable (bound by an
                // enclosing `<T>` quantifier or by an alias's parameter
                // list — see `preset_var` and `parse_generic_type`).
                if let Some(&var_id) = self.type_vars.get(ident) {
                    Ok(Type::flex(var_id))
                } else {
                    // Unknown identifier: not a primitive, not an alias,
                    // not a quantifier-bound parameter. Reject rather
                    // than silently inventing a fresh existential, so
                    // typos like `Stirng` and forgotten quantifiers
                    // surface as errors at the annotation site.
                    Err(self.error(format!(
                        "unknown type '{}' — declare it with `/** type {} = ... */` \
                         or bind it as a parameter (e.g. `<{}>(...) => ...`)",
                        ident, ident, ident
                    )))
                }
            }
        }
    }

    /// Parse an identifier.
    fn parse_ident(&mut self) -> ParseResult<String> {
        let start = self.pos;

        if !self.is_ident_start(self.peek_char()) {
            return Err(self.error("expected identifier".to_string()));
        }

        while self.is_ident_cont(self.peek_char()) {
            self.pos += 1;
        }

        Ok(self.input[start..self.pos].to_string())
    }

    /// Check if a character can start an identifier.
    fn is_ident_start(&self, c: Option<char>) -> bool {
        matches!(c, Some('a'..='z' | 'A'..='Z' | '_'))
    }

    /// Check if a character can continue an identifier.
    fn is_ident_cont(&self, c: Option<char>) -> bool {
        matches!(c, Some('a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
    }

    /// Skip whitespace.
    fn skip_whitespace(&mut self) {
        while matches!(self.peek_char(), Some(' ' | '\t' | '\n' | '\r')) {
            self.pos += 1;
        }
    }

    /// Peek at the current character.
    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    /// Peek at a character at an offset from current position.
    fn peek_char_at(&self, offset: usize) -> Option<char> {
        self.input[self.pos..].chars().nth(offset)
    }

    /// Get the current character.
    fn current_char(&self) -> Option<char> {
        self.peek_char()
    }

    /// Expect and consume a specific character.
    fn expect_char(&mut self, expected: char) -> ParseResult<()> {
        if self.peek_char() == Some(expected) {
            self.pos += expected.len_utf8();
            Ok(())
        } else {
            Err(self.error(format!(
                "expected '{}', found {:?}",
                expected,
                self.peek_char()
            )))
        }
    }

    /// Expect and consume a specific string.
    fn expect_str(&mut self, expected: &str) -> ParseResult<()> {
        if self.input[self.pos..].starts_with(expected) {
            self.pos += expected.len();
            Ok(())
        } else {
            Err(self.error(format!("expected '{}'", expected)))
        }
    }

    /// Create an error with the current span.
    fn error(&self, message: String) -> TypeError {
        TypeError::TypeAnnotationParse {
            message,
            span: self.span,
        }
    }
}

/// Parse a type annotation string.
///
/// Returns the parsed type, the variable-name map, and the next free
/// presence-variable ID consumed by the parser (so callers can bump
/// their own pvar source in lockstep — `x?: T` allocates one fresh
/// presence variable per optional field).
pub fn parse_type_annotation(
    content: &str,
    span: Span,
    start_var_id: u32,
) -> ParseResult<(Type, HashMap<String, u32>)> {
    let mut parser = TypeParser::new(content, span, start_var_id);
    let ty = parser.parse()?;
    Ok((ty, parser.type_vars.clone()))
}

/// Like [`parse_type_annotation`] but consults the supplied alias
/// env when it encounters `Foo<args>` for a user-defined alias.
pub fn parse_type_annotation_with_aliases(
    content: &str,
    span: Span,
    start_var_id: u32,
    aliases: &HashMap<String, AliasDef>,
) -> ParseResult<(Type, HashMap<String, u32>)> {
    let mut parser = TypeParser::with_aliases(content, span, start_var_id, aliases);
    let ty = parser.parse()?;
    Ok((ty, parser.type_vars.clone()))
}

/// As [`parse_type_annotation_with_aliases`] but also accepts a
/// pvar-id seed and returns the next free pvar id, so the caller can
/// keep its own pvar counter in sync with the parser's allocations.
pub fn parse_type_annotation_with_pvars(
    content: &str,
    span: Span,
    start_var_id: u32,
    start_pvar_id: u32,
    aliases: &HashMap<String, AliasDef>,
) -> ParseResult<(Type, HashMap<String, u32>, u32)> {
    let mut parser = TypeParser::with_aliases(content, span, start_var_id, aliases);
    parser.seed_pvar_id(start_pvar_id);
    let ty = parser.parse()?;
    Ok((ty, parser.type_vars.clone(), parser.next_pvar_id_value()))
}

/// As [`parse_type_annotation_with_pvars`] but also installs a
/// [`TypeOfTable`] so the annotation can reference the surrounding
/// scope through `typeof Name`. The caller pre-instantiates each
/// `typeof` reference (allocating fresh IDs from its own counter,
/// which it advances accordingly before calling this function). The
/// table is consulted directly by the parser. Returns the parsed
/// type, the type-variable map, and the next free pvar id so the
/// caller can keep its pvar counter in sync.
pub fn parse_type_annotation_with_typeof(
    content: &str,
    span: Span,
    start_var_id: u32,
    start_pvar_id: u32,
    aliases: &HashMap<String, AliasDef>,
    typeof_table: &TypeOfTable,
) -> ParseResult<(Type, HashMap<String, u32>, u32)> {
    let mut parser =
        TypeParser::with_aliases(content, span, start_var_id, aliases).with_typeof(typeof_table);
    parser.seed_pvar_id(start_pvar_id);
    let ty = parser.parse()?;
    Ok((ty, parser.type_vars.clone(), parser.next_pvar_id_value()))
}

/// Map a rejected TS-style type name to a suggested inty
/// alternative. Returns `None` if the identifier isn't a known
/// TS-only construct — caller falls through to the regular type-
/// variable / alias-application paths.
fn unsupported_ts_alternative(ident: &str) -> Option<&'static str> {
    match ident {
        "any" => Some(
            "Help: use a concrete type, or a closed union of the values you actually accept.",
        ),
        "unknown" => Some(
            "Help: same as `any` — the parser cannot model an opaque \"any value\" without subtyping.",
        ),
        // `never` is supported as the empty union; not rejected.
        _ => None,
    }
}

/// Capture-avoiding substitution against an alias body. Walks a
/// `Type` cloning structure and replaces every flex variable whose
/// id is a key in `subst` with the corresponding type. Other type
/// variables are left alone — alias parameters use the dedicated
/// IDs the alias was registered with, so collisions are impossible.
pub(crate) fn substitute_alias_body(ty: &Type, subst: &HashMap<u32, Type>) -> Type {
    use crate::types::{RowTail, RowType, TVarName};
    match ty {
        Type::Var(TVarName::Flex(id)) => {
            if let Some(replacement) = subst.get(id) {
                replacement.clone()
            } else {
                ty.clone()
            }
        }
        Type::Var(_) => ty.clone(),
        Type::Number
        | Type::String
        | Type::Boolean
        | Type::Undefined
        | Type::Null
        | Type::Regex
        | Type::Literal(_)
        | Type::Error => ty.clone(),
        Type::Array(elem) => Type::array(substitute_alias_body(elem, subst)),
        Type::Map(value) => Type::Map(Box::new(substitute_alias_body(value, subst))),
        Type::Promise(inner) => Type::promise(substitute_alias_body(inner, subst)),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| substitute_alias_body(e, subst))
                .collect(),
        ),
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type
                .as_ref()
                .map(|t| Box::new(substitute_alias_body(t, subst))),
            params: params
                .iter()
                .map(|p| crate::types::FuncParam {
                    presence: p.presence.clone(),
                    ty: substitute_alias_body(&p.ty, subst),
                    name: p.name.clone(),
                })
                .collect(),
            ret: Box::new(substitute_alias_body(ret, subst)),
        },
        Type::Union(members) => {
            Type::union(members.iter().map(|m| substitute_alias_body(m, subst)))
        }
        Type::Row(row) => {
            let new_props: std::collections::BTreeMap<_, _> = row
                .props
                .iter()
                .map(|(k, e)| {
                    (
                        k.clone(),
                        crate::types::FieldEntry {
                            presence: e.presence.clone(),
                            ty: substitute_alias_body(&e.ty, subst),
                        },
                    )
                })
                .collect();
            let new_tail = match &row.tail {
                RowTail::Closed => RowTail::Closed,
                RowTail::Open(v) => RowTail::Open(v.clone()),
                RowTail::Recursive(id, args) => RowTail::Recursive(
                    *id,
                    args.iter()
                        .map(|a| substitute_alias_body(a, subst))
                        .collect(),
                ),
            };
            Type::Row(RowType {
                props: new_props,
                tail: new_tail,
            })
        }
        Type::Named(id, args) => Type::Named(
            *id,
            args.iter()
                .map(|a| substitute_alias_body(a, subst))
                .collect(),
        ),
        Type::Module(_) => ty.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Type {
        parse_type_annotation(s, Span::new(0, s.len()), 1000)
            .unwrap()
            .0
    }

    #[test]
    fn test_parse_primitives() {
        assert_eq!(parse("Number"), Type::Number);
        assert_eq!(parse("String"), Type::String);
        assert_eq!(parse("Boolean"), Type::Boolean);
        assert_eq!(parse("undefined"), Type::Undefined);
        assert_eq!(parse("null"), Type::Null);
    }

    #[test]
    fn test_parse_array() {
        assert_eq!(parse("Number[]"), Type::array(Type::Number));
        assert_eq!(parse("String[][]"), Type::array(Type::array(Type::String)));
    }

    #[test]
    fn test_parse_simple_function() {
        let ty = parse("() => Number");
        assert_eq!(ty, Type::simple_func(vec![], Type::Number));
    }

    #[test]
    fn test_parse_function_with_params() {
        let ty = parse("(a: Number, b: String) => Boolean");
        assert_eq!(
            ty,
            Type::simple_func(vec![Type::Number, Type::String], Type::Boolean)
        );
    }

    #[test]
    fn test_parse_function_without_param_names() {
        let ty = parse("(Number, String) => Boolean");
        assert_eq!(
            ty,
            Type::simple_func(vec![Type::Number, Type::String], Type::Boolean)
        );
    }

    /// Shape B: `name?: T` allocates a fresh presence variable on
    /// that parameter so the formal accepts both a 1-arg and a
    /// 2-arg call.
    #[test]
    fn parses_optional_named_param() {
        let ty = parse("(start: Number, end?: Number) => String");
        // Drill into the callable row's `<CALL>` field to inspect
        // the bare Type::Func.
        let (_, params, ret) = ty.as_callable().expect("callable shape");
        assert_eq!(params.len(), 2);
        assert!(matches!(params[0].presence, crate::types::Presence::Pre));
        assert!(
            matches!(params[1].presence, crate::types::Presence::Var(_)),
            "second param should be presence-polymorphic, got {:?}",
            params[1].presence
        );
        assert_eq!(params[0].ty, Type::Number);
        assert_eq!(params[1].ty, Type::Number);
        assert_eq!(*ret, Type::String);
    }

    /// Without the `?`, params stay required even with names.
    #[test]
    fn parses_required_named_params() {
        let ty = parse("(start: Number, end: Number) => String");
        let (_, params, _) = ty.as_callable().expect("callable shape");
        assert!(matches!(params[0].presence, crate::types::Presence::Pre));
        assert!(matches!(params[1].presence, crate::types::Presence::Pre));
    }

    /// Optional-then-required is rejected at parse time via the
    /// dedicated `OptionalParameterFollowedByRequired` variant —
    /// matches TypeScript ts(1016). Tests both the leading-
    /// optional case and the optional-in-the-middle case.
    #[test]
    fn rejects_required_after_optional() {
        let src = "(a?: Number, b: Number) => String";
        let err = parse_type_annotation(src, Span::new(0, src.len()), 1000).unwrap_err();
        match err {
            crate::error::TypeError::OptionalParameterFollowedByRequired {
                optional_idx,
                required_idx,
                ..
            } => {
                assert_eq!(optional_idx, 0);
                assert_eq!(required_idx, 1);
            }
            other => panic!(
                "expected OptionalParameterFollowedByRequired, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn rejects_required_after_optional_middle() {
        let src = "(a: Number, b?: Number, c: Number) => String";
        let err = parse_type_annotation(src, Span::new(0, src.len()), 1000).unwrap_err();
        match err {
            crate::error::TypeError::OptionalParameterFollowedByRequired {
                optional_idx,
                required_idx,
                ..
            } => {
                assert_eq!(optional_idx, 1);
                assert_eq!(required_idx, 2);
            }
            other => panic!(
                "expected OptionalParameterFollowedByRequired, got: {:?}",
                other
            ),
        }
    }

    /// Multiple trailing optionals are fine — the canonical case
    /// for stdlib decls like `replace(pattern, replacement, limit?)`.
    #[test]
    fn accepts_multiple_trailing_optionals() {
        let ty = parse("(a: Number, b?: Number, c?: Number) => String");
        let (_, params, _) = ty.as_callable().expect("callable shape");
        assert!(matches!(params[0].presence, crate::types::Presence::Pre));
        assert!(matches!(params[1].presence, crate::types::Presence::Var(_)));
        assert!(matches!(params[2].presence, crate::types::Presence::Var(_)));
    }

    #[test]
    fn test_parse_generic_function() {
        let (ty, vars) = parse_type_annotation("<T>(x: T) => T", Span::new(0, 14), 1000).unwrap();
        let t_id = vars["T"];
        assert_eq!(
            ty,
            Type::simple_func(vec![Type::flex(t_id)], Type::flex(t_id))
        );
    }

    #[test]
    fn test_parse_object_type() {
        let ty = parse("{name: String, age: Number}");
        match ty {
            Type::Row(row) => {
                assert_eq!(row.props.len(), 2);
            }
            _ => panic!("expected row type"),
        }
    }

    #[test]
    fn test_parse_nested_function() {
        let ty = parse("(f: (x: Number) => String) => Boolean");
        // Top-level `(args) => ret` parses as a callable row.
        let (_, params, ret) = ty.as_callable().expect("expected callable type");
        assert_eq!(params.len(), 1);
        assert!(
            params[0].ty.as_callable().is_some(),
            "nested function param should also be callable"
        );
        assert_eq!(*ret, Type::Boolean);
    }

    #[test]
    fn test_rank1_restriction_in_param() {
        // Higher-rank type: <A>(f: <T>(x: T) => T, a: A) => A
        // This should fail because <T> is nested inside a parameter
        let result =
            parse_type_annotation("<A>(f: <T>(x: T) => T, a: A) => A", Span::new(0, 33), 1000);
        match result {
            Err(TypeError::Rank1Restriction { .. }) => {} // Expected
            Err(e) => panic!("Expected Rank1Restriction error, got: {:?}", e),
            Ok(_) => panic!("Should reject higher-rank type in parameter position"),
        }
    }

    #[test]
    fn test_rank1_restriction_in_return() {
        // Higher-rank type in return position: (x: Number) => <T>(y: T) => T
        // This should also fail
        let result = parse_type_annotation("(x: Number) => <T>(y: T) => T", Span::new(0, 29), 1000);
        match result {
            Err(TypeError::Rank1Restriction { .. }) => {} // Expected
            Err(e) => panic!("Expected Rank1Restriction error, got: {:?}", e),
            Ok(_) => panic!("Should reject higher-rank type in return position"),
        }
    }

    #[test]
    fn test_rank1_allowed_in_object_at_top_level() {
        // Polymorphic function in object property at TOP LEVEL: { fn: <T>(x: T) => T }
        // This IS allowed because the quantifier is at the top level of the type.
        let result = parse_type_annotation("{ fn: <T>(x: T) => T }", Span::new(0, 22), 1000);
        assert!(
            result.is_ok(),
            "Should allow polymorphic function in object property at top level"
        );
    }

    #[test]
    fn test_rank1_rejected_in_object_param() {
        // Polymorphic function in object property INSIDE FUNCTION PARAM:
        // (obj: { fn: <T>(x: T) => T }) => Number
        // This is Rank-2 and should be rejected.
        let input = "(obj: { fn: <T>(x: T) => T }) => Number";
        let result = parse_type_annotation(input, Span::new(0, input.len()), 1000);
        match result {
            Err(TypeError::Rank1Restriction { .. }) => {} // Expected
            Err(e) => panic!("Expected Rank1Restriction error, got: {:?}", e),
            Ok(_) => panic!("Should reject polymorphic object property in function parameter"),
        }
    }

    #[test]
    fn test_rank1_allowed_at_top_level() {
        // Rank-1 polymorphic function: <T>(x: T) => T
        // This should succeed
        let result = parse_type_annotation("<T>(x: T) => T", Span::new(0, 14), 1000);
        assert!(result.is_ok(), "Should allow type parameters at top level");
    }

    #[test]
    fn test_rank1_multiple_params() {
        // Multiple type parameters: <A, B>(f: (a: A) => B, x: A) => B
        // This should succeed - type params at top level, no nested quantifiers
        let result =
            parse_type_annotation("<A, B>(f: (a: A) => B, x: A) => B", Span::new(0, 33), 1000);
        assert!(
            result.is_ok(),
            "Should allow multiple type parameters at top level"
        );
    }

    #[test]
    fn test_parse_array_of_functions() {
        let ty = parse("((x: Number) => String)[]");
        match ty {
            Type::Array(elem) => {
                assert!(
                    elem.as_callable().is_some(),
                    "element should be a callable type (Row{{<CALL>: …}})"
                );
            }
            _ => panic!("expected array type"),
        }
    }

    /// Check if two types are structurally equal, ignoring type variable IDs.
    /// Returns a mapping of variable IDs if equal, None if not.
    fn types_structurally_equal(
        t1: &Type,
        t2: &Type,
        var_map: &mut std::collections::HashMap<u32, u32>,
    ) -> bool {
        use crate::types::TVarName;

        match (t1, t2) {
            (Type::Number, Type::Number) => true,
            (Type::String, Type::String) => true,
            (Type::Boolean, Type::Boolean) => true,
            (Type::Undefined, Type::Undefined) => true,
            (Type::Null, Type::Null) => true,
            (Type::Regex, Type::Regex) => true,

            (Type::Var(TVarName::Flex(id1)), Type::Var(TVarName::Flex(id2))) => {
                if let Some(&mapped) = var_map.get(id1) {
                    mapped == *id2
                } else {
                    var_map.insert(*id1, *id2);
                    true
                }
            }

            (Type::Array(e1), Type::Array(e2)) => types_structurally_equal(e1, e2, var_map),

            (Type::Promise(i1), Type::Promise(i2)) => types_structurally_equal(i1, i2, var_map),

            (Type::Map(v1), Type::Map(v2)) => types_structurally_equal(v1, v2, var_map),

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
                if p1.len() != p2.len() {
                    return false;
                }
                // Compare this_type (both None, or both Some with equal types)
                let this_eq = match (t1, t2) {
                    (None, None) => true,
                    (Some(a), Some(b)) => types_structurally_equal(a, b, var_map),
                    _ => false,
                };
                this_eq
                    && p1.iter().zip(p2.iter()).all(|(a, b)| {
                        a.presence == b.presence && types_structurally_equal(&a.ty, &b.ty, var_map)
                    })
                    && types_structurally_equal(r1, r2, var_map)
            }

            (Type::Row(r1), Type::Row(r2)) => {
                if r1.props.len() != r2.props.len() {
                    return false;
                }
                r1.props
                    .iter()
                    .zip(r2.props.iter())
                    .all(|((k1, e1), (k2, e2))| {
                        k1 == k2 && types_structurally_equal(&e1.ty, &e2.ty, var_map)
                    })
            }

            _ => false,
        }
    }

    fn assert_round_trip(ty: &Type) {
        let printed = ty.to_string();
        let parsed = parse(&printed);
        let mut var_map = std::collections::HashMap::new();
        assert!(
            types_structurally_equal(ty, &parsed, &mut var_map),
            "Round-trip failed:\nOriginal: {:?}\nPrinted: {}\nParsed: {:?}",
            ty,
            printed,
            parsed
        );
    }

    #[test]
    fn test_round_trip_primitives() {
        assert_round_trip(&Type::Number);
        assert_round_trip(&Type::String);
        assert_round_trip(&Type::Boolean);
        assert_round_trip(&Type::Undefined);
        assert_round_trip(&Type::Null);
    }

    #[test]
    fn test_round_trip_arrays() {
        assert_round_trip(&Type::array(Type::Number));
        assert_round_trip(&Type::array(Type::array(Type::String)));
        assert_round_trip(&Type::array(Type::simple_func(
            vec![Type::Number],
            Type::String,
        )));
    }

    #[test]
    fn test_round_trip_functions() {
        assert_round_trip(&Type::simple_func(vec![], Type::Number));
        assert_round_trip(&Type::simple_func(vec![Type::Number], Type::String));
        assert_round_trip(&Type::simple_func(
            vec![Type::Number, Type::String],
            Type::Boolean,
        ));
        // Nested function
        assert_round_trip(&Type::simple_func(
            vec![Type::simple_func(vec![Type::Number], Type::String)],
            Type::Boolean,
        ));
    }

    #[test]
    fn test_round_trip_objects() {
        assert_round_trip(&Type::object([("x", Type::Number)]));
        assert_round_trip(&Type::object([
            ("name", Type::String),
            ("age", Type::Number),
        ]));
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    /// Generate arbitrary types for property testing.
    fn arb_type() -> impl Strategy<Value = Type> {
        let leaf = prop_oneof![
            Just(Type::Number),
            Just(Type::String),
            Just(Type::Boolean),
            Just(Type::Undefined),
            Just(Type::Null),
        ];

        leaf.prop_recursive(
            3,  // depth
            64, // max nodes
            10, // items per collection
            |inner| {
                prop_oneof![
                    // Arrays
                    inner.clone().prop_map(|t| Type::array(t)),
                    // Simple functions (no this type)
                    (prop::collection::vec(inner.clone(), 0..3), inner.clone())
                        .prop_map(|(params, ret)| Type::simple_func(params, ret)),
                    // Objects with string keys
                    prop::collection::vec(("[a-z]{1,4}", inner.clone()), 0..3)
                        .prop_map(|props| Type::object(props)),
                ]
            },
        )
    }

    /// Check structural equality (ignoring type variable IDs).
    fn types_equal(t1: &Type, t2: &Type) -> bool {
        let mut var_map = std::collections::HashMap::new();
        types_structurally_equal(t1, t2, &mut var_map)
    }

    /// Check if two types are structurally equal, ignoring type variable IDs.
    fn types_structurally_equal(
        t1: &Type,
        t2: &Type,
        var_map: &mut std::collections::HashMap<u32, u32>,
    ) -> bool {
        use crate::types::TVarName;

        match (t1, t2) {
            (Type::Number, Type::Number) => true,
            (Type::String, Type::String) => true,
            (Type::Boolean, Type::Boolean) => true,
            (Type::Undefined, Type::Undefined) => true,
            (Type::Null, Type::Null) => true,
            (Type::Regex, Type::Regex) => true,

            (Type::Var(TVarName::Flex(id1)), Type::Var(TVarName::Flex(id2))) => {
                if let Some(&mapped) = var_map.get(id1) {
                    mapped == *id2
                } else {
                    var_map.insert(*id1, *id2);
                    true
                }
            }

            (Type::Array(e1), Type::Array(e2)) => types_structurally_equal(e1, e2, var_map),

            (Type::Promise(i1), Type::Promise(i2)) => types_structurally_equal(i1, i2, var_map),

            (Type::Map(v1), Type::Map(v2)) => types_structurally_equal(v1, v2, var_map),

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
                if p1.len() != p2.len() {
                    return false;
                }
                // Compare this_type (both None, or both Some with equal types)
                let this_eq = match (t1, t2) {
                    (None, None) => true,
                    (Some(a), Some(b)) => types_structurally_equal(a, b, var_map),
                    _ => false,
                };
                this_eq
                    && p1.iter().zip(p2.iter()).all(|(a, b)| {
                        a.presence == b.presence && types_structurally_equal(&a.ty, &b.ty, var_map)
                    })
                    && types_structurally_equal(r1, r2, var_map)
            }

            (Type::Row(r1), Type::Row(r2)) => {
                if r1.props.len() != r2.props.len() {
                    return false;
                }
                r1.props
                    .iter()
                    .zip(r2.props.iter())
                    .all(|((k1, e1), (k2, e2))| {
                        k1 == k2 && types_structurally_equal(&e1.ty, &e2.ty, var_map)
                    })
            }

            _ => false,
        }
    }

    proptest! {
        #[test]
        fn prop_round_trip(ty in arb_type()) {
            let printed = ty.to_string();
            let parsed = parse_type_annotation(&printed, Span::new(0, printed.len()), 1000);

            match parsed {
                Ok((parsed_ty, _)) => {
                    prop_assert!(
                        types_equal(&ty, &parsed_ty),
                        "Round-trip failed:\nOriginal: {:?}\nPrinted: {}\nParsed: {:?}",
                        ty,
                        printed,
                        parsed_ty
                    );
                }
                Err(e) => {
                    prop_assert!(false, "Parse failed for '{}': {:?}", printed, e);
                }
            }
        }
    }
}
