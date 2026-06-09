//! Object literals, member access, and row polymorphism.

use std::collections::{BTreeMap, HashMap};

use crate::ast::{AnnotationKind, Expr, Literal, PropDef, PropKey};
use crate::span::Span;
use crate::types::{FieldEntry, PropName, RowTail, RowType, TVarId, TVarName, Type, TypeScheme};

use super::super::env::TypeEnv;
use super::super::state::InferState;
use super::super::type_parser::{parse_type_annotation_with_typeof, TypeOfTable};
use super::super::InferResult;

/// Render a [`TypeError`] from the annotation parser as a short
/// warning message. We keep just the human-readable text; the span
/// is supplied separately when the warning is logged.
fn format_parse_error(e: &crate::error::TypeError) -> String {
    use crate::error::TypeError;
    match e {
        TypeError::TypeAnnotationParse { message, .. } => message.clone(),
        other => format!("{}", other),
    }
}

/// Scan a type-annotation content string for `typeof IDENT` references
/// and return the bare identifiers in source order. Whitespace-only
/// matches and identifiers that appear inside string-literal type
/// expressions are accepted as false positives — they don't cause
/// harm (we'd attempt a lookup, find nothing, and the parser would
/// error at parse time, which is the desired behaviour).
///
/// JSDoc / TS convention requires `typeof` as a keyword preceding the
/// identifier with at least one whitespace separator. We match that
/// shape so `typeofKey: T` (a row property literally named `typeofKey`)
/// doesn't false-positive.
fn collect_typeof_names(content: &str) -> Vec<String> {
    let bytes = content.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i + 6 < bytes.len() {
        if &bytes[i..i + 6] != b"typeof" {
            i += 1;
            continue;
        }
        let prefix_ok = i == 0
            || matches!(
                bytes[i - 1],
                b' ' | b'\t' | b'\n' | b'\r' | b'(' | b',' | b'|' | b'<' | b'{'
            );
        let after = bytes[i + 6];
        let suffix_ok = matches!(after, b' ' | b'\t' | b'\n' | b'\r');
        if !prefix_ok || !suffix_ok {
            i += 6;
            continue;
        }
        let mut j = i + 6;
        while j < bytes.len() && matches!(bytes[j], b' ' | b'\t' | b'\n' | b'\r') {
            j += 1;
        }
        let id_start = j;
        while j < bytes.len()
            && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_' || bytes[j] == b'$')
        {
            j += 1;
        }
        if j > id_start {
            out.push(content[id_start..j].to_string());
        }
        i = j.max(i + 6);
    }
    out
}

impl InferState {
    /// Pre-instantiate every `typeof X` reference found in `content`
    /// into a lookup table the type parser consults at parse time.
    /// Identifiers absent from `env` are silently skipped — the parser
    /// will then produce a clean `is not a value in scope` error
    /// pointing at the annotation span (better than failing in the
    /// scanner where we have less context).
    pub(in crate::infer) fn build_typeof_table(
        &mut self,
        env: &TypeEnv,
        content: &str,
    ) -> TypeOfTable {
        let mut table: TypeOfTable = HashMap::new();
        for name in collect_typeof_names(content) {
            if table.contains_key(&name) {
                continue;
            }
            if let Some(scheme) = env.lookup(&name).cloned() {
                let ty = self.instantiate(&scheme);
                table.insert(name, ty);
            }
        }
        table
    }

    /// Infer the type of an object literal.
    ///
    /// Properties are walked in source order. Object spreads
    /// (`...expr`) merge the spread argument's row in right-bias
    /// fashion: keys later in source order overwrite earlier ones.
    /// Per spec, the result row's tail is the tail of the last
    /// spread operand if that tail is a row variable; otherwise the
    /// row is closed.
    pub(in crate::infer) fn infer_object(
        &mut self,
        env: &TypeEnv,
        properties: &[PropDef],
        span: Span,
    ) -> InferResult<Type> {
        // Create a shared 'this' type for all methods in this object
        // This ensures that when one method's 'this' is unified with the object type,
        // all methods are connected, avoiding infinite types during method chaining.
        let shared_this = self.fresh_type_var();

        let mut props: BTreeMap<PropName, FieldEntry> = BTreeMap::new();
        let mut row_tail: RowTail = RowTail::Closed;
        // True if any spread was processed — even a closed-row spread
        // counts; the result is closed but `row_tail` may have been
        // set and then overridden back to Closed.
        let mut had_spread = false;

        for prop in properties {
            match prop {
                PropDef::Property {
                    key,
                    value,
                    type_annotation,
                    type_ast,
                    span: prop_span,
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    let value_type = self.infer_expr(env, value)?;
                    // IR-channel annotation (Python `field: T`): lower the
                    // shared `TypeAst` to a `Type` through the canonical
                    // bridge — the same path params and method returns use
                    // — then unify the initialiser against it. An
                    // annotation-only field is seeded with a placeholder
                    // initialiser (`undefined`); in that case the
                    // declaration alone types the field and the
                    // placeholder is not checked, mirroring the JSDoc
                    // `@type` + placeholder convention below.
                    if let Some(ast) = type_ast {
                        let ann_span = Span::new(prop_span.start, prop_span.end);
                        let annotated = self.lower_type_ast_in_env_with_span(ast, env, ann_span);
                        let is_placeholder = matches!(
                            value,
                            Expr::Lit {
                                value: Literal::Null | Literal::Undefined,
                                ..
                            }
                        );
                        if !is_placeholder {
                            // Annotation first so the message reads
                            // "expected <annotated>, found <value>".
                            self.subsume(ann_span, &value_type, &annotated)?;
                        }
                        let prop_type = self.zonk(&annotated);
                        // A field declared more than once in the same class
                        // body (e.g. `bar: int` and `bar: str`) must agree:
                        // unify the declarations rather than letting the
                        // last one silently win. Only same-key Python field
                        // declarations carry a `type_ast`, so this can't
                        // disturb JS object-literal duplicate semantics.
                        if let Some(existing) = props.get(&prop_name) {
                            let existing_ty = existing.ty.clone();
                            self.unify(ann_span, &existing_ty, &prop_type)?;
                        }
                        props.insert(prop_name, FieldEntry::pre(prop_type));
                        continue;
                    }
                    // If the property carries an inline annotation, parse
                    // it and unify with the value's inferred type so the
                    // annotation is enforced the same way a variable
                    // declaration's annotation is.
                    let prop_type = if let Some(ann) = type_annotation {
                        let ann_span = Span::new(ann.span.start, ann.span.end);
                        // Pre-instantiate any `typeof X` references so
                        // the parser sees a flat lookup table; saves
                        // threading `&mut InferState` into the parser.
                        let typeof_table = self.build_typeof_table(env, &ann.content);
                        let parse_result = parse_type_annotation_with_typeof(
                            &ann.content,
                            ann_span,
                            self.next_var_id(),
                            self.next_pvar_id(),
                            &self.type_aliases,
                            &typeof_table,
                        );
                        let is_jsdoc = ann.kind == AnnotationKind::JsDoc;
                        let (annotated_type, var_map, next_pvar) = match parse_result {
                            Ok(triple) => triple,
                            Err(e) if is_jsdoc => {
                                // JSDoc annotations are best-effort hints
                                // (TypeScript ignores unrecognised JSDoc
                                // tags); a `@type` that references a
                                // TypeScript-only alias inty doesn't
                                // model shouldn't fail the whole field.
                                // Surface the parse failure as a
                                // non-fatal warning and fall back to the
                                // value's synthesised type.
                                self.warn(
                                    ann_span,
                                    format!(
                                        "ignoring `@type` annotation: {}",
                                        format_parse_error(&e)
                                    ),
                                );
                                let inferred = value_type.widen_fresh_literals();
                                props.insert(prop_name, FieldEntry::pre(inferred));
                                continue;
                            }
                            Err(e) => return Err(e.into()),
                        };
                        self.bump_pvar_id_to(next_pvar);
                        if let Some(&max) = var_map.values().max() {
                            self.bump_var_id_to(max + 1);
                        }
                        // TypeScript's JSDoc convention is to allow a
                        // `null` / `undefined` placeholder initialiser
                        // for a `@type`-annotated field — the field is
                        // declared *as if* it were the annotated type
                        // and filled in by later assignment, exactly
                        // the htmx public-API pattern. We mirror that:
                        // when the source-side syntax is `@type` and
                        // the value is a literal placeholder, skip the
                        // subsume check. Inline `/*: T */` annotations
                        // and non-placeholder values still check
                        // normally so honest mismatches surface.
                        let is_placeholder = matches!(
                            value,
                            Expr::Lit {
                                value: Literal::Null | Literal::Undefined,
                                ..
                            }
                        );
                        if !(is_jsdoc && is_placeholder) {
                            // Annotation first: it's what the user wrote,
                            // so the error message reads as "expected
                            // <annotated>, found <value>".
                            self.subsume(ann_span, &value_type, &annotated_type)?;
                        }
                        self.zonk(&annotated_type)
                    } else {
                        // Synthesis-mode object literal: widen primitive
                        // singleton field values so e.g. `{value: 0}`
                        // synthesises as `{value: Number}`. Without this,
                        // mutation through methods (`this.value = v`)
                        // would be pinned to the initial literal. The
                        // bidirectional path (`check_object` from
                        // `infer_call`) bypasses this widening so a
                        // tagged-union argument like `{kind: "circle"}`
                        // keeps its singleton field — that's what makes
                        // discriminated unions work at call sites.
                        value_type.widen_fresh_literals()
                    };
                    props.insert(prop_name, FieldEntry::pre(prop_type));
                }

                PropDef::Method {
                    key,
                    params,
                    body,
                    return_type_ast,
                    span: method_span,
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Infer method with the shared 'this' type. A Python
                    // method's `-> T` return annotation (if any) is checked
                    // here too.
                    let method_type = self.infer_function_with_this(
                        env,
                        None,
                        params,
                        body,
                        &None,
                        return_type_ast.as_ref(),
                        shared_this.clone(),
                        *method_span,
                    )?;
                    props.insert(prop_name, FieldEntry::pre(method_type));
                }

                PropDef::Getter { key, body, span } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Bind `this` in the getter body to the shared
                    // instance row so `this.foo` references see the
                    // surrounding object's fields (same trick as
                    // methods, but the getter's value type is just
                    // the body's return type — there's no callable
                    // wrapper). Inferred through a `return`-collection
                    // frame so the getter's `return`s don't leak into an
                    // enclosing function's return type.
                    let getter_env =
                        env.extend("this".to_string(), TypeScheme::mono(shared_this.clone()));
                    let ret_type = self.infer_body_return_type(&getter_env, body, true, *span)?;
                    props.insert(prop_name, FieldEntry::pre(ret_type));
                }

                PropDef::Setter {
                    key,
                    param,
                    body,
                    span,
                } => {
                    let prop_name = self.prop_key_to_name(key);
                    // Setter: param type is fresh, body returns undefined.
                    // Inferred through a frame (return value discarded) so
                    // any `return` doesn't leak upward.
                    let param_type = self.fresh_type_var();
                    let setter_env = env.extend(param.clone(), TypeScheme::mono(param_type));
                    let _ = self.infer_body_return_type(&setter_env, body, true, *span)?;
                    // For simplicity, we use the parameter type as the property type
                    // In a full implementation, we'd track getter/setter separately
                    props.insert(prop_name, FieldEntry::pre(self.fresh_type_var()));
                }

                PropDef::Spread {
                    argument,
                    span: spread_span,
                } => {
                    had_spread = true;
                    let arg_ty = self.infer_expr(env, argument)?;
                    let resolved = self.zonk(&arg_ty);
                    let spread_row = self.coerce_to_row(&resolved, *spread_span)?;
                    // Right-biased merge: this spread's properties
                    // overwrite anything earlier — including the
                    // result of an earlier spread or property.
                    for (k, v) in spread_row.props {
                        props.insert(k, v);
                    }
                    // Per spec: "the result row's tail is the tail
                    // of the last spread operand if it's a row
                    // variable." A `Closed` tail flips the result
                    // back to closed; an `Open(α)` tail makes the
                    // result open at `α` (any later spread overwrites).
                    row_tail = spread_row.tail;
                }
            }
        }

        let final_row = match row_tail {
            RowTail::Open(var) => RowType::open_entries(props, var),
            // Closed and Recursive both produce a closed row at the
            // surface — Recursive doesn't arise from a fresh row
            // var introduced by spread inference, but if a user
            // spreads a recursive-typed value the result is still
            // soundly closed for the keys we know about.
            _ => RowType::closed_entries(props),
        };
        let obj_type = Type::Row(final_row);

        // Unify the shared 'this' with the complete object type so
        // method bodies that mention `this.foo` see the correct
        // row. This is the equi-recursive bit.
        self.unify(span, &shared_this, &obj_type)?;

        let _ = had_spread;
        Ok(self.zonk(&obj_type))
    }

    /// Bidirectional checking for an object literal against an
    /// expected row (or union of rows). Returns `Ok(Some(ty))` when
    /// the contextual rule applies, `Ok(None)` when the caller
    /// should fall back to plain synthesis (e.g. expected is a fresh
    /// var, a primitive, or anything other than a row/union of
    /// rows). Errors are real type errors and propagate.
    ///
    /// The "checking" specifically means: each property value is
    /// checked against the expected per-field type (`check_expr`),
    /// not synthesised then subsumed. This propagates singleton
    /// literal types into property values that the synthesis path
    /// (`infer_object`) would have widened.
    ///
    /// Limitations: only handles plain `PropDef::Property` entries.
    /// Methods, getters, setters, and spreads bail to the synthesis
    /// fallback — if the user wants those, they'll go through the
    /// synthesis-mode widening rule.
    pub(in crate::infer) fn try_check_object(
        &mut self,
        env: &TypeEnv,
        properties: &[PropDef],
        span: Span,
        expected: &Type,
    ) -> InferResult<Option<Type>> {
        // Distribute over a union: pick the unique arm whose row
        // shape (key set) matches the literal's keys exactly.
        if let Type::Union(members) = expected {
            let lit_keys: std::collections::BTreeSet<PropName> = properties
                .iter()
                .filter_map(|p| match p {
                    PropDef::Property { key, .. }
                    | PropDef::Method { key, .. }
                    | PropDef::Getter { key, .. }
                    | PropDef::Setter { key, .. } => Some(self.prop_key_to_name(key)),
                    PropDef::Spread { .. } => None,
                })
                .collect();
            let mut chosen: Option<Type> = None;
            let mut count = 0;
            for m in members {
                let m_resolved = self.zonk(m);
                if let Type::Row(row) = &m_resolved {
                    if row.is_closed()
                        && row
                            .props
                            .keys()
                            .cloned()
                            .collect::<std::collections::BTreeSet<_>>()
                            == lit_keys
                    {
                        count += 1;
                        if count == 1 {
                            chosen = Some(m_resolved.clone());
                        } else {
                            // Multiple shape-matching arms — defer
                            // to synthesis, where S-UnionR with the
                            // exactly-one disambiguator can sort it
                            // out (or fail loudly).
                            return Ok(None);
                        }
                    }
                }
            }
            if let Some(arm) = chosen {
                return self.try_check_object(env, properties, span, &arm);
            }
            return Ok(None);
        }

        // Single row case: push expected per-field types into each
        // property value. Bail to synthesis on any complexity we
        // don't model (methods, spreads, missing/extra keys).
        let expected_row = match expected {
            Type::Row(r) if r.is_closed() => r,
            _ => return Ok(None),
        };

        let mut props: BTreeMap<PropName, Type> = BTreeMap::new();
        for prop in properties {
            match prop {
                PropDef::Property {
                    key,
                    value,
                    type_annotation,
                    type_ast,
                    ..
                } => {
                    // An IR-channel field annotation (Python `field: T`)
                    // isn't modelled on this bidirectional path; defer to
                    // synthesis (`infer_object`), which lowers and unifies
                    // it. In practice such fields only arise inside class
                    // factories, which synthesise their row anyway.
                    if type_ast.is_some() {
                        return Ok(None);
                    }
                    let prop_name = self.prop_key_to_name(key);
                    let Some(expected_prop_ty) =
                        expected_row.props.get(&prop_name).map(|e| e.ty.clone())
                    else {
                        // Extra key not in expected row — let
                        // synthesis fall through and produce its own
                        // closed-row mismatch error.
                        return Ok(None);
                    };
                    if let Some(ann) = type_annotation {
                        // An inline annotation overrides the
                        // contextual expected — we still check the
                        // value against the user-stated type, with
                        // the same JSDoc-placeholder relaxation as
                        // the synthesis arm (see `infer_object`).
                        let ann_span = Span::new(ann.span.start, ann.span.end);
                        let typeof_table = self.build_typeof_table(env, &ann.content);
                        let is_jsdoc = ann.kind == AnnotationKind::JsDoc;
                        let parse_result = parse_type_annotation_with_typeof(
                            &ann.content,
                            ann_span,
                            self.next_var_id(),
                            self.next_pvar_id(),
                            &self.type_aliases,
                            &typeof_table,
                        );
                        let (annotated_type, var_map, next_pvar) = match parse_result {
                            Ok(triple) => triple,
                            Err(e) if is_jsdoc => {
                                self.warn(
                                    ann_span,
                                    format!(
                                        "ignoring `@type` annotation: {}",
                                        format_parse_error(&e)
                                    ),
                                );
                                let value_type = self.check_expr(env, value, &expected_prop_ty)?;
                                props.insert(prop_name, value_type);
                                continue;
                            }
                            Err(e) => return Err(e.into()),
                        };
                        self.bump_pvar_id_to(next_pvar);
                        if let Some(&max) = var_map.values().max() {
                            self.bump_var_id_to(max + 1);
                        }
                        let is_placeholder = matches!(
                            value,
                            Expr::Lit {
                                value: Literal::Null | Literal::Undefined,
                                ..
                            }
                        );
                        if is_jsdoc && is_placeholder {
                            // Skip the inner check — placeholder accepts.
                            self.subsume(ann_span, &annotated_type, &expected_prop_ty)?;
                        } else {
                            let value_type = self.check_expr(env, value, &annotated_type)?;
                            self.subsume(ann_span, &value_type, &expected_prop_ty)?;
                        }
                        props.insert(prop_name, self.zonk(&annotated_type));
                    } else {
                        let value_type = self.check_expr(env, value, &expected_prop_ty)?;
                        props.insert(prop_name, value_type);
                    }
                }
                _ => {
                    // Methods/getters/setters/spreads: synthesis
                    // fallback knows how to handle them; we don't
                    // (yet) push contextual types into method
                    // bodies.
                    return Ok(None);
                }
            }
        }

        // Make sure every expected key is present (closed row
        // matching). Missing keys are a hard error here — we've
        // already committed to checking-mode for the visible props.
        if expected_row.props.keys().any(|k| !props.contains_key(k)) {
            return Ok(None); // synthesis will produce the right error
        }

        let result = Type::Row(crate::types::RowType::closed(props));
        // Final sanity check against the expected row — any
        // outstanding constraints (e.g. from row-tail variables)
        // resolve here.
        self.subsume(span, &result, expected)?;
        Ok(Some(self.zonk(&result)))
    }

    /// Infer `Expr::RestRow { source, excluded }` — the synthetic
    /// node emitted when desugaring `const {a, ...rest} = obj`. The
    /// source's type must be a row (or a free variable, in which
    /// case we pin it to a row). The result is that row with
    /// `excluded` keys removed; the tail (open or closed) is
    /// preserved so a row variable still carries "the rest of the
    /// caller's row" through.
    pub(in crate::infer) fn infer_rest_row(
        &mut self,
        env: &TypeEnv,
        source: &Expr,
        excluded: &[String],
        span: Span,
    ) -> InferResult<Type> {
        let source_ty = self.infer_expr(env, source)?;
        let row = self.coerce_to_row(&source_ty, span)?;
        let mut new_props = row.props.clone();
        for key in excluded {
            new_props.remove(&PropName(key.clone()));
        }
        let new_row = RowType {
            props: new_props,
            tail: row.tail,
        };
        Ok(Type::Row(new_row))
    }

    /// Resolve a type that's expected to be a row (because an
    /// object spread or destructuring rest is operating on it).
    /// If the type is already a row, return it unchanged. If it's
    /// a free type variable, unify it with a fresh open row.
    /// Otherwise reject with a span-anchored diagnostic.
    fn coerce_to_row(&mut self, ty: &Type, span: Span) -> InferResult<RowType> {
        let resolved = self.zonk(ty);
        match resolved {
            Type::Row(row) => Ok(row),
            Type::Var(_) => {
                // Open row of unknown shape; pin the type variable
                // to a fresh open row so it can be merged in.
                let row_var = self.fresh_tvar_name();
                let row = RowType::empty_open(row_var);
                let row_ty = Type::Row(row.clone());
                self.unify(span, &resolved, &row_ty)?;
                Ok(row)
            }
            other => Err(crate::error::TypeError::TypeMismatch {
                expected: format!("{}", Type::Row(RowType::empty_closed())),
                found: format!("{}", other),
                span,
            }
            .into()),
        }
    }

    /// Generate a fresh row-tail variable name. Mirrors the bare
    /// type-var helper but flagged as a row variable through its
    /// usage in `RowTail::Open`.
    fn fresh_tvar_name(&mut self) -> TVarName {
        TVarName::Flex(self.next_var_id())
    }

    /// Convert a property key to a property name.
    fn prop_key_to_name(&self, key: &PropKey) -> PropName {
        match key {
            PropKey::Ident(s) => PropName(s.clone()),
            PropKey::String(s) => PropName(s.clone()),
            PropKey::Number(n) => PropName(n.to_string()),
        }
    }

    /// Infer the type of a member access (obj.prop).
    pub(in crate::infer) fn infer_member(
        &mut self,
        env: &TypeEnv,
        object: &Expr,
        property: &str,
        span: Span,
    ) -> InferResult<Type> {
        let obj_type = self.infer_expr(env, object)?;
        let obj_type = self.zonk(&obj_type);
        self.infer_member_on_type(&obj_type, property, span)
    }

    /// Look up a property on a (substituted) object type. Used by
    /// `infer_member` after evaluating the object expression, by
    /// optional-chain handling for each segment, by call-expression
    /// handling to extract the method type without re-inferring the
    /// receiver, and recursively for union elimination.
    pub(in crate::infer) fn infer_member_on_type(
        &mut self,
        obj_type: &Type,
        property: &str,
        span: Span,
    ) -> InferResult<Type> {
        // Error sentinel propagates through member access. A binding
        // that already failed produces `Type::Error`; any `.foo` /
        // `.bar` reached from it is also `Error`, so subsequent uses
        // don't generate noise.
        if matches!(obj_type, Type::Error) {
            let _ = property;
            let _ = span;
            return Ok(Type::Error);
        }

        // Singleton literal types are values of their base type — every
        // operation defined on `String` is defined on `Lit("hi")`.
        // Route property lookups through the base so e.g.
        // `"hello".length` works after `infer_literal` started
        // synthesising singletons.
        if let Type::Literal(lit) = obj_type {
            return self.infer_member_on_type(&lit.base_type(), property, span);
        }

        // Union elimination: read the property from every member and
        // join the results. Fails if any member lacks the property at
        // a compatible type. This is the load-bearing rule that lets
        // users *do* something with a union after they've formed one.
        if let Type::Union(members) = obj_type {
            let mut result: Option<Type> = None;
            for m in members {
                let m_resolved = self.zonk(m);
                let prop_ty = self.infer_member_on_type(&m_resolved, property, span)?;
                result = Some(match result {
                    None => prop_ty,
                    Some(acc) => self.join(span, &acc, &prop_ty),
                });
            }
            // The empty union (`never`) can be accessed at any property
            // — it's unreachable. Synthesise `never` for the result.
            return Ok(result.unwrap_or_else(Type::never));
        }

        // Built-in prototype methods on primitive carriers. Each match
        // arm returns a fresh function type; polymorphic methods bind
        // their type variables when the surrounding call unifies.
        use crate::ast::SourceLanguage;
        let language = self.language;
        match obj_type {
            Type::Array(elem_ty) => {
                if property == "length" {
                    return Ok(Type::Number);
                }
                // The primitive-method surface is language-specific: Python
                // `list` vs JavaScript `Array` (issue #67). Lua has no
                // method-call surface on sequences (yet).
                let method = match language {
                    SourceLanguage::Python => {
                        crate::builtins::python_list_method_type(self, elem_ty, property)
                    }
                    SourceLanguage::JavaScript => {
                        crate::builtins::array_method_type(self, elem_ty, property)
                    }
                    SourceLanguage::Lua => None,
                };
                if let Some(ty) = method {
                    return Ok(ty);
                }
            }
            Type::String => {
                if property == "length" {
                    return Ok(Type::Number);
                }
                let method = match language {
                    SourceLanguage::Python => {
                        crate::builtins::python_string_method_type(self, property)
                    }
                    SourceLanguage::JavaScript => {
                        crate::builtins::string_method_type(self, property)
                    }
                    SourceLanguage::Lua => None,
                };
                if let Some(ty) = method {
                    return Ok(ty);
                }
            }
            Type::Promise(inner_ty) => {
                if let Some(ty) = crate::builtins::promise_method_type(self, inner_ty, property) {
                    return Ok(ty);
                }
            }
            Type::Regex => {
                // Regex.prototype methods. `test` is a Boolean
                // predicate; `match`/`exec` would return
                // `match-info | Null` in JS, but inty has no nullable
                // types — for now we type them optimistically (assume a
                // match), letting downstream code that checks
                // `=== null` fail to narrow.
                if let Some(ty) = crate::builtins::regex_method_type(self, property) {
                    return Ok(ty);
                }
            }
            Type::Row(row) => {
                // Direct hit in the row's own props is the common case
                // and avoids creating unnecessary type variables.
                if let Some(entry) = row.props.get(&PropName(property.to_string())) {
                    // Property access demands presence: unify the
                    // field's presence with `Pre`. If the entry was
                    // presence-polymorphic the variable gets pinned;
                    // if it was already `Abs` we get a structured
                    // presence-mismatch error.
                    self.unify_presence(span, &entry.presence, &crate::types::Presence::Pre)?;
                    return Ok(self.zonk(&entry.ty));
                }
                // Otherwise the property may live in a row reached
                // through the tail (e.g., a flex tail bound by an
                // earlier unification to another row).
                if let Some(prop_type) = self.lookup_property_in_row_tail(row, property) {
                    return Ok(self.zonk(&prop_type));
                }
                // If property still not found and row is closed, the
                // unification fall-through below will report it.
            }
            Type::Module(m) => {
                if let Some(scheme) = m.exports.get(property) {
                    let ty = self.instantiate(scheme);
                    return Ok(self.zonk(&ty));
                }
                return Err(crate::error::TypeError::Module {
                    message: format!("module {:?} has no export named {:?}", m.source, property),
                    span,
                }
                .into());
            }
            // Nominal types have brand identity but *transparent* field
            // access: unroll to the representation (e.g. a class's
            // instance row) and read the property from there. The value's
            // type stays nominal everywhere else — only this read sees
            // through. Equi-recursive named types are intentionally left
            // to the row-constraint fall-through below, which already
            // handles them by unrolling during unification.
            Type::Named(id, args) if self.is_nominal_type(*id) => {
                if let Some(unrolled) = self.unroll_named(*id, args) {
                    return self.infer_member_on_type(&unrolled, property, span);
                }
            }
            _ => {}
        }

        // Fall through (type variables, open rows that don't yet name
        // the property, etc.): pose the property access as a row
        // constraint and let unification resolve it.
        let result_type = self.fresh_type_var();

        if let Type::Var(var) = &result_type {
            self.record_origin(
                var.clone(),
                crate::error::TypeOrigin::PropertyAccess {
                    property: property.to_string(),
                    span,
                },
            );
        }

        let row_var = self.fresh_flex();
        let expected_row = Type::object_open([(property, result_type.clone())], row_var);

        self.unify(span, obj_type, &expected_row)?;

        Ok(self.zonk(&result_type))
    }

    /// Look up a property by following row tail chains.
    /// Returns the property type if found in any row that the tail resolves to.
    fn lookup_property_in_row_tail(&self, row: &RowType, property: &str) -> Option<Type> {
        use std::collections::HashSet;
        let prop_name = PropName(property.to_string());
        let mut visited: HashSet<TVarId> = HashSet::new();
        let mut current_tail = &row.tail;

        loop {
            match current_tail {
                RowTail::Closed => return None,
                RowTail::Open(TVarName::Flex(id)) => {
                    // Avoid infinite loops
                    if visited.contains(id) {
                        return None;
                    }
                    visited.insert(*id);

                    // Look up what this variable is bound to
                    if let Some(ty) = self.main_subst.get(&TVarName::Flex(*id)) {
                        match ty {
                            Type::Row(tail_row) => {
                                // Check if property is in this row
                                if let Some(entry) = tail_row.props.get(&prop_name) {
                                    return Some(entry.ty.clone());
                                }
                                // Continue with this row's tail
                                current_tail = &tail_row.tail;
                            }
                            Type::Var(TVarName::Flex(next_id)) => {
                                // The variable is bound to another variable, follow it
                                if visited.contains(next_id) {
                                    return None;
                                }
                                visited.insert(*next_id);
                                if let Some(next_ty) =
                                    self.main_subst.get(&TVarName::Flex(*next_id))
                                {
                                    if let Type::Row(tail_row) = next_ty {
                                        if let Some(entry) = tail_row.props.get(&prop_name) {
                                            return Some(entry.ty.clone());
                                        }
                                        current_tail = &tail_row.tail;
                                        continue;
                                    }
                                }
                                return None;
                            }
                            _ => return None,
                        }
                    } else {
                        return None;
                    }
                }
                RowTail::Open(TVarName::Skolem(_)) => return None,
                RowTail::Recursive(_, _) => return None,
            }
        }
    }
}
