//! Mapping from inty types to Go types.
//!
//! | inty                         | Go                                  |
//! | ---------------------------- | ----------------------------------- |
//! | `Number`, fractional literals | `float64`                          |
//! | `Int`, integral literals     | `int` (checked against ±2^53)       |
//! | `String`, string literals    | `string`                            |
//! | `Boolean`, boolean literals  | `bool`                              |
//! | `T[]`                        | `*[]T` (JS arrays are references)   |
//! | closed row `{a: A, b: B}`    | `*ObjN` — one struct per row shape  |
//! | callable row `(A) => R`      | `func(A) R`                         |
//! | `T \| null`, `T \| undefined` | `T` when `T` is a pointer (`nil`)   |
//!
//! Struct identity is structural, like the row types it comes from: two
//! rows with the same field names and field types share one Go struct.
//! Equi-recursive (`Named`) types get a struct keyed by their id so the
//! Go type can refer to itself through a pointer.

use std::collections::{BTreeMap, HashMap};

use inty::infer::InferState;
use inty::span::Span;
use inty::types::{
    is_callable_key, FieldEntry, FuncParam, Presence, RowTail, RowType, TVarName, Type, TypeId,
};

use crate::{unsupported, Result};

/// A resolved Go type, with enough structure for the emitter to pick
/// the right translation of operators and methods.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GoType {
    Float,
    /// An inty `Int`: Go `int` (64 bits).
    Int,
    Str,
    Bool,
    /// JS `undefined` as a value type — only legal as a function
    /// result, where it becomes "no result".
    Unit,
    /// `*[]T`.
    Array(Box<GoType>),
    /// `*ObjN`, by index into [`TypeMapper::structs`].
    Struct(usize),
    Func(Vec<GoType>, Box<GoType>),
    /// A type variable nothing constrained (e.g. an array that is never
    /// read). Any Go type would do; `any` keeps it honest.
    Any,
}

impl GoType {
    /// Pointer-like types have `nil`, so `T | null` can reuse them.
    pub fn is_nullable(&self) -> bool {
        matches!(
            self,
            GoType::Array(_) | GoType::Struct(_) | GoType::Func(..) | GoType::Any
        )
    }
}

pub struct GoStruct {
    pub name: String,
    /// `(js name, go field name, type)`, sorted by JS name.
    pub fields: Vec<(String, String, GoType)>,
}

#[derive(Default)]
pub struct TypeMapper {
    pub structs: Vec<GoStruct>,
    by_shape: HashMap<Vec<(String, GoType)>, usize>,
    by_named: HashMap<TypeId, usize>,
}

impl TypeMapper {
    /// Map a (flattened, fully substituted) inty type to a Go type.
    pub fn map(&mut self, state: &mut InferState, ty: &Type, span: Span) -> Result<GoType> {
        self.map_depth(state, ty, span, 0)
    }

    fn map_depth(
        &mut self,
        state: &mut InferState,
        ty: &Type,
        span: Span,
        depth: usize,
    ) -> Result<GoType> {
        if depth > 64 {
            return Err(unsupported(
                "deeply nested or unguarded recursive type",
                span,
            ));
        }
        let d = depth + 1;
        Ok(match ty {
            Type::Number => GoType::Float,
            Type::Int => GoType::Int,
            Type::String => GoType::Str,
            Type::Boolean => GoType::Bool,
            Type::Undefined => GoType::Unit,
            Type::Literal(lit) => match lit {
                inty::types::LitValue::Number(n) if is_int(*n) => GoType::Int,
                inty::types::LitValue::Number(_) => GoType::Float,
                inty::types::LitValue::String(_) => GoType::Str,
                inty::types::LitValue::Bool(_) => GoType::Bool,
            },
            Type::Var(_) => GoType::Any,
            Type::Array(elem) => GoType::Array(Box::new(self.map_depth(state, elem, span, d)?)),
            Type::Func { params, ret, .. } => self.map_func(state, params, ret, span, d)?,
            Type::Row(row) => {
                if let Some((_, params, ret)) = ty.as_callable() {
                    let extra = row
                        .props
                        .iter()
                        .any(|(k, f)| !is_callable_key(k) && !f.presence.is_abs());
                    if extra {
                        return Err(unsupported(
                            format!(
                                "function value carrying extra properties (`{}`)",
                                pretty(ty)
                            ),
                            span,
                        ));
                    }
                    return self.map_func(state, params, ret, span, d);
                }
                self.map_row(state, row, None, span, d)?
            }
            Type::Named(id, args) => {
                if let Some(&idx) = self.by_named.get(id) {
                    return Ok(GoType::Struct(idx));
                }
                let body = state
                    .unroll_named(*id, args)
                    .ok_or_else(|| unsupported("unknown named type", span))?;
                let body = resolve(state, &body);
                match &body {
                    Type::Row(row) if body.as_callable().is_none() => {
                        self.map_row(state, row, Some(*id), span, d)?
                    }
                    other => self.map_depth(state, other, span, d)?,
                }
            }
            Type::Union(members) => {
                let non_null: Vec<&Type> = members
                    .iter()
                    .filter(|m| !matches!(m, Type::Null | Type::Undefined))
                    .collect();
                let has_null = non_null.len() != members.len();
                let mut mapped = Vec::new();
                for m in &non_null {
                    let g = self.map_depth(state, m, span, d)?;
                    if !mapped.contains(&g) {
                        mapped.push(g);
                    }
                }
                match mapped.as_slice() {
                    [single] if !has_null || single.is_nullable() => single.clone(),
                    _ => return Err(unsupported(format!("union type `{}`", pretty(ty)), span)),
                }
            }
            Type::Null => GoType::Any,
            Type::Error => return Err(unsupported("ill-typed expression", span)),
            other => {
                return Err(unsupported(format!("type `{}`", pretty(other)), span));
            }
        })
    }

    fn map_func(
        &mut self,
        state: &mut InferState,
        params: &[inty::types::FuncParam],
        ret: &Type,
        span: Span,
        d: usize,
    ) -> Result<GoType> {
        let mut ps = Vec::new();
        for p in params {
            if !p.presence.is_pre() {
                if matches!(p.presence, Presence::Abs) {
                    continue;
                }
                return Err(unsupported("optional function parameter", span));
            }
            ps.push(self.map_depth(state, &p.ty, span, d)?);
        }
        let r = self.map_depth(state, ret, span, d)?;
        Ok(GoType::Func(ps, Box::new(r)))
    }

    fn map_row(
        &mut self,
        state: &mut InferState,
        row: &RowType,
        named: Option<TypeId>,
        span: Span,
        d: usize,
    ) -> Result<GoType> {
        // A recursive tail contributes the named type's fields.
        let mut props: Vec<(String, Type)> = Vec::new();
        for (k, f) in &row.props {
            if is_callable_key(k) || f.presence.is_abs() {
                continue;
            }
            if k.0.starts_with('\u{2}') {
                return Err(unsupported("private class field", span));
            }
            props.push((k.0.clone(), f.ty.clone()));
        }
        if let RowTail::Recursive(id, args) = &row.tail {
            if let Some(Type::Row(inner)) =
                state.unroll_named(*id, args).map(|t| resolve(state, &t))
            {
                for (k, f) in &inner.props {
                    if !is_callable_key(k)
                        && !f.presence.is_abs()
                        && !props.iter().any(|(n, _)| n == &k.0)
                    {
                        props.push((k.0.clone(), f.ty.clone()));
                    }
                }
            }
        }
        props.sort_by(|a, b| a.0.cmp(&b.0));

        // A recursive (named) type reserves its slot before mapping the
        // fields so self-references resolve to it. Plain rows can't
        // refer to themselves, so their fields are mapped first and the
        // shape deduplicated against earlier structs.
        let reserved = named.map(|id| {
            let idx = self.structs.len();
            self.structs.push(GoStruct {
                name: format!("Obj{}", idx + 1),
                fields: Vec::new(),
            });
            self.by_named.insert(id, idx);
            idx
        });
        let mut fields = Vec::new();
        for (name, ty) in &props {
            let g = self.map_depth(state, ty, span, d)?;
            fields.push((name.clone(), field_name(name), g));
        }
        let shape: Vec<(String, GoType)> = fields
            .iter()
            .map(|(n, _, t)| (n.clone(), t.clone()))
            .collect();
        let idx = match reserved {
            Some(idx) => idx,
            None => {
                if let Some(&existing) = self.by_shape.get(&shape) {
                    return Ok(GoType::Struct(existing));
                }
                let idx = self.structs.len();
                self.structs.push(GoStruct {
                    name: format!("Obj{}", idx + 1),
                    fields: Vec::new(),
                });
                idx
            }
        };
        self.by_shape.entry(shape).or_insert(idx);
        self.structs[idx].fields = fields;
        Ok(GoType::Struct(idx))
    }

    /// Render a Go type.
    pub fn render(&self, ty: &GoType) -> String {
        match ty {
            GoType::Float => "float64".into(),
            GoType::Int => "int".into(),
            GoType::Str => "string".into(),
            GoType::Bool => "bool".into(),
            GoType::Unit => "struct{}".into(),
            GoType::Any => "any".into(),
            GoType::Array(e) => format!("*[]{}", self.render(e)),
            GoType::Struct(i) => format!("*{}", self.structs[*i].name),
            GoType::Func(ps, r) => {
                format!("func({}){}", self.render_list(ps), self.render_result(r))
            }
        }
    }

    pub fn render_list(&self, tys: &[GoType]) -> String {
        tys.iter()
            .map(|t| self.render(t))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Result clause of a func signature: empty for `Unit`.
    pub fn render_result(&self, ty: &GoType) -> String {
        match ty {
            GoType::Unit => String::new(),
            t => format!(" {}", self.render(t)),
        }
    }

    /// The Go struct declarations for every row shape seen.
    pub fn render_structs(&self) -> String {
        let mut out = String::new();
        for s in &self.structs {
            let js: Vec<&str> = s.fields.iter().map(|(n, _, _)| n.as_str()).collect();
            out.push_str(&format!(
                "// {} is the JS object shape {{{}}}.\n",
                s.name,
                js.join(", ")
            ));
            out.push_str(&format!("type {} struct {{\n", s.name));
            for (_, go, ty) in &s.fields {
                out.push_str(&format!("\t{} {}\n", go, self.render(ty)));
            }
            out.push_str("}\n\n");
        }
        out
    }

    pub fn field(&self, idx: usize, js_name: &str) -> Option<&(String, String, GoType)> {
        self.structs[idx]
            .fields
            .iter()
            .find(|(n, _, _)| n == js_name)
    }
}

/// Fully apply inty's final substitution to `ty`: resolve every bound
/// variable (at any depth) and merge row tails bound to rows into the
/// row's own fields. `InferState::zonk` does the former and
/// `flatten_type` the latter, but neither does both everywhere.
pub fn resolve(state: &mut InferState, ty: &Type) -> Type {
    resolve_depth(state, ty, 0)
}

fn resolve_depth(state: &mut InferState, ty: &Type, depth: usize) -> Type {
    if depth > 256 {
        return ty.clone();
    }
    let d = depth + 1;
    match ty {
        Type::Var(_) => {
            let z = state.zonk(ty);
            if &z == ty {
                z
            } else {
                resolve_depth(state, &z, d)
            }
        }
        Type::Row(row) => {
            let mut props = BTreeMap::new();
            for (k, f) in &row.props {
                props.insert(
                    k.clone(),
                    FieldEntry {
                        presence: f.presence.clone(),
                        ty: resolve_depth(state, &f.ty, d),
                    },
                );
            }
            let mut tail = row.tail.clone();
            for _ in 0..256 {
                let RowTail::Open(v) = &tail else { break };
                match state.zonk(&Type::Var(v.clone())) {
                    Type::Row(more) => {
                        for (k, f) in &more.props {
                            if !props.contains_key(k) {
                                let t = resolve_depth(state, &f.ty, d);
                                props.insert(
                                    k.clone(),
                                    FieldEntry {
                                        presence: f.presence.clone(),
                                        ty: t,
                                    },
                                );
                            }
                        }
                        tail = more.tail.clone();
                    }
                    Type::Var(v2) if &v2 != v => tail = RowTail::Open(v2),
                    _ => break,
                }
            }
            if let RowTail::Recursive(id, args) = &tail {
                let args = args.iter().map(|a| resolve_depth(state, a, d)).collect();
                tail = RowTail::Recursive(*id, args);
            }
            Type::Row(RowType { props, tail })
        }
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type
                .as_ref()
                .map(|t| Box::new(resolve_depth(state, t, d))),
            params: params
                .iter()
                .map(|p| FuncParam {
                    presence: p.presence.clone(),
                    ty: resolve_depth(state, &p.ty, d),
                    name: p.name.clone(),
                })
                .collect(),
            ret: Box::new(resolve_depth(state, ret, d)),
        },
        Type::Array(e) => Type::Array(Box::new(resolve_depth(state, e, d))),
        Type::Map(e) => Type::Map(Box::new(resolve_depth(state, e, d))),
        Type::Promise(e) => Type::Promise(Box::new(resolve_depth(state, e, d))),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| resolve_depth(state, t, d)).collect()),
        Type::Named(id, args) => Type::Named(
            *id,
            args.iter().map(|t| resolve_depth(state, t, d)).collect(),
        ),
        Type::Union(ts) => Type::union(
            ts.iter()
                .map(|t| resolve_depth(state, t, d))
                .collect::<Vec<_>>(),
        ),
        other => other.clone(),
    }
}

/// A monomorphisation substitution: quantified type variable → the
/// concrete type it stands for in one specialisation.
pub type Mapping = HashMap<TVarName, Type>;

/// Stand-in for a type variable nothing constrained. Specialisation keys
/// and mappings use it so that two otherwise-identical instantiations
/// that differ only in *which* fresh unbound variable they carry share
/// one specialisation. It maps to Go `any`.
pub fn unconstrained() -> Type {
    Type::Var(TVarName::Flex(u32::MAX))
}

/// Substitute `m` into an already-resolved type, merging row tails whose
/// variable maps to a row (as `resolve` does for the final substitution).
pub fn apply_mapping(ty: &Type, m: &Mapping) -> Type {
    if m.is_empty() {
        return ty.clone();
    }
    match ty {
        Type::Var(v) => m.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Type::Row(row) => {
            let mut props: BTreeMap<_, _> = row
                .props
                .iter()
                .map(|(k, f)| {
                    (
                        k.clone(),
                        FieldEntry {
                            presence: f.presence.clone(),
                            ty: apply_mapping(&f.ty, m),
                        },
                    )
                })
                .collect();
            let mut tail = match &row.tail {
                RowTail::Recursive(id, args) => {
                    RowTail::Recursive(*id, args.iter().map(|a| apply_mapping(a, m)).collect())
                }
                t => t.clone(),
            };
            for _ in 0..256 {
                let RowTail::Open(v) = &tail else { break };
                match m.get(v) {
                    Some(Type::Row(more)) => {
                        for (k, f) in &more.props {
                            props.entry(k.clone()).or_insert_with(|| f.clone());
                        }
                        tail = more.tail.clone();
                    }
                    Some(Type::Var(w)) if w != v => tail = RowTail::Open(w.clone()),
                    _ => break,
                }
            }
            Type::Row(RowType { props, tail })
        }
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type.as_ref().map(|t| Box::new(apply_mapping(t, m))),
            params: params
                .iter()
                .map(|p| FuncParam {
                    presence: p.presence.clone(),
                    ty: apply_mapping(&p.ty, m),
                    name: p.name.clone(),
                })
                .collect(),
            ret: Box::new(apply_mapping(ret, m)),
        },
        Type::Array(e) => Type::Array(Box::new(apply_mapping(e, m))),
        Type::Map(e) => Type::Map(Box::new(apply_mapping(e, m))),
        Type::Promise(e) => Type::Promise(Box::new(apply_mapping(e, m))),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| apply_mapping(t, m)).collect()),
        Type::Named(id, args) => {
            Type::Named(*id, args.iter().map(|t| apply_mapping(t, m)).collect())
        }
        Type::Union(ts) => Type::union(ts.iter().map(|t| apply_mapping(t, m)).collect::<Vec<_>>()),
        other => other.clone(),
    }
}

/// Normal form for an instantiation type: literal types widen to their
/// base type and unbound variables become [`unconstrained`], so that
/// equal Go types give equal specialisation keys.
pub fn canonical(ty: &Type) -> Type {
    let unconstrained_names: Mapping = ty
        .free_vars()
        .into_iter()
        .map(|v| (v, unconstrained()))
        .collect();
    widen(&apply_mapping(ty, &unconstrained_names))
}

fn widen(ty: &Type) -> Type {
    match ty {
        Type::Literal(inty::types::LitValue::Number(n)) if is_int(*n) => Type::Int,
        Type::Literal(inty::types::LitValue::Number(_)) => Type::Number,
        Type::Literal(inty::types::LitValue::String(_)) => Type::String,
        Type::Literal(inty::types::LitValue::Bool(_)) => Type::Boolean,
        Type::Row(row) => Type::Row(RowType {
            props: row
                .props
                .iter()
                .map(|(k, f)| {
                    (
                        k.clone(),
                        FieldEntry {
                            presence: f.presence.clone(),
                            ty: widen(&f.ty),
                        },
                    )
                })
                .collect(),
            tail: row.tail.clone(),
        }),
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type.as_ref().map(|t| Box::new(widen(t))),
            params: params
                .iter()
                .map(|p| FuncParam {
                    presence: p.presence.clone(),
                    ty: widen(&p.ty),
                    name: p.name.clone(),
                })
                .collect(),
            ret: Box::new(widen(ret)),
        },
        Type::Array(e) => Type::Array(Box::new(widen(e))),
        Type::Map(e) => Type::Map(Box::new(widen(e))),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(widen).collect()),
        Type::Named(id, args) => Type::Named(*id, args.iter().map(widen).collect()),
        Type::Union(ts) => Type::union(ts.iter().map(widen).collect::<Vec<_>>()),
        other => other.clone(),
    }
}

/// Whether a number literal is an `Int`.
pub fn is_int(n: f64) -> bool {
    inty::types::is_safe_int(n)
}

/// Go field name for a JS property. Keywords get a trailing underscore;
/// characters Go identifiers can't hold are hex-escaped.
pub fn field_name(js: &str) -> String {
    crate::emit::mangle(js)
}

fn pretty(ty: &Type) -> String {
    format!("{}", ty)
}
