//! One-step (and recursive) evaluation for the typed subset.
//!
//! This is *not* a JS engine. It implements just enough operational
//! behaviour to give the typing rules something to be consistent with:
//! literals, lambdas/application, let/const/var, control flow, binops,
//! unops, object & array literals + indexing, sequences, template
//! literals, throw/try, simple loops.
//!
//! Reduction is structured as recursive `eval_expr` / `eval_stmt`
//! functions over the parser AST. A single `step` consumes one
//! statement of a program; `run_to_end` drives `step` to completion.
//! Fuel is decremented on every loop iteration and every recursion
//! into a `Block`-like form so non-terminating typed programs raise
//! `Stuck::FuelExhausted` cleanly.

use std::collections::BTreeMap;

use crate::parser::ast::{
    AssignOp, BinOp, Expr, ForInLhs, ForInit, Literal, PropDef, PropKey, Stmt, UnaryOp,
};
use crate::types::PropName;

use super::env::RuntimeEnv;
use super::heap::{Cell, Heap, Loc};
use super::value::{Closure, Value};

/// Reasons reduction is stuck. A stuck typed term is a soundness
/// violation; phase 5 turns these into useful failure reports.
#[derive(Clone, Debug)]
pub enum Stuck {
    UndefinedVariable(String),
    NotCallable(&'static str),
    NotIndexable(&'static str),
    PropertyNotFound { kind: &'static str, property: String },
    TypeMismatch { op: &'static str, expected: &'static str, got: &'static str },
    ArityMismatch { expected: usize, got: usize },
    BadAssignmentTarget,
    NotImplemented(&'static str),
    /// An uncaught `throw`. The payload is the thrown value.
    UncaughtThrow(Value),
    FuelExhausted,
}

impl std::fmt::Display for Stuck {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stuck::UndefinedVariable(n) => write!(f, "undefined variable `{}`", n),
            Stuck::NotCallable(k) => write!(f, "not callable: {}", k),
            Stuck::NotIndexable(k) => write!(f, "not indexable: {}", k),
            Stuck::PropertyNotFound { kind, property } => {
                write!(f, "property `{}` not found on {}", property, kind)
            }
            Stuck::TypeMismatch { op, expected, got } => {
                write!(f, "{}: expected {}, got {}", op, expected, got)
            }
            Stuck::ArityMismatch { expected, got } => {
                write!(f, "arity mismatch: expected {}, got {}", expected, got)
            }
            Stuck::BadAssignmentTarget => write!(f, "bad assignment target"),
            Stuck::NotImplemented(s) => write!(f, "not implemented in dynamics: {}", s),
            Stuck::UncaughtThrow(v) => write!(f, "uncaught throw: {}", v),
            Stuck::FuelExhausted => write!(f, "fuel exhausted"),
        }
    }
}

/// Mutable interpreter state threaded through every eval call.
#[derive(Debug)]
pub struct State {
    pub heap: Heap,
    pub fuel: usize,
}

impl State {
    pub fn new(fuel: usize) -> Self {
        State { heap: Heap::new(), fuel }
    }

    pub fn alloc_var(&mut self, value: Value) -> Loc {
        self.heap.alloc(Cell::Var(value))
    }

    fn tick(&mut self) -> Result<(), Stuck> {
        if self.fuel == 0 {
            return Err(Stuck::FuelExhausted);
        }
        self.fuel -= 1;
        Ok(())
    }
}

/// What a statement produces in addition to a possibly-extended env.
#[derive(Clone, Debug)]
pub enum StmtOutcome {
    Normal(Value),
    Return(Value),
    Break(Option<String>),
    Continue(Option<String>),
    Throw(Value),
}

impl StmtOutcome {
    pub fn is_terminating(&self) -> bool {
        !matches!(self, StmtOutcome::Normal(_))
    }
}

// ---------------------------------------------------------------------
// Expression evaluation.
// ---------------------------------------------------------------------

pub fn eval_expr(state: &mut State, env: &RuntimeEnv, expr: &Expr) -> Result<Value, Stuck> {
    state.tick()?;
    match expr {
        Expr::Lit { value, .. } => eval_literal(value),

        Expr::Ident { name, .. } => match env.lookup(name) {
            Some(loc) => deref_var(&state.heap, loc),
            None => Err(Stuck::UndefinedVariable(name.clone())),
        },

        Expr::This { .. } => match env.lookup("this") {
            Some(loc) => deref_var(&state.heap, loc),
            None => Ok(Value::Undefined),
        },

        Expr::Array { elements, .. } => {
            let mut vs = Vec::with_capacity(elements.len());
            for e in elements {
                let v = match e {
                    Some(e) => eval_expr(state, env, e)?,
                    None => Value::Undefined,
                };
                vs.push(v);
            }
            let loc = state.heap.alloc(Cell::Array(vs));
            Ok(Value::Array(loc))
        }

        Expr::Object { properties, .. } => {
            let mut props: BTreeMap<PropName, Value> = BTreeMap::new();
            for prop in properties {
                match prop {
                    PropDef::Property { key, value, .. } => {
                        let name = prop_key_to_name(key);
                        let v = eval_expr(state, env, value)?;
                        props.insert(name, v);
                    }
                    PropDef::Method { key, params, body, .. } => {
                        let name = prop_key_to_name(key);
                        let closure = Value::Closure(Closure {
                            name: None,
                            params: params.clone(),
                            body: body.clone(),
                            env: env.clone(),
                        });
                        props.insert(name, closure);
                    }
                    PropDef::Getter { .. } | PropDef::Setter { .. } => {
                        return Err(Stuck::NotImplemented("getters/setters"));
                    }
                }
            }
            let loc = state.heap.alloc(Cell::Object(props));
            Ok(Value::Object(loc))
        }

        Expr::Function { name, params, body, .. } => Ok(Value::Closure(Closure {
            name: name.clone(),
            params: params.clone(),
            body: body.clone(),
            env: env.clone(),
        })),

        Expr::Member { object, property, .. } => {
            let obj = eval_expr(state, env, object)?;
            read_member(&state.heap, &obj, property)
        }

        Expr::ComputedMember { object, property, .. } => {
            let obj = eval_expr(state, env, object)?;
            let idx = eval_expr(state, env, property)?;
            read_index(&state.heap, &obj, &idx)
        }

        Expr::Call { callee, arguments, .. } => {
            // Method call: `obj.m(args)` binds `this` to obj.
            let (callee_val, this_val) = match callee.as_ref() {
                Expr::Member { object, property, .. } => {
                    let obj = eval_expr(state, env, object)?;
                    let m = read_member(&state.heap, &obj, property)?;
                    (m, Some(obj))
                }
                Expr::ComputedMember { object, property, .. } => {
                    let obj = eval_expr(state, env, object)?;
                    let idx = eval_expr(state, env, property)?;
                    let m = read_index(&state.heap, &obj, &idx)?;
                    (m, Some(obj))
                }
                _ => (eval_expr(state, env, callee)?, None),
            };
            let mut args = Vec::with_capacity(arguments.len());
            for a in arguments {
                args.push(eval_expr(state, env, a)?);
            }
            apply(state, callee_val, this_val, args)
        }

        Expr::New { callee, arguments, .. } => {
            let callee_val = eval_expr(state, env, callee)?;
            let mut args = Vec::with_capacity(arguments.len());
            for a in arguments {
                args.push(eval_expr(state, env, a)?);
            }
            // Bind `this` to a fresh empty object; the constructor
            // populates it. Return that object regardless of what
            // the constructor returns (the standard JS rule for
            // "constructor returned a primitive" — we return `this`).
            let this_loc = state.heap.alloc(Cell::Object(BTreeMap::new()));
            let this = Value::Object(this_loc);
            let _ = apply(state, callee_val, Some(this.clone()), args)?;
            Ok(this)
        }

        Expr::NewTarget { .. } => Ok(Value::Undefined),

        Expr::Unary { op, argument, span: _ } => {
            // `delete` and `typeof` need to inspect the syntactic form
            // before evaluating; both are ok with eager evaluation in
            // this minimal model.
            let v = eval_expr(state, env, argument)?;
            apply_unary(state, env, *op, argument, v)
        }

        Expr::Binary { op, left, right, .. } => {
            // `&&` and `||` short-circuit on the left operand.
            if matches!(op, BinOp::And | BinOp::Or) {
                let l = eval_expr(state, env, left)?;
                let want_truthy = matches!(op, BinOp::And);
                if l.truthy() == want_truthy {
                    return eval_expr(state, env, right);
                }
                return Ok(l);
            }
            let l = eval_expr(state, env, left)?;
            let r = eval_expr(state, env, right)?;
            apply_binary(*op, &l, &r)
        }

        Expr::Assign { op, left, right, .. } => {
            let rhs = eval_expr(state, env, right)?;
            let new_value = match op {
                AssignOp::Assign => rhs,
                _ => {
                    let cur = eval_expr(state, env, left)?;
                    let bin = compound_to_binop(*op);
                    apply_binary(bin, &cur, &rhs)?
                }
            };
            assign_to(state, env, left, new_value.clone())?;
            Ok(new_value)
        }

        Expr::Conditional { test, consequent, alternate, .. } => {
            let t = eval_expr(state, env, test)?;
            if t.truthy() {
                eval_expr(state, env, consequent)
            } else {
                eval_expr(state, env, alternate)
            }
        }

        Expr::Sequence { expressions, .. } => {
            let mut last = Value::Undefined;
            for e in expressions {
                last = eval_expr(state, env, e)?;
            }
            Ok(last)
        }

        Expr::TemplateLiteral { quasis, expressions, .. } => {
            let mut out = String::new();
            for (i, q) in quasis.iter().enumerate() {
                out.push_str(q);
                if let Some(e) = expressions.get(i) {
                    let v = eval_expr(state, env, e)?;
                    out.push_str(&value_to_string(&v));
                }
            }
            Ok(Value::String(out))
        }
    }
}

fn eval_literal(lit: &Literal) -> Result<Value, Stuck> {
    Ok(match lit {
        Literal::Null => Value::Null,
        Literal::Undefined => Value::Undefined,
        Literal::Boolean(b) => Value::Boolean(*b),
        Literal::Number(n) => Value::Number(*n),
        Literal::String(s) => Value::String(s.clone()),
        Literal::Regex { .. } => return Err(Stuck::NotImplemented("regex literal")),
    })
}

fn prop_key_to_name(key: &PropKey) -> PropName {
    match key {
        PropKey::Ident(s) | PropKey::String(s) => PropName(s.clone()),
        PropKey::Number(n) => PropName(n.to_string()),
    }
}

fn deref_var(heap: &Heap, loc: Loc) -> Result<Value, Stuck> {
    match heap.get(loc) {
        Some(Cell::Var(v)) => Ok(v.clone()),
        Some(_) => Err(Stuck::NotImplemented("non-Var cell as binding")),
        None => Err(Stuck::NotImplemented("dangling loc")),
    }
}

fn read_member(heap: &Heap, obj: &Value, property: &str) -> Result<Value, Stuck> {
    match obj {
        Value::Object(loc) => match heap.get(*loc) {
            Some(Cell::Object(props)) => props
                .get(&PropName(property.to_string()))
                .cloned()
                .ok_or_else(|| Stuck::PropertyNotFound {
                    kind: "object",
                    property: property.to_string(),
                }),
            _ => Err(Stuck::NotImplemented("object loc not an Object cell")),
        },
        Value::Array(loc) => {
            if property == "length" {
                let len = match heap.get(*loc) {
                    Some(Cell::Array(v)) => v.len(),
                    _ => return Err(Stuck::NotImplemented("array loc not Array cell")),
                };
                Ok(Value::Number(len as f64))
            } else {
                Err(Stuck::PropertyNotFound { kind: "array", property: property.to_string() })
            }
        }
        Value::String(s) => {
            if property == "length" {
                Ok(Value::Number(s.chars().count() as f64))
            } else {
                Err(Stuck::PropertyNotFound { kind: "string", property: property.to_string() })
            }
        }
        _ => Err(Stuck::NotIndexable(obj.type_string())),
    }
}

fn read_index(heap: &Heap, obj: &Value, index: &Value) -> Result<Value, Stuck> {
    match (obj, index) {
        (Value::Array(loc), Value::Number(n)) => {
            let idx = *n as usize;
            match heap.get(*loc) {
                Some(Cell::Array(v)) => {
                    Ok(v.get(idx).cloned().unwrap_or(Value::Undefined))
                }
                _ => Err(Stuck::NotImplemented("array loc not Array cell")),
            }
        }
        (Value::String(s), Value::Number(n)) => {
            let idx = *n as usize;
            Ok(s.chars()
                .nth(idx)
                .map(|c| Value::String(c.to_string()))
                .unwrap_or(Value::Undefined))
        }
        (Value::Object(loc), Value::String(prop)) => match heap.get(*loc) {
            Some(Cell::Object(props)) => Ok(props
                .get(&PropName(prop.clone()))
                .cloned()
                .unwrap_or(Value::Undefined)),
            _ => Err(Stuck::NotImplemented("object loc not an Object cell")),
        },
        (Value::Object(loc), Value::Number(n)) => match heap.get(*loc) {
            Some(Cell::Object(props)) => Ok(props
                .get(&PropName(n.to_string()))
                .cloned()
                .unwrap_or(Value::Undefined)),
            _ => Err(Stuck::NotImplemented("object loc not an Object cell")),
        },
        _ => Err(Stuck::NotIndexable(obj.type_string())),
    }
}

fn apply(
    state: &mut State,
    callee: Value,
    this: Option<Value>,
    args: Vec<Value>,
) -> Result<Value, Stuck> {
    let closure = match callee {
        Value::Closure(c) => c,
        other => return Err(Stuck::NotCallable(other.type_string())),
    };
    if args.len() != closure.params.len() {
        return Err(Stuck::ArityMismatch {
            expected: closure.params.len(),
            got: args.len(),
        });
    }
    let mut call_env = closure.env.clone();
    let this_value = this.unwrap_or(Value::Undefined);
    let this_loc = state.alloc_var(this_value);
    call_env = call_env.extend("this".to_string(), this_loc);
    if let Some(name) = &closure.name {
        // Self-reference for named function expressions.
        let self_loc = state.alloc_var(Value::Closure(closure.clone()));
        call_env = call_env.extend(name.clone(), self_loc);
    }
    for (param, arg) in closure.params.iter().zip(args.into_iter()) {
        let loc = state.alloc_var(arg);
        call_env = call_env.extend(param.clone(), loc);
    }
    match eval_stmt(state, &call_env, &closure.body)? {
        (StmtOutcome::Return(v), _) => Ok(v),
        (StmtOutcome::Throw(v), _) => Err(Stuck::UncaughtThrow(v)),
        (_, _) => Ok(Value::Undefined),
    }
}

fn compound_to_binop(op: AssignOp) -> BinOp {
    match op {
        AssignOp::Assign => unreachable!("Assign handled separately"),
        AssignOp::AddAssign => BinOp::Add,
        AssignOp::SubAssign => BinOp::Sub,
        AssignOp::MulAssign => BinOp::Mul,
        AssignOp::DivAssign => BinOp::Div,
        AssignOp::ModAssign => BinOp::Mod,
        AssignOp::PowAssign => BinOp::Pow,
        AssignOp::LShiftAssign => BinOp::LShift,
        AssignOp::RShiftAssign => BinOp::RShift,
        AssignOp::URShiftAssign => BinOp::URShift,
        AssignOp::BitAndAssign => BinOp::BitAnd,
        AssignOp::BitOrAssign => BinOp::BitOr,
        AssignOp::BitXorAssign => BinOp::BitXor,
    }
}

fn assign_to(
    state: &mut State,
    env: &RuntimeEnv,
    target: &Expr,
    value: Value,
) -> Result<(), Stuck> {
    match target {
        Expr::Ident { name, .. } => {
            let loc = env
                .lookup(name)
                .ok_or_else(|| Stuck::UndefinedVariable(name.clone()))?;
            match state.heap.get_mut(loc) {
                Some(Cell::Var(slot)) => {
                    *slot = value;
                    Ok(())
                }
                _ => Err(Stuck::BadAssignmentTarget),
            }
        }
        Expr::Member { object, property, .. } => {
            let obj = eval_expr(state, env, object)?;
            match obj {
                Value::Object(loc) => match state.heap.get_mut(loc) {
                    Some(Cell::Object(props)) => {
                        props.insert(PropName(property.clone()), value);
                        Ok(())
                    }
                    _ => Err(Stuck::BadAssignmentTarget),
                },
                _ => Err(Stuck::BadAssignmentTarget),
            }
        }
        Expr::ComputedMember { object, property, .. } => {
            let obj = eval_expr(state, env, object)?;
            let idx = eval_expr(state, env, property)?;
            match (&obj, &idx) {
                (Value::Array(loc), Value::Number(n)) => {
                    let idx = *n as usize;
                    match state.heap.get_mut(*loc) {
                        Some(Cell::Array(v)) => {
                            if idx >= v.len() {
                                v.resize(idx + 1, Value::Undefined);
                            }
                            v[idx] = value;
                            Ok(())
                        }
                        _ => Err(Stuck::BadAssignmentTarget),
                    }
                }
                (Value::Object(loc), Value::String(prop)) => match state.heap.get_mut(*loc) {
                    Some(Cell::Object(props)) => {
                        props.insert(PropName(prop.clone()), value);
                        Ok(())
                    }
                    _ => Err(Stuck::BadAssignmentTarget),
                },
                _ => Err(Stuck::BadAssignmentTarget),
            }
        }
        _ => Err(Stuck::BadAssignmentTarget),
    }
}

// ---------------------------------------------------------------------
// Operator semantics.
// ---------------------------------------------------------------------

fn apply_unary(
    state: &mut State,
    _env: &RuntimeEnv,
    op: UnaryOp,
    arg_expr: &Expr,
    v: Value,
) -> Result<Value, Stuck> {
    match op {
        UnaryOp::Neg => match v {
            Value::Number(n) => Ok(Value::Number(-n)),
            other => Err(Stuck::TypeMismatch {
                op: "unary -",
                expected: "number",
                got: other.type_string(),
            }),
        },
        UnaryOp::Pos => match v {
            Value::Number(n) => Ok(Value::Number(n)),
            other => Err(Stuck::TypeMismatch {
                op: "unary +",
                expected: "number",
                got: other.type_string(),
            }),
        },
        UnaryOp::Not => Ok(Value::Boolean(!v.truthy())),
        UnaryOp::BitNot => match v {
            Value::Number(n) => Ok(Value::Number(!(n as i32) as f64)),
            other => Err(Stuck::TypeMismatch {
                op: "~",
                expected: "number",
                got: other.type_string(),
            }),
        },
        UnaryOp::Typeof => Ok(Value::String(v.type_string().to_string())),
        UnaryOp::Void => Ok(Value::Undefined),
        UnaryOp::Delete => Ok(Value::Boolean(true)),
        UnaryOp::Await => match v {
            Value::Promise(inner) => Ok(*inner),
            other => Ok(other),
        },
        UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
            let cur = match v {
                Value::Number(n) => n,
                other => {
                    return Err(Stuck::TypeMismatch {
                        op: "++/--",
                        expected: "number",
                        got: other.type_string(),
                    })
                }
            };
            let delta = if matches!(op, UnaryOp::PreInc | UnaryOp::PostInc) {
                1.0
            } else {
                -1.0
            };
            let new_val = Value::Number(cur + delta);
            assign_to(state, _env, arg_expr, new_val.clone())?;
            if matches!(op, UnaryOp::PreInc | UnaryOp::PreDec) {
                Ok(new_val)
            } else {
                Ok(Value::Number(cur))
            }
        }
    }
}

fn apply_binary(op: BinOp, l: &Value, r: &Value) -> Result<Value, Stuck> {
    use BinOp::*;
    match op {
        Add => match (l, r) {
            (Value::Number(a), Value::Number(b)) => Ok(Value::Number(a + b)),
            (Value::String(a), Value::String(b)) => Ok(Value::String(format!("{}{}", a, b))),
            _ => Err(Stuck::TypeMismatch {
                op: "+",
                expected: "Number+Number or String+String",
                got: l.type_string(),
            }),
        },
        Sub => num_op(l, r, "-", |a, b| a - b),
        Mul => num_op(l, r, "*", |a, b| a * b),
        Div => num_op(l, r, "/", |a, b| a / b),
        Mod => num_op(l, r, "%", |a, b| a % b),
        Pow => num_op(l, r, "**", |a, b| a.powf(b)),
        BitAnd => bit_op(l, r, "&", |a, b| a & b),
        BitOr => bit_op(l, r, "|", |a, b| a | b),
        BitXor => bit_op(l, r, "^", |a, b| a ^ b),
        LShift => bit_op(l, r, "<<", |a, b| a << (b & 31)),
        RShift => bit_op(l, r, ">>", |a, b| a >> (b & 31)),
        URShift => match (l, r) {
            (Value::Number(a), Value::Number(b)) => {
                let av = *a as u32;
                let bv = (*b as u32) & 31;
                Ok(Value::Number((av >> bv) as f64))
            }
            _ => Err(Stuck::TypeMismatch {
                op: ">>>",
                expected: "number",
                got: l.type_string(),
            }),
        },
        Lt => cmp_op(l, r, "<", |o| o == std::cmp::Ordering::Less),
        Gt => cmp_op(l, r, ">", |o| o == std::cmp::Ordering::Greater),
        LtEq => cmp_op(l, r, "<=", |o| o != std::cmp::Ordering::Greater),
        GtEq => cmp_op(l, r, ">=", |o| o != std::cmp::Ordering::Less),
        EqEq | EqEqEq => Ok(Value::Boolean(strict_equal(l, r))),
        NotEq | NotEqEq => Ok(Value::Boolean(!strict_equal(l, r))),
        And | Or => unreachable!("short-circuit handled in eval_expr"),
        In | Instanceof => Err(Stuck::NotImplemented("in / instanceof")),
    }
}

fn num_op(l: &Value, r: &Value, name: &'static str, f: fn(f64, f64) -> f64) -> Result<Value, Stuck> {
    match (l, r) {
        (Value::Number(a), Value::Number(b)) => Ok(Value::Number(f(*a, *b))),
        _ => Err(Stuck::TypeMismatch {
            op: name,
            expected: "number",
            got: l.type_string(),
        }),
    }
}

fn bit_op(l: &Value, r: &Value, name: &'static str, f: fn(i32, i32) -> i32) -> Result<Value, Stuck> {
    match (l, r) {
        (Value::Number(a), Value::Number(b)) => Ok(Value::Number(f(*a as i32, *b as i32) as f64)),
        _ => Err(Stuck::TypeMismatch {
            op: name,
            expected: "number",
            got: l.type_string(),
        }),
    }
}

fn cmp_op(
    l: &Value,
    r: &Value,
    name: &'static str,
    pred: fn(std::cmp::Ordering) -> bool,
) -> Result<Value, Stuck> {
    match (l, r) {
        (Value::Number(a), Value::Number(b)) => match a.partial_cmp(b) {
            Some(o) => Ok(Value::Boolean(pred(o))),
            None => Ok(Value::Boolean(false)),
        },
        (Value::String(a), Value::String(b)) => Ok(Value::Boolean(pred(a.cmp(b)))),
        _ => Err(Stuck::TypeMismatch {
            op: name,
            expected: "number or string",
            got: l.type_string(),
        }),
    }
}

fn strict_equal(l: &Value, r: &Value) -> bool {
    match (l, r) {
        (Value::Number(a), Value::Number(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Boolean(a), Value::Boolean(b)) => a == b,
        (Value::Null, Value::Null) | (Value::Undefined, Value::Undefined) => true,
        (Value::Array(a), Value::Array(b)) => a == b,
        (Value::Object(a), Value::Object(b)) => a == b,
        _ => false,
    }
}

fn value_to_string(v: &Value) -> String {
    match v {
        Value::Number(n) => n.to_string(),
        Value::String(s) => s.clone(),
        Value::Boolean(b) => b.to_string(),
        Value::Null => "null".to_string(),
        Value::Undefined => "undefined".to_string(),
        _ => format!("{}", v),
    }
}

// ---------------------------------------------------------------------
// Statement evaluation.
// ---------------------------------------------------------------------

pub fn eval_stmt(
    state: &mut State,
    env: &RuntimeEnv,
    stmt: &Stmt,
) -> Result<(StmtOutcome, RuntimeEnv), Stuck> {
    state.tick()?;
    match stmt {
        Stmt::Empty { .. } => Ok((StmtOutcome::Normal(Value::Undefined), env.clone())),

        Stmt::Block { body, .. } => {
            let (outcome, _) = eval_block(state, env, body)?;
            Ok((outcome, env.clone()))
        }

        Stmt::Expr { expression, .. } => {
            let v = eval_expr(state, env, expression)?;
            Ok((StmtOutcome::Normal(v), env.clone()))
        }

        Stmt::Var { kind: _, declarations, .. } => {
            let mut new_env = env.clone();
            for decl in declarations {
                let v = match &decl.init {
                    Some(e) => eval_expr(state, &new_env, e)?,
                    None => Value::Undefined,
                };
                let loc = state.alloc_var(v);
                new_env = new_env.extend(decl.name.clone(), loc);
            }
            Ok((StmtOutcome::Normal(Value::Undefined), new_env))
        }

        Stmt::FunctionDecl { name, params, body, .. } => {
            let closure = Value::Closure(Closure {
                name: Some(name.clone()),
                params: params.clone(),
                body: body.clone(),
                env: env.clone(),
            });
            let loc = state.alloc_var(closure);
            let new_env = env.extend(name.clone(), loc);
            Ok((StmtOutcome::Normal(Value::Undefined), new_env))
        }

        Stmt::Return { argument, .. } => {
            let v = match argument {
                Some(e) => eval_expr(state, env, e)?,
                None => Value::Undefined,
            };
            Ok((StmtOutcome::Return(v), env.clone()))
        }

        Stmt::Throw { argument, .. } => {
            let v = eval_expr(state, env, argument)?;
            Ok((StmtOutcome::Throw(v), env.clone()))
        }

        Stmt::Break { label, .. } => Ok((StmtOutcome::Break(label.clone()), env.clone())),
        Stmt::Continue { label, .. } => Ok((StmtOutcome::Continue(label.clone()), env.clone())),

        Stmt::If { test, consequent, alternate, .. } => {
            let t = eval_expr(state, env, test)?;
            let outcome = if t.truthy() {
                eval_stmt(state, env, consequent)?.0
            } else if let Some(alt) = alternate {
                eval_stmt(state, env, alt)?.0
            } else {
                StmtOutcome::Normal(Value::Undefined)
            };
            Ok((outcome, env.clone()))
        }

        Stmt::While { test, body, .. } => {
            loop {
                state.tick()?;
                let t = eval_expr(state, env, test)?;
                if !t.truthy() {
                    break;
                }
                match eval_stmt(state, env, body)?.0 {
                    StmtOutcome::Normal(_) | StmtOutcome::Continue(None) => continue,
                    StmtOutcome::Break(None) => break,
                    other => return Ok((other, env.clone())),
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::DoWhile { body, test, .. } => {
            loop {
                state.tick()?;
                match eval_stmt(state, env, body)?.0 {
                    StmtOutcome::Normal(_) | StmtOutcome::Continue(None) => {}
                    StmtOutcome::Break(None) => return Ok((
                        StmtOutcome::Normal(Value::Undefined),
                        env.clone(),
                    )),
                    other => return Ok((other, env.clone())),
                }
                let t = eval_expr(state, env, test)?;
                if !t.truthy() {
                    break;
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::For { init, test, update, body, .. } => {
            let mut loop_env = env.clone();
            if let Some(init) = init {
                match init {
                    ForInit::VarDecl(decls) => {
                        for decl in decls {
                            let v = match &decl.init {
                                Some(e) => eval_expr(state, &loop_env, e)?,
                                None => Value::Undefined,
                            };
                            let loc = state.alloc_var(v);
                            loop_env = loop_env.extend(decl.name.clone(), loc);
                        }
                    }
                    ForInit::Expr(e) => {
                        eval_expr(state, &loop_env, e)?;
                    }
                }
            }
            loop {
                state.tick()?;
                if let Some(test) = test {
                    let t = eval_expr(state, &loop_env, test)?;
                    if !t.truthy() {
                        break;
                    }
                }
                match eval_stmt(state, &loop_env, body)?.0 {
                    StmtOutcome::Normal(_) | StmtOutcome::Continue(None) => {}
                    StmtOutcome::Break(None) => break,
                    other => return Ok((other, env.clone())),
                }
                if let Some(update) = update {
                    eval_expr(state, &loop_env, update)?;
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::ForIn { left, right, body, .. } => {
            let r = eval_expr(state, env, right)?;
            let keys: Vec<String> = match r {
                Value::Object(loc) => match state.heap.get(loc) {
                    Some(Cell::Object(props)) => props.keys().map(|k| k.0.clone()).collect(),
                    _ => return Err(Stuck::NotImplemented("for-in object cell")),
                },
                Value::Array(loc) => match state.heap.get(loc) {
                    Some(Cell::Array(v)) => (0..v.len()).map(|i| i.to_string()).collect(),
                    _ => return Err(Stuck::NotImplemented("for-in array cell")),
                },
                other => {
                    return Err(Stuck::TypeMismatch {
                        op: "for-in",
                        expected: "object or array",
                        got: other.type_string(),
                    })
                }
            };
            for key in keys {
                let v = Value::String(key);
                let loop_env = bind_for_lhs(state, env, left, v)?;
                match eval_stmt(state, &loop_env, body)?.0 {
                    StmtOutcome::Normal(_) | StmtOutcome::Continue(None) => continue,
                    StmtOutcome::Break(None) => break,
                    other => return Ok((other, env.clone())),
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::ForOf { left, right, body, .. } => {
            let r = eval_expr(state, env, right)?;
            let elems: Vec<Value> = match r {
                Value::Array(loc) => match state.heap.get(loc) {
                    Some(Cell::Array(v)) => v.clone(),
                    _ => return Err(Stuck::NotImplemented("for-of array cell")),
                },
                Value::String(s) => s.chars().map(|c| Value::String(c.to_string())).collect(),
                other => {
                    return Err(Stuck::TypeMismatch {
                        op: "for-of",
                        expected: "iterable",
                        got: other.type_string(),
                    })
                }
            };
            for v in elems {
                let loop_env = bind_for_lhs(state, env, left, v)?;
                match eval_stmt(state, &loop_env, body)?.0 {
                    StmtOutcome::Normal(_) | StmtOutcome::Continue(None) => continue,
                    StmtOutcome::Break(None) => break,
                    other => return Ok((other, env.clone())),
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::Try { block, handler, finalizer, .. } => {
            let outcome = eval_stmt(state, env, block)?.0;
            let outcome = match outcome {
                StmtOutcome::Throw(v) => match handler {
                    Some(catch) => {
                        let loc = state.alloc_var(v);
                        let catch_env = env.extend(catch.param.clone(), loc);
                        eval_stmt(state, &catch_env, &catch.body)?.0
                    }
                    None => StmtOutcome::Throw(v),
                },
                other => other,
            };
            if let Some(f) = finalizer {
                let final_outcome = eval_stmt(state, env, f)?.0;
                if let StmtOutcome::Throw(_) | StmtOutcome::Return(_) = final_outcome {
                    return Ok((final_outcome, env.clone()));
                }
            }
            Ok((outcome, env.clone()))
        }

        Stmt::Switch { discriminant, cases, .. } => {
            let d = eval_expr(state, env, discriminant)?;
            let mut matched = false;
            for case in cases {
                if !matched {
                    match &case.test {
                        Some(t) => {
                            let tv = eval_expr(state, env, t)?;
                            if strict_equal(&d, &tv) {
                                matched = true;
                            }
                        }
                        None => matched = true,
                    }
                }
                if matched {
                    for s in &case.consequent {
                        match eval_stmt(state, env, s)?.0 {
                            StmtOutcome::Normal(_) => continue,
                            StmtOutcome::Break(None) => {
                                return Ok((
                                    StmtOutcome::Normal(Value::Undefined),
                                    env.clone(),
                                ));
                            }
                            other => return Ok((other, env.clone())),
                        }
                    }
                }
            }
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }

        Stmt::Labeled { body, .. } => eval_stmt(state, env, body),

        Stmt::Import { .. } | Stmt::Export { .. } => {
            Ok((StmtOutcome::Normal(Value::Undefined), env.clone()))
        }
    }
}

fn eval_block(
    state: &mut State,
    env: &RuntimeEnv,
    body: &[Stmt],
) -> Result<(StmtOutcome, RuntimeEnv), Stuck> {
    // JS hoists `var` and `function` declarations to the top of their
    // enclosing scope. We approximate by pre-allocating a `Cell::Var`
    // for every directly-declared name in this block and binding it in
    // `block_env` before any statement runs. This is what lets a
    // closure defined earlier in the block see assignments to names
    // declared later in the same block.
    let mut block_env = env.clone();
    let mut already_bound = std::collections::HashSet::new();
    for s in body {
        for name in declared_names(s) {
            if already_bound.insert(name.to_string()) {
                let loc = state.alloc_var(Value::Undefined);
                block_env = block_env.extend(name.to_string(), loc);
            }
        }
    }

    // Now bind every `function f() { ... }` to the closure value at
    // the loc we pre-allocated above. The closure captures `block_env`,
    // which already contains every var name in the scope.
    for s in body {
        if let Stmt::FunctionDecl { name, params, body, .. } = s {
            let closure = Value::Closure(Closure {
                name: Some(name.clone()),
                params: params.clone(),
                body: body.clone(),
                env: block_env.clone(),
            });
            let loc = block_env.lookup(name).expect("function name was pre-allocated");
            if let Some(Cell::Var(slot)) = state.heap.get_mut(loc) {
                *slot = closure;
            }
        }
    }

    let mut last = Value::Undefined;
    for stmt in body {
        if matches!(stmt, Stmt::FunctionDecl { .. }) {
            continue; // already hoisted above
        }
        // For `var` decls, write into the pre-allocated cell instead
        // of allocating a fresh one (otherwise a closure captured
        // before the decl wouldn't see the new value).
        if let Stmt::Var { declarations, .. } = stmt {
            for decl in declarations {
                let v = match &decl.init {
                    Some(e) => eval_expr(state, &block_env, e)?,
                    None => Value::Undefined,
                };
                let loc = block_env
                    .lookup(&decl.name)
                    .expect("var name was pre-allocated");
                if let Some(Cell::Var(slot)) = state.heap.get_mut(loc) {
                    *slot = v;
                }
            }
            continue;
        }
        let (outcome, new_env) = eval_stmt(state, &block_env, stmt)?;
        block_env = new_env;
        match outcome {
            StmtOutcome::Normal(v) => last = v,
            other => return Ok((other, block_env)),
        }
    }
    Ok((StmtOutcome::Normal(last), block_env))
}

/// Names directly declared by `stmt` (not by nested blocks).
fn declared_names(stmt: &Stmt) -> Vec<&str> {
    match stmt {
        Stmt::Var { declarations, .. } => declarations.iter().map(|d| d.name.as_str()).collect(),
        Stmt::FunctionDecl { name, .. } => vec![name.as_str()],
        Stmt::Export { declaration, .. } => match declaration {
            crate::parser::ast::ExportDecl::Var { declarations, .. } => {
                declarations.iter().map(|d| d.name.as_str()).collect()
            }
            crate::parser::ast::ExportDecl::Function { name, .. } => vec![name.as_str()],
            crate::parser::ast::ExportDecl::Default { value, .. } => match value {
                crate::parser::ast::Expr::Function {
                    name: Some(name), ..
                } => vec![name.as_str(), "default"],
                _ => vec!["default"],
            },
            crate::parser::ast::ExportDecl::List { .. } => Vec::new(),
            crate::parser::ast::ExportDecl::From { .. } => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn bind_for_lhs(
    state: &mut State,
    env: &RuntimeEnv,
    lhs: &ForInLhs,
    value: Value,
) -> Result<RuntimeEnv, Stuck> {
    match lhs {
        ForInLhs::VarDecl(name, _, _) => {
            let loc = state.alloc_var(value);
            Ok(env.extend(name.clone(), loc))
        }
        ForInLhs::Expr(e) => {
            assign_to(state, env, e, value)?;
            Ok(env.clone())
        }
    }
}

/// Run a `Program`'s top-level statements to completion. The returned
/// value is the value of the last statement (matching how the type
/// inferencer reports a program's "type").
pub fn run_program(
    state: &mut State,
    env: &RuntimeEnv,
    program: &crate::parser::ast::Program,
) -> Result<Value, Stuck> {
    let (outcome, _) = eval_block(state, env, &program.statements)?;
    match outcome {
        StmtOutcome::Normal(v) => Ok(v),
        StmtOutcome::Return(v) => Ok(v),
        StmtOutcome::Throw(v) => Err(Stuck::UncaughtThrow(v)),
        StmtOutcome::Break(_) | StmtOutcome::Continue(_) => Err(Stuck::NotImplemented(
            "top-level break/continue",
        )),
    }
}
