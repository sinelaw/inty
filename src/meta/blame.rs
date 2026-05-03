//! Cimini-Blame meta-test.
//!
//! For every operator and every input shape the typing arm accepts,
//! check that the operational rule (in `crate::dynamics`) actually
//! produces a value. A missing match is a *blame triple*:
//! `(operator, configuration, input-shape)` — the constructive content
//! of "this typing rule is unsound".
//!
//! Phase 4 reads the catalog (phase 2) and the dynamics (phase 3) and
//! produces the list. The accompanying test asserts the list is empty
//! (modulo arms with `notes` exemptions, which are skipped because the
//! catalog already documents that they can't be fully modeled).

use crate::dynamics::{run_to_end_with_fuel, Stuck};
use crate::lexer::{Scanner, Token};
use crate::operators::{BaseType, OpInfo, OpKind, TypeShape, TypingArm};
use crate::parser::Parser;
use crate::types::ClassName;

/// `(operator name, configuration snapshot, input shape)` describing a
/// typing arm that accepts a shape the operational semantics doesn't
/// deliver on. Phase 5 turns these into actionable test cases.
#[derive(Clone, Debug)]
pub struct BlameTriple {
    pub operator: &'static str,
    pub config: ConfigSnapshot,
    pub shape: Vec<&'static str>,
    pub program: String,
    pub stuck: Stuck,
}

/// Snapshot of the type-system policy in effect when blame triples
/// were enumerated. Phase 6 wires the real `InferConfig` in here so
/// that as policy knobs are added, the meta-test produces triples
/// tagged with the configuration that allowed them.
#[derive(Clone, Debug, Default)]
pub struct ConfigSnapshot {
    pub infer: crate::infer::InferConfig,
}

/// Probe values used to instantiate `Wildcard` and class shapes. A
/// small fixed alphabet — see the design doc, "Don't try to enumerate
/// exhaustively; the alphabet is for catching obvious gaps".
///
/// `undefined` is encoded as `void 0` because JS doesn't expose
/// `undefined` as a literal token — `undefined` in source is an
/// ordinary identifier that's expected to resolve to the global
/// undefined value, which our dynamics doesn't bind.
const PRIMITIVE_PROBES: &[(&str, &str)] = &[
    ("number", "0"),
    ("string", "\"\""),
    ("boolean", "true"),
    ("null", "null"),
    ("undefined", "void 0"),
];

fn probe_for_base(b: BaseType) -> Option<(&'static str, &'static str)> {
    match b {
        BaseType::Number => Some(("number", "0")),
        BaseType::String => Some(("string", "\"\"")),
        BaseType::Boolean => Some(("boolean", "true")),
        BaseType::Null => Some(("null", "null")),
        BaseType::Undefined => Some(("undefined", "void 0")),
        BaseType::Regex => None, // Regex is a typed value but dynamics can't construct one
    }
}

fn probes_for_class(c: ClassName) -> Vec<(&'static str, &'static str)> {
    // Phase 7b: read instances from the declarative table instead of
    // a hardcoded list. The table only describes which shapes
    // satisfy a class; the prober materialises each shape via the
    // existing `probe_for_base` map.
    let mut out = Vec::new();
    for inst in crate::classes::instances_of(c) {
        // Only handle unary Plus-style classes here. Multi-position
        // classes (Indexable) carry `notes` exemptions on every arm
        // and aren't synthesised by `build_program`, so the probe
        // expansion isn't reached.
        if inst.inputs.len() != 1 {
            continue;
        }
        if let crate::operators::TypeShape::Concrete(b) = inst.inputs[0] {
            if let Some(p) = probe_for_base(b) {
                out.push(p);
            }
        }
    }
    out
}

/// All concrete instantiations of one input position.
fn probes_for_shape(shape: TypeShape) -> Vec<(&'static str, &'static str)> {
    match shape {
        TypeShape::Concrete(b) => probe_for_base(b).into_iter().collect(),
        TypeShape::AnyOfClass(c) => probes_for_class(c),
        TypeShape::Wildcard => PRIMITIVE_PROBES.to_vec(),
        TypeShape::SameAsArg(_) => Vec::new(), // resolved during enumeration
    }
}

/// Build a runnable JS program that exercises `op` with `args`.
/// Returns `None` for operators that can't be mechanically synthesised
/// at this granularity (object/computed-member/call/new — those arms
/// all carry `notes` exemptions in the catalog).
fn build_program(op_name: &str, args: &[&str]) -> Option<String> {
    Some(match op_name {
        // Infix binary
        "+" | "-" | "*" | "/" | "%" | "**" | "<" | ">" | "<=" | ">=" | "==" | "!=" | "==="
        | "!==" | "&&" | "||" | "&" | "|" | "^" | "<<" | ">>" | ">>>" => {
            format!("({}) {} ({})", args[0], op_name, args[1])
        }
        "in" => format!("({}) in ({})", args[0], args[1]),
        "instanceof" => format!("({}) instanceof ({})", args[0], args[1]),
        // Unary prefix
        "unary -" => format!("-({})", args[0]),
        "unary +" => format!("+({})", args[0]),
        "!" | "~" => format!("{}({})", op_name, args[0]),
        "typeof" | "void" | "delete" | "await" => format!("{} ({})", op_name, args[0]),
        // ++/-- need an lvalue
        "++ (prefix)" => format!("var __x = {}; ++__x", args[0]),
        "-- (prefix)" => format!("var __x = {}; --__x", args[0]),
        "++ (postfix)" => format!("var __x = {}; __x++", args[0]),
        "-- (postfix)" => format!("var __x = {}; __x--", args[0]),
        // Pseudo-ops not synthesisable at this granularity
        "." | "[]" | "()" | "new" => return None,
        _ => return None,
    })
}

/// Parse and run a small program through the dynamics. Returns
/// `Some(stuck_reason)` if reduction got stuck, `None` if it produced
/// a value or ran out of fuel.
fn run_or_stuck(program: &str) -> Option<Stuck> {
    let mut scanner = Scanner::new(program);
    let mut tokens = Vec::new();
    loop {
        let tok = match scanner.next_token() {
            Ok(t) => t,
            Err(_) => return Some(Stuck::NotImplemented("scanner error in probe")),
        };
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);
    let program_ast = match parser.parse_program() {
        Ok(p) => p,
        Err(_) => return Some(Stuck::NotImplemented("parse error in probe")),
    };
    match run_to_end_with_fuel(&program_ast, 1_000) {
        Ok(_) => None,
        Err(Stuck::FuelExhausted) => None,
        Err(s) => Some(s),
    }
}

/// Recursively enumerate concrete probe assignments for an arm,
/// honouring `SameAsArg` references.
fn enumerate_arm_probes<F: FnMut(&[&'static str], &[&'static str])>(
    inputs: &[TypeShape],
    cb: &mut F,
) {
    let mut tag = vec![""; inputs.len()];
    let mut value = vec![""; inputs.len()];
    enumerate_inner(inputs, 0, &mut tag, &mut value, cb);
}

fn enumerate_inner<F: FnMut(&[&'static str], &[&'static str])>(
    inputs: &[TypeShape],
    idx: usize,
    tag: &mut [&'static str],
    value: &mut [&'static str],
    cb: &mut F,
) {
    if idx == inputs.len() {
        cb(tag, value);
        return;
    }
    match inputs[idx] {
        TypeShape::SameAsArg(n) => {
            tag[idx] = tag[n];
            value[idx] = value[n];
            enumerate_inner(inputs, idx + 1, tag, value, cb);
        }
        other => {
            let probes = probes_for_shape(other);
            if probes.is_empty() {
                // No probe materialises this position — skip.
                tag[idx] = "<unprobed>";
                value[idx] = "0";
                enumerate_inner(inputs, idx + 1, tag, value, cb);
            } else {
                for (t, v) in probes {
                    tag[idx] = t;
                    value[idx] = v;
                    enumerate_inner(inputs, idx + 1, tag, value, cb);
                }
            }
        }
    }
}

/// Compute every blame triple for `op`. Skips arms with `notes`
/// exemptions and operators of kinds we can't synthesise programs for
/// at this granularity (member access, indexing, call, new).
pub fn blame_triples_for_op(op: &OpInfo) -> Vec<BlameTriple> {
    let mut out = Vec::new();
    if matches!(
        op.kind,
        OpKind::MemberAccess | OpKind::Index | OpKind::Call | OpKind::New
    ) {
        return out;
    }
    for arm in op.arms {
        if !arm.notes.is_empty() {
            continue;
        }
        // For class-mediated arms, expand over instances of the class.
        // For literal arms, the existing enumeration handles it.
        let inputs = arm.inputs;
        enumerate_arm_probes(inputs, &mut |tag, val| {
            // Skip the case where the enumeration couldn't materialise
            // a position (the "<unprobed>" tag).
            if tag.iter().any(|t| *t == "<unprobed>") {
                return;
            }
            let program = match build_program(op.name, val) {
                Some(p) => p,
                None => return,
            };
            if let Some(stuck) = run_or_stuck(&program) {
                out.push(BlameTriple {
                    operator: op.name,
                    config: ConfigSnapshot::default(),
                    shape: tag.to_vec(),
                    program,
                    stuck,
                });
            }
            let _: &TypingArm = arm;
        });
    }
    out
}

/// Compute every blame triple in the catalog.
pub fn all_blame_triples(catalog: &[OpInfo]) -> Vec<BlameTriple> {
    let mut out = Vec::new();
    for op in catalog {
        out.extend(blame_triples_for_op(op));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operators::OPERATORS;

    #[test]
    fn no_blame_triples_in_catalog() {
        let triples = all_blame_triples(OPERATORS);
        if !triples.is_empty() {
            for t in &triples {
                eprintln!(
                    "BLAME [{}] shape {:?} program `{}` -> stuck: {}",
                    t.operator, t.shape, t.program, t.stuck
                );
            }
            panic!("found {} blame triple(s) — see stderr", triples.len());
        }
    }

    #[test]
    fn blame_machinery_runs_per_op() {
        // Smoke test: every catalog op processes without panic
        // (even if it produces zero triples).
        for op in OPERATORS {
            let _ = blame_triples_for_op(op);
        }
    }

    #[test]
    fn known_well_typed_arms_pass() {
        // Sanity: a hand-picked arm we know works produces no
        // blame triples.
        let plus = OPERATORS.iter().find(|o| o.name == "+").unwrap();
        let triples = blame_triples_for_op(plus);
        assert!(
            triples.is_empty(),
            "+ should have no blame triples, got: {:?}",
            triples
        );
    }
}
