//! Property-tested soundness probe.
//!
//! Generates well-typed expressions *by construction* (sample a target
//! type, then build an expression of that type using only the rules
//! we've enumerated), parses + type-checks the synthesised source,
//! reduces it through `crate::dynamics`, and asserts reduction
//! produces a value of the expected type — never gets stuck.
//!
//! A stuck typed term is the operational signature of a soundness
//! violation. The randomised generator is here to find shapes the
//! hand-written tests in `crate::infer::tests` and
//! `crate::dynamics::tests` won't think to construct.
//!
//! Generation is deliberately conservative: we cover the part of the
//! language where the typing rules and the operational rules already
//! agree (literals, arithmetic, comparisons, conditionals, let-binds,
//! string concat, function call to identity). Adding cases here is
//! how we widen coverage as the type system grows.

use crate::builtins::initial_env;
use crate::dynamics::{run_to_end_with_fuel, Stuck, Value};
use crate::infer::InferState;
use crate::lexer::{Scanner, Token};
use crate::parser::Parser;
use crate::types::Type;

/// Target type for a generated expression.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SynthType {
    Number,
    String,
    Boolean,
}

impl SynthType {
    fn matches_value(self, v: &Value) -> bool {
        match (self, v) {
            (SynthType::Number, Value::Number(_)) => true,
            (SynthType::String, Value::String(_)) => true,
            (SynthType::Boolean, Value::Boolean(_)) => true,
            _ => false,
        }
    }

    fn matches_type(self, t: &Type) -> bool {
        // Singleton literals are values of their base type — accept
        // them where the corresponding base is expected. This mirrors
        // the language semantics: `0` is a `Number`, `"a"` is a
        // `String`, `true` is a `Boolean`. Without this, the soundness
        // checker would see `0` typed as `Lit(0)` and fail the
        // "synth equals expected" check after `infer_literal` started
        // returning singletons.
        match (self, t) {
            (SynthType::Number, Type::Number)
            | (SynthType::String, Type::String)
            | (SynthType::Boolean, Type::Boolean) => true,
            (SynthType::Number, Type::Literal(crate::types::LitValue::Number(_)))
            | (SynthType::String, Type::Literal(crate::types::LitValue::String(_)))
            | (SynthType::Boolean, Type::Literal(crate::types::LitValue::Bool(_))) => true,
            _ => false,
        }
    }
}

// The proptest strategies live behind `#[cfg(test)]` because
// `proptest` is a dev-dependency. Public callers use `check_program`
// directly with their own source.

#[cfg(test)]
use proptest::prelude::*;

/// Strategy for a small Number expression at the given depth.
#[cfg(test)]
pub fn arb_number(depth: u32) -> BoxedStrategy<String> {
    if depth == 0 {
        return prop_oneof![
            (0i32..100).prop_map(|n| n.to_string()),
            Just("0".to_string()),
            Just("1".to_string()),
        ]
        .boxed();
    }
    prop_oneof![
        // leaves
        arb_number(0),
        // arithmetic
        (arb_number(depth - 1), arb_number(depth - 1))
            .prop_map(|(a, b)| format!("({} + {})", a, b)),
        (arb_number(depth - 1), arb_number(depth - 1))
            .prop_map(|(a, b)| format!("({} - {})", a, b)),
        (arb_number(depth - 1), arb_number(depth - 1))
            .prop_map(|(a, b)| format!("({} * {})", a, b)),
        // unary
        arb_number(depth - 1).prop_map(|a| format!("-({})", a)),
        // conditional with boolean test
        (
            arb_boolean(depth - 1),
            arb_number(depth - 1),
            arb_number(depth - 1)
        )
            .prop_map(|(t, a, b)| format!("({} ? {} : {})", t, a, b)),
        // identity application
        arb_number(depth - 1).prop_map(|a| format!("(function(x) {{ return x; }})({})", a)),
    ]
    .boxed()
}

#[cfg(test)]
pub fn arb_string(depth: u32) -> BoxedStrategy<String> {
    if depth == 0 {
        return prop_oneof![
            Just("\"\"".to_string()),
            Just("\"a\"".to_string()),
            Just("\"abc\"".to_string()),
        ]
        .boxed();
    }
    prop_oneof![
        arb_string(0),
        (arb_string(depth - 1), arb_string(depth - 1))
            .prop_map(|(a, b)| format!("({} + {})", a, b)),
        (
            arb_boolean(depth - 1),
            arb_string(depth - 1),
            arb_string(depth - 1)
        )
            .prop_map(|(t, a, b)| format!("({} ? {} : {})", t, a, b)),
    ]
    .boxed()
}

#[cfg(test)]
pub fn arb_boolean(depth: u32) -> BoxedStrategy<String> {
    if depth == 0 {
        return prop_oneof![Just("true".to_string()), Just("false".to_string())].boxed();
    }
    prop_oneof![
        arb_boolean(0),
        // negation
        arb_boolean(depth - 1).prop_map(|a| format!("!({})", a)),
        // numeric comparison
        (arb_number(depth - 1), arb_number(depth - 1))
            .prop_map(|(a, b)| format!("({} < {})", a, b)),
        (arb_number(depth - 1), arb_number(depth - 1))
            .prop_map(|(a, b)| format!("({} === {})", a, b)),
        // logical
        (arb_boolean(depth - 1), arb_boolean(depth - 1))
            .prop_map(|(a, b)| format!("({} && {})", a, b)),
    ]
    .boxed()
}

/// One-shot soundness check on a single source program: the inferred
/// type matches `expected`, evaluation succeeds, the value matches.
pub fn check_program(source: &str, expected: SynthType) -> Result<(), String> {
    // Parse.
    let mut scanner = Scanner::new(source);
    let mut tokens = Vec::new();
    loop {
        let tok = scanner
            .next_token()
            .map_err(|e| format!("scanner error: {:?}", e))?;
        let is_eof = matches!(tok.value, Token::Eof);
        tokens.push(tok);
        if is_eof {
            break;
        }
    }
    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);
    let program = parser
        .parse_program()
        .map_err(|e| format!("parse error: {:?}", e))?;

    // Phase 7c: refuse to feed non-surface AST forms into the prober.
    // Anything coming from `parse_program` is by definition surface,
    // so this only fires if a future AST extension forgets to update
    // `crate::meta::surface::is_surface_*`.
    for stmt in &program.statements {
        if !crate::meta::surface::is_surface_stmt(stmt) {
            return Err("non-surface AST form in synthesised program".to_string());
        }
    }

    // Type-check.
    let mut infer = InferState::new();
    let env = initial_env();
    let ty = infer
        .infer_program(&env, &program)
        .map_err(|e| format!("infer error: {}", e))?;
    let ty = infer.apply_subst(&ty);
    if !expected.matches_type(&ty) {
        return Err(format!(
            "synthesized program at expected type {:?} inferred to {} — generator bug",
            expected, ty
        ));
    }

    // Reduce.
    let value = run_to_end_with_fuel(&program, 5_000).map_err(|s| match s {
        Stuck::FuelExhausted => "fuel exhausted (not a soundness violation)".to_string(),
        other => format!("STUCK: {}", other),
    })?;

    if !expected.matches_value(&value) {
        return Err(format!(
            "value-type mismatch: expected {:?}, got {}",
            expected, value
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Soundness on a hand-picked set of expressions known to type-
    /// check, exercising every branch of the generator.
    #[test]
    fn handcrafted_well_typed_programs_never_stuck() {
        let cases: &[(SynthType, &str)] = &[
            (SynthType::Number, "1 + 2"),
            (SynthType::Number, "(true ? 3 : 4)"),
            (SynthType::Number, "(function(x) { return x + 1; })(5)"),
            (SynthType::String, "\"a\" + \"b\""),
            (SynthType::Boolean, "1 < 2"),
            (SynthType::Boolean, "!(1 === 2)"),
            (SynthType::Boolean, "(true && false) || true"),
        ];
        for (ty, src) in cases {
            check_program(src, *ty).unwrap_or_else(|e| {
                panic!("{:?} on `{}`: {}", ty, src, e);
            });
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            max_global_rejects: 1024,
            .. ProptestConfig::default()
        })]

        #[test]
        fn generated_number_programs_sound(src in arb_number(3)) {
            // The generator only emits programs typed at Number. Any
            // failure here — type mismatch, stuck reduction, value
            // mismatch — is a soundness violation we want to surface.
            check_program(&src, SynthType::Number)
                .map_err(|e| TestCaseError::fail(format!("source: {}\nerror: {}", src, e)))?;
        }

        #[test]
        fn generated_string_programs_sound(src in arb_string(3)) {
            check_program(&src, SynthType::String)
                .map_err(|e| TestCaseError::fail(format!("source: {}\nerror: {}", src, e)))?;
        }

        #[test]
        fn generated_boolean_programs_sound(src in arb_boolean(3)) {
            check_program(&src, SynthType::Boolean)
                .map_err(|e| TestCaseError::fail(format!("source: {}\nerror: {}", src, e)))?;
        }
    }
}
