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
use crate::frontends::javascript::lexer::{Scanner, Token};
use crate::frontends::javascript::parser::Parser;
use crate::infer::InferState;
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
            (SynthType::Number, Type::Number | Type::Int)
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
        // a fraction: the `Int`/`Number` split
        arb_number(depth - 1).prop_map(|a| format!("({} / 2)", a)),
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
    // An `Int` has no fractional part. (Arithmetic can still make a `-0`
    // from `Int`s — `-0 * 1` — which a Go `int` holds as 0: a known corner.)
    if ty == Type::Int && !matches!(value, Value::Number(n) if crate::types::is_safe_int(n.abs())) {
        return Err(format!("value-type mismatch: expected Int, got {}", value));
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

// ---- Declarations, hoisting and generalisation ----------------------------
//
// The generators above build programs that are well-typed by construction,
// which can't catch the checker *accepting* an ill-typed program. The
// generator below builds programs that may or may not type-check: a few
// top-level helper functions in random order, each written either as
// `function h(x)` or as `const h = (x) => …`, calling each other forwards
// and backwards (so generalisation, hoisting and let-polymorphism are
// exercised) and used at several argument types. Two properties:
//
// * **Accepted ⇒ not stuck.** Whenever inty accepts a program, the
//   operational semantics must not get stuck on it (fuel exhaustion from
//   unbounded recursion is fine). This is the property the
//   generalisation bugs fixed alongside this test violated — e.g.
//   `function f(x) { return g(x); } const g = (y) => y * 2; f("hi") * 2`.
// * **Declaration form is irrelevant to typing.** Writing a helper as
//   `function h` or `const h = (x) =>` must not change whether the
//   program type-checks, nor any helper's inferred scheme.

/// Body of a generated helper `h_i(x)`.
#[cfg(test)]
#[derive(Debug, Clone)]
pub enum HelperBody {
    Id,
    Num,
    Str,
    Pair,
    Call(usize),
    CallLit(usize, &'static str),
    First(usize),
    /// A property read or method call on the parameter itself, whose
    /// type isn't known inside the helper (`HasProp`).
    Prop(&'static str),
    /// `h_j` applied to the result of a method call on the parameter.
    CallProp(usize, &'static str),
    /// Recursion through a method result, like a string-processing
    /// function: `x.length > 1 ? h_i(x.slice(1)) : x`.
    Shrink,
}

#[cfg(test)]
#[derive(Debug, Clone)]
pub struct DeclProgram {
    /// `(body, written as const)` per helper `h0, h1, …`.
    pub helpers: Vec<(HelperBody, bool)>,
    /// Declaration order: a permutation of helper indices.
    pub order: Vec<usize>,
    /// Final uses: `(helper, argument literal, consumer)`.
    pub uses: Vec<(usize, &'static str, &'static str)>,
}

#[cfg(test)]
impl DeclProgram {
    pub fn render(&self) -> String {
        let mut out = String::new();
        for &i in &self.order {
            let (body, as_const) = &self.helpers[i];
            let expr = match body {
                HelperBody::Id => "x".to_string(),
                HelperBody::Num => "x * 2".to_string(),
                HelperBody::Str => "x + \"!\"".to_string(),
                HelperBody::Pair => "({ first: x, second: x })".to_string(),
                HelperBody::Call(j) => format!("h{}(x)", j),
                HelperBody::CallLit(j, lit) => format!("h{}({})", j, lit),
                HelperBody::First(j) => format!("h{}(x).first", j),
                HelperBody::Prop(p) => format!("x{}", p),
                HelperBody::CallProp(j, p) => format!("h{}(x{})", j, p),
                HelperBody::Shrink => format!("x.length > 1 ? h{}(x.slice(1)) : x", i),
            };
            if *as_const {
                out.push_str(&format!("const h{} = (x) => {};\n", i, expr));
            } else {
                out.push_str(&format!("function h{}(x) {{ return {}; }}\n", i, expr));
            }
        }
        for (k, (h, arg, consumer)) in self.uses.iter().enumerate() {
            out.push_str(&format!("const r{} = h{}({});\n", k, h, arg));
            out.push_str(&consumer.replace("R", &format!("r{}", k)));
            out.push_str(";\n");
        }
        out
    }

    /// The same program with every helper written in the given form.
    pub fn with_forms(&self, as_const: impl Fn(usize) -> bool) -> DeclProgram {
        let mut p = self.clone();
        for (i, h) in p.helpers.iter_mut().enumerate() {
            h.1 = as_const(i);
        }
        p
    }
}

#[cfg(test)]
pub fn arb_decl_program() -> BoxedStrategy<DeclProgram> {
    const LITS: [&str; 6] = [
        "1",
        "\"s\"",
        "true",
        "\"abc\"",
        "[1, 2]",
        "({ first: \"s\", length: 2 })",
    ];
    const CONSUMERS: [&str; 7] = [
        "R * 2",
        "R + \"!\"",
        "R.first",
        "R",
        "R.length * 2",
        "R.slice(1)",
        "R.toUpperCase()",
    ];
    // Property reads and method calls a helper makes on its parameter:
    // some every string has, some arrays have too, some only objects.
    const PROPS: [&str; 7] = [
        ".length",
        ".slice(1)",
        ".slice(0, 1)",
        ".toUpperCase()",
        ".charCodeAt(0)",
        ".indexOf(\"s\")",
        ".first",
    ];
    (2usize..=4)
        .prop_flat_map(|n| {
            // `h_i` only calls `h_j` for `j > i`: the call graph is acyclic,
            // so evaluation terminates (the reduction relation recurses per
            // call). Declaration order is shuffled independently, so calls
            // still go forwards and backwards in the source.
            let body = |i: usize| {
                let mut arms: Vec<BoxedStrategy<HelperBody>> = vec![
                    Just(HelperBody::Id).boxed(),
                    Just(HelperBody::Num).boxed(),
                    Just(HelperBody::Str).boxed(),
                    Just(HelperBody::Pair).boxed(),
                    (0..PROPS.len())
                        .prop_map(|p| HelperBody::Prop(PROPS[p]))
                        .boxed(),
                    Just(HelperBody::Shrink).boxed(),
                ];
                if i + 1 < n {
                    arms.push(((i + 1)..n).prop_map(HelperBody::Call).boxed());
                    arms.push(
                        ((i + 1)..n, 0..LITS.len())
                            .prop_map(|(j, l)| HelperBody::CallLit(j, LITS[l]))
                            .boxed(),
                    );
                    arms.push(((i + 1)..n).prop_map(HelperBody::First).boxed());
                    arms.push(
                        ((i + 1)..n, 0..PROPS.len())
                            .prop_map(|(j, p)| HelperBody::CallProp(j, PROPS[p]))
                            .boxed(),
                    );
                }
                (proptest::strategy::Union::new(arms), any::<bool>())
            };
            let helpers: Vec<_> = (0..n).map(body).collect();
            let order = Just((0..n).collect::<Vec<usize>>()).prop_shuffle();
            let uses = proptest::collection::vec(
                (0..n, 0..LITS.len(), 0..CONSUMERS.len())
                    .prop_map(|(h, l, c)| (h, LITS[l], CONSUMERS[c])),
                1..=2,
            );
            (helpers, order, uses)
        })
        .prop_map(|(helpers, order, uses)| DeclProgram {
            helpers,
            order,
            uses,
        })
        .boxed()
}

/// Type-check `source` like the CLI does (inference, then constraint
/// resolution, with every accumulated error counted). `Ok` holds the
/// display form of each helper's scheme.
pub fn infer_helpers(source: &str, helpers: usize) -> Result<Vec<String>, String> {
    let program = crate::frontends::javascript::parse_source(source).map_err(|e| e.to_string())?;
    let mut state = InferState::new();
    let (_, env) = state
        .infer_program_with_env(&initial_env(), &program)
        .map_err(|e| e.to_string())?;
    if let Some(e) = state.errors.first() {
        return Err(e.to_string());
    }
    state.resolve_constraints().map_err(|e| e.to_string())?;
    Ok((0..helpers)
        .map(|i| match env.lookup(&format!("h{}", i)) {
            Some(scheme) => format!("{}", state.display_scheme(scheme)),
            None => "<unbound>".to_string(),
        })
        .collect())
}

/// Accepted ⇒ not stuck, for one program. Runs on a worker thread with
/// the inference stack size: generated helpers can recurse without bound,
/// and the reduction relation recurses per call until fuel runs out.
pub fn check_accepted_not_stuck(source: &str, helpers: usize) -> Result<(), String> {
    let source = source.to_string();
    crate::worker::run_with_inference_stack("inty-soundness-probe", move || {
        if infer_helpers(&source, helpers).is_err() {
            return Ok(()); // rejected: nothing to check
        }
        let program =
            crate::frontends::javascript::parse_source(&source).map_err(|e| e.to_string())?;
        match run_to_end_with_fuel(&program, 5_000) {
            Ok(_) | Err(Stuck::FuelExhausted) | Err(Stuck::NotImplemented(_)) => Ok(()),
            Err(stuck) => Err(format!("accepted by inty but STUCK: {}", stuck)),
        }
    })
}

#[cfg(test)]
mod decl_tests {
    use super::*;

    /// The programs from the generalisation fix: accepted before and
    /// stuck at runtime; rejected now.
    #[test]
    fn known_unsound_programs_are_rejected() {
        for src in [
            "function f(x) { return g(x); }\nconst g = (y) => y * 2;\nconst r = f(\"hi\");\nr;",
            "function both(x) { return pair(x, x); }\n\
             const pair = (a, b) => ({ first: a, second: b });\n\
             const b = both(1).first;\nb * 2;",
        ] {
            check_accepted_not_stuck(src, 0).unwrap_or_else(|e| panic!("{}\n{}", src, e));
        }
    }

    /// The generator must not be vacuous: a healthy share of its programs
    /// type-check, and a healthy share don't.
    #[test]
    fn decl_generator_produces_accepted_and_rejected_programs() {
        use proptest::strategy::ValueTree;
        use proptest::test_runner::{Config, TestRng, TestRunner};
        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::deterministic_rng(proptest::test_runner::RngAlgorithm::ChaCha),
        );
        let strategy = arb_decl_program();
        let (mut accepted, mut with_props, total) = (0, 0, 600);
        for _ in 0..total {
            let p = strategy.new_tree(&mut runner).unwrap().current();
            if infer_helpers(&p.render(), p.helpers.len()).is_ok() {
                accepted += 1;
                if p.helpers.iter().any(|(b, _)| {
                    matches!(
                        b,
                        HelperBody::Prop(_) | HelperBody::CallProp(..) | HelperBody::Shrink
                    )
                }) {
                    with_props += 1;
                }
            }
        }
        assert!(
            accepted >= total / 10 && accepted <= total * 9 / 10,
            "{} of {} generated programs type-check",
            accepted,
            total
        );
        // Accepted programs whose helpers read properties of a parameter
        // of unknown type — the `HasProp` path — are well represented.
        assert!(
            with_props >= accepted / 4,
            "only {} of {} accepted programs read properties of a parameter",
            with_props,
            accepted
        );
    }

    // 256 cases by default; set PROPTEST_CASES for a longer soak.
    proptest! {
        #![proptest_config(ProptestConfig::default())]

        #[test]
        fn accepted_programs_never_get_stuck(p in arb_decl_program()) {
            let src = p.render();
            check_accepted_not_stuck(&src, p.helpers.len())
                .map_err(|e| TestCaseError::fail(format!("source:\n{}\n{}", src, e)))?;
        }

        #[test]
        fn declaration_form_does_not_change_typing(p in arb_decl_program()) {
            let n = p.helpers.len();
            let as_functions = p.with_forms(|_| false).render();
            let as_consts = p.with_forms(|_| true).render();
            let mixed = p.render();
            let reference = infer_helpers(&as_functions, n).map_err(|_| ());
            for (label, src) in [("const", &as_consts), ("mixed", &mixed)] {
                let other = infer_helpers(src, n).map_err(|_| ());
                prop_assert_eq!(
                    &reference,
                    &other,
                    "{} form typed differently from `function` form\n--- function form:\n{}--- {} form:\n{}",
                    label,
                    as_functions,
                    label,
                    src
                );
            }
        }
    }
}
