//! Property + metamorphic tests for Python `class` lowering and nominal
//! instance branding.
//!
//! The unit tests in `frontends::python::tests` pin concrete cases; this
//! file asserts *relational* invariants over randomly generated class
//! shapes, where there's no simple oracle for "is this well-typed?" but
//! there is a property that must hold regardless of the shape:
//!
//!   - **Rename invariance.** A brand's identity is its allocated id, not
//!     its name, so renaming a class (and its uses) must not change the
//!     accept/reject outcome. Catches any path where branding or
//!     unification accidentally keys off the class *name*.
//!   - **Brand distinctness.** Two *distinct* classes never interchange,
//!     whatever their fields — even when structurally identical.
//!   - **Access transparency.** Branding is invisible to field access:
//!     reading a declared field always checks; reading an absent one
//!     always fails (the instance row stays closed through the brand).
//!   - **Per-instantiation generics.** A generic class brands per call
//!     site, so two instances at different element types don't contaminate
//!     each other (which a monomorphic brand would).
//!
//! See `docs/pyi-import-mapping.md` §8.

use proptest::prelude::*;

use inty::frontends::{parse, Language};
use inty::stdlib::initial_env_with_stdlib;

/// `true` iff `src` parses and type-checks with no errors. Mirrors the
/// CLI's accept condition: a clean inference run, no accumulated
/// `Type::Error` recoveries, and no unresolved type-class constraints.
fn checks(src: &str) -> bool {
    let Ok(program) = parse(Language::Python, src) else {
        return false;
    };
    let Ok((env, mut state)) = initial_env_with_stdlib() else {
        return false;
    };
    if state.infer_program_with_env(&env, &program).is_err() {
        return false;
    }
    if state.resolve_constraints().is_err() {
        return false;
    }
    state.errors.is_empty()
}

/// `true` iff `src` parses (used to keep generated inputs honest).
fn parses(src: &str) -> bool {
    parse(Language::Python, src).is_ok()
}

/// The printed type of the program's final statement, or `None` if it
/// doesn't cleanly type-check. Used to compare brand structure across a
/// rename.
fn program_type(src: &str) -> Option<String> {
    let program = parse(Language::Python, src).ok()?;
    let (env, mut state) = initial_env_with_stdlib().ok()?;
    let (ty, _) = state.infer_program_with_env(&env, &program).ok()?;
    state.resolve_constraints().ok()?;
    if !state.errors.is_empty() {
        return None;
    }
    let resolved = state.apply_subst(&ty);
    // Render brands by their declared name (a bare context prints them
    // anonymously as `μ<id>`).
    let names: std::collections::HashMap<_, _> = state
        .named_types
        .iter()
        .filter_map(|(id, d)| {
            if d.nominal {
                d.name.clone().map(|n| (*id, n))
            } else {
                None
            }
        })
        .collect();
    let mut ctx = inty::types::PrettyContext::with_nominal_names(names);
    Some(ctx.format_type(&resolved))
}

const FIELD_POOL: [&str; 4] = ["fa", "fb", "fc", "fd"];
/// A field name guaranteed never produced by `fields_strategy`.
const ABSENT_FIELD: &str = "fz";
const VALUES: [&str; 3] = ["1", "\"s\"", "True"];

/// Generate a non-empty set of `(field, value-literal)` pairs with
/// distinct field names drawn from a small pool.
fn fields_strategy() -> impl Strategy<Value = Vec<(String, String)>> {
    proptest::sample::subsequence(FIELD_POOL.to_vec(), 1..=FIELD_POOL.len())
        .prop_flat_map(|names| {
            let n = names.len();
            let vals = prop::collection::vec(proptest::sample::select(VALUES.to_vec()), n);
            (Just(names), vals)
        })
        .prop_map(|(names, vals)| {
            names
                .into_iter()
                .map(String::from)
                .zip(vals.into_iter().map(String::from))
                .collect()
        })
}

/// Render a class whose `__init__` takes one parameter per field and
/// assigns it, e.g.
///
/// ```text
/// class Name:
///     def __init__(self, fa, fb):
///         self.fa = fa
///         self.fb = fb
/// ```
fn render_class(name: &str, fields: &[(String, String)]) -> String {
    let params: Vec<&str> = fields.iter().map(|(f, _)| f.as_str()).collect();
    let mut s = format!(
        "class {}:\n    def __init__(self, {}):\n",
        name,
        params.join(", ")
    );
    for (f, _) in fields {
        s.push_str(&format!("        self.{} = {}\n", f, f));
    }
    s
}

/// A constructor call supplying each field's value literal positionally.
fn render_ctor_call(name: &str, fields: &[(String, String)]) -> String {
    let args: Vec<&str> = fields.iter().map(|(_, v)| v.as_str()).collect();
    format!("{}({})", name, args.join(", "))
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 48, ..ProptestConfig::default() })]

    /// Reading any *declared* field of an instance type-checks; the
    /// generated programs must also always parse.
    #[test]
    fn declared_field_reads_check(fields in fields_strategy()) {
        let mut src = render_class("Klass", &fields);
        src.push_str(&format!("inst = {}\n", render_ctor_call("Klass", &fields)));
        for (f, _) in &fields {
            src.push_str(&format!("read_{} = inst.{}\n", f, f));
        }
        prop_assert!(parses(&src), "generated program must parse:\n{}", src);
        prop_assert!(checks(&src), "reading declared fields should type-check:\n{}", src);
    }

    /// Reading a field the class never declares is rejected — the
    /// instance row stays closed *through* the brand.
    #[test]
    fn absent_field_read_is_rejected(fields in fields_strategy()) {
        let mut src = render_class("Klass", &fields);
        src.push_str(&format!("inst = {}\n", render_ctor_call("Klass", &fields)));
        src.push_str(&format!("oops = inst.{}\n", ABSENT_FIELD));
        prop_assert!(parses(&src), "generated program must parse:\n{}", src);
        prop_assert!(!checks(&src), "reading an absent field must fail:\n{}", src);
    }

    /// Brand identity is the allocated id, not the source name: renaming
    /// a class and all its uses preserves the accept/reject outcome.
    #[test]
    fn class_rename_preserves_outcome(
        fields in fields_strategy(),
        read_absent in any::<bool>(),
    ) {
        let build = |name: &str| {
            let mut src = render_class(name, &fields);
            src.push_str(&format!("inst = {}\n", render_ctor_call(name, &fields)));
            // Either a valid read (outcome: ok) or an absent read
            // (outcome: err) — both must be invariant under renaming.
            let field = if read_absent { ABSENT_FIELD } else { fields[0].0.as_str() };
            src.push_str(&format!("val = inst.{}\n", field));
            src
        };
        let a = build("Alpha");
        let b = build("Bravo");
        prop_assert!(parses(&a) && parses(&b));
        prop_assert_eq!(
            checks(&a),
            checks(&b),
            "renaming a class changed the outcome:\n--- Alpha ---\n{}\n--- Bravo ---\n{}",
            a, b
        );
    }

    /// Two *distinct* classes never interchange, even with identical
    /// fields. Reassigning a binding across the two brands must fail.
    #[test]
    fn distinct_classes_never_interchange(
        fa in fields_strategy(),
        fb in fields_strategy(),
    ) {
        let mut src = render_class("Aaa", &fa);
        src.push_str(&render_class("Bbb", &fb));
        src.push_str(&format!("v = {}\n", render_ctor_call("Aaa", &fa)));
        src.push_str(&format!("v = {}\n", render_ctor_call("Bbb", &fb)));
        prop_assert!(parses(&src), "generated program must parse:\n{}", src);
        prop_assert!(
            !checks(&src),
            "two distinct class brands must not unify:\n{}",
            src
        );
    }

    /// Stronger than outcome invariance: the *inferred instance type*
    /// must be identical up to the class name. Ending in a bare `inst`
    /// expression makes the program type the brand itself.
    #[test]
    fn class_rename_preserves_instance_type(fields in fields_strategy()) {
        let build = |name: &str| {
            let mut src = render_class(name, &fields);
            src.push_str(&format!("inst = {}\n", render_ctor_call(name, &fields)));
            src.push_str("inst\n");
            src
        };
        let a = build("Alpha");
        let b = build("Bravo");
        let ta = program_type(&a).expect("Alpha should type-check");
        let tb = program_type(&b).expect("Bravo should type-check");
        // Normalise the brand name out of each so only structure remains.
        prop_assert_eq!(
            ta.replace("Alpha", "Brand"),
            tb.replace("Bravo", "Brand"),
            "instance type differed under rename"
        );
        // And the brand name really is present (we're comparing brands,
        // not accidentally-unrolled rows).
        prop_assert!(ta.contains("Alpha"), "expected a brand type, got {}", ta);
    }

    /// Reassigning a binding between two instances of the *same* class
    /// type-checks (same brand, matching field value types).
    #[test]
    fn same_class_reassignment_checks(fields in fields_strategy()) {
        let mut src = render_class("Same", &fields);
        src.push_str(&format!("v = {}\n", render_ctor_call("Same", &fields)));
        src.push_str(&format!("v = {}\n", render_ctor_call("Same", &fields)));
        prop_assert!(parses(&src), "generated program must parse:\n{}", src);
        prop_assert!(checks(&src), "same-brand reassignment should check:\n{}", src);
    }
}

/// A generic class brands per call site: constructing two instances at
/// different element types must not contaminate each other. A monomorphic
/// brand would force the second construction to unify with the first and
/// fail; per-instantiation branding keeps them independent.
#[test]
fn generic_class_brands_per_instantiation() {
    for (v1, v2) in [("1", "\"s\""), ("\"s\"", "1"), ("True", "1"), ("1", "True")] {
        let src = format!(
            "class Box:\n    def __init__(self, v):\n        self.value = v\n\
             a = Box({v1})\nb = Box({v2})\nx = a.value\ny = b.value\n"
        );
        assert!(
            checks(&src),
            "Box<{}> and Box<{}> should construct independently:\n{}",
            v1,
            v2,
            src
        );
    }
}

/// Field access reads *through* the brand to the representation's field
/// type, so a String field combined with `+ 1` is a type error while a
/// Number field is fine — the brand doesn't hide the field's real type.
#[test]
fn field_type_is_visible_through_brand() {
    let ok = "class Box:\n    def __init__(self, v):\n        self.value = v\n\
              b = Box(1)\nn = b.value + 1\n";
    assert!(checks(ok), "Number field + 1 should check:\n{}", ok);

    let bad = "class Box:\n    def __init__(self, v):\n        self.value = v\n\
               b = Box(\"s\")\nn = b.value + 1\n";
    assert!(
        !checks(bad),
        "String field + 1 must fail through the brand:\n{}",
        bad
    );
}
