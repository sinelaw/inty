//! Type-checker oracle for metamorphic testing.
//!
//! Running the type checker on a program gives either an error or a
//! successful result. We encode the successful result as:
//!
//!   - the program's reported type (the last statement's type), and
//!   - a map from each user-introduced binding name to its printed
//!     type scheme.
//!
//! Both pieces use a normalising pretty-printer so that fresh-variable
//! numbering differences between runs don't show up as spurious
//! disagreements. When comparing two programs we explicitly describe
//! which names correspond via [`Comparison`] — most transformations
//! preserve all names (identity), but a rename transformation maps one
//! name to another, and transformations that inject temps declare
//! those in `p_only` / `q_only` so they're excluded.

use std::collections::{BTreeMap, HashSet};

use minfern::infer::{InferState, TypeEnv};
use minfern::parser::ast::Program;
use minfern::parser::pretty::print_program;
use minfern::stdlib::initial_env_with_stdlib;
use minfern::types::PrettyContext;

/// Successful check result. `program_ty` is the top-level program's
/// type; `bindings` is the set of bindings the program *introduced*
/// (stdlib names are filtered out unless the program shadowed them).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckOk {
    pub program_ty: String,
    pub bindings: BTreeMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    Ok(CheckOk),
    /// The type checker rejected the program. We don't compare error
    /// messages across runs — those are brittle — only that both runs
    /// ended up here.
    Err,
}

pub fn check(program: &Program) -> CheckResult {
    let (env, mut state) = match initial_env_with_stdlib() {
        Ok(r) => r,
        Err(_) => return CheckResult::Err,
    };
    run_check(env, &mut state, program)
}

fn run_check(env: TypeEnv, state: &mut InferState, program: &Program) -> CheckResult {
    // Snapshot the starting env so we can later filter out everything
    // stdlib already supplied — we only care about what the program
    // introduced or shadowed.
    let base_names: HashSet<String> = env.names().cloned().collect();
    let base_schemes: BTreeMap<String, String> = env
        .iter()
        .map(|(name, scheme)| {
            let mut ctx = PrettyContext::new();
            (name.clone(), ctx.format_scheme(scheme))
        })
        .collect();

    let (program_ty, final_env) = match state.infer_program_with_env(&env, program) {
        Ok(r) => r,
        Err(_) => return CheckResult::Err,
    };
    if state.resolve_constraints().is_err() {
        return CheckResult::Err;
    }

    let mut ctx = PrettyContext::new();
    let program_ty = ctx.format_type(&state.apply_subst(&program_ty));

    // For each name in the final env, decide whether it belongs in the
    // result: names the program added are always included; stdlib names
    // are included only if their scheme changed (the program shadowed
    // them). Each binding gets a fresh PrettyContext so its printed
    // representation is self-contained — no cross-binding numbering
    // dependency.
    let mut bindings = BTreeMap::new();
    for (name, scheme) in final_env.iter() {
        let mut ctx = PrettyContext::new();
        let printed = ctx.format_scheme(scheme);
        if base_names.contains(name) {
            if base_schemes.get(name) != Some(&printed) {
                bindings.insert(name.clone(), printed);
            }
        } else {
            bindings.insert(name.clone(), printed);
        }
    }

    CheckResult::Ok(CheckOk {
        program_ty,
        bindings,
    })
}

// -------------------------------------------------------------------------
// Comparison spec — how the two programs' bindings correspond.
//
// Default is identity: every binding name in p should also appear in q
// with the same printed scheme. Renames and excluded sets override that
// on a per-name basis. The comparison logic splits bindings into:
//
//   - renamed:  compared via the explicit mapping
//   - p_only:   present only in p, skipped
//   - q_only:   present only in q, skipped
//   - shared:   everything else, must match
// -------------------------------------------------------------------------

#[derive(Default, Debug, Clone)]
pub struct Comparison {
    pub rename: Vec<(String, String)>,
    pub p_only: HashSet<String>,
    pub q_only: HashSet<String>,
}

impl Comparison {
    pub fn identity() -> Self {
        Self::default()
    }

    pub fn with_p_only(mut self, names: impl IntoIterator<Item = String>) -> Self {
        self.p_only.extend(names);
        self
    }

    pub fn with_q_only(mut self, names: impl IntoIterator<Item = String>) -> Self {
        self.q_only.extend(names);
        self
    }

    pub fn with_rename(mut self, from: String, to: String) -> Self {
        self.rename.push((from, to));
        self
    }
}

/// Core consistency assertion. Either both runs succeed with matching
/// types (up to the rename / excluded-name spec) or both fail.
pub fn assert_consistent(label: &str, p: &Program, q: &Program, cmp: &Comparison) {
    let r_p = check(p);
    let r_q = check(q);

    match (&r_p, &r_q) {
        (CheckResult::Err, CheckResult::Err) => return,
        (CheckResult::Ok(_), CheckResult::Err) | (CheckResult::Err, CheckResult::Ok(_)) => {
            panic!(
                "metamorphic property `{label}` violated: one side ok, other err\n\
                 p:\n{}\nresult(p): {:?}\n\
                 q:\n{}\nresult(q): {:?}\n",
                print_program(p),
                r_p,
                print_program(q),
                r_q,
            );
        }
        (CheckResult::Ok(ok_p), CheckResult::Ok(ok_q)) => {
            // Program type: always expected to match, regardless of
            // rename spec. Transformations that change which statement
            // ends up last should exclude themselves from this oracle,
            // not be "allowed" here.
            assert_eq!(
                ok_p.program_ty, ok_q.program_ty,
                "metamorphic property `{label}`: program-level type differs\n\
                 p:\n{}\np.type = {}\nq:\n{}\nq.type = {}\n",
                print_program(p),
                ok_p.program_ty,
                print_program(q),
                ok_q.program_ty,
            );

            let mut p_bindings = ok_p.bindings.clone();
            let mut q_bindings = ok_q.bindings.clone();

            // Excluded names: drop silently.
            for name in &cmp.p_only {
                p_bindings.remove(name);
            }
            for name in &cmp.q_only {
                q_bindings.remove(name);
            }

            // Explicit renames: each (old, new) pair removes one entry
            // from each side and asserts their printed types match.
            for (old, new) in &cmp.rename {
                let left = p_bindings.remove(old).unwrap_or_else(|| {
                    panic!(
                        "metamorphic property `{label}`: renamed name `{old}` \
                         absent from p's bindings\np bindings: {:?}",
                        ok_p.bindings
                    )
                });
                let right = q_bindings.remove(new).unwrap_or_else(|| {
                    panic!(
                        "metamorphic property `{label}`: renamed name `{new}` \
                         absent from q's bindings\nq bindings: {:?}",
                        ok_q.bindings
                    )
                });
                assert_eq!(
                    left, right,
                    "metamorphic property `{label}`: types for renamed \
                     binding `{old}`→`{new}` differ\np:\n{}\nq:\n{}\n",
                    print_program(p),
                    print_program(q),
                );
            }

            // Shared names: everything that's left must match by name
            // and printed type.
            assert_eq!(
                p_bindings, q_bindings,
                "metamorphic property `{label}`: shared-bindings map differs\n\
                 p:\n{}\nq:\n{}\np.bindings = {:#?}\nq.bindings = {:#?}\n",
                print_program(p),
                print_program(q),
                p_bindings,
                q_bindings,
            );
        }
    }
}
