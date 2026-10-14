//! The pipeline: enumerate, sort, observe, search, verify.
//!
//! 1. Enumerate every term up to a size and run it: the corpus.
//! 2. Partition the values into sorts by behaviour (`sorts`).
//! 3. Observe each constructor locally: for every corpus term whose
//!    children all evaluate to sorted values, record the children's sorts
//!    and what the term did.
//! 4. Search each constructor's rules on its own. Because sorts are
//!    semantic, not syntactic, a rule's soundness is a local fact (its
//!    compatibility lemma), so the search factors by constructor:
//!    enumerate the schemas, refute the ones an observation contradicts,
//!    refute the ones a sampled compatibility test breaks, and cover the
//!    child sort tuples, weighted by how often the corpus runs each, with
//!    as few and as general rules as possible.
//! 5. Check the composed system end to end on a larger corpus than it was
//!    learned from: every typed term must run to a value of its type, and
//!    the safe terms it can't type measure what it gave up.

use crate::enumerate::terms_up_to;
use crate::lang::{Language, Outcome, Term};
use crate::rules::{all_tuples, anti_unify, enumerate_schemas, Pat, RuleSet, Schema, Show};
use crate::sorts::{Oracle, SortId, Sorts};
use std::collections::{BTreeMap, HashSet};
use std::fmt;

#[derive(Clone, Debug)]
pub struct Config {
    /// Terms up to this size are observed.
    pub learn_size: usize,
    /// Terms up to this size check the result.
    pub check_size: usize,
    /// Values filling the other holes of a fingerprinting context.
    pub probes: usize,
    /// Values per sort tried in a compatibility test.
    pub samples: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            learn_size: 4,
            check_size: 6,
            probes: 8,
            samples: 6,
        }
    }
}

/// What a term did, abstracted to sorts.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Res {
    Sort(SortId),
    Stuck,
    Fault,
    /// A value no pool value behaves like.
    Unsorted,
}

#[derive(Default)]
struct Obs {
    counts: BTreeMap<Res, usize>,
    example: BTreeMap<Res, Term>,
}

/// One constructor's search.
pub struct ConSearch {
    pub con: String,
    pub candidates: usize,
    pub refuted_by_observation: usize,
    pub refuted_by_compatibility: usize,
    pub chosen: Vec<Schema>,
    /// The most general schema refuted, and the term that refuted it.
    pub best_refuted: Option<(Schema, String)>,
    /// When `chosen` folds into one schema: it, and its variables' instances.
    pub class: Option<(Schema, Vec<Vec<SortId>>)>,
}

pub struct Check {
    pub size: usize,
    pub terms: usize,
    pub safe: usize,
    pub typed: usize,
    /// Typed terms that get stuck or give a value of another type.
    pub unsound: usize,
    pub violations: Vec<String>,
    pub untyped_safe: usize,
    pub untyped_safe_examples: Vec<String>,
}

pub struct Discovery {
    pub language: String,
    pub config: Config,
    pub sort_names: Vec<String>,
    pub sort_examples: Vec<Vec<String>>,
    pub searches: Vec<ConSearch>,
    pub rules: RuleSet,
    pub check: Check,
    pub evals: usize,
}

pub fn discover<L: Language>(lang: &L, cfg: &Config) -> Discovery {
    let sig = lang.signature();
    let mut oracle = Oracle::new(lang);

    // 1. The corpus, and the values it reaches.
    let corpus = terms_up_to(sig, cfg.learn_size);
    let mut seen = HashSet::new();
    let mut pool = Vec::new();
    for t in &corpus {
        if let Outcome::Value(v) = oracle.eval(t) {
            if seen.insert(v.clone()) {
                pool.push(v);
            }
        }
    }
    let probes: Vec<L::Value> = pool.iter().take(cfg.probes).cloned().collect();

    // 2. Sorts.
    let mut sorts = Sorts::discover(&mut oracle, &pool, &probes);
    let nsorts = sorts.count();
    let sort_names: Vec<String> = (0..nsorts).map(|s| format!("T{s}")).collect();
    let sort_examples = (0..nsorts)
        .map(|s| {
            sorts.members[s]
                .iter()
                .take(4)
                .map(|v| lang.show_value(v))
                .collect()
        })
        .collect();

    // 3. Observations.
    let mut table: BTreeMap<(usize, Vec<SortId>), Obs> = BTreeMap::new();
    for t in &corpus {
        let mut kid_sorts = Vec::new();
        for k in &t.kids {
            match oracle.eval(k) {
                Outcome::Value(v) => match sorts.classify(&mut oracle, &v) {
                    Some(s) => kid_sorts.push(s),
                    None => break,
                },
                _ => break,
            }
        }
        if kid_sorts.len() != t.kids.len() {
            continue;
        }
        let res = match oracle.eval(t) {
            Outcome::Value(v) => sorts
                .classify(&mut oracle, &v)
                .map_or(Res::Unsorted, Res::Sort),
            Outcome::Stuck(_) => Res::Stuck,
            Outcome::Fault(_) => Res::Fault,
            Outcome::Timeout => continue,
        };
        let obs = table.entry((t.con, kid_sorts)).or_default();
        *obs.counts.entry(res).or_default() += 1;
        obs.example.entry(res).or_insert_with(|| t.clone());
    }

    // 4. Search, one constructor at a time.
    let mut searches = Vec::new();
    let mut rules = RuleSet::default();
    for (ci, c) in sig.iter().enumerate() {
        let candidates = enumerate_schemas(ci, c.arity, nsorts);
        let mut s = ConSearch {
            con: c.name.to_string(),
            candidates: candidates.len(),
            refuted_by_observation: 0,
            refuted_by_compatibility: 0,
            chosen: Vec::new(),
            best_refuted: None,
            class: None,
        };
        let mut sound = Vec::new();
        let mut refuted: Vec<(Schema, Term)> = Vec::new();
        for schema in candidates {
            if let Some(w) = contradicts(&schema, ci, &table) {
                s.refuted_by_observation += 1;
                refuted.push((schema, w));
            } else if let Some(w) = incompatible(&schema, &mut oracle, &mut sorts, cfg.samples) {
                s.refuted_by_compatibility += 1;
                refuted.push((schema, w));
            } else {
                sound.push(schema);
            }
        }
        s.best_refuted = refuted
            .into_iter()
            .max_by_key(|(r, _)| (r.generality(nsorts), std::cmp::Reverse(r.constants())))
            .map(|(r, w)| (r, lang.show_term(&w)));

        // Cover as many child sort tuples as possible: each counts once,
        // plus how often the corpus ran the constructor on it safely. A
        // chosen rule is sound, so whatever tuple it accepts it types right.
        let targets: Vec<(Vec<SortId>, usize)> = all_tuples(c.arity, nsorts)
            .into_iter()
            .map(|ks| {
                let seen = table.get(&(ci, ks.clone())).map_or(0, |obs| {
                    obs.counts
                        .iter()
                        .filter(|(r, _)| matches!(r, Res::Sort(_)))
                        .map(|(_, n)| n)
                        .sum()
                });
                (ks, 1 + seen)
            })
            .collect();
        let mut covered = vec![false; targets.len()];
        loop {
            let gain = |r: &Schema| -> usize {
                targets
                    .iter()
                    .zip(&covered)
                    .filter(|((ks, _), done)| !**done && r.apply(ks).is_some())
                    .map(|((_, w), _)| w)
                    .sum()
            };
            let Some(best) = sound
                .iter()
                .max_by_key(|r| (gain(r), std::cmp::Reverse(r.constants())))
                .filter(|r| gain(r) > 0)
                .cloned()
            else {
                break;
            };
            for ((ks, _), done) in targets.iter().zip(covered.iter_mut()) {
                *done |= best.apply(ks).is_some();
            }
            s.chosen.push(best);
        }
        if s.chosen.len() > 1 {
            s.class = Some(anti_unify(&s.chosen));
        }
        rules.rules.extend(s.chosen.iter().cloned());
        searches.push(s);
    }

    // 5. Check end to end.
    let check = check(lang, &mut oracle, &mut sorts, &rules, cfg.check_size);
    Discovery {
        language: lang.name().to_string(),
        config: cfg.clone(),
        sort_names,
        sort_examples,
        searches,
        rules,
        check,
        evals: oracle.evals,
    }
}

/// An observed term the schema types wrongly: it gets stuck, or runs to a
/// value of another sort.
fn contradicts(
    schema: &Schema,
    con: usize,
    table: &BTreeMap<(usize, Vec<SortId>), Obs>,
) -> Option<Term> {
    for ((c, ks), obs) in table {
        if *c != con {
            continue;
        }
        let Some(p) = schema.apply(ks) else { continue };
        for (res, t) in &obs.example {
            if !matches!(res, Res::Fault) && *res != Res::Sort(p) {
                return Some(t.clone());
            }
        }
    }
    None
}

/// The schema's compatibility lemma, tested: for every instance of its
/// variables and sampled values of its argument sorts, the constructor
/// applied to them runs to a value of the result sort (or an allowed
/// fault, or out of fuel). Returns a term that breaks it.
fn incompatible<L: Language>(
    schema: &Schema,
    oracle: &mut Oracle<L>,
    sorts: &mut Sorts<L::Value>,
    samples: usize,
) -> Option<Term> {
    let nsorts = sorts.count();
    let con = &oracle.lang.signature()[schema.con];
    for assign in all_tuples(schema.vars(), nsorts) {
        let sort_of = |p: &Pat| match *p {
            Pat::Sort(s) => s,
            Pat::Var(v) => assign[v],
        };
        let expect = sort_of(&schema.res);
        let pools: Vec<Vec<Term>> = schema
            .args
            .iter()
            .map(|p| {
                sorts
                    .samples(sort_of(p), samples)
                    .iter()
                    .map(|v| oracle.lang.quote(v))
                    .collect()
            })
            .collect();
        let refs: Vec<&[Term]> = pools.iter().map(|p| p.as_slice()).collect();
        let mut terms = Vec::new();
        for atom in con.atoms_or_none() {
            crate::enumerate::product(&refs, &mut Vec::new(), &mut |kids| {
                terms.push(Term {
                    con: schema.con,
                    atom: atom.clone(),
                    kids: kids.to_vec(),
                })
            });
        }
        for t in terms {
            let ok = match oracle.eval(&t) {
                Outcome::Value(v) => sorts.classify(oracle, &v) == Some(expect),
                Outcome::Stuck(_) => false,
                Outcome::Fault(_) | Outcome::Timeout => true,
            };
            if !ok {
                return Some(t);
            }
        }
    }
    None
}

fn check<L: Language>(
    lang: &L,
    oracle: &mut Oracle<L>,
    sorts: &mut Sorts<L::Value>,
    rules: &RuleSet,
    size: usize,
) -> Check {
    let terms = terms_up_to(lang.signature(), size);
    let mut c = Check {
        size,
        terms: terms.len(),
        safe: 0,
        typed: 0,
        unsound: 0,
        violations: Vec::new(),
        untyped_safe: 0,
        untyped_safe_examples: Vec::new(),
    };
    for t in &terms {
        let out = oracle.eval(t);
        if matches!(out, Outcome::Timeout) {
            continue;
        }
        let safe = !matches!(out, Outcome::Stuck(_));
        c.safe += safe as usize;
        let types = rules.type_of(t);
        if types.is_empty() {
            if safe {
                c.untyped_safe += 1;
                if c.untyped_safe_examples.len() < 3 {
                    c.untyped_safe_examples.push(lang.show_term(t));
                }
            }
            continue;
        }
        c.typed += 1;
        let good = match &out {
            Outcome::Value(v) => {
                let s = sorts.classify(oracle, v);
                types.iter().all(|ty| s == Some(*ty))
            }
            Outcome::Fault(_) | Outcome::Timeout => true,
            Outcome::Stuck(_) => false,
        };
        if !good {
            c.unsound += 1;
            if c.violations.len() < 5 {
                c.violations.push(format!(
                    "{} : {:?} but gives {:?}",
                    lang.show_term(t),
                    types,
                    out
                ));
            }
        }
    }
    c
}

impl Discovery {
    pub fn show<'a>(&'a self, r: &'a Schema) -> Show<'a> {
        Show {
            schema: r,
            con: &self.searches[r.con].con,
            sort_names: &self.sort_names,
        }
    }

    /// The chosen rules, printed one per line.
    pub fn rule_strings(&self) -> Vec<String> {
        self.rules
            .rules
            .iter()
            .map(|r| self.show(r).to_string())
            .collect()
    }
}

impl fmt::Display for Discovery {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "language: {}", self.language)?;
        writeln!(
            f,
            "learned from terms of size <= {}, checked on size <= {}\n",
            self.config.learn_size, self.config.check_size
        )?;
        writeln!(
            f,
            "sorts (values that get stuck in the same immediate contexts):"
        )?;
        for (n, ex) in self.sort_names.iter().zip(&self.sort_examples) {
            writeln!(f, "  {n} = {{{}, ...}}", ex.join(", "))?;
        }
        writeln!(f, "\nrules:")?;
        for s in &self.searches {
            if s.chosen.is_empty() {
                writeln!(f, "  {} : (no rule; not typable)", s.con)?;
            }
            for r in &s.chosen {
                writeln!(f, "  {}", self.show(r))?;
            }
            if let Some((r, inst)) = &s.class {
                let names = |t: &Vec<SortId>| {
                    let n: Vec<&str> = t.iter().map(|&s| self.sort_names[s].as_str()).collect();
                    if n.len() == 1 {
                        n[0].to_string()
                    } else {
                        format!("({})", n.join(", "))
                    }
                };
                let vars: Vec<String> = (0..r.vars())
                    .map(|v| ((b'a' + v as u8) as char).to_string())
                    .collect();
                let inst: Vec<String> = inst.iter().map(names).collect();
                let vars = if vars.len() == 1 {
                    vars[0].clone()
                } else {
                    format!("({})", vars.join(", "))
                };
                writeln!(
                    f,
                    "    = class: {}  where {vars} in {{{}}}",
                    self.show(r),
                    inst.join(", ")
                )?;
            }
        }
        writeln!(f, "\nsearch:")?;
        for s in &self.searches {
            write!(
                f,
                "  {:<8} {:>5} schemas, {:>5} refuted by observation, {:>5} by compatibility testing",
                s.con, s.candidates, s.refuted_by_observation, s.refuted_by_compatibility
            )?;
            if let Some((r, w)) = &s.best_refuted {
                write!(f, "; e.g. {} fails on {w}", self.show(r))?;
            }
            writeln!(f)?;
        }
        let c = &self.check;
        writeln!(
            f,
            "\nend-to-end check on all {} terms of size <= {}:",
            c.terms, c.size
        )?;
        writeln!(f, "  safe terms:           {}", c.safe)?;
        writeln!(f, "  typed terms:          {}", c.typed)?;
        writeln!(f, "  typed but unsound:    {}", c.unsound)?;
        for v in &c.violations {
            writeln!(f, "    {v}")?;
        }
        writeln!(
            f,
            "  safe but untyped:     {} ({:.1}% of safe terms typed)",
            c.untyped_safe,
            100.0 * c.typed as f64 / c.safe.max(1) as f64
        )?;
        for e in &c.untyped_safe_examples {
            writeln!(f, "    e.g. {e}")?;
        }
        writeln!(f, "  evaluations:          {}", self.evals)
    }
}
