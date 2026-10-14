//! The pipeline: enumerate, find the sorts, search each constructor's
//! rules, then check the whole system on terms it never saw.
//!
//! 1. Enumerate every closed term up to a size and run it: the values
//!    reached are the pool, and the terms are representatives of their
//!    types.
//! 2. Find the sorts, which of them are refined, and the universe of
//!    ground types (`semantics`).
//! 3. Search each constructor's rules on its own (`search`). Because types
//!    mean sets of values, a rule's soundness is a local fact, its
//!    compatibility lemma, so the search factors by constructor.
//! 4. Check the composed system end to end, with the checker it induces
//!    (`infer`): every typed term must run to a value of its type, on all
//!    terms up to a size and on random bigger ones. The safe terms it
//!    can't type measure what it gave up.

use crate::enumerate::{Enumerator, Rng};
use crate::infer::Checker;
use crate::lang::{Atom, Kind, Language, Outcome, Term};
use crate::search::{search_con, ConSearch, Pools, SearchConfig};
use crate::semantics::{Oracle, Semantics};
use crate::types::{lgg, Names, Schema, Ty};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Clone, Debug)]
pub struct Config {
    /// Closed terms up to this size make the pool.
    pub corpus_size: usize,
    /// Open terms up to this size are the bodies under binders.
    pub open_size: usize,
    /// Values filling the other holes of a fingerprinting context.
    pub probes: usize,
    pub samples_per_type: usize,
    pub search: SearchConfig,
    /// All closed terms up to this size check the result...
    pub check_size: usize,
    /// ...and this many random ones up to `random_size`.
    pub random_terms: usize,
    pub random_size: usize,
    pub seed: u64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            corpus_size: 4,
            open_size: 3,
            probes: 8,
            samples_per_type: 3,
            search: SearchConfig::default(),
            check_size: 4,
            random_terms: 20000,
            random_size: 9,
            seed: 1,
        }
    }
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
    pub con_names: Vec<&'static str>,
    pub sort_names: Vec<String>,
    pub sort_examples: Vec<Vec<String>>,
    /// Per sort, the eliminator it is refined by.
    pub refined_by: Vec<Option<String>>,
    pub universe: usize,
    pub searches: Vec<ConSearch>,
    pub rules: Vec<Schema>,
    pub check: Check,
    pub evals: usize,
}

pub fn discover<L: Language>(lang: &L, cfg: &Config) -> Discovery {
    let sig = lang.signature();
    let mut oracle = Oracle::new(lang);
    let mut rng = Rng(cfg.seed);

    // 1. The corpus and its values, each with the smallest term giving it.
    let mut en = Enumerator::new(sig, cfg.corpus_size.max(cfg.open_size));
    en.cap = 400_000;
    let corpus = en.up_to(cfg.corpus_size, 0);
    let mut pool = Vec::new();
    let mut origin: HashMap<L::Value, Term> = HashMap::new();
    for t in &corpus {
        if let Outcome::Value(v) = oracle.eval(t) {
            if !origin.contains_key(&v) {
                origin.insert(v.clone(), t.clone());
                pool.push(v);
            }
        }
    }
    let probes: Vec<L::Value> = pool.iter().take(cfg.probes).cloned().collect();
    let clock = std::time::Instant::now();
    let trace = std::env::var_os("TYSEARCH_TRACE").is_some();
    let note = |what: &str| {
        if trace {
            eprintln!("[{:>7.2}s] {what}", clock.elapsed().as_secs_f64());
        }
    };
    note(&format!(
        "corpus {} terms, pool {} values",
        corpus.len(),
        pool.len()
    ));

    // 2. Sorts, refinements and the universe.
    let mut sem = Semantics::discover(&mut oracle, &pool, &probes, cfg.samples_per_type);
    let nsorts = sem.count();
    note(&format!("{nsorts} sorts, universe {}", sem.universe.len()));
    let sort_names: Vec<String> = (0..nsorts).map(|s| format!("T{s}")).collect();
    let sort_examples = (0..nsorts)
        .map(|s| {
            sem.members[s]
                .iter()
                .take(4)
                .map(|v| lang.show_value(v))
                .collect()
        })
        .collect();
    let refined_by = sem
        .templates
        .iter()
        .map(|t| t.as_ref().map(|t| sig[t.elim].name.to_string()))
        .collect();

    // Representatives: per behaviour (the set of universe types a value
    // is in), its smallest closed terms.
    let mut reps: Vec<Term> = Vec::new();
    let mut per_sig: HashMap<Vec<usize>, usize> = HashMap::new();
    for v in &pool {
        let n = per_sig.entry(sem.types_of(&mut oracle, v)).or_default();
        if *n < cfg.search.reps_per_type {
            *n += 1;
            reps.push(origin[v].clone());
        }
    }
    let mut open = HashMap::new();
    for c in sig {
        for &b in &c.binds {
            if b > 0 && !open.contains_key(&b) {
                let terms = en.up_to(cfg.open_size, b);
                open.insert(b, rng.sample(&terms, 3000));
            }
        }
    }
    let pools = Pools { reps, open };
    note(&format!("{} representatives", pools.reps.len()));

    // 3. Search.
    let mut searches = Vec::new();
    let mut rules = Vec::new();
    for (ci, c) in sig.iter().enumerate() {
        if c.kind == Kind::Var {
            continue;
        }
        let s = search_con(&mut oracle, &mut sem, &pools, ci, &cfg.search, &mut rng);
        note(&format!(
            "searched {} ({} candidates)",
            c.name, s.candidates
        ));
        rules.extend(s.chosen.iter().cloned());
        searches.push(s);
    }

    // 4. Check.
    let check = check(lang, &mut oracle, &mut sem, &rules, cfg, &mut en, &mut rng);
    Discovery {
        language: lang.name().to_string(),
        config: cfg.clone(),
        con_names: sig.iter().map(|c| c.name).collect(),
        sort_names,
        sort_examples,
        refined_by,
        universe: sem.universe.len(),
        searches,
        rules,
        check,
        evals: oracle.evals,
    }
}

fn check<L: Language>(
    lang: &L,
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    rules: &[Schema],
    cfg: &Config,
    en: &mut Enumerator,
    rng: &mut Rng,
) -> Check {
    let checker = Checker::new(lang.signature(), rules);
    let mut terms = Enumerator::new(lang.signature(), cfg.check_size);
    terms.cap = en.cap;
    let mut terms = terms.up_to(cfg.check_size, 0);
    let mut seen: HashSet<Term> = terms.iter().cloned().collect();
    for _ in 0..cfg.random_terms {
        let t = random_term(lang.signature(), rng, cfg.random_size, 0);
        if seen.insert(t.clone()) {
            terms.push(t);
        }
    }
    let bases: Vec<Ty> = sem
        .universe
        .iter()
        .filter(|t| matches!(t, Ty::Base(_)))
        .cloned()
        .collect();
    let mut c = Check {
        size: cfg.check_size,
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
        let safe = !out.is_stuck();
        c.safe += safe as usize;
        let types = checker.types(t);
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
        // A type with variables claims every instance: try each with the
        // unrefined sorts.
        let good = types.iter().all(|ty| {
            let mut vs = Vec::new();
            ty.vars(&mut vs);
            ground_instances(ty, &vs, &bases)
                .iter()
                .all(|g| sem.in_e(oracle, &out, g))
        });
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

fn ground_instances(t: &Ty, vars: &[u32], bases: &[Ty]) -> Vec<Ty> {
    let mut out = vec![t.clone()];
    for &v in vars.iter().take(3) {
        out = out
            .into_iter()
            .flat_map(|t| {
                bases.iter().map(move |b| {
                    let mut m = HashMap::new();
                    m.insert(v, b.clone());
                    crate::types::subst(&t, &m)
                })
            })
            .collect();
    }
    out.into_iter().filter(Ty::is_ground).collect()
}

/// A random closed term of at most `size` nodes.
pub fn random_term(sig: &[crate::lang::Con], rng: &mut Rng, size: usize, depth: usize) -> Term {
    loop {
        let ci = rng.below(sig.len());
        let c = &sig[ci];
        if c.kind == Kind::Var {
            if depth > 0 {
                return Term::leaf(ci, Atom::Int(rng.below(depth) as i64));
            }
            continue;
        }
        if c.arity + 1 > size {
            continue;
        }
        let atoms = c.atoms_or_none();
        let atom = atoms[rng.below(atoms.len())].clone();
        let mut budget = size - 1;
        let mut kids = Vec::new();
        for (i, b) in c.binds.iter().enumerate() {
            let rest = c.arity - i - 1;
            let mine = 1 + rng.below(budget - rest);
            budget -= mine;
            kids.push(random_term(sig, rng, mine, depth + b));
        }
        return Term {
            con: ci,
            atom,
            kids,
        };
    }
}

impl Discovery {
    pub fn names(&self) -> Names<'_> {
        Names {
            sorts: &self.sort_names,
            cons: &self.con_names,
        }
    }

    /// The chosen rules, printed one per line.
    pub fn rule_strings(&self) -> Vec<String> {
        self.rules.iter().map(|r| self.names().schema(r)).collect()
    }

    pub fn search(&self, con: &str) -> &ConSearch {
        self.searches
            .iter()
            .find(|s| self.con_names[s.con] == con)
            .unwrap_or_else(|| panic!("no constructor {con}"))
    }
}

impl fmt::Display for Discovery {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names = self.names();
        writeln!(f, "language: {}\n", self.language)?;
        writeln!(
            f,
            "sorts (values that get stuck in the same immediate contexts):"
        )?;
        for (i, (n, ex)) in self.sort_names.iter().zip(&self.sort_examples).enumerate() {
            write!(f, "  {n} = {{{}, ...}}", ex.join(", "))?;
            if let Some(e) = &self.refined_by[i] {
                write!(f, "  refined by what `{e}` gives: {n}<args -> result>")?;
            }
            writeln!(f)?;
        }
        writeln!(f, "  ({} ground types observed)", self.universe)?;
        writeln!(f, "\nrules:")?;
        for s in &self.searches {
            if s.chosen.is_empty() {
                writeln!(f, "  {} : (no rule; not typable)", self.con_names[s.con])?;
            }
            for r in &s.chosen {
                writeln!(f, "  {}", names.schema(r))?;
            }
            if let Some((r, cols)) = (s.chosen.len() > 1).then(|| lgg(&s.chosen)).flatten() {
                let vs = r.vars();
                let fresh: Vec<String> = (0..cols.len())
                    .map(|i| crate::types::var_name(vs[vs.len() - cols.len() + i]))
                    .collect();
                let rows: Vec<String> = (0..s.chosen.len())
                    .map(|j| {
                        let row: Vec<String> = cols.iter().map(|c| names.ty(&c[j])).collect();
                        if row.len() == 1 {
                            row[0].clone()
                        } else {
                            format!("({})", row.join(", "))
                        }
                    })
                    .collect();
                let lhs = if fresh.len() == 1 {
                    fresh[0].clone()
                } else {
                    format!("({})", fresh.join(", "))
                };
                writeln!(
                    f,
                    "    = class: {}  where {lhs} in {{{}}}",
                    names.schema(&r),
                    rows.join(", ")
                )?;
            }
        }
        writeln!(
            f,
            "\nbinder flow (where each bound variable's value comes from):"
        )?;
        for s in &self.searches {
            for (i, srcs) in s.sources.iter().enumerate() {
                for (j, src) in srcs.iter().enumerate() {
                    writeln!(f, "  {} child {i}, x{j}: {src:?}", self.con_names[s.con])?;
                }
            }
        }
        writeln!(f, "\nsearch:")?;
        for s in &self.searches {
            write!(
                f,
                "  {:<9} {:>5} observations, {:>5} candidates, {:>5} refuted, {:>2} falsified",
                self.con_names[s.con], s.observations, s.candidates, s.refuted, s.falsified
            )?;
            if let Some((r, w)) = &s.best_refuted {
                write!(f, "; e.g. {} fails on {w}", names.schema(r))?;
            }
            writeln!(f)?;
        }
        let c = &self.check;
        writeln!(
            f,
            "\nend-to-end check on {} terms (all of size <= {}, and random ones up to {}):",
            c.terms, c.size, self.config.random_size
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
