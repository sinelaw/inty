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
use crate::infer::{Checker, Order, Policy};
use crate::lang::{Atom, Kind, Language, Outcome, Term};
use crate::search::{search_con, ConSearch, Features, Pools, SearchConfig, Source};
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
    /// ...and this many random ones up to `random_size`...
    pub random_terms: usize,
    pub random_size: usize,
    /// ...and this many generated well typed, of sizes up to `typed_size`
    /// (also how many try each generalisation policy).
    pub typed_terms: usize,
    pub typed_size: usize,
    /// Child terms whose value is tested in all instances of its type at
    /// once, to choose a generalisation policy.
    pub poly_tests: usize,
    /// Bodies up to this size are enumerated for the aimed tests.
    pub aimed_size: usize,
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
            typed_terms: 4000,
            typed_size: 14,
            poly_tests: 300,
            aimed_size: 6,
            seed: 1,
        }
    }
}

pub struct Check {
    pub size: usize,
    pub terms: usize,
    /// How many of the terms were generated well typed.
    pub generated: usize,
    pub safe: usize,
    pub typed: usize,
    /// Typed terms that get stuck or give a value of another type.
    pub unsound: usize,
    pub violations: Vec<String>,
    pub untyped_safe: usize,
    pub untyped_safe_examples: Vec<String>,
    /// Of the terms every run checks (all small ones and the same random
    /// ones, not those generated from the rules): the safe, and the typed
    /// among them. What runs with different type languages compare on.
    pub fixed_safe: usize,
    pub fixed_typed: usize,
    /// The programs generated well typed by these rules (some may still
    /// get stuck): what the climb pools to judge other systems on.
    pub generated_terms: Vec<Term>,
}

impl Check {
    /// The share of the fixed terms' safe ones that are typed.
    pub fn coverage(&self) -> f64 {
        self.fixed_typed as f64 / self.fixed_safe.max(1) as f64
    }
}

pub struct Discovery {
    pub language: String,
    pub config: Config,
    pub con_names: Vec<&'static str>,
    pub sort_names: Vec<String>,
    /// Per sort, the name the language gives its members (only to print
    /// rules for people), or its own name.
    pub kind_names: Vec<String>,
    pub sort_examples: Vec<Vec<String>>,
    /// Per sort, the eliminators it is refined by.
    pub refined_by: Vec<Option<String>>,
    /// Per sort, its eliminators' names and parameter counts.
    pub shapes: Vec<Vec<(String, usize)>>,
    pub universe: usize,
    pub searches: Vec<ConSearch>,
    pub rules: Vec<Schema>,
    /// The subtyping kept, as pairs `(s, t)` for `s <: t`; empty without.
    pub subtypes: Vec<(usize, usize)>,
    /// The description lengths of the system without subtyping and, if
    /// tried, with it.
    pub sizes: (usize, Option<usize>),
    pub generalisation: Generalisation,
    pub check: Check,
    pub evals: usize,
    /// The checker the rules induce, as checked.
    pub checker: Checker,
    /// The capabilities that could matter for this language at all: no
    /// binders, no `let`-generalisation or narrowing; nothing returns, no
    /// exit types.
    pub applicable: Features,
}

impl Discovery {
    /// The system's description length: a rule and each sort it commits to.
    pub fn size(&self) -> usize {
        self.rules.iter().map(|r| 1 + r.constants()).sum()
    }
}

/// Searches kept across runs (by the ladder): per constructor and what of
/// the type language bears on its search.
pub type SearchCache = HashMap<(usize, Vec<bool>), ConSearch>;

pub fn discover<L: Language>(lang: &L, cfg: &Config) -> Discovery {
    discover_with(lang, cfg, &mut SearchCache::new())
}

/// `discover`, reusing (and adding to) `cache`.
pub fn discover_with<L: Language>(lang: &L, cfg: &Config, cache: &mut SearchCache) -> Discovery {
    let sig = lang.signature();
    let mut oracle = Oracle::new(lang);
    let mut rng = Rng(cfg.seed);

    // 1. The corpus and its values, each with the smallest term giving it.
    let mut en = Enumerator::new(sig, cfg.corpus_size.max(cfg.open_size));
    en.cap = 400_000;
    let (corpus, pool, origin) = ground(&mut oracle, &mut en, cfg);
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
    let feats = cfg.search.features;
    let any_refined = sem.templates.iter().any(|t| !t.is_empty());
    if !feats.refined {
        sem.unrefine();
    }
    let nsorts = sem.count();
    note(&format!("{nsorts} sorts, universe {}", sem.universe.len()));
    let sort_names: Vec<String> = (0..nsorts).map(|s| format!("T{s}")).collect();
    let agreed: Vec<Option<String>> = (0..nsorts)
        .map(|s| {
            let mut names = sem.members[s].iter().map(|v| lang.kind_name(v));
            let first = names.next().flatten()?;
            names.all(|n| n.as_deref() == Some(&first)).then_some(first)
        })
        .collect();
    let kind_names: Vec<String> = (0..nsorts)
        .map(|s| match &agreed[s] {
            Some(n) if agreed.iter().filter(|m| m.as_ref() == Some(n)).count() == 1 => n.clone(),
            _ => sort_names[s].clone(),
        })
        .collect();
    let sort_examples = (0..nsorts)
        .map(|s| {
            sem.members[s]
                .iter()
                .take(4)
                .map(|v| lang.show_value(v))
                .collect()
        })
        .collect();
    let shapes: Vec<Vec<(String, usize)>> = sem
        .templates
        .iter()
        .map(|ts| {
            ts.iter()
                .map(|t| (sig[t.elim].name.to_string(), t.k + 1))
                .collect()
        })
        .collect();
    let refined_by = sem
        .templates
        .iter()
        .map(|ts| {
            (!ts.is_empty()).then(|| {
                ts.iter()
                    .map(|t| sig[t.elim].name)
                    .collect::<Vec<_>>()
                    .join(", ")
            })
        })
        .collect();

    // Representatives: per behaviour (the set of universe types a value
    // is in), its smallest closed terms.
    let mut reps: Vec<Term> = Vec::new();
    let mut per_sig: HashMap<Vec<usize>, usize> = HashMap::new();
    for v in &pool {
        // By the types a value is in, and, where refinement is off, by
        // how its eliminator behaves, which the types no longer say.
        let mut key = sem.types_of(&mut oracle, v);
        if !feats.refined {
            key.extend(
                sem.behaviour(&mut oracle, v)
                    .iter()
                    .map(|b| (b + 1000) as usize),
            );
        }
        let n = per_sig.entry(key).or_default();
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
    // Abrupt completions: per kind (the reason's first word), a few of the
    // smallest terms, each a different reason (a different value thrown).
    let mut faults = Vec::new();
    let mut fault_kinds = Vec::new();
    let mut reasons = std::collections::HashSet::new();
    let mut per_kind: HashMap<String, usize> = HashMap::new();
    let mut kinds: Vec<String> = Vec::new();
    for t in &corpus {
        let reason = match oracle.eval(t) {
            Outcome::Fault(r) => r,
            Outcome::Return(v) => format!("return {}", lang.show_value(&v)),
            _ => continue,
        };
        let kind = reason.split(' ').next().unwrap_or("").to_string();
        let n = per_kind.entry(kind.clone()).or_default();
        if *n < cfg.search.reps_per_type * 2 && reasons.insert(reason) {
            *n += 1;
            faults.push(t.clone());
            if !kinds.contains(&kind) {
                kinds.push(kind.clone());
            }
            fault_kinds.push(kinds.iter().position(|k| *k == kind).unwrap());
        }
    }
    let mut by_sort: Vec<Vec<Term>> = vec![Vec::new(); sem.count()];
    for t in &reps {
        if let Outcome::Value(v) = oracle.eval(t) {
            if let Some(s) = sem.sort(&mut oracle, &v) {
                by_sort[s].push(t.clone());
            }
        }
    }
    let pools = Pools {
        reps,
        open,
        faults,
        fault_kinds,
        by_sort,
    };
    note(&format!("{} representatives", pools.reps.len()));
    // `unknown` is a type only where something binds a value of no known
    // source: otherwise no term has it, and a rule's variables don't range
    // over it (`==` on two values of one type is not for two unknowns).
    let mut probe_rng = Rng(cfg.seed ^ 0x5EED_0F_70B);
    let unknown = (0..sig.len()).any(|ci| {
        sig[ci].kind == Kind::Op
            && sig[ci].binds.iter().any(|&b| b > 0)
            && crate::search::binder_sources(&mut oracle, &mut sem, &pools, ci, &mut probe_rng)
                .iter()
                .flatten()
                .any(|s| *s == crate::search::Source::Unknown)
    });
    if !unknown || !feats.unknown {
        sem.universe.retain(|t| *t != Ty::Top);
    }

    // 3. Search, without subtyping and, if the fingerprints order any
    // sorts, with it; keep the shorter system (the one without, on a tie).
    // `reuse` has, per constructor, a search to keep rather than redo.
    let returns = pools
        .faults
        .iter()
        .any(|t| matches!(oracle.eval(t), Outcome::Return(_)));
    let mut run = |sem: &mut Semantics<L::Value>,
                   oracle: &mut Oracle<L>,
                   rng: &mut Rng,
                   reuse: &[Option<ConSearch>]| {
        let mut searches = Vec::new();
        let mut rules = Vec::new();
        for (ci, c) in sig.iter().enumerate() {
            if c.kind != Kind::Op || (!feats.binders && c.binds.iter().any(|&b| b > 0)) {
                continue;
            }
            // For working on the search: `TYSEARCH_ONLY='app2|.x='` searches
            // just those.
            if let Ok(only) = std::env::var("TYSEARCH_ONLY") {
                if !only.split('|').any(|n| n == c.name) {
                    continue;
                }
            }
            if let Some(Some(s)) = reuse.get(ci) {
                rules.extend(s.chosen.iter().cloned());
                searches.push(s.clone());
                continue;
            }
            // Each constructor draws from its own stream, so its search
            // doesn't depend on how many draws the others made.
            let mut own = Rng(rng.0 ^ (ci as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            // What bears on this search, as it actually is: a search is
            // kept across runs that differ in none of it.
            let binds = c.binds.iter().any(|&b| b > 0);
            let key = (
                ci,
                vec![
                    feats.vars,
                    feats.refined,
                    sem.universe.contains(&Ty::Top),
                    feats.exits && returns,
                    feats.narrowing && binds,
                    sem.subtyping,
                ],
            );
            if let Some(s) = cache.get_mut(&key) {
                if feats.unions && !s.unions_tested {
                    s.no_unions = s
                        .chosen
                        .clone()
                        .iter()
                        .map(|r| {
                            crate::search::no_union_vars(
                                oracle,
                                sem,
                                &pools,
                                r,
                                &cfg.search,
                                &mut own,
                            )
                        })
                        .collect();
                    s.unions_tested = true;
                }
                let mut s = s.clone();
                if !feats.unions {
                    s.no_unions = vec![Vec::new(); s.chosen.len()];
                }
                for (i, vs) in s.narrow.iter().enumerate() {
                    for (j, n) in vs.iter().enumerate() {
                        if let Some(sorts) = n {
                            sem.narrow.insert((ci, i, j), sorts.clone());
                        }
                    }
                }
                note(&format!("kept {}", c.name));
                rules.extend(s.chosen.iter().cloned());
                searches.push(s);
                continue;
            }
            let s = search_con(oracle, sem, &pools, ci, &cfg.search, &mut own);
            cache.insert(key, s.clone());
            note(&format!(
                "searched {} ({} candidates)",
                c.name, s.candidates
            ));
            rules.extend(s.chosen.iter().cloned());
            searches.push(s);
        }
        (searches, rules)
    };
    let (mut searches, mut rules) = run(&mut sem, &mut oracle, &mut rng, &[]);
    let size = |rules: &[Schema]| rules.iter().map(|r| 1 + r.constants()).sum::<usize>();
    let mut subtypes: Vec<(usize, usize)> = Vec::new();
    let mut sizes = (size(&rules), None);
    // Subtyping can shorten a system only where a constructor's rules differ
    // in sorts the order relates (`+` on `Int` and on `Float`).
    let could_help = sem.has_order()
        && searches.iter().any(|s| {
            lgg(&s.chosen).is_some_and(|(_, cols)| {
                cols.iter().any(|col| {
                    col.iter().any(|a| {
                        col.iter().any(|b| matches!((a, b), (Ty::Base(x), Ty::Base(y)) if x != y && sem.le[*x][*y]))
                    })
                })
            })
        });
    if could_help && feats.subtyping {
        sem.set_subtyping(true);
        // Subtyping widens only the sorts with strict subsorts: a
        // constructor whose rules mention none of them, and that has rules,
        // keeps its search.
        let widened: Vec<bool> = (0..nsorts)
            .map(|t| (0..nsorts).any(|u| u != t && sem.le[u][t]))
            .collect();
        let mut reuse: Vec<Option<ConSearch>> = vec![None; sig.len()];
        for sr in &searches {
            let mentions = sr.chosen.iter().any(|r| {
                r.types().any(|t| {
                    fn has(t: &Ty, w: &[bool]) -> bool {
                        match t {
                            Ty::Base(s) => w[*s],
                            Ty::Var(_) | Ty::Top | Ty::Never => false,
                            Ty::Ref(_, ps) | Ty::Union(ps) => ps.iter().any(|p| has(p, w)),
                        }
                    }
                    has(t, &widened)
                })
            });
            if !sr.chosen.is_empty() && !mentions {
                reuse[sr.con] = Some(sr.clone());
            }
        }
        let (s2, r2) = run(&mut sem, &mut oracle, &mut rng, &reuse);
        let order: Vec<(usize, usize)> = (0..nsorts)
            .flat_map(|a| (0..nsorts).map(move |b| (a, b)))
            .filter(|&(a, b)| a != b && sem.le[a][b])
            .collect();
        let with = size(&r2) + order.len();
        sizes.1 = Some(with);
        if with < sizes.0 {
            searches = s2;
            rules = r2;
            subtypes = order;
        } else {
            sem.set_subtyping(false);
        }
    }

    // 4. Generalisation: for each binder, the most permissive policy that
    // typed programs don't refute.
    let gen = generalise(
        lang,
        &mut oracle,
        &mut sem,
        &rules,
        &searches,
        &corpus,
        cfg,
        &mut rng,
    );
    note("generalised");

    // 5. Check.
    let check = check(
        lang,
        &mut oracle,
        &mut sem,
        &rules,
        &gen,
        cfg,
        &mut en,
        &mut rng,
    );
    let checker = checker_for(lang, &sem, &rules, &gen);
    let binders = sig.iter().any(|c| c.binds.iter().any(|&b| b > 0));
    let applicable = Features {
        vars: true,
        refined: any_refined,
        binders,
        unknown: binders,
        generalise: binders,
        exits: returns,
        subtyping: sem.has_order(),
        unions: true,
        narrowing: binders,
    };
    Discovery {
        applicable,
        checker,
        language: lang.name().to_string(),
        config: cfg.clone(),
        con_names: sig.iter().map(|c| c.name).collect(),
        sort_names,
        kind_names,
        sort_examples,
        refined_by,
        shapes,
        universe: sem.universe.len(),
        searches,
        rules,
        subtypes,
        sizes,
        generalisation: gen,
        check,
        evals: oracle.evals,
    }
}

/// The checker for a rule set, with the order (if subtyping is on), the
/// binders' policies and the syntactic values.
fn checker_for<L: Language>(
    lang: &L,
    sem: &Semantics<L::Value>,
    rules: &[Schema],
    gen: &Generalisation,
) -> Checker {
    let mut checker = Checker::new(lang.signature(), rules);
    if sem.subtyping {
        let n = sem.count();
        checker.order = Some(Order {
            le: sem.le.clone(),
            join: (0..n)
                .map(|a| (0..n).map(|b| sem.join(a, b)).collect())
                .collect(),
        });
    }
    checker.policies = gen.policies.clone();
    checker.inert = gen.inert.clone();
    checker.narrow = sem.narrow.clone();
    for (r, vs) in &gen.no_unions {
        checker.set_no_unions(r, vs);
    }
    if gen.no_widening {
        checker.no_widening();
    }
    checker
}

/// Whether running a term typed `types` gave a member of each: a type
/// with variables claims every instance, tried with the unrefined sorts.
fn sound_for<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    out: &Outcome<L::Value>,
    types: &[Ty],
) -> bool {
    let bases: Vec<Ty> = sem
        .universe
        .iter()
        .filter(|t| matches!(t, Ty::Base(_)))
        .cloned()
        .collect();
    types.iter().all(|ty| {
        let mut vs = Vec::new();
        ty.vars(&mut vs);
        ground_instances(ty, &vs, &bases)
            .iter()
            .all(|g| sem.in_e(oracle, out, g))
    })
}

#[allow(clippy::too_many_arguments)]
fn check<L: Language>(
    lang: &L,
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    rules: &[Schema],
    gen: &Generalisation,
    cfg: &Config,
    en: &mut Enumerator,
    rng: &mut Rng,
) -> Check {
    let checker = checker_for(lang, sem, rules, gen);
    let clock = std::time::Instant::now();
    let trace = std::env::var_os("TYSEARCH_TRACE").is_some();
    let lap = |what: &str| {
        if trace {
            eprintln!("    {:>7.2}s check: {what}", clock.elapsed().as_secs_f64());
        }
    };
    let mut terms = Enumerator::new(lang.signature(), cfg.check_size);
    terms.cap = en.cap;
    let mut terms = terms.up_to(cfg.check_size, 0);
    let mut seen: HashSet<Term> = terms.iter().cloned().collect();
    // The same random terms whatever the rules, so runs compare.
    let mut fixed_rng = Rng(cfg.seed ^ 0xC0FF_EE00);
    for _ in 0..cfg.random_terms {
        let t = random_term(lang.signature(), &mut fixed_rng, cfg.random_size, 0);
        if seen.insert(t.clone()) {
            terms.push(t);
        }
    }
    let n_fixed = terms.len();
    lap(&format!("{} terms", terms.len()));
    // And programs well typed by construction (T2).
    let mut generated = 0;
    for k in 0..cfg.typed_terms {
        if let Some(t) = checker.generate(rng, 3 + k % cfg.typed_size) {
            if seen.insert(t.clone()) {
                terms.push(t);
                generated += 1;
            }
        }
    }
    lap(&format!("{generated} generated"));
    let mut c = Check {
        size: cfg.check_size,
        terms: terms.len(),
        generated,
        safe: 0,
        typed: 0,
        unsound: 0,
        violations: Vec::new(),
        untyped_safe: 0,
        untyped_safe_examples: Vec::new(),
        fixed_safe: 0,
        fixed_typed: 0,
        generated_terms: terms[n_fixed..].to_vec(),
    };
    let (mut t_eval, mut t_types, mut t_sound) = (0.0, 0.0, 0.0);
    let mut tick = std::time::Instant::now();
    let mut lapse = |acc: &mut f64| {
        *acc += tick.elapsed().as_secs_f64();
        tick = std::time::Instant::now();
    };
    for (i, t) in terms.iter().enumerate() {
        let out = oracle.eval(t);
        lapse(&mut t_eval);
        if matches!(out, Outcome::Timeout) {
            continue;
        }
        // A `return` with nothing to return from is as wrong as stuck.
        let safe = !out.is_stuck() && !matches!(out, Outcome::Return(_));
        c.safe += safe as usize;
        let types = checker.types(t);
        lapse(&mut t_types);
        if i < n_fixed && safe {
            c.fixed_safe += 1;
            c.fixed_typed += !types.is_empty() as usize;
        }
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
        let sound = sound_for(oracle, sem, &out, &types);
        lapse(&mut t_sound);
        if !sound {
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
    lap(&format!(
        "ran {t_eval:.1}s, typed {t_types:.1}s, judged {t_sound:.1}s"
    ));
    c
}

/// A binder `(con, child, index)`, a policy tried for it, how many terms it
/// would generalise, and the term that refuted it, if one did.
pub type Trial = ((usize, usize, usize), Policy, usize, Option<String>);

/// How each binder's variables are generalised, and why.
#[derive(Clone, Default)]
pub struct Generalisation {
    pub policies: HashMap<(usize, usize, usize), (Policy, usize)>,
    pub inert: Vec<bool>,
    /// Per policy tried: the binder, the policy, programs it typed that
    /// the next stricter one didn't, and a typed program that got stuck.
    pub trials: Vec<Trial>,
    /// Per rule, the variables that may not stand for unions (the
    /// search's).
    pub no_unions: Vec<(Schema, Vec<u32>)>,
    /// No variable widens to a union (the ladder's rungs before unions).
    pub no_widening: bool,
}

/// Which constructors make syntactic values: those that, given children
/// that would get stuck, still give a value, so run none of them.
fn inert<L: Language>(lang: &L) -> Vec<bool> {
    let sig = lang.signature();
    let var = sig.iter().position(|c| c.kind == Kind::Var);
    sig.iter()
        .enumerate()
        .map(|(ci, c)| match c.kind {
            Kind::Var => true,
            Kind::Assign => false,
            Kind::Op => {
                let Some(var) = var else { return c.arity == 0 };
                let stuck = Term::leaf(var, Atom::Int(1_000));
                let node = Term {
                    con: ci,
                    atom: c.atoms_or_none()[0].clone(),
                    kids: vec![stuck; c.arity],
                };
                matches!(lang.eval(&node), Outcome::Value(_))
            }
        })
        .collect()
}

/// Whether `t` mentions variable `idx` (de Bruijn, shifted under binders)
/// by a constructor of `kind`: reads it, or assigns it.
fn touches(t: &Term, idx: usize, kind: Kind, sig: &[crate::lang::Con]) -> bool {
    let c = &sig[t.con];
    if c.kind == kind && t.atom == Atom::Int(idx as i64) {
        return true;
    }
    t.kids
        .iter()
        .zip(&c.binds)
        .any(|(k, b)| touches(k, idx + b, kind, sig))
}

/// The corpus, the values it reaches, and the smallest term giving each.
type Ground<V> = (Vec<Term>, Vec<V>, HashMap<V, Term>);

fn ground<L: Language>(
    oracle: &mut Oracle<L>,
    en: &mut Enumerator,
    cfg: &Config,
) -> Ground<L::Value> {
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
    (corpus, pool, origin)
}

/// Whether `t`, typed by `d`'s rules with its binders generalising
/// always, has a value in every instance of its type at once: the test
/// that chooses generalisation policies, on a term of one's choosing (the
/// semantics rebuilt as `discover` builds it, so the sorts agree).
pub fn generalisable<L: Language>(lang: &L, cfg: &Config, d: &Discovery, t: &Term) -> Option<bool> {
    let mut oracle = Oracle::new(lang);
    let mut en = Enumerator::new(lang.signature(), cfg.corpus_size.max(cfg.open_size));
    en.cap = 400_000;
    let (_, pool, _) = ground(&mut oracle, &mut en, cfg);
    let probes: Vec<L::Value> = pool.iter().take(cfg.probes).cloned().collect();
    let mut sem = Semantics::discover(&mut oracle, &pool, &probes, cfg.samples_per_type);
    if !cfg.search.features.refined {
        sem.unrefine();
    }
    if !d.subtypes.is_empty() {
        sem.set_subtyping(true);
    }
    let mut gen = d.generalisation.clone();
    for p in gen.policies.values_mut() {
        p.0 = Policy::Always;
    }
    let checker = checker_for(lang, &sem, &d.rules, &gen);
    let ty = checker.types(t).into_iter().find(|ty| !ty.is_ground())?;
    let Outcome::Value(v) = oracle.eval(t) else {
        return None;
    };
    Some(poly_member(
        &mut oracle,
        &mut sem,
        &d.rules,
        &v,
        &ty,
        64,
        &mut Rng(cfg.seed),
    ))
}

/// Whether `v` is in every instance of `ty` at once: used again and again,
/// each time at an instance chosen at random, by a rule that takes that
/// instance (an eliminator, but also, say, a store into a reference), its
/// other children sampled from their types, and each result checked, all
/// without starting over. A pure value passes as it would one instance at a
/// time; one over a fresh mutable cell fails once a use at one instance
/// sees what a use at another stored. That difference is the value
/// restriction's reason.
fn poly_member<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    rules: &[Schema],
    v: &L::Value,
    ty: &Ty,
    rounds: usize,
    rng: &mut Rng,
) -> bool {
    let sig = oracle.lang.signature();
    let Some(var) = sig.iter().position(|c| c.kind == Kind::Var) else {
        return true;
    };
    let bases: Vec<Ty> = sem
        .universe
        .iter()
        .filter(|t| matches!(t, Ty::Base(_)))
        .cloned()
        .collect();
    let mut vars = Vec::new();
    ty.vars(&mut vars);
    // The uses: a rule without binders, and a child of it to put `v` in,
    // where the result depends on its type (not `typeof(v)`, `throw(v)`).
    let tells = |r: &Schema, p: usize| {
        let mut res = Vec::new();
        r.res.vars(&mut res);
        r.res_bound()
            && match &r.kids[p].ty {
                Ty::Var(x) => res.contains(x),
                _ => true,
            }
    };
    let uses: Vec<(&Schema, usize)> = rules
        .iter()
        .filter(|r| r.kids.iter().all(|k| k.bound.is_empty()))
        .flat_map(|r| (0..r.kids.len()).map(move |p| (r, p)))
        .filter(|&(r, p)| tells(r, p))
        .collect();
    let mut tried = 0;
    for _ in 0..rounds * 8 {
        if tried >= rounds || uses.is_empty() {
            break;
        }
        let sigma: HashMap<u32, Ty> = vars
            .iter()
            .map(|&x| (x, bases[rng.below(bases.len())].clone()))
            .collect();
        let want = crate::types::subst(ty, &sigma);
        let (rule, p) = uses[rng.below(uses.len())];
        // Fresh variables above any in `ty`.
        let mut u = crate::types::Unifier::default();
        u.next = 1_000_000;
        let r = u.instantiate(rule);
        if !u.unify(&r.kids[p].ty, &want) {
            continue;
        }
        // The rule's other variables, at random sorts.
        let mut rest = Vec::new();
        for k in &r.kids {
            u.resolve(&k.ty).vars(&mut rest);
        }
        u.resolve(&r.res).vars(&mut rest);
        for x in rest {
            let b = bases[rng.below(bases.len())].clone();
            u.unify(&Ty::Var(x), &b);
        }
        // The other children are sampled, and samples of a higher-order
        // type (functions of functions) are too few to trust: a sampled
        // `g` passes as taking any `(bool) => a` though it calls it on 0.
        if r.kids
            .iter()
            .enumerate()
            .any(|(k, prem)| k != p && u.resolve(&prem.ty).depth() > 1)
        {
            continue;
        }
        let mut env = Vec::new();
        let mut kids = Vec::new();
        let mut ok = true;
        for (k, prem) in r.kids.iter().enumerate() {
            let value = if k == p {
                v.clone()
            } else {
                let samples = sem.samples(oracle, &u.resolve(&prem.ty));
                if samples.is_empty() {
                    ok = false;
                    break;
                }
                oracle.lang.isolate(&samples[rng.below(samples.len())])
            };
            kids.push(Term::leaf(var, Atom::Int(env.len() as i64)));
            env.push(value);
        }
        if !ok {
            continue;
        }
        tried += 1;
        let atoms = sig[rule.con].atoms_or_none();
        let node = Term {
            con: rule.con,
            atom: atoms[0].clone(),
            kids,
        };
        // `v` itself, not a copy: the uses share its state.
        let o = oracle.eval_shared(&node, &env);
        if !sem.in_e(oracle, &o, &u.resolve(&r.res)) {
            if std::env::var_os("TYSEARCH_TRACE").is_some() {
                let vals: Vec<String> = env.iter().map(|v| oracle.lang.show_value(v)).collect();
                eprintln!(
                    "    not in all instances: {} on [{}] gives {:?}, not a {:?}",
                    oracle.lang.show_term(&node),
                    vals.join(", "),
                    o,
                    u.resolve(&r.res)
                );
            }
            return false;
        }
    }
    true
}

/// For each bound variable whose value is a child's, the most permissive
/// generalisation the semantics supports. A policy generalises some of the
/// child terms (all of them, or the syntactic values); it is refuted by one
/// whose value, typed with free variables, is not in all their instances
/// at once (`Semantics::holds_poly`), and it is worth having only if it
/// generalises some. The child terms tried are the corpus and programs
/// generated well typed.
#[allow(clippy::too_many_arguments)]
fn generalise<L: Language>(
    lang: &L,
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    rules: &[Schema],
    searches: &[ConSearch],
    corpus: &[Term],
    cfg: &Config,
    rng: &mut Rng,
) -> Generalisation {
    let mut gen = Generalisation {
        inert: inert(lang),
        no_widening: !cfg.search.features.unions,
        no_unions: searches
            .iter()
            .flat_map(|s| s.chosen.iter().cloned().zip(s.no_unions.iter().cloned()))
            .filter(|(_, vs)| !vs.is_empty())
            .collect(),
        ..Default::default()
    };
    let mut binders = Vec::new();
    for s in searches {
        for (i, srcs) in s.sources.iter().enumerate() {
            for (j, src) in srcs.iter().enumerate() {
                if let Source::Child(k) = src {
                    binders.push(((s.con, i, j), *k));
                }
            }
        }
    }
    if binders.is_empty() || !cfg.search.features.generalise {
        return gen;
    }
    // Candidate child terms, with a type that has free variables.
    let checker = checker_for(lang, sem, rules, &gen);
    let clock = std::time::Instant::now();
    let mut inits: Vec<Term> = corpus.to_vec();
    for n in 0..cfg.typed_terms {
        inits.extend(checker.generate(rng, 3 + n % cfg.typed_size));
    }
    // And, aimed at state that outlives its initialiser: a binder whose
    // body makes a refined value (a function) that may keep the binder's
    // cell, with assignments likely.
    let sig = lang.signature();
    let binding: Vec<bool> = (0..sig.len())
        .map(|c| binders.iter().any(|((b, ..), _)| *b == c))
        .collect();
    let makers: Vec<bool> = (0..sig.len())
        .map(|c| {
            rules
                .iter()
                .any(|r| r.con == c && matches!(r.res, Ty::Ref(..)))
        })
        .collect();
    let mut aimed = checker_for(lang, sem, rules, &gen);
    aimed.assign_weight = 6;
    // Inside the function, constructors that commit to no sort: where
    // state is moved around rather than computed on.
    let structural: Vec<bool> = (0..sig.len())
        .map(|c| {
            sig[c].kind != Kind::Op
                || (rules.iter().any(|r| r.con == c)
                    && rules
                        .iter()
                        .filter(|r| r.con == c)
                        .all(|r| r.types().all(|t| !matches!(t, Ty::Base(_)))))
        })
        .collect();
    let shape = [binding, makers, structural];
    // The binder's initial value: a syntactic value with a polymorphic type,
    // what generalising would act on.
    let poly_values: Vec<Term> = corpus
        .iter()
        .filter(|t| gen.inert[t.con] && t.size() <= 3)
        .filter(|t| checker.types(t).iter().any(|ty| !ty.is_ground()))
        .cloned()
        .collect();
    let mut aimed_inits = Vec::new();
    // Exhaustively, small: `binder(value, maker(body))` for every body up to
    // size 5 of structural constructors that assigns something.
    let assigns = |t: &Term| -> bool {
        fn go(t: &Term, sig: &[crate::lang::Con]) -> bool {
            sig[t.con].kind == Kind::Assign || t.kids.iter().any(|k| go(k, sig))
        }
        go(t, sig)
    };
    // A value whose type shares a variable between positions behaves
    // parametrically, like `(x) => x`: the one whose instances a cell can
    // confuse.
    let shares = |t: &Term| {
        checker.types(t).iter().any(|ty| {
            let mut vs = Vec::new();
            fn all(t: &Ty, out: &mut Vec<u32>) {
                match t {
                    Ty::Var(v) => out.push(*v),
                    Ty::Base(_) | Ty::Top | Ty::Never => {}
                    Ty::Ref(_, ps) | Ty::Union(ps) => ps.iter().for_each(|p| all(p, out)),
                }
            }
            all(ty, &mut vs);
            let n = vs.len();
            vs.sort();
            vs.dedup();
            vs.len() < n
        })
    };
    if let Some(value) = poly_values
        .iter()
        .find(|t| shares(t))
        .or(poly_values.first())
    {
        let mut en = Enumerator::new(sig, cfg.aimed_size);
        en.allowed = Some(shape[2].clone());
        en.cap = 200_000;
        for (b, &is_binder) in shape[0].iter().enumerate() {
            if !is_binder {
                continue;
            }
            let Some(&((_, i, _), k)) = binders.iter().find(|((c, ..), _)| *c == b) else {
                continue;
            };
            for (m, &is_maker) in shape[1].iter().enumerate() {
                if !is_maker || sig[m].arity != 1 {
                    continue;
                }
                let depth = sig[b].binds[i] + sig[m].binds[0];
                // The binder's variable, as the body sees it.
                let outer = sig[m].binds[0] + sig[b].binds[i] - 1 - (sig[b].binds[i] - 1);
                for body in en.up_to(cfg.aimed_size, depth) {
                    // State can leak between instances only if the function
                    // both writes and reads the cell.
                    if !assigns(&body)
                        || !touches(&body, outer, Kind::Assign, sig)
                        || !touches(&body, outer, Kind::Var, sig)
                    {
                        continue;
                    }
                    let mut kids = vec![value.clone(); sig[b].arity];
                    kids[i] = Term::new(m, vec![body]);
                    kids[k] = value.clone();
                    aimed_inits.push(Term::new(b, kids));
                }
            }
        }
    }
    for n in 0..cfg.typed_terms * 2 {
        let Some(mut t) = aimed.generate_shaped(rng, 7 + n % 8, &shape) else {
            continue;
        };
        if !poly_values.is_empty() {
            let (_, k) = binders
                .iter()
                .find(|((b, ..), _)| *b == t.con)
                .copied()
                .unwrap();
            t.kids[k] = poly_values[rng.below(poly_values.len())].clone();
            if aimed.types(&t).is_empty() {
                continue;
            }
        }
        aimed_inits.push(t);
    }
    if std::env::var_os("TYSEARCH_TRACE").is_some() {
        eprintln!(
            "    generated initialisers in {:.2}s",
            clock.elapsed().as_secs_f64()
        );
    }
    // Per candidate: whether it is a syntactic value, and whether its value
    // is in every instance of its type at once.
    let mut verdicts: Vec<(bool, bool, Term, Ty)> = Vec::new();
    let mut typing = 0.0;
    // Non-values first (only they can tell `Always` from `IfValue`), small
    // first, and a bounded number: each test runs many uses.
    let mut seen = HashSet::new();
    inits.retain(|t| seen.insert(t.clone()));
    inits.sort_by_key(|t| (gen.inert[t.con], t.size()));
    aimed_inits.retain(|t| seen.insert(t.clone()));
    aimed_inits.sort_by_key(|t| t.size());
    if std::env::var_os("TYSEARCH_TRACE").is_some() {
        let shown: Vec<String> = aimed_inits.iter().map(|t| lang.show_term(t)).collect();
        let at = shown.iter().position(|s| s.contains("seq(x3 =(x1), x0)"));
        eprintln!(
            "    swap-like at {at:?} of {}: {:?}",
            shown.len(),
            at.map(|i| &shown[i])
        );
    }
    if std::env::var_os("TYSEARCH_TRACE").is_some() {
        eprintln!("    {} aimed initialisers, e.g.", aimed_inits.len());
        for t in aimed_inits
            .iter()
            .step_by((aimed_inits.len() / 8).max(1))
            .take(8)
        {
            eprintln!("      {}", lang.show_term(t));
        }
    }
    // Each list gets its own allowance: the aimed terms are bigger, and
    // sorted with the rest would never be reached.
    // Three allowances: plain non-values, plain values, aimed terms.
    let mut tested = 0;
    let n_values = inits
        .iter()
        .position(|t| gen.inert[t.con])
        .unwrap_or(inits.len());
    let n_plain = inits.len();
    inits.extend(aimed_inits);
    for (i, t) in inits.into_iter().enumerate() {
        if i == n_plain || i == n_values {
            tested = 0;
        }
        // The aimed terms are many: all of them get a quick screen.
        let cap = if i >= n_plain {
            usize::MAX
        } else {
            cfg.poly_tests
        };
        if tested >= cap {
            continue;
        }
        // A value of an unrefined sort has a ground type: nothing to
        // generalise, and no need to type it.
        let Outcome::Value(v) = oracle.eval(&t) else {
            continue;
        };
        if sem
            .sort(oracle, &v)
            .is_none_or(|s| sem.templates[s].is_empty())
        {
            continue;
        }
        let t0 = std::time::Instant::now();
        let Some(ty) = checker
            .types(&t)
            .into_iter()
            .find(|ty| !ty.is_ground() && ty.depth() <= 2)
        else {
            continue;
        };
        typing += t0.elapsed().as_secs_f64();
        tested += 1;
        if i >= n_plain && std::env::var_os("TYSEARCH_TRACE").is_some() && tested <= 6 {
            eprintln!("      tested {} : {:?}", lang.show_term(&t), ty);
        }
        let rounds = if i >= n_plain { 6 } else { 16 };
        let ok = poly_member(oracle, sem, rules, &v, &ty, rounds, rng);
        verdicts.push((gen.inert[t.con], ok, t, ty));
        // The aimed terms are all non-values: one refutation settles what
        // they can tell.
        if i >= n_plain && !ok {
            break;
        }
    }
    if std::env::var_os("TYSEARCH_TRACE").is_some() {
        eprintln!(
            "    tested {} in {:.2}s ({typing:.2}s typing)",
            verdicts.len(),
            clock.elapsed().as_secs_f64()
        );
    }
    for (key, k) in binders {
        let mut chosen = Policy::Never;
        for policy in [Policy::Always, Policy::IfValue] {
            let applies = |value: bool| policy == Policy::Always || value;
            let gained = verdicts
                .iter()
                .filter(|(value, ..)| applies(*value))
                .count();
            let bad = verdicts
                .iter()
                .filter(|(value, ok, ..)| applies(*value) && !ok)
                .min_by_key(|(_, _, t, _)| t.size());
            let why = bad.map(|(_, _, t, ty)| {
                format!(
                    "{} has type {:?} but is not in all its instances",
                    lang.show_term(t),
                    ty
                )
            });
            let ok = why.is_none() && gained > 0;
            gen.trials.push((key, policy, gained, why));
            if ok {
                chosen = policy;
                break;
            }
        }
        gen.policies.insert(key, (chosen, k));
    }
    gen
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
        if c.kind == Kind::Assign {
            if depth > 0 && size >= 2 {
                return Term {
                    con: ci,
                    atom: Atom::Int(rng.below(depth) as i64),
                    kids: vec![random_term(sig, rng, size - 1, depth)],
                };
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
            shapes: &self.shapes,
            records: false,
        }
    }

    /// Names for people: sorts by the language's names for their members,
    /// records as records.
    pub fn readable_names(&self) -> Names<'_> {
        Names {
            sorts: &self.kind_names,
            cons: &self.con_names,
            shapes: &self.shapes,
            records: true,
        }
    }

    /// The chosen rules, printed one per line.
    pub fn rule_strings(&self) -> Vec<String> {
        self.rules.iter().map(|r| self.names().schema(r)).collect()
    }

    /// What the checker knows besides the rules, one fact a line: which
    /// bound variables are generic, which a test narrows, and which rule
    /// variables may stand for unions.
    pub fn fact_strings(&self) -> Vec<String> {
        self.facts_with(&self.names())
    }

    fn facts_with(&self, names: &Names) -> Vec<String> {
        let mut out = Vec::new();
        let mut policies: Vec<_> = self.checker.policies.iter().collect();
        policies.sort_by_key(|(k, _)| **k);
        for ((con, i, j), (policy, _)) in policies {
            let when = match policy {
                Policy::Never => continue,
                Policy::IfValue => "generic when bound to a value",
                Policy::Always => "generic",
            };
            out.push(format!("{} child {i}, x{j}: {when}", self.con_names[*con]));
        }
        let mut narrow: Vec<_> = self.checker.narrow.iter().collect();
        narrow.sort_by_key(|(k, _)| **k);
        for ((con, i, j), sorts) in narrow {
            let to: Vec<&str> = sorts.iter().map(|&t| names.sorts[t].as_str()).collect();
            let to = if to.is_empty() {
                "never".to_string()
            } else {
                to.join(" | ")
            };
            out.push(format!(
                "{} child {i}, x{j}: narrowed to {to}",
                self.con_names[*con]
            ));
        }
        for (r, vs) in self.checker.union_vars() {
            let vs: Vec<String> = vs.iter().map(|&v| crate::types::var_name(v)).collect();
            out.push(format!(
                "in {}, {} may be a union",
                names.schema(r),
                vs.join(", ")
            ));
        }
        out
    }

    /// The rules and the facts, as `step_report` compares them.
    pub fn system(&self) -> System {
        System {
            rules: self.rule_strings(),
            facts: self.fact_strings(),
        }
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
                write!(f, "  refined by what {e} gives")?;
            }
            writeln!(f)?;
        }
        writeln!(f, "  ({} ground types observed)", self.universe)?;
        if let (a, Some(b)) = self.sizes {
            writeln!(
                f,
                "\nsubtyping from the fingerprints' order: size {b} with it, {a} without"
            )?;
            for &(x, y) in &self.subtypes {
                writeln!(f, "  {} <: {}", self.sort_names[x], self.sort_names[y])?;
            }
            if self.subtypes.is_empty() {
                writeln!(f, "  (not kept)")?;
            }
        }
        writeln!(f, "\nrules:")?;
        for s in &self.searches {
            if s.chosen.is_empty() {
                writeln!(f, "  {} : (no rule; not typable)", self.con_names[s.con])?;
            }
            for (i, r) in s.chosen.iter().enumerate() {
                let no = s.no_unions.get(i).filter(|vs| !vs.is_empty());
                match no {
                    Some(vs) => {
                        let vs: Vec<String> =
                            vs.iter().map(|v| crate::types::var_name(*v)).collect();
                        writeln!(
                            f,
                            "  {}  ({} may not be a union)",
                            names.schema(r),
                            vs.join(", ")
                        )?
                    }
                    None => writeln!(f, "  {}", names.schema(r))?,
                }
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
                    let narrow = match s.narrow.get(i).and_then(|n| n.get(j)).cloned().flatten() {
                        Some(sorts) => {
                            let names: Vec<String> =
                                sorts.iter().map(|&t| self.sort_names[t].clone()).collect();
                            format!(", reached by {} only", names.join(", "))
                        }
                        None => String::new(),
                    };
                    writeln!(
                        f,
                        "  {} child {i}, x{j}: {src:?}{narrow}",
                        self.con_names[s.con]
                    )?;
                }
            }
        }
        if !self.generalisation.trials.is_empty() {
            writeln!(f, "\ngeneralisation (does each term's value inhabit every instance of its type at once?):")?;
            for ((con, i, j), policy, gained, why) in &self.generalisation.trials {
                write!(
                    f,
                    "  {} child {i}, x{j}: {policy:?} would generalise {gained} terms",
                    self.con_names[*con]
                )?;
                match why {
                    Some(w) => writeln!(f, "; refuted: {w}")?,
                    None => writeln!(f)?,
                }
            }
            for ((con, i, j), (policy, _)) in &self.generalisation.policies {
                writeln!(
                    f,
                    "  => {} child {i}, x{j}: {policy:?}",
                    self.con_names[*con]
                )?;
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
            "\nend-to-end check on {} terms (all of size <= {}, random ones up to {}, and {} generated well typed):",
            c.terms, c.size, self.config.random_size, c.generated
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

/// A capability of the type language the climb may add or remove.
pub struct Capability {
    pub name: &'static str,
    get: fn(&Features) -> bool,
    set: fn(&mut Features, bool),
}

/// What the climb chooses from, in the order it tries them: each needs
/// only those before it to be of any use.
pub fn capabilities() -> Vec<Capability> {
    vec![
        Capability {
            name: "type variables",
            get: |f| f.vars,
            set: |f, b| f.vars = b,
        },
        Capability {
            name: "refined sorts (function, object and array types)",
            get: |f| f.refined,
            set: |f, b| f.refined = b,
        },
        Capability {
            name: "binders (and `unknown` for what they bind from nowhere)",
            get: |f| f.binders,
            set: |f, b| {
                f.binders = b;
                f.unknown = b
            },
        },
        Capability {
            name: "let-generalisation",
            get: |f| f.generalise,
            set: |f, b| f.generalise = b,
        },
        Capability {
            name: "exit types (for return)",
            get: |f| f.exits,
            set: |f, b| f.exits = b,
        },
        Capability {
            name: "subtyping",
            get: |f| f.subtyping,
            set: |f, b| f.subtyping = b,
        },
        Capability {
            name: "unions",
            get: |f| f.unions,
            set: |f, b| f.unions = b,
        },
        Capability {
            name: "narrowing",
            get: |f| f.narrowing,
            set: |f, b| f.narrowing = b,
        },
    ]
}

/// One run of the climb: the type language tried, the change that made
/// it, whether the climb kept it, and what it found.
pub struct Step {
    pub features: Features,
    pub change: String,
    pub kept: bool,
    pub discovery: Discovery,
    /// Its score when it ran (`Score`), and the best's on the same
    /// programs, which it was judged against.
    pub score: Score,
    pub against: Score,
}

/// How a system does on the programs the climb judges by: the fixed set,
/// and the pool of programs the systems tried so far generated.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Score {
    /// Safe programs, and those of them typed.
    pub safe: usize,
    pub typed: usize,
    /// Typed programs that get stuck.
    pub unsound: usize,
}

impl Score {
    pub fn coverage(&self) -> f64 {
        self.typed as f64 / self.safe.max(1) as f64
    }
}

/// `d`'s score on its fixed set and on `pool` (programs, and whether
/// each is safe).
fn score(d: &Discovery, pool: &[(Term, bool)]) -> Score {
    let mut s = Score {
        safe: d.check.fixed_safe,
        typed: d.check.fixed_typed,
        unsound: d.check.unsound,
    };
    for (t, safe) in pool {
        s.safe += *safe as usize;
        if !d.checker.types(t).is_empty() {
            if *safe {
                s.typed += 1;
            } else {
                s.unsound += 1;
            }
        }
    }
    s
}

pub struct Climb {
    pub steps: Vec<Step>,
    /// The step whose system the climb ends with.
    pub last: usize,
}

impl Climb {
    pub fn result(&self) -> &Discovery {
        &self.steps[self.last].discovery
    }
}

/// Discovers a type system by climbing: from sorts and ground rules only,
/// it adds, one at a time, each capability that types more of the safe
/// programs and keeps every typed one safe; it stops when none does, or
/// when nearly every safe program is typed. Then it minimises: it drops
/// each capability the system can do without, typing no fewer programs.
/// No configuration: the language decides what the type system needs.
pub fn climb<L: Language>(lang: &L, cfg: &Config) -> Climb {
    climb_with(lang, cfg, |_, _| {})
}

/// Programs that use a generalised value at two types, built from `d`'s
/// own pieces: a binder its policy generalises, a closed syntactic value
/// its rules give a type with variables (from its generated programs), and
/// a body joining two uses of the variable, each an eliminator applied to
/// a different small leaf. What `let`-generalisation adds, and random
/// generation almost never builds: `let id = (x) => x; id(0); id("a")`.
pub fn poly_contrast<L: Language>(lang: &L, d: &Discovery, rng: &mut Rng, n: usize) -> Vec<Term> {
    let sig = lang.signature();
    let gen = &d.generalisation;
    let binders: Vec<(usize, usize, usize)> = gen
        .policies
        .iter()
        .filter(|(_, (p, _))| *p != Policy::Never)
        .map(|(&(con, i, _), &(_, k))| (con, i, k))
        .filter(|&(con, i, k)| {
            sig[con].arity == 2 && sig[con].binds[i] == 1 && sig[con].binds[k] == 0
        })
        .collect();
    let Some(var) = sig.iter().position(|c| c.kind == Kind::Var) else {
        return Vec::new();
    };
    // Closed syntactic values whose type has variables, with the sort it
    // refines: the uses must eliminate that sort.
    fn subterms(t: &Term, out: &mut Vec<Term>) {
        out.push(t.clone());
        t.kids.iter().for_each(|k| subterms(k, out));
    }
    let mut inits: Vec<(Term, usize)> = Vec::new();
    let mut seen = HashSet::new();
    for t in d.check.generated_terms.iter().take(2000) {
        let mut subs = Vec::new();
        subterms(t, &mut subs);
        for s in subs {
            if gen.inert.get(s.con) != Some(&true) || !seen.insert(s.clone()) {
                continue;
            }
            let sort = d.checker.types(&s).iter().find_map(|ty| match ty {
                Ty::Ref(sort, _) if !ty.is_ground() => Some(*sort),
                _ => None,
            });
            if let Some(sort) = sort {
                inits.push((s, sort));
            }
        }
        if inits.len() >= 40 {
            break;
        }
    }
    // Leaves that are values (not `break`), rules that join any two
    // things, and per sort the rules that eliminate it (a call).
    let leaves: Vec<Term> = (0..sig.len())
        .filter(|&c| sig[c].kind == Kind::Op && sig[c].arity == 0)
        .flat_map(|c| {
            sig[c].atoms_or_none().into_iter().map(move |a| Term {
                con: c,
                atom: a,
                kids: Vec::new(),
            })
        })
        .filter(|t| matches!(lang.eval_in(t, &[]), Outcome::Value(_)))
        .collect();
    let joins: Vec<usize> = d
        .rules
        .iter()
        .filter(|r| {
            r.kids.len() >= 2
                && r.kids
                    .iter()
                    .all(|k| k.bound.is_empty() && matches!(k.ty, Ty::Var(_)))
                && r.kids[0].ty != r.kids[1].ty
        })
        .map(|r| r.con)
        .collect();
    let elims: Vec<(usize, usize)> = d
        .rules
        .iter()
        .filter(|r| r.kids.iter().all(|k| k.bound.is_empty()))
        .filter_map(|r| match r.kids.first().map(|k| &k.ty) {
            Some(Ty::Ref(sort, _)) => Some((*sort, r.con)),
            _ => None,
        })
        .collect();
    if binders.is_empty() || inits.is_empty() || joins.is_empty() || leaves.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for _ in 0..n {
        let (con, i, k) = binders[rng.below(binders.len())];
        let (init, sort) = inits[rng.below(inits.len())].clone();
        let mine: Vec<usize> = elims
            .iter()
            .filter(|(s, _)| *s == sort)
            .map(|(_, c)| *c)
            .collect();
        if mine.is_empty() {
            continue;
        }
        let use_of = |rng: &mut Rng| {
            let e = mine[rng.below(mine.len())];
            let kids = (0..sig[e].arity)
                .map(|m| {
                    if m == 0 {
                        Term::leaf(var, Atom::Int(0))
                    } else {
                        leaves[rng.below(leaves.len())].clone()
                    }
                })
                .collect();
            Term {
                con: e,
                atom: sig[e].atoms_or_none()[0].clone(),
                kids,
            }
        };
        let j = joins[rng.below(joins.len())];
        let jk: Vec<Term> = (0..sig[j].arity).map(|_| use_of(rng)).collect();
        let body = Term {
            con: j,
            atom: sig[j].atoms_or_none()[0].clone(),
            kids: jk,
        };
        let mut kids = vec![Term::leaf(var, Atom::Int(0)); 2];
        kids[k] = init;
        kids[i] = body;
        out.push(Term {
            con,
            atom: sig[con].atoms_or_none()[0].clone(),
            kids,
        });
    }
    out
}

/// `climb`, calling `on_step` with each step as soon as it is run (and its
/// number), so the type systems can be shown as they appear.
pub fn climb_with<L: Language>(
    lang: &L,
    cfg: &Config,
    mut on_step: impl FnMut(usize, &Step),
) -> Climb {
    let mut cache = SearchCache::new();
    // The programs systems generated well typed, kept to judge every later
    // system on too: what a capability types that the fixed set of small
    // programs rarely shows (a `let`-bound function used at two types).
    let mut pool: Vec<(Term, bool)> = Vec::new();
    let pooled: std::cell::RefCell<HashSet<Term>> = Default::default();
    let mut prng = Rng(cfg.seed ^ 0x9001);
    let mut run = |f: Features, pool: &mut Vec<(Term, bool)>| {
        let mut c = cfg.clone();
        c.search.features = f;
        let d = discover_with(lang, &c, &mut cache);
        for t in prng.sample(&d.check.generated_terms, 400) {
            if pooled.borrow_mut().insert(t.clone()) {
                match lang.eval_in(&t, &[]) {
                    Outcome::Timeout => {}
                    o => pool.push((t, !o.is_stuck() && !matches!(o, Outcome::Return(_)))),
                }
            }
        }
        d
    };
    let caps = capabilities();
    let mut steps: Vec<Step> = Vec::new();
    let mut cur = Features::NONE;
    let d = run(cur, &mut pool);
    let sc = score(&d, &pool);
    steps.push(Step {
        features: cur,
        change: "start: sorts and ground rules only".into(),
        kept: true,
        discovery: d,
        score: sc,
        against: sc,
    });
    on_step(steps.len() - 1, steps.last().unwrap());
    let mut best = 0;
    let applicable = steps[0].discovery.applicable;
    // Better: sound, and at least one program in two thousand (and at
    // least one) more typed; or as many by a smaller system. Both judged on
    // the pool as it is now, which the candidate's own run added to: each
    // run adds a few hundred programs, so what only a capability types
    // (`let`-generalisation's, say) is a small share of the whole.
    let better = |c: &Score, cd: &Discovery, b: &Score, bd: &Discovery| {
        let tol = (b.safe / 2000).max(1);
        c.unsound == 0
            && (c.typed >= b.typed + tol || (c.typed >= b.typed && cd.size() < bd.size()))
    };
    let covered = |s: &Score| s.coverage() >= 0.99;
    // Try a set of changes to the best so far; keep it if better.
    let mut crng = Rng(cfg.seed ^ 0xC0_7A57);
    let mut attempt = |cand: Features,
                       change: String,
                       grow: bool,
                       steps: &mut Vec<Step>,
                       best: &mut usize,
                       pool: &mut Vec<(Term, bool)>|
     -> bool {
        let d = run(cand, pool);
        // Contrast: programs the candidate's rules generate and the best's
        // reject, the evidence for (or, if they crash, against) what the
        // candidate adds. Random programs rarely show it: a `let`-bound
        // function used at two types, a branch that relies on narrowing.
        let bd = &steps[*best].discovery;
        // Half of them rooted at a constructor that binds (a `let`), whose
        // body may use what it binds more than once, at different types.
        let sig = lang.signature();
        let binding: Vec<bool> = sig.iter().map(|c| c.binds.iter().any(|&b| b > 0)).collect();
        let shape = vec![binding];
        let mut found = 0;
        for t in poly_contrast(lang, &d, &mut crng, 400) {
            if found >= 100 {
                break;
            }
            if d.checker.types(&t).is_empty()
                || !bd.checker.types(&t).is_empty()
                || !pooled.borrow_mut().insert(t.clone())
            {
                continue;
            }
            match lang.eval_in(&t, &[]) {
                Outcome::Timeout => {}
                o => {
                    pool.push((t, !o.is_stuck() && !matches!(o, Outcome::Return(_))));
                    found += 1;
                }
            }
        }
        for k in 0..40_000 {
            if found >= 300 {
                break;
            }
            let size = 3 + k % cfg.typed_size;
            let t = if k % 2 == 0 {
                d.checker.generate(&mut crng, size)
            } else {
                d.checker.generate_shaped(&mut crng, size.max(6), &shape)
            };
            let Some(t) = t else {
                continue;
            };
            if !bd.checker.types(&t).is_empty() || !pooled.borrow_mut().insert(t.clone()) {
                continue;
            }
            match lang.eval_in(&t, &[]) {
                Outcome::Timeout => {}
                o => {
                    pool.push((t, !o.is_stuck() && !matches!(o, Outcome::Return(_))));
                    found += 1;
                }
            }
        }
        let sc = score(&d, pool);
        let bs = score(&steps[*best].discovery, pool);
        let bd = &steps[*best].discovery;
        let kept = if grow {
            better(&sc, &d, &bs, bd)
        } else {
            // Removing: as many typed, sound, no bigger.
            sc.unsound == 0 && sc.typed >= bs.typed && d.size() <= bd.size()
        };
        steps.push(Step {
            features: cand,
            change,
            kept,
            discovery: d,
            score: sc,
            against: bs,
        });
        on_step(steps.len() - 1, steps.last().unwrap());
        if kept {
            *best = steps.len() - 1;
        }
        kept
    };
    // Grow: each capability in turn, round after round while any helps;
    // when none does alone, pairs, for capabilities that only pay
    // together.
    'grow: loop {
        let mut progress = false;
        for cap in &caps {
            if covered(&steps[best].score) {
                break 'grow;
            }
            if (cap.get)(&cur) || !(cap.get)(&applicable) {
                continue;
            }
            let mut cand = cur;
            (cap.set)(&mut cand, true);
            if attempt(
                cand,
                format!("+ {}", cap.name),
                true,
                &mut steps,
                &mut best,
                &mut pool,
            ) {
                cur = cand;
                progress = true;
            }
        }
        if !progress {
            let off: Vec<&Capability> = caps
                .iter()
                .filter(|c| !(c.get)(&cur) && (c.get)(&applicable))
                .collect();
            'pairs: for (i, a) in off.iter().enumerate() {
                for b in &off[i + 1..] {
                    let mut cand = cur;
                    (a.set)(&mut cand, true);
                    (b.set)(&mut cand, true);
                    let change = format!("+ {} and {}", a.name, b.name);
                    if attempt(cand, change, true, &mut steps, &mut best, &mut pool) {
                        cur = cand;
                        progress = true;
                        break 'pairs;
                    }
                }
            }
        }
        if !progress {
            break;
        }
    }
    // Minimise: the latest additions first, which may have made earlier
    // ones redundant.
    loop {
        let mut removed = false;
        for cap in caps.iter().rev() {
            if !(cap.get)(&cur) {
                continue;
            }
            let mut cand = cur;
            (cap.set)(&mut cand, false);
            if attempt(
                cand,
                format!("- {}", cap.name),
                false,
                &mut steps,
                &mut best,
                &mut pool,
            ) {
                cur = cand;
                removed = true;
            }
        }
        if !removed {
            break;
        }
    }
    Climb { steps, last: best }
}

/// What one step of the climb did, and, if it was kept, the type system
/// it leaves: every rule, those new since `prev` (the last kept step's)
/// marked `+`, and those gone listed after.
/// A type system as printed: its rules, and what the checker knows
/// besides them.
#[derive(Clone, Default)]
pub struct System {
    pub rules: Vec<String>,
    pub facts: Vec<String>,
}

/// One step of the climb, with a kept step's type system marked against
/// the previous kept one's: `+` new, `-` gone.
pub fn step_report(i: usize, s: &Step, prev: &System) -> String {
    let d = &s.discovery;
    let gain = s.score.typed as i64 - s.against.typed as i64;
    let mut out = format!(
        "step {i}: {}  ->  {:.1}% of {} safe programs typed ({}{gain} vs the best), {} unsound, {} rules (size {})  [{}]\n",
        s.change,
        100.0 * s.score.coverage(),
        s.score.safe,
        if gain >= 0 { "+" } else { "" },
        s.score.unsound,
        d.rules.len(),
        d.size(),
        if s.kept { "kept" } else { "dropped" }
    );
    if !s.kept {
        return out;
    }
    let names = d.names();
    let now = d.rule_strings();
    if i == 0 {
        out.push_str("  sorts (kinds of value, by where they get stuck):\n");
        for (t, ex) in d.sort_examples.iter().enumerate() {
            out.push_str(&format!("    T{t} = {}, ...\n", ex.join(", ")));
        }
    }
    let caps: Vec<&str> = capabilities()
        .into_iter()
        .filter(|c| (c.get)(&s.features))
        .map(|c| c.name)
        .collect();
    out.push_str(&format!(
        "  the type system now, with {}:\n",
        if caps.is_empty() {
            "ground rules only".to_string()
        } else {
            caps.join(", ")
        }
    ));
    if !d.subtypes.is_empty() {
        let order: Vec<String> = d
            .subtypes
            .iter()
            .map(|&(a, b)| format!("{} <: {}", names.sorts[a], names.sorts[b]))
            .collect();
        out.push_str(&format!("    subtyping: {}\n", order.join(", ")));
    }
    let facts = d.fact_strings();
    let marked = |out: &mut String, now: &[String], prev: &[String]| {
        for r in now {
            let mark = if prev.contains(r) { ' ' } else { '+' };
            out.push_str(&format!("  {mark} {r}\n"));
        }
        for r in prev.iter().filter(|r| !now.contains(r)) {
            out.push_str(&format!("  - {r}\n"));
        }
    };
    marked(&mut out, &now, &prev.rules);
    if !facts.is_empty() || !prev.facts.is_empty() {
        out.push_str("  and, besides the rules:\n");
        marked(&mut out, &facts, &prev.facts);
    }
    out
}

/// A kept step's type system for a document: in Markdown, with readable
/// names, what is new (`+`) or gone (`-`) since `prev`, the rest only
/// counted, and a family of more than three like rules cut to two.
pub fn step_doc(i: usize, s: &Step, prev: Option<&Discovery>) -> String {
    let d = &s.discovery;
    let rules = |d: &Discovery| -> Vec<(usize, String)> {
        let names = d.readable_names();
        let mut rs: Vec<(usize, String)> =
            d.rules.iter().map(|r| (r.con, names.schema(r))).collect();
        rs.sort();
        rs
    };
    let now = rules(d);
    let before = prev.map(rules).unwrap_or_default();
    let facts = d.facts_with(&d.readable_names());
    let facts_before = prev
        .map(|p| p.facts_with(&p.readable_names()))
        .unwrap_or_default();
    let mut out = format!(
        "#### Step {i}: {} ({:.1}% of safe programs typed)\n\n",
        s.change,
        100.0 * s.score.coverage()
    );
    if prev.is_none() {
        out.push_str("Kinds of value:\n\n");
        for (t, ex) in d.sort_examples.iter().enumerate() {
            out.push_str(&format!(
                "- `{}`: {}, ...\n",
                d.kind_names[t],
                ex.join(", ")
            ));
        }
        out.push('\n');
    }
    let kept = now.iter().filter(|r| before.contains(r)).count();
    out.push_str(&format!("{} rules", now.len()));
    if prev.is_some() {
        out.push_str(&format!(", {kept} of them as before"));
    }
    out.push_str(":\n\n```\n");
    // Each constructor's new rules, then its gone ones, families cut.
    let family = |out: &mut String, mark: char, rs: Vec<&String>| {
        let n = rs.len();
        let shown = if n > 3 { 2 } else { n };
        for r in &rs[..shown] {
            out.push_str(&format!("{mark} {r}\n"));
        }
        if n > shown {
            out.push_str(&format!("  ... and {} more like these\n", n - shown));
        }
    };
    let mut cons: Vec<usize> = now.iter().chain(&before).map(|(c, _)| *c).collect();
    cons.sort();
    cons.dedup();
    for c in cons {
        let new: Vec<&String> = now
            .iter()
            .filter(|r| r.0 == c && !before.contains(r))
            .map(|r| &r.1)
            .collect();
        let gone: Vec<&String> = before
            .iter()
            .filter(|r| r.0 == c && !now.contains(r))
            .map(|r| &r.1)
            .collect();
        // The first step has nothing to be new against.
        family(&mut out, if prev.is_some() { '+' } else { ' ' }, new);
        family(&mut out, '-', gone);
    }
    let changed = facts.iter().any(|f| !facts_before.contains(f))
        || facts_before.iter().any(|f| !facts.contains(f));
    if changed {
        if out.ends_with("```\n") {
            out.push_str("(no rule changes)\n");
        }
        let same = facts.iter().filter(|f| facts_before.contains(f)).count();
        out.push_str("\nbesides the rules");
        if same > 0 {
            out.push_str(&format!(" ({same} facts as before)"));
        }
        out.push_str(":\n");
        let mark = if prev.is_some() { '+' } else { ' ' };
        for f in facts.iter().filter(|f| !facts_before.contains(f)) {
            out.push_str(&format!("{mark} {f}\n"));
        }
        for f in facts_before.iter().filter(|f| !facts.contains(f)) {
            out.push_str(&format!("- {f}\n"));
        }
    }
    out.push_str("```\n");
    out
}

impl Climb {
    /// Every kept step's `step_doc`, each against the kept one before.
    pub fn doc(&self) -> String {
        let mut out = String::new();
        let mut prev: Option<&Discovery> = None;
        for (i, s) in self.steps.iter().enumerate().filter(|(_, s)| s.kept) {
            out.push_str(&step_doc(i, s, prev));
            out.push('\n');
            prev = Some(&s.discovery);
        }
        out
    }
}

impl fmt::Display for Climb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut prev = System::default();
        for (i, s) in self.steps.iter().enumerate() {
            write!(f, "{}", step_report(i, s, &prev))?;
            if s.kept {
                prev = s.discovery.system();
            }
        }
        write!(f, "{}", self.summary())
    }
}

impl Climb {
    /// The capabilities kept, and the coverage.
    pub fn summary(&self) -> String {
        let last = &self.steps[self.last];
        let caps: Vec<&str> = capabilities()
            .into_iter()
            .filter(|c| (c.get)(&last.features))
            .map(|c| c.name)
            .collect();
        format!(
            "\nresult (step {}): {:.1}% of safe programs typed, with {}\n",
            self.last,
            100.0 * last.score.coverage(),
            if caps.is_empty() {
                "nothing beyond ground rules".to_string()
            } else {
                caps.join(", ")
            }
        )
    }
}
