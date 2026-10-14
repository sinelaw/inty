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
use crate::search::{search_con, ConSearch, Pools, SearchConfig, Source};
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
}

pub struct Discovery {
    pub language: String,
    pub config: Config,
    pub con_names: Vec<&'static str>,
    pub sort_names: Vec<String>,
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
}

pub fn discover<L: Language>(lang: &L, cfg: &Config) -> Discovery {
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

    // 3. Search, without subtyping and, if the fingerprints order any
    // sorts, with it; keep the shorter system (the one without, on a tie).
    let run = |sem: &mut Semantics<L::Value>, oracle: &mut Oracle<L>, rng: &mut Rng| {
        let mut searches = Vec::new();
        let mut rules = Vec::new();
        for (ci, c) in sig.iter().enumerate() {
            if c.kind != Kind::Op {
                continue;
            }
            let s = search_con(oracle, sem, &pools, ci, &cfg.search, rng);
            note(&format!(
                "searched {} ({} candidates)",
                c.name, s.candidates
            ));
            rules.extend(s.chosen.iter().cloned());
            searches.push(s);
        }
        (searches, rules)
    };
    let (mut searches, mut rules) = run(&mut sem, &mut oracle, &mut rng);
    let size = |rules: &[Schema]| rules.iter().map(|r| 1 + r.constants()).sum::<usize>();
    let mut subtypes: Vec<(usize, usize)> = Vec::new();
    let mut sizes = (size(&rules), None);
    if sem.has_order() {
        sem.set_subtyping(true);
        let (s2, r2) = run(&mut sem, &mut oracle, &mut rng);
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
    Discovery {
        language: lang.name().to_string(),
        config: cfg.clone(),
        con_names: sig.iter().map(|c| c.name).collect(),
        sort_names,
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
        if !sound_for(oracle, sem, &out, &types) {
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

/// How each binder's variables are generalised, and why.
#[derive(Clone, Default)]
pub struct Generalisation {
    pub policies: HashMap<(usize, usize, usize), (Policy, usize)>,
    pub inert: Vec<bool>,
    /// Per policy tried: the binder, the policy, programs it typed that
    /// the next stricter one didn't, and a typed program that got stuck.
    pub trials: Vec<((usize, usize, usize), Policy, usize, Option<String>)>,
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
    // The uses: a rule without binders, and a child of it to put `v` in.
    let uses: Vec<(&Schema, usize)> = rules
        .iter()
        .filter(|r| r.kids.iter().all(|k| k.bound.is_empty()))
        .flat_map(|r| (0..r.kids.len()).map(move |p| (r, p)))
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
    if binders.is_empty() {
        return gen;
    }
    // Candidate child terms, with a type that has free variables.
    let checker = checker_for(lang, sem, rules, &gen);
    let clock = std::time::Instant::now();
    let mut inits: Vec<Term> = corpus.to_vec();
    for n in 0..cfg.typed_terms {
        inits.extend(checker.generate(rng, 3 + n % cfg.typed_size));
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
    let mut tested = 0;
    for t in inits {
        if tested >= cfg.poly_tests {
            break;
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
        let ok = poly_member(oracle, sem, rules, &v, &ty, 16, rng);
        verdicts.push((gen.inert[t.con], ok, t, ty));
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
