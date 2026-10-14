//! The search for one constructor's rules: find where bound variables come
//! from, observe, propose, refute, select.
//!
//! **Binder flow.** A bound variable's type is the type of what flows into
//! it, which is found by probing: make the child the variable itself and
//! see where its value comes out. `const(e, x0)` gives `e`'s value, so
//! `x0` is child 0's; `func1(x1)` gives a closure that, called, returns
//! itself, so `x1` is the node's own value (recursion); `func1(x0)` gives
//! one that returns its argument, so `x0` is the eliminator's argument.
//!
//! **Observe.** Build nodes `c(e₁, …, eₙ)` from representative children: a
//! closed child is a term whose value has a known type; a child under
//! binders is an open term. For each typing `β` of the bound variables
//! that their sources allow, find each child's types: a closed child's are
//! its value's, an open child's are those every run of it gives a value
//! of, with its bound variables set to sampled members of `β`. With the
//! node's own outcome, that is one observation.
//!
//! **Propose.** Top down, every rule that commits to at most one sort
//! (`simple_rules`), so the simplest are never missed. Bottom up, from
//! the observations: each is a set of ground rule instances, and the
//! candidates are those instances, the least general generalisations
//! (`types::lgg`) of random pairs and triples of them, and the summits of
//! climbs: from a seed instance, lgg with one instance after another,
//! kept while no observation refutes it (Golem's bottom-up search).
//!
//! Candidates must be faithful to what refined types mean (`faithful`).
//!
//! **Refute.** A candidate is refuted by an observation it matches whose
//! node doesn't run to a member of the type it predicts.
//!
//! **Select.** Greedily cover the observations with unrefuted candidates,
//! each observation weighed so every tuple of child sorts counts once: of
//! the rules that gain a good share of the best gain, the one that commits
//! to the fewest types, until what is left is a small share. Before
//! a candidate joins, it is attacked directly: its variables instantiated,
//! children found that meet its premises, and the node run (`falsify`).
//! That is the rule's compatibility lemma, tested, CEGIS-style.

use crate::enumerate::{product, Rng};
use crate::lang::{Atom, Kind, Language, Outcome, Term};
use crate::semantics::{Oracle, Semantics};
use crate::types::{lgg, match_ground, subst, Premise, Schema, Ty};
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Debug)]
pub struct SearchConfig {
    /// Closed representatives per type in the universe.
    pub reps_per_type: usize,
    /// Nodes observed per constructor.
    pub nodes: usize,
    /// Bound-variable typings tried per node.
    pub betas: usize,
    /// Observations whose instances propose candidates.
    pub proposers: usize,
    /// Pairs (and triples) of ground instances whose lgg is proposed.
    pub pairs: usize,
    /// Climbs started per group of instances of one shape, and the steps
    /// each takes.
    pub seeds_per_group: usize,
    pub climb: usize,
    /// Instantiations of a candidate's variables `falsify` tries.
    pub attacks: usize,
    /// A rule joins only if it gains this share of what the best rule
    /// chosen gained...
    pub min_gain: f64,
    /// ...and the first, this share of all the weight the candidates cover.
    pub first_gain: f64,
    /// Rules gaining this share of the best gain compete on simplicity.
    pub substantial: f64,
}

impl Default for SearchConfig {
    fn default() -> Self {
        SearchConfig {
            reps_per_type: 2,
            nodes: 1500,
            betas: 6,
            proposers: 400,
            pairs: 1500,
            seeds_per_group: 3,
            climb: 120,
            attacks: 60,
            min_gain: 0.2,
            first_gain: 0.005,
            substantial: 0.25,
        }
    }
}

/// Where a bound variable's value comes from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Source {
    /// A closed child's value.
    Child(usize),
    /// The node's own value: the variable is a fixpoint.
    Node,
    /// An argument of the node's value's eliminator: a parameter.
    Arg(usize),
    Unknown,
}

/// Where `return`s go, if the language has them: per child, whether its
/// `return` goes through the node (its exit type is the node's) or is
/// caught (a function's body's, by the call); and whether the node starts
/// one itself.
#[derive(Clone, Debug)]
pub struct ExitFlow {
    pub caught: Vec<bool>,
    pub origin: bool,
}

pub struct Observation<V> {
    pub node: Term,
    pub outcome: Outcome<V>,
    /// Per child, the universe indices of its bound variables' types.
    pub beta: Vec<Vec<usize>>,
    /// Per child, the universe indices of the types it has; `None` if a
    /// run of it got stuck.
    pub kid_types: Vec<Option<Vec<usize>>>,
    /// Per child, the universe indices of the types its `return`s carry
    /// (all of them if it returns nothing).
    pub kid_exits: Vec<Option<Vec<usize>>>,
    /// Types the binder flow fixed: per child, and for the node.
    pub kid_fixed: Vec<Option<usize>>,
    pub res_fixed: Option<usize>,
}

#[derive(Clone)]
pub struct ConSearch {
    pub con: usize,
    pub sources: Vec<Vec<Source>>,
    pub exits: Option<ExitFlow>,
    pub observations: usize,
    pub candidates: usize,
    pub refuted: usize,
    /// Candidates the greedy cover picked but `falsify` refuted.
    pub falsified: usize,
    pub chosen: Vec<Schema>,
    /// Per rule chosen, the variables that may not stand for a union of
    /// types: those the attacks break the rule with when they do.
    pub no_unions: Vec<Vec<u32>>,
    /// The most general refuted candidate, and why.
    pub best_refuted: Option<(Schema, String)>,
}

/// The pools children are drawn from.
pub struct Pools {
    /// Small closed terms covering the universe's types.
    pub reps: Vec<Term>,
    /// Open terms by how many variables they may use.
    pub open: HashMap<usize, Vec<Term>>,
    /// Small closed terms that complete abruptly, one per kind of fault or
    /// value returned: a fault is in every type, and these are what
    /// catchers catch.
    pub faults: Vec<Term>,
    /// Each one's kind (its reason's first word: a throw, a `break`, a
    /// `return`), numbered.
    pub fault_kinds: Vec<usize>,
}

pub fn search_con<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    pools: &Pools,
    con: usize,
    cfg: &SearchConfig,
    rng: &mut Rng,
) -> ConSearch {
    let clock = std::time::Instant::now();
    let trace = std::env::var_os("TYSEARCH_TRACE").is_some();
    let lap = |what: &str| {
        if trace {
            eprintln!("    {:>7.2}s {what}", clock.elapsed().as_secs_f64());
        }
    };
    let sources = binder_sources(oracle, sem, pools, con, rng);
    let flow = exit_flow(oracle, pools, con, rng);
    let obs = observe(oracle, sem, pools, con, &sources, cfg, rng);
    // A construct that never completes normally may claim any result type.
    let free_res = !obs.iter().any(|o| matches!(o.outcome, Outcome::Value(_)));
    lap(&format!("observed {}", obs.len()));
    let index: HashMap<Ty, usize> = sem
        .universe
        .iter()
        .enumerate()
        .map(|(i, t)| (t.clone(), i))
        .collect();

    // Propose.
    let proposers: Vec<usize> = {
        let good: Vec<usize> = (0..obs.len())
            .filter(|&i| {
                matches!(obs[i].outcome, Outcome::Value(_))
                    && obs[i].kid_types.iter().all(Option::is_some)
            })
            .collect();
        rng.sample(&good, cfg.proposers)
    };
    let mut ground: Vec<Schema> = Vec::new();
    for i in proposers {
        ground.extend(instances(oracle, sem, &obs[i], con, flow.as_ref(), rng));
    }
    ground.sort();
    ground.dedup();
    let mut candidates: BTreeSet<Schema> = ground.iter().cloned().collect();
    // Anti-unify within groups of one shape (sorts blanked out), where a
    // pair's lgg keeps the structure they share, and across them.
    let mut groups: std::collections::BTreeMap<Schema, Vec<usize>> = Default::default();
    for (i, g) in ground.iter().enumerate() {
        groups.entry(skeleton(g)).or_default().push(i);
    }
    let groups: Vec<Vec<usize>> = groups.into_values().collect();
    if std::env::var("TYSEARCH_EXPLAIN").ok() == Some(oracle.lang.signature()[con].name.to_string())
    {
        for g in &groups {
            eprintln!("  group of {}:", g.len());
            for &i in g.iter().take(12) {
                eprintln!("     {:?}", ground[i]);
            }
        }
    }
    if !ground.is_empty() {
        for k in 0..cfg.pairs {
            // Pairs, and every third time a triple; half within a group.
            let n = if k % 3 == 2 { 3 } else { 2 };
            let pick: Vec<Schema> = if k % 2 == 0 {
                let g = &groups[rng.below(groups.len())];
                (0..n)
                    .map(|_| ground[g[rng.below(g.len())]].clone())
                    .collect()
            } else {
                (0..n)
                    .map(|_| ground[rng.below(ground.len())].clone())
                    .collect()
            };
            if let Some((g, _)) = lgg(&pick) {
                if g.res_bound() {
                    candidates.insert(g.normalize());
                }
            }
        }
    }
    // Climb: from seeds in every group, generalise by lgg with other
    // instances as long as no observation refutes the result (Golem's
    // bottom-up search). The climbs' summits are what random pairs miss.
    let mut verdicts: HashMap<Schema, bool> = HashMap::new();
    if !ground.is_empty() {
        let mut seeds: Vec<(usize, usize)> = Vec::new();
        for (gi, g) in groups.iter().enumerate() {
            seeds.extend(
                rng.sample(g, cfg.seeds_per_group)
                    .into_iter()
                    .map(|s| (gi, s)),
            );
        }
        for (gi, seed) in seeds {
            let mut cur = ground[seed].clone();
            for step in 0..cfg.climb {
                // Mostly within the seed's group, which keeps its shape.
                let g = &groups[gi];
                let h = if step % 4 != 3 {
                    &ground[g[rng.below(g.len())]]
                } else {
                    &ground[rng.below(ground.len())]
                };
                let Some((g, _)) = lgg(&[cur.clone(), h.clone()]) else {
                    continue;
                };
                let g = g.normalize();
                if g == cur || !g.res_bound() {
                    continue;
                }
                let ok = *verdicts
                    .entry(g.clone())
                    .or_insert_with(|| test(oracle, sem, &index, &g, &obs).is_ok());
                candidates.insert(g.clone());
                if ok {
                    cur = g;
                }
            }
        }
    }
    // Top down: every rule committing to at most one sort, so the simplest
    // sound rules are always candidates.
    candidates.extend(simple_rules(
        oracle.lang.signature(),
        sem,
        con,
        &sources,
        flow.as_ref(),
        free_res,
    ));
    candidates.retain(|r| faithful(sem, r));
    lap(&format!("proposed {}", candidates.len()));
    // Refute by observation.
    let mut s = ConSearch {
        con,
        sources,
        exits: flow.clone(),
        observations: obs.len(),
        candidates: candidates.len(),
        refuted: 0,
        falsified: 0,
        chosen: Vec::new(),
        no_unions: Vec::new(),
        best_refuted: None,
    };
    let mut sound: Vec<(Schema, Vec<(usize, Ty)>)> = Vec::new();
    let mut refuted: Vec<(Schema, String)> = Vec::new();
    for cand in candidates {
        match test(oracle, sem, &index, &cand, &obs) {
            Err(w) => refuted.push((cand, describe(oracle.lang, sem, &obs[w]))),
            Ok(covered) => sound.push((cand, covered)),
        }
    }
    s.refuted = refuted.len();
    lap("tested");
    let explain = std::env::var("TYSEARCH_EXPLAIN").ok()
        == Some(oracle.lang.signature()[con].name.to_string());
    if explain {
        let mut all: Vec<(usize, String)> = sound
            .iter()
            .map(|(r, c)| (c.len(), format!("sound, covers {:>4}: {:?}", c.len(), r)))
            .chain(
                refuted
                    .iter()
                    .map(|(r, w)| (0, format!("refuted: {:?}\n        by {w}", r))),
            )
            .collect();
        all.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        for (_, line) in all.iter() {
            eprintln!("  {line}");
        }
    }

    // Weigh observations so each tuple of the closed children's sorts
    // counts once: the representatives have many more kinds of closure
    // than of number, and the choice of rules shouldn't follow that.
    let keys: Vec<Vec<Option<usize>>> = obs
        .iter()
        .map(|o| {
            o.node
                .kids
                .iter()
                .zip(&oracle.lang.signature()[con].binds)
                .map(|(k, &b)| match (b, oracle.eval(k)) {
                    (0, Outcome::Value(v)) => sem.sort(oracle, &v),
                    _ => None,
                })
                .collect()
        })
        .collect();
    let mut per_key: HashMap<&Vec<Option<usize>>, usize> = HashMap::new();
    for k in &keys {
        *per_key.entry(k).or_default() += 1;
    }
    let weight: Vec<f64> = keys.iter().map(|k| 1.0 / per_key[k] as f64).collect();
    if explain {
        let mut hist: std::collections::BTreeMap<String, usize> = Default::default();
        for (o, k) in obs.iter().zip(&keys) {
            let kind = match &o.outcome {
                Outcome::Value(_) => "value",
                Outcome::Stuck { .. } => "stuck",
                Outcome::Fault(_) => "fault",
                Outcome::Timeout => "timeout",
                Outcome::Return(_) => "return",
            };
            *hist.entry(format!("{k:?} {kind}")).or_default() += 1;
        }
        for (k, n) in hist {
            eprintln!("  obs {k}: {n}");
        }
    }

    // Select: among the rules gaining a good share of the most any rule
    // gains, the simplest, attacked before it joins; until what is left to
    // gain is a small share of all there is.
    // Per observation, the most specific type a chosen rule gives it. A
    // rule gains where none does yet, or where it gives a strictly more
    // specific type (with subtyping: `+ : (Int, Int) -> Int` after `+ :
    // (Float, Float) -> Float`).
    let mut covered: Vec<Option<Ty>> = vec![None; obs.len()];
    // All the weight the candidates still standing, and those chosen, can
    // cover: recomputed as candidates fall, so that rules refuted late
    // don't keep the bar high.
    let coverable_of = |sound: &[(Schema, Vec<(usize, Ty)>)], covered: &[Option<Ty>]| -> f64 {
        let mut any: Vec<bool> = covered.iter().map(Option::is_some).collect();
        for (_, c) in sound {
            for (i, _) in c {
                any[*i] = true;
            }
        }
        (0..any.len()).filter(|&i| any[i]).map(|i| weight[i]).sum()
    };
    let mut best_gain: f64 = 0.0;
    loop {
        let coverable = coverable_of(&sound, &covered);
        let order = (sem.subtyping, sem.le.clone());
        let improves = move |i: usize, p: &Ty, covered: &[Option<Ty>]| match (&covered[i], p) {
            (None, _) => true,
            (Some(Ty::Base(b)), Ty::Base(a)) => a != b && order.0 && order.1[*a][*b],
            _ => false,
        };
        let gain = |c: &[(usize, Ty)], covered: &[Option<Ty>]| -> f64 {
            c.iter()
                .filter(|(i, p)| improves(*i, p, covered))
                .map(|(i, _)| weight[*i])
                .sum()
        };
        let gains: Vec<f64> = sound.iter().map(|(_, c)| gain(c, &covered)).collect();
        // A rule must gain a share of what the best rule chosen gained (or,
        // for the first, a small share of all there is). A simple rule (at
        // most one constant) that types what no rule does yet needs only
        // the small share: an overload for a rare shape (`app2` on
        // two-argument functions, next to `app2` on one-argument ones) is
        // no less a rule for being rare. A gain in precision alone must
        // pull its weight.
        let small = cfg.first_gain * coverable;
        let bar = if best_gain > 0.0 {
            cfg.min_gain * best_gain
        } else {
            small
        };
        let fresh = |i: usize| -> f64 {
            sound[i]
                .1
                .iter()
                .filter(|(j, _)| covered[*j].is_none())
                .map(|(j, _)| weight[*j])
                .sum()
        };
        let passing: Vec<usize> = (0..sound.len())
            .filter(|&i| {
                gains[i] > 1e-9
                    && (gains[i] >= bar
                        || (sound[i].0.constants() <= 1 && fresh(i) >= small.max(1e-9)))
            })
            .collect();
        let max = passing.iter().map(|&i| gains[i]).fold(0.0, f64::max);
        if passing.is_empty() {
            break;
        }
        let at = passing
            .iter()
            .copied()
            .filter(|&i| gains[i] >= cfg.substantial * max)
            .min_by(|&i, &j| {
                let key = |k: usize| {
                    (
                        sound[k].0.constants(),
                        std::cmp::Reverse(sound[k].0.vars().len()),
                    )
                };
                key(i).cmp(&key(j)).then(gains[j].total_cmp(&gains[i]))
            })
            .unwrap();
        let (best, cov) = sound.swap_remove(at);
        // The open children of nodes it covers fit its premises, where
        // random open terms may not.
        // Those only it covers first: what it adds is where it is wrong,
        // if anywhere.
        let fresh_cov: Vec<usize> = cov
            .iter()
            .map(|(i, _)| *i)
            .filter(|&i| covered[i].is_none())
            .collect();
        let pool_cov = if fresh_cov.is_empty() {
            cov.iter().map(|(i, _)| *i).collect::<Vec<_>>()
        } else {
            fresh_cov
        };
        let examples: Vec<Term> = rng
            .sample(&pool_cov, 6)
            .into_iter()
            .map(|i| obs[i].node.clone())
            .collect();
        if let Some(why) = falsify(
            oracle,
            sem,
            pools,
            &best,
            &examples,
            &HashMap::new(),
            cfg,
            rng,
        ) {
            if std::env::var_os("TYSEARCH_TRACE").is_some() {
                eprintln!("    falsified {:?}: {why}", best);
            }
            s.falsified += 1;
            refuted.push((best, why));
            continue;
        }
        best_gain = best_gain.max(gains[at]);
        if trace {
            eprintln!(
                "    chose {:?} gaining {:.1}% of {coverable:.1}",
                best,
                100.0 * gains[at] / coverable
            );
        }
        for (i, p) in cov {
            if improves(i, &p, &covered) {
                covered[i] = Some(p);
            }
        }
        s.chosen.push(best);
    }
    // A construct that never completes normally (`throw`, `break`), only
    // abruptly, which is allowed, is of every type: its result's variable
    // is free, which no observation can claim, so no proposal has it.
    let abrupt = obs.iter().any(|o| matches!(o.outcome, Outcome::Fault(_)))
        && !obs.iter().any(|o| {
            matches!(
                o.outcome,
                Outcome::Value(_) | Outcome::Stuck { root: true, .. }
            )
        });
    if s.chosen.is_empty() && abrupt {
        let n = c_arity(oracle, con) as u32;
        let kids = (0..n)
            .map(|k| Premise {
                bound: s.sources[k as usize].iter().map(|_| Ty::Top).collect(),
                ty: Ty::Var(k),
                exit: None,
            })
            .collect();
        let r = Schema {
            con,
            kids,
            res: Ty::Var(n),
            exit: None,
        };
        match falsify(oracle, sem, pools, &r, &[], &HashMap::new(), cfg, rng) {
            None => s.chosen.push(r),
            Some(why) => refuted.push((r, why)),
        }
    }
    s.no_unions = s
        .chosen
        .clone()
        .iter()
        .map(|r| no_union_vars(oracle, sem, pools, r, cfg, rng))
        .collect();
    lap(&format!(
        "selected ({} forgets, memo {})",
        sem.forgets,
        sem.memo_size()
    ));
    s.best_refuted = refuted
        .into_iter()
        .min_by_key(|(r, _)| (r.constants(), std::cmp::Reverse(r.vars().len())));
    s
}

/// Whether a rule uses refined types only for what they mean. `T<A -> R>`
/// says what `T`'s eliminator gives on arguments of types `A`, and nothing
/// else; so a rule for that eliminator, with a refined type at the hole,
/// must give the other children the argument types and claim the result
/// type. (`app1 : (T3<a -> T1>, b) -> T1` is unfaithful: it says what
/// `f` does to a `b` from what it does to an `a`.)
fn faithful<V: Clone + Eq + std::hash::Hash + std::fmt::Debug>(
    sem: &Semantics<V>,
    r: &Schema,
) -> bool {
    // An alias (an eliminator that repeats a refining one, extra arguments
    // ignored) is held to the same meaning: its leading arguments have the
    // parameters' types and its result the result's.
    for (s, aliases) in sem.aliases.iter().enumerate() {
        for &(elim, hole, ti) in aliases {
            if elim != r.con {
                continue;
            }
            let Ty::Ref(s2, ps) = &r.kids[hole].ty else {
                continue;
            };
            if *s2 != s {
                continue;
            }
            let (at, n) = sem.slices(s)[ti];
            let others: Vec<&Ty> = (0..r.kids.len())
                .filter(|&j| j != hole)
                .map(|j| &r.kids[j].ty)
                .collect();
            let (res, args) = ps[at..at + n].split_last().unwrap();
            if others.len() < args.len()
                || others.iter().zip(args).any(|(o, a)| *o != a)
                || r.res != *res
            {
                return false;
            }
        }
    }
    for (s, ts) in sem.templates.iter().enumerate() {
        for (t, (at, n)) in ts.iter().zip(sem.slices(s)) {
            if t.elim != r.con {
                continue;
            }
            let Ty::Ref(s2, ps) = &r.kids[t.hole].ty else {
                continue;
            };
            if *s2 != s {
                continue;
            }
            let others: Vec<&Ty> = (0..r.kids.len())
                .filter(|&j| j != t.hole)
                .map(|j| &r.kids[j].ty)
                .collect();
            let (res, args) = ps[at..at + n].split_last().unwrap();
            if others.len() != args.len()
                || others.iter().zip(args).any(|(o, a)| *o != a)
                || r.res != *res
            {
                return false;
            }
        }
    }
    true
}

/// Every rule for `con` that commits to at most one sort constant (a
/// sort, or a refined sort whose parameters are variables), its variables
/// shared in every way, and its bound variables typed as their sources
/// say.
fn simple_rules<V: Clone + Eq + std::hash::Hash + std::fmt::Debug>(
    sig: &[crate::lang::Con],
    sem: &Semantics<V>,
    con: usize,
    sources: &[Vec<Source>],
    flow: Option<&ExitFlow>,
    free_res: bool,
) -> Vec<Schema> {
    let c = &sig[con];
    // The children's types, the result's, and the exit types that aren't
    // the node's: caught children's, and the node's if it starts a return.
    let caught: Vec<bool> = flow.map_or(vec![false; c.arity], |f| f.caught.clone());
    let origin = flow.is_some_and(|f| f.origin);
    let n_exits = caught.iter().filter(|c| **c).count() + origin as usize;
    let positions = c.arity + 1 + n_exits;
    // Each position: a variable (an old one, or the next new one), or, once
    // per rule, a constant.
    fn go<V: Clone + Eq + std::hash::Hash + std::fmt::Debug>(
        sem: &Semantics<V>,
        positions: usize,
        acc: &mut Vec<Ty>,
        next: u32,
        constant_used: bool,
        out: &mut Vec<Vec<Ty>>,
    ) {
        if acc.len() == positions {
            out.push(acc.clone());
            return;
        }
        for v in 0..=next {
            acc.push(Ty::Var(v));
            go(sem, positions, acc, next.max(v + 1), constant_used, out);
            acc.pop();
        }
        if constant_used {
            return;
        }
        for s in 0..sem.count() {
            match sem.arity(s) {
                0 => {
                    acc.push(Ty::Base(s));
                    go(sem, positions, acc, next, true, out);
                    acc.pop();
                }
                arity => {
                    // Parameters: variables, old or new, in order, or
                    // unrefined sorts (`T7<num -> a>`, an array indexed by
                    // numbers, is one commitment).
                    let bases: Vec<usize> =
                        (0..sem.count()).filter(|&b| sem.arity(b) == 0).collect();
                    let mut params: Vec<(Vec<Ty>, u32)> = vec![(Vec::new(), next)];
                    for _ in 0..arity {
                        params = params
                            .into_iter()
                            .flat_map(|(ps, n)| {
                                let vars = (0..=n).map(|v| (Ty::Var(v), n.max(v + 1)));
                                let sorts = bases.iter().map(|&b| (Ty::Base(b), n));
                                vars.chain(sorts)
                                    .map(|(p, n2)| {
                                        let mut ps = ps.clone();
                                        ps.push(p);
                                        (ps, n2)
                                    })
                                    .collect::<Vec<_>>()
                            })
                            .collect();
                    }
                    for (ps, n) in params {
                        acc.push(Ty::Ref(s, ps));
                        go(sem, positions, acc, n, true, out);
                        acc.pop();
                    }
                }
            }
        }
    }
    let mut tuples = Vec::new();
    go(sem, positions, &mut Vec::new(), 0, false, &mut tuples);
    let mut out = Vec::new();
    // A bound variable of no known source is anything: some type, or every
    // value at once.
    let unknown = sources.iter().flatten().any(|s| *s == Source::Unknown);
    let tops: &[bool] = if unknown { &[false, true] } else { &[false] };
    for (tys, &top) in tuples.iter().flat_map(|t| tops.iter().map(move |b| (t, b))) {
        let (kid_tys, rest) = tys.split_at(c.arity);
        let res = &rest[0];
        let mut exits = rest[1..].iter().cloned();
        let mut fresh = tys
            .iter()
            .map(|t| {
                let mut v = Vec::new();
                t.vars(&mut v);
                v.into_iter().max().map_or(0, |m| m + 1)
            })
            .max()
            .unwrap_or(0);
        let mut ok = true;
        let kids: Vec<Premise> = kid_tys
            .iter()
            .enumerate()
            .map(|(i, ty)| Premise {
                bound: sources[i]
                    .iter()
                    .map(|src| match *src {
                        Source::Child(k) => kid_tys[k].clone(),
                        Source::Node => res.clone(),
                        Source::Arg(m) => match res {
                            Ty::Ref(_, ps) if m + 1 < ps.len() => ps[m].clone(),
                            _ => {
                                ok = false;
                                Ty::Var(0)
                            }
                        },
                        Source::Unknown if top => Ty::Top,
                        Source::Unknown => {
                            fresh += 1;
                            Ty::Var(fresh - 1)
                        }
                    })
                    .collect(),
                ty: ty.clone(),
                exit: None,
            })
            .collect();
        let mut kids = kids;
        for (k, kid) in kids.iter_mut().enumerate() {
            if caught[k] {
                kid.exit = exits.next();
            }
        }
        let r = Schema {
            con,
            kids,
            res: res.clone(),
            exit: if origin { exits.next() } else { None },
        };
        if ok && (free_res || r.res_bound()) {
            out.push(r.normalize());
        }
    }
    out
}

/// A rule with its sorts blanked out: its shape.
fn skeleton(s: &Schema) -> Schema {
    fn blank(t: &Ty) -> Ty {
        match t {
            Ty::Base(_) => Ty::Base(0),
            Ty::Top => Ty::Top,
            Ty::Never => Ty::Never,
            Ty::Var(v) => Ty::Var(*v),
            Ty::Ref(s, ps) => Ty::Ref(*s, ps.iter().map(blank).collect()),
            Ty::Union(ts) => Ty::Union(ts.iter().map(blank).collect()),
        }
    }
    Schema {
        con: s.con,
        kids: s
            .kids
            .iter()
            .map(|k| Premise {
                bound: k.bound.iter().map(blank).collect(),
                ty: blank(&k.ty),
                exit: k.exit.as_ref().map(blank),
            })
            .collect(),
        res: blank(&s.res),
        exit: s.exit.as_ref().map(blank),
    }
}

fn describe<L: Language>(lang: &L, sem: &Semantics<L::Value>, o: &Observation<L::Value>) -> String {
    let beta: Vec<String> = o
        .beta
        .iter()
        .flatten()
        .map(|&u| format!("{:?}", sem.universe[u]))
        .collect();
    if beta.is_empty() {
        lang.show_term(&o.node)
    } else {
        format!("{} with bound {}", lang.show_term(&o.node), beta.join(", "))
    }
}

/// The variable constructor.
/// Terms that use bound variables of types `beta` (ground) where their
/// sorts are accepted and others are not: `app2(x0, 0, 1)`, `neg(x1)`; the
/// other children are small closed terms.
fn uses_of<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &Semantics<L::Value>,
    pools: &Pools,
    beta: &[Ty],
    rng: &mut Rng,
) -> Vec<Term> {
    let sig = oracle.lang.signature();
    let var = var_con(sig);
    let mut out = Vec::new();
    for (j, t) in beta.iter().enumerate() {
        let s = match t {
            Ty::Base(s) | Ty::Ref(s, _) => *s,
            _ => continue,
        };
        for (con, hole) in rng.sample(&sem.uses[s], 4) {
            let c = &sig[con];
            if c.binds.iter().any(|&b| b > 0) || pools.reps.is_empty() {
                continue;
            }
            let kids = (0..c.arity)
                .map(|i| {
                    if i == hole {
                        Term::leaf(var, Atom::Int(j as i64))
                    } else {
                        pools.reps[rng.below(pools.reps.len())].clone()
                    }
                })
                .collect();
            out.push(Term {
                con,
                atom: c.atoms_or_none()[0].clone(),
                kids,
            });
        }
    }
    out
}

/// Where `return`s go through `con`, found by putting a returning term in
/// each child; `None` if nothing returns.
fn exit_flow<L: Language>(
    oracle: &mut Oracle<L>,
    pools: &Pools,
    con: usize,
    rng: &mut Rng,
) -> Option<ExitFlow> {
    let returning: Vec<Term> = pools
        .faults
        .iter()
        .filter(|t| matches!(oracle.eval(t), Outcome::Return(_)))
        .cloned()
        .collect();
    if returning.is_empty() || pools.reps.is_empty() {
        return None;
    }
    let sig = oracle.lang.signature();
    let var = var_con(sig);
    let c = sig[con].clone();
    let atoms = c.atoms_or_none();
    let others = |k: usize, rng: &mut Rng, plain: bool| -> Term {
        if c.binds[k] == 0 {
            // Values, or (to run a catcher) faults.
            if !plain && rng.below(2) == 0 && !pools.faults.is_empty() {
                pools.faults[rng.below(pools.faults.len())].clone()
            } else {
                pools.reps[rng.below(pools.reps.len())].clone()
            }
        } else if plain {
            Term::leaf(var, Atom::Int(0))
        } else {
            let open = &pools.open[&c.binds[k]];
            open[rng.below(open.len())].clone()
        }
    };
    let mut caught = Vec::new();
    for k in 0..c.arity {
        let (mut through, mut not) = (0, 0);
        for _ in 0..16 {
            let r = &returning[rng.below(returning.len())];
            let kids: Vec<Term> = (0..c.arity)
                .map(|j| {
                    if j == k {
                        r.clone()
                    } else {
                        others(j, rng, false)
                    }
                })
                .collect();
            let atom = atoms[rng.below(atoms.len())].clone();
            let node = Term { con, atom, kids };
            let o = oracle.eval(&node);
            // Only if the child ran: another child there changes things.
            let mut alt = node.clone();
            alt.kids[k] = pools.reps[rng.below(pools.reps.len())].clone();
            if oracle.lang.same_outcome(&oracle.eval(&alt), &o) {
                continue;
            }
            if oracle.lang.same_outcome(&o, &oracle.eval(r)) {
                through += 1;
            } else {
                not += 1;
            }
        }
        caught.push(not > through);
    }
    // A node that returns with children that are values or variables.
    let mut origin = false;
    for _ in 0..16 {
        let kids: Vec<Term> = (0..c.arity).map(|j| others(j, rng, true)).collect();
        let atom = atoms[rng.below(atoms.len())].clone();
        if matches!(oracle.eval(&Term { con, atom, kids }), Outcome::Return(_)) {
            origin = true;
            break;
        }
    }
    Some(ExitFlow { caught, origin })
}

/// The variables of `r` that may not stand for a union of two types: those
/// the attacks break the rule with when they do (`== : (a, a) -> T2` where
/// `1 == "a"` is stuck).
fn no_union_vars<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    pools: &Pools,
    r: &Schema,
    cfg: &SearchConfig,
    rng: &mut Rng,
) -> Vec<u32> {
    let bases: Vec<Ty> = sem
        .universe
        .iter()
        .filter(|t| matches!(t, Ty::Base(_)))
        .cloned()
        .collect();
    let mut out = Vec::new();
    for v in r.vars() {
        let quick = SearchConfig {
            attacks: cfg.attacks / 6,
            ..cfg.clone()
        };
        let mut ok = true;
        'pairs: for (i, a) in bases.iter().enumerate() {
            for b in &bases[i + 1..] {
                let fixed: HashMap<u32, Ty> = [(v, Ty::union(a, b))].into_iter().collect();
                if falsify(oracle, sem, pools, r, &[], &fixed, &quick, rng).is_some() {
                    ok = false;
                    break 'pairs;
                }
            }
        }
        if !ok {
            out.push(v);
        }
    }
    out
}

fn c_arity<L: Language>(oracle: &Oracle<L>, con: usize) -> usize {
    oracle.lang.signature()[con].arity
}

fn var_con(sig: &[crate::lang::Con]) -> usize {
    sig.iter().position(|c| c.kind == Kind::Var).unwrap()
}

/// Where each bound variable's value comes from, found by making the child
/// the variable itself.
pub fn binder_sources<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    pools: &Pools,
    con: usize,
    rng: &mut Rng,
) -> Vec<Vec<Source>> {
    let sig = oracle.lang.signature();
    let c = sig[con].clone();
    let var = var_con(sig);
    let pool: Vec<L::Value> = sem.members.iter().flatten().cloned().collect();
    let mut out = Vec::new();
    for (i, &b) in c.binds.iter().enumerate() {
        let mut mine = Vec::new();
        for j in 0..b {
            let mut verdicts: Vec<Vec<Source>> = Vec::new();
            for _ in 0..8 {
                let kids: Vec<Term> = c
                    .binds
                    .iter()
                    .enumerate()
                    .map(|(k, &bk)| {
                        if k == i {
                            Term::leaf(var, Atom::Int(j as i64))
                        } else if bk == 0 {
                            pools.reps[rng.below(pools.reps.len())].clone()
                        } else {
                            let open = &pools.open[&bk];
                            open[rng.below(open.len())].clone()
                        }
                    })
                    .collect();
                let atoms = c.atoms_or_none();
                let node = Term {
                    con,
                    atom: atoms[rng.below(atoms.len())].clone(),
                    kids,
                };
                let Outcome::Value(v) = oracle.eval(&node) else {
                    continue;
                };
                // A trial says something only if the child ran: the node
                // gives something else with another child there (a `catch`
                // runs only on a throw).
                let mut alt = node.clone();
                alt.kids[i] = pools.reps[rng.below(pools.reps.len())].clone();
                if oracle
                    .lang
                    .same_outcome(&oracle.eval(&alt), &Outcome::Value(v.clone()))
                {
                    continue;
                }
                let mut fits = Vec::new();
                for (k, &bk) in c.binds.iter().enumerate() {
                    if bk == 0
                        && k != i
                        && oracle
                            .lang
                            .same_outcome(&oracle.eval(&node.kids[k]), &Outcome::Value(v.clone()))
                    {
                        fits.push(Source::Child(k));
                    }
                }
                // Through the value's eliminator, with arguments drawn at
                // random: an argument that comes back names its position.
                if let Some(t) = sem
                    .sort(oracle, &v)
                    .and_then(|s| sem.templates[s].first().cloned())
                {
                    let args: Vec<L::Value> = (0..t.k)
                        .map(|_| pool[rng.below(pool.len())].clone())
                        .collect();
                    let mut env = vec![v.clone()];
                    env.extend(args.iter().cloned());
                    if let Outcome::Value(r) = oracle.eval_in(&t.term, &env) {
                        let same = |x: &L::Value, y: &L::Value| oracle.lang.same(x, y);
                        if same(&r, &v) {
                            fits.push(Source::Node);
                        }
                        for (m, a) in args.iter().enumerate() {
                            if same(a, &r) && args.iter().filter(|x| same(x, a)).count() == 1 {
                                fits.push(Source::Arg(m));
                            }
                        }
                    }
                }
                verdicts.push(fits);
            }
            // A source most trials agree on, and none contradicts.
            let candidates: Vec<Source> = verdicts.iter().flatten().copied().collect();
            let agreed = candidates.iter().copied().find(|s| {
                let n = verdicts.iter().filter(|v| v.contains(s)).count();
                n >= 3 && n * 4 >= verdicts.len() * 3
            });
            mine.push(agreed.unwrap_or(Source::Unknown));
        }
        out.push(mine);
    }
    out
}

/// A typing of the bound variables (universe indices), with the child and
/// node types it fixes.
type Try = (Vec<usize>, Vec<Option<usize>>, Option<usize>);

/// A closed child for `falsify`: a variable, and the value it is bound to.
type Child<V> = (Term, Option<V>);

/// Builds and runs nodes of `con`.
fn observe<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    pools: &Pools,
    con: usize,
    sources: &[Vec<Source>],
    cfg: &SearchConfig,
    rng: &mut Rng,
) -> Vec<Observation<L::Value>> {
    let c = oracle.lang.signature()[con].clone();
    // Closed children: values, and computations that fault.
    let closed_pool: Vec<Term> = pools.reps.iter().chain(&pools.faults).cloned().collect();
    let kid_pools: Vec<&[Term]> = c
        .binds
        .iter()
        .map(|b| {
            if *b == 0 {
                closed_pool.as_slice()
            } else {
                pools.open.get(b).map_or(&[][..], |v| v.as_slice())
            }
        })
        .collect();
    let mut nodes: Vec<Term> = Vec::new();
    let total: usize =
        kid_pools.iter().map(|p| p.len()).product::<usize>() * c.atoms_or_none().len();
    if total <= cfg.nodes {
        for atom in c.atoms_or_none() {
            product(&kid_pools, &mut Vec::new(), &mut |kids| {
                nodes.push(Term {
                    con,
                    atom: atom.clone(),
                    kids: kids.to_vec(),
                })
            });
        }
    } else {
        // Stratified: a sort for each closed child at random, then one of
        // its representatives, so that every tuple of sorts is tried.
        let by_sort: Vec<Vec<Term>> = {
            let mut m: Vec<Vec<Term>> = vec![Vec::new(); sem.count()];
            for t in &pools.reps {
                if let Outcome::Value(v) = oracle.eval(t) {
                    if let Some(s) = sem.sort(oracle, &v) {
                        m[s].push(t.clone());
                    }
                }
            }
            m.push(pools.faults.clone());
            m.into_iter().filter(|v| !v.is_empty()).collect()
        };
        let atoms = c.atoms_or_none();
        let mut seen = std::collections::HashSet::new();
        // Every tuple of groups for the closed children, each its share of
        // the nodes (a tuple with few terms, like a string and a number,
        // gets them all); or, if there are too many tuples, at random.
        let closed = c.binds.iter().filter(|&&b| b == 0).count();
        let n_keys = by_sort
            .len()
            .checked_pow(closed as u32)
            .unwrap_or(usize::MAX);
        let keys: Vec<Option<Vec<usize>>> = if !by_sort.is_empty() && n_keys <= cfg.nodes {
            let groups: Vec<usize> = (0..by_sort.len()).collect();
            let refs: Vec<&[usize]> = (0..closed).map(|_| groups.as_slice()).collect();
            let mut all = Vec::new();
            product(&refs, &mut Vec::new(), &mut |k| all.push(Some(k.to_vec())));
            all
        } else {
            vec![None]
        };
        let share = cfg.nodes / keys.len();
        for key in &keys {
            let mut mine = 0;
            for _ in 0..share * 3 {
                let mut at = 0;
                let kids = c
                    .binds
                    .iter()
                    .zip(&kid_pools)
                    .map(|(&b, p)| {
                        if b == 0 && !by_sort.is_empty() {
                            let g = match key {
                                Some(k) => k[at],
                                None => rng.below(by_sort.len()),
                            };
                            at += 1;
                            let s = &by_sort[g];
                            s[rng.below(s.len())].clone()
                        } else {
                            p[rng.below(p.len())].clone()
                        }
                    })
                    .collect();
                let t = Term {
                    con,
                    atom: atoms[rng.below(atoms.len())].clone(),
                    kids,
                };
                if seen.insert(t.clone()) {
                    nodes.push(t);
                    mine += 1;
                }
                if mine >= share {
                    break;
                }
            }
        }
    }

    let flat: Vec<Source> = sources.iter().flatten().copied().collect();
    let n_u = sem.universe.len();
    let mut out = Vec::new();
    for node in nodes {
        let outcome = oracle.eval(&node);
        if matches!(outcome, Outcome::Timeout) {
            continue;
        }
        // Closed children's types don't depend on the bound variables.
        let mut closed: Vec<Option<Vec<usize>>> = Vec::new();
        let mut closed_exits: Vec<Option<Vec<usize>>> = Vec::new();
        let every: Vec<usize> = (0..n_u).filter(|&u| sem.universe[u] != Ty::Top).collect();
        for (k, b) in node.kids.iter().zip(&c.binds) {
            let (t, x) = if *b == 0 {
                match oracle.eval(k) {
                    Outcome::Value(v) => (Some(sem.types_of(oracle, &v)), Some(every.clone())),
                    Outcome::Fault(_) | Outcome::Timeout => {
                        (Some(every.clone()), Some(every.clone()))
                    }
                    Outcome::Return(v) => (Some(every.clone()), Some(sem.types_of(oracle, &v))),
                    Outcome::Stuck { .. } => (None, None),
                }
            } else {
                (None, None)
            };
            closed.push(t);
            closed_exits.push(x);
        }
        if flat.is_empty() {
            out.push(Observation {
                node,
                outcome,
                beta: vec![Vec::new(); c.arity],
                kid_types: closed,
                kid_exits: closed_exits,
                kid_fixed: vec![None; c.arity],
                res_fixed: None,
            });
            continue;
        }
        let node_types: Vec<usize> = match &outcome {
            Outcome::Value(v) => sem.types_of(oracle, v),
            _ => Vec::new(),
        };
        // Typings of the bound variables their sources allow: one choice of
        // the node's type (for `Node` and `Arg`), one per child named, and
        // anything for the unknown.
        let needs_node = flat
            .iter()
            .any(|s| matches!(s, Source::Node | Source::Arg(_)));
        let mut tries: BTreeSet<Try> = BTreeSet::new();
        for _ in 0..cfg.betas * 6 {
            if tries.len() >= cfg.betas {
                break;
            }
            let res_fixed = if needs_node {
                if node_types.is_empty() {
                    break;
                }
                Some(node_types[rng.below(node_types.len())])
            } else {
                None
            };
            let mut kid_fixed = vec![None; c.arity];
            let mut beta = Vec::new();
            let mut ok = true;
            for s in &flat {
                let t = match *s {
                    Source::Child(k) => closed[k]
                        .as_ref()
                        .filter(|ts| !ts.is_empty())
                        .map(|ts| *kid_fixed[k].get_or_insert_with(|| ts[rng.below(ts.len())])),
                    Source::Node => res_fixed,
                    Source::Arg(m) => match res_fixed.map(|r| &sem.universe[r]) {
                        Some(Ty::Ref(_, ps)) if m + 1 < ps.len() => {
                            sem.universe.iter().position(|u| *u == ps[m])
                        }
                        _ => None,
                    },
                    // Anything, so everything at once: `Top`, last in the
                    // universe.
                    Source::Unknown => Some(n_u - 1),
                };
                match t {
                    Some(t) => beta.push(t),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                tries.insert((beta, kid_fixed, res_fixed));
            }
        }
        // The values flowing into the bound variables, where known.
        let actual: Vec<Option<L::Value>> = flat
            .iter()
            .map(|s| match *s {
                Source::Child(k) => match oracle.eval(&node.kids[k]) {
                    Outcome::Value(v) => Some(v),
                    _ => None,
                },
                Source::Node => match &outcome {
                    Outcome::Value(v) => Some(v.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        for (flat_beta, kid_fixed, res_fixed) in tries {
            let mut beta = Vec::new();
            let mut kid_types = Vec::new();
            let mut kid_exits = Vec::new();
            let mut at = 0;
            for (i, b) in c.binds.iter().enumerate() {
                let mine: Vec<usize> = flat_beta[at..at + b].to_vec();
                at += b;
                let (t, x) = if *b == 0 {
                    (closed[i].clone(), closed_exits[i].clone())
                } else {
                    let tys: Vec<Ty> = mine.iter().map(|&u| sem.universe[u].clone()).collect();
                    match open_types(oracle, sem, &node.kids[i], &tys, &actual[at - b..at]) {
                        Some((t, x)) => (Some(t), Some(x)),
                        None => (None, None),
                    }
                };
                kid_types.push(t);
                kid_exits.push(x);
                beta.push(mine);
            }
            out.push(Observation {
                node: node.clone(),
                outcome: outcome.clone(),
                beta,
                kid_types,
                kid_exits,
                kid_fixed,
                res_fixed,
            });
        }
    }
    out
}

/// Runs open `t` on copies of `env`, its variables of types `beta`: the
/// outcome, or `None` if the run left a variable outside its type (Kripke
/// monotonicity: a premise about a body is about what it does to its
/// variables, too).
fn run_keeping<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    t: &Term,
    env: &[L::Value],
    beta: &[Ty],
) -> Option<Outcome<L::Value>> {
    let env: Vec<L::Value> = env.iter().map(|x| oracle.lang.isolate(x)).collect();
    let before: Vec<L::Value> = env.iter().map(|x| oracle.lang.isolate(x)).collect();
    let o = oracle.eval_shared(t, &env);
    // Only a variable the run changed needs checking again.
    for ((x, b), ty) in env.iter().zip(&before).zip(beta) {
        if !oracle.lang.same(x, b) {
            sem.forget(x);
            if !sem.holds(oracle, x, ty) {
                return None;
            }
        }
    }
    Some(o)
}

/// Environments binding variables of types `beta` to sampled members:
/// the same samples wherever the same types are tested.
fn envs<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    beta: &[Ty],
) -> Vec<Vec<L::Value>> {
    let samples: Vec<Vec<L::Value>> = beta.iter().map(|t| sem.samples(oracle, t)).collect();
    let refs: Vec<&[L::Value]> = samples.iter().map(|s| s.as_slice()).collect();
    let mut out = Vec::new();
    product(&refs, &mut Vec::new(), &mut |e| out.push(e.to_vec()));
    out.truncate(81);
    out
}

/// The universe types every run of open `t` gives, and those every value
/// it returns is in, its variables bound to sampled members of `beta` (and
/// to the `actual` values that flow into them, where known); `None` if a
/// run gets stuck.
fn open_types<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    t: &Term,
    beta: &[Ty],
    actual: &[Option<L::Value>],
) -> Option<(Vec<usize>, Vec<usize>)> {
    let mut envs = envs(oracle, sem, beta);
    // The values that really flow in, where the binder flow says which:
    // a premise judged on samples alone can miss them.
    if actual.iter().any(Option::is_some) {
        let first: Option<Vec<L::Value>> = actual
            .iter()
            .zip(beta)
            .map(|(a, ty)| {
                a.clone()
                    .or_else(|| sem.samples(oracle, ty).into_iter().next())
            })
            .collect();
        envs.extend(first);
    }
    let mut outcomes = Vec::new();
    for e in &envs {
        // A run that leaves a bound variable outside its type breaks the
        // premise just as getting stuck does.
        outcomes.push(run_keeping(oracle, sem, t, e, beta)?);
    }
    if outcomes.iter().any(Outcome::is_stuck) {
        return None;
    }
    let returned: Vec<L::Value> = outcomes
        .iter()
        .filter_map(|o| match o {
            Outcome::Return(v) => Some(v.clone()),
            _ => None,
        })
        .collect();
    let mut types = Vec::new();
    let mut exits = Vec::new();
    for u in 0..sem.universe.len() {
        let ty = sem.universe[u].clone();
        if ty == Ty::Top {
            continue;
        }
        // A `return` is in every type, as the node's value goes.
        if outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Return(_)) || sem.in_e(oracle, o, &ty))
        {
            types.push(u);
        }
        if returned.iter().all(|v| sem.holds(oracle, v, &ty)) {
            exits.push(u);
        }
    }
    Some((types, exits))
}

/// Ground rule instances an observation supports, a few at random.
fn instances<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    o: &Observation<L::Value>,
    con: usize,
    flow: Option<&ExitFlow>,
    rng: &mut Rng,
) -> Vec<Schema> {
    let Outcome::Value(v) = &o.outcome else {
        return Vec::new();
    };
    let arity = o.kid_types.len();
    let caught: Vec<bool> = flow.map_or(vec![false; arity], |f| f.caught.clone());
    let origin = flow.is_some_and(|f| f.origin);
    let res = match o.res_fixed {
        Some(r) => vec![r],
        None => sem.types_of(oracle, v),
    };
    let mut choices: Vec<Vec<usize>> = o
        .kid_types
        .iter()
        .zip(&o.kid_fixed)
        .map(|(k, f)| match f {
            Some(f) => vec![*f],
            None => k.clone().unwrap_or_default(),
        })
        .collect();
    choices.push(res);
    // Then the exit types that aren't the node's.
    for (k, x) in o.kid_exits.iter().enumerate() {
        if caught[k] {
            choices.push(x.clone().unwrap_or_default());
        }
    }
    if origin {
        choices.push(
            (0..sem.universe.len())
                .filter(|&u| sem.universe[u] != Ty::Top)
                .collect(),
        );
    }
    if choices.iter().any(Vec::is_empty) {
        return Vec::new();
    }
    // Equal types in several positions are a shared variable's evidence:
    // of all the instances (or many at random), keep the most coherent ones
    // (types mentioned by the most positions), and a few others.
    fn subterms(t: &Ty, out: &mut Vec<Ty>) {
        out.push(t.clone());
        if let Ty::Ref(_, ps) = t {
            ps.iter().for_each(|p| subterms(p, out));
        }
    }
    let total: usize = choices.iter().map(|c| c.len()).product();
    let picks: Vec<Vec<usize>> = if total <= 4096 {
        let refs: Vec<&[usize]> = choices.iter().map(|c| c.as_slice()).collect();
        let mut all = Vec::new();
        product(&refs, &mut Vec::new(), &mut |p| all.push(p.to_vec()));
        all
    } else {
        (0..256)
            .map(|_| choices.iter().map(|c| c[rng.below(c.len())]).collect())
            .collect()
    };
    let mut drawn: Vec<(usize, Vec<usize>)> = picks
        .into_iter()
        .map(|pick| {
            // Per type, how many positions mention it, beyond the first.
            let mut seen: HashMap<Ty, usize> = HashMap::new();
            for &p in &pick {
                let mut subs: Vec<Ty> = Vec::new();
                subterms(&sem.universe[p], &mut subs);
                subs.sort();
                subs.dedup();
                for t in subs {
                    *seen.entry(t).or_default() += 1;
                }
            }
            let score: usize = seen.values().map(|n| n - 1).sum();
            (score, pick)
        })
        .collect();
    drawn.sort_by_key(|d| std::cmp::Reverse(d.0));
    let mut out = Vec::new();
    for (k, (_, pick)) in drawn.into_iter().enumerate() {
        if k >= 4 && k % 16 != 0 {
            continue;
        }
        let u = &sem.universe;
        let mut exits = pick[arity + 1..].iter().map(|&x| u[x].clone());
        out.push(Schema {
            con,
            kids: o
                .beta
                .iter()
                .zip(&pick)
                .enumerate()
                .map(|(k, (b, &t))| Premise {
                    bound: b.iter().map(|&x| u[x].clone()).collect(),
                    ty: u[t].clone(),
                    exit: if caught[k] { exits.next() } else { None },
                })
                .collect(),
            res: u[pick[arity]].clone(),
            exit: if origin { exits.next() } else { None },
        });
    }
    out.sort();
    out.dedup();
    out
}

/// Tests a candidate against every observation: the observations it
/// covers, or the first that refutes it.
fn test<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    index: &HashMap<Ty, usize>,
    cand: &Schema,
    obs: &[Observation<L::Value>],
) -> Result<Vec<(usize, Ty)>, usize> {
    let mut covered = Vec::new();
    for (i, o) in obs.iter().enumerate() {
        let thetas = matches(cand, o, &sem.universe, index);
        if thetas.is_empty() {
            continue;
        }
        let mut preds = Vec::new();
        let mut applied = false;
        for theta in &thetas {
            // The node's exit types the premises allow: those of every
            // child whose exit is the node's, and the rule's own.
            let mut exits: Vec<usize> = (0..sem.universe.len())
                .filter(|&u| sem.universe[u] != Ty::Top)
                .collect();
            for (k, xs) in cand.kids.iter().zip(&o.kid_exits) {
                if k.exit.is_none() {
                    let xs = xs.as_deref().unwrap_or(&[]);
                    exits.retain(|u| xs.contains(u));
                }
            }
            if let Some(x) = &cand.exit {
                match index.get(&subst(x, theta)) {
                    Some(u) => exits.retain(|w| w == u),
                    None => continue,
                }
            }
            if exits.is_empty() {
                continue;
            }
            applied = true;
            match &o.outcome {
                // Wrong if any exit type allowed is wrong for it.
                Outcome::Return(v) => {
                    for u in exits {
                        let t = sem.universe[u].clone();
                        if !sem.holds(oracle, v, &t) {
                            return Err(i);
                        }
                    }
                    continue;
                }
                _ => {}
            }
            let p = subst(&cand.res, theta);
            if !sem.in_e(oracle, &o.outcome, &p) {
                return Err(i);
            }
            preds.push(p);
        }
        if !applied {
            continue;
        }
        if matches!(o.outcome, Outcome::Return(_)) {
            covered.push((i, Ty::Top));
            continue;
        }
        if matches!(o.outcome, Outcome::Value(_)) {
            // The most specific type the rule gives the node.
            let best = preds
                .iter()
                .find(|p| preds.iter().all(|q| *p == q || below(sem, p, q)))
                .unwrap_or(&preds[0])
                .clone();
            covered.push((i, best));
        }
    }
    Ok(covered)
}

/// Whether ground `a` is a strict subtype of `b`.
fn below<V>(sem: &Semantics<V>, a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Base(x), Ty::Base(y)) => x != y && sem.subtyping && sem.le[*x][*y],
        _ => false,
    }
}

/// The ways the candidate's premises match an observation.
fn matches<V>(
    cand: &Schema,
    o: &Observation<V>,
    universe: &[Ty],
    index: &HashMap<Ty, usize>,
) -> Vec<HashMap<u32, Ty>> {
    let mut theta = HashMap::new();
    for (k, b) in cand.kids.iter().zip(&o.beta) {
        for (p, &u) in k.bound.iter().zip(b) {
            if !match_ground(p, &universe[u], &mut theta) {
                return Vec::new();
            }
        }
    }
    let mut thetas = vec![theta];
    // Each child's type, and its exit type where the rule gives one.
    let pats = cand
        .kids
        .iter()
        .zip(&o.kid_types)
        .map(|(k, ts)| (&k.ty, ts))
        .chain(
            cand.kids
                .iter()
                .zip(&o.kid_exits)
                .filter_map(|(k, xs)| k.exit.as_ref().map(|x| (x, xs))),
        );
    for (pat, ts) in pats {
        let Some(ts) = ts else {
            return Vec::new();
        };
        let mut next = Vec::new();
        for th in thetas {
            let p = subst(pat, &th);
            if p.is_ground() {
                if index.get(&p).is_some_and(|u| ts.contains(u)) {
                    next.push(th);
                }
                continue;
            }
            for &u in ts {
                let mut t2 = th.clone();
                if match_ground(&p, &universe[u], &mut t2) {
                    next.push(t2);
                }
                if next.len() > 32 {
                    break;
                }
            }
        }
        thetas = next;
        if thetas.is_empty() {
            break;
        }
    }
    thetas
}

/// Attacks a rule's compatibility lemma: for instantiations of its
/// variables, children that meet its premises (closed ones sampled from
/// the whole pool of values, open ones from the open terms), and the node
/// run. A description of the first node that breaks the rule.
pub fn falsify<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    pools: &Pools,
    rule: &Schema,
    examples: &[Term],
    fixed: &HashMap<u32, Ty>,
    cfg: &SearchConfig,
    rng: &mut Rng,
) -> Option<String> {
    let sig = oracle.lang.signature();
    let c = sig[rule.con].clone();
    let var = var_con(sig);
    // The variables to instantiate: all but those `fixed` says.
    let vars: Vec<u32> = rule
        .vars()
        .into_iter()
        .filter(|v| !fixed.contains_key(v))
        .collect();
    let u = sem.universe.clone();
    let all: usize = u.len().saturating_pow(vars.len() as u32);
    // Every instantiation with the unrefined sorts first (cheap, and where
    // most wrong rules break), then random ones from the whole universe.
    let bases: Vec<Ty> = u
        .iter()
        .filter(|t| matches!(t, Ty::Base(_)))
        .cloned()
        .collect();
    let mut thetas: Vec<HashMap<u32, Ty>> = Vec::new();
    let n_base = bases.len().saturating_pow(vars.len() as u32);
    for k in 0..n_base.min(cfg.attacks) {
        thetas.push(
            vars.iter()
                .enumerate()
                .map(|(j, &v)| {
                    (
                        v,
                        bases[(k / bases.len().pow(j as u32)) % bases.len()].clone(),
                    )
                })
                .collect(),
        );
    }
    let more = if all <= cfg.attacks { all } else { cfg.attacks };
    for _ in 0..more.saturating_sub(thetas.len()).max(cfg.attacks / 3) {
        thetas.push(
            vars.iter()
                .map(|&v| (v, u[rng.below(u.len())].clone()))
                .collect(),
        );
    }
    for theta in thetas.iter_mut() {
        theta.extend(fixed.iter().map(|(v, t)| (*v, t.clone())));
    }
    let returns = pools
        .faults
        .iter()
        .any(|t| matches!(oracle.eval(t), Outcome::Return(_)));
    for theta in thetas {
        // The node's exit type: the rule's, or any.
        let node_exit = match &rule.exit {
            Some(x) => subst(x, &theta),
            None if bases.is_empty() || !returns => Ty::Never,
            None => bases[rng.below(bases.len())].clone(),
        };
        let mut choices: Vec<Vec<Child<L::Value>>> = Vec::new();
        for (k, prem) in rule.kids.iter().enumerate() {
            let want = subst(&prem.ty, &theta);
            let exit = prem
                .exit
                .as_ref()
                .map_or(node_exit.clone(), |x| subst(x, &theta));
            if c.binds[k] == 0 {
                // A closed child is a variable bound, in the environment, to
                // a member of its type (numbered below); or a computation
                // that faults, which is in every type, or that returns a
                // member of its exit type.
                let vals = sem.samples(oracle, &want);
                let mut mine: Vec<Child<L::Value>> = vals
                    .into_iter()
                    .map(|v| (Term::leaf(var, Atom::Int(0)), Some(v)))
                    .collect();
                // One of each kind.
                let mut by_kind: std::collections::BTreeMap<usize, Vec<Term>> = Default::default();
                for (t, &kind) in pools.faults.iter().zip(&pools.fault_kinds) {
                    if let Outcome::Return(v) = oracle.eval(t) {
                        if !sem.holds(oracle, &v, &exit) {
                            continue;
                        }
                    }
                    by_kind.entry(kind).or_default().push(t.clone());
                }
                for ts in by_kind.values() {
                    mine.push((ts[rng.below(ts.len())].clone(), None));
                }
                choices.push(mine);
            } else {
                let beta: Vec<Ty> = prem.bound.iter().map(|b| subst(b, &theta)).collect();
                let es = envs(oracle, sem, &beta);
                let open = &pools.open[&c.binds[k]];
                let mut fit = Vec::new();
                // Uses of the bound variables first (`app2(x0, 0, 1)` for
                // a function of two parameters: open terms that small are
                // rare), then the children of nodes the rule covers, then
                // any.
                let uses = uses_of(oracle, sem, pools, &beta, rng);
                let tries: Vec<&Term> = uses
                    .iter()
                    .chain(examples.iter().map(|e| &e.kids[k]))
                    .chain((0..60).map(|_| &open[rng.below(open.len())]))
                    .collect();
                for t in tries {
                    if fit.iter().any(|(f, _)| f == t) {
                        continue;
                    }
                    // A child that only ever faults makes the node fault,
                    // which breaks no rule (one that returns may).
                    let mut ok = !es.is_empty();
                    let mut completes = false;
                    for e in &es {
                        match run_keeping(oracle, sem, t, e, &beta) {
                            Some(o) if sem.in_x(oracle, &o, &want, Some(&exit)) => {
                                completes |= matches!(o, Outcome::Value(_) | Outcome::Return(_));
                            }
                            _ => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if ok && completes {
                        fit.push((t.clone(), None));
                        if fit.len() >= 4 {
                            break;
                        }
                    }
                }
                choices.push(fit);
            }
        }
        let want = subst(&rule.res, &theta);
        let refs: Vec<&[Child<L::Value>]> = choices.iter().map(|c| c.as_slice()).collect();
        let mut nodes = Vec::new();
        product(&refs, &mut Vec::new(), &mut |kids| {
            nodes.push(kids.to_vec())
        });
        // A sample, faults and all.
        let take = 36.min(nodes.len());
        for i in 0..take {
            let j = i + rng.below(nodes.len() - i);
            nodes.swap(i, j);
        }
        for kids in nodes.into_iter().take(take) {
            // Closed children given by value are the environment's slots,
            // in order.
            let mut slot = 0;
            let terms: Vec<Term> = kids
                .iter()
                .map(|(t, v)| match v {
                    Some(_) => {
                        slot += 1;
                        Term::leaf(var, Atom::Int(slot as i64 - 1))
                    }
                    None => t.clone(),
                })
                .collect();
            let premises: Vec<Ty> = rule
                .kids
                .iter()
                .zip(&kids)
                .filter(|(_, (_, v))| v.is_some())
                .map(|(p, _)| subst(&p.ty, &theta))
                .collect();
            for atom in c.atoms_or_none() {
                // Closed children refer to the environment by slot, under
                // no binders, so unshifted. The node runs on copies it may
                // store into, which are then checked again: a rule must
                // also keep its children in their types (Kripke
                // monotonicity), or `set : (Ref<a>, b) -> b` would pass.
                let env: Vec<L::Value> = kids
                    .iter()
                    .filter_map(|(_, v)| v.as_ref().map(|v| oracle.lang.isolate(v)))
                    .collect();
                let before: Vec<L::Value> = env.iter().map(|v| oracle.lang.isolate(v)).collect();
                let node = Term {
                    con: rule.con,
                    atom,
                    kids: terms.clone(),
                };
                let o = oracle.eval_shared(&node, &env);
                let vals: Vec<String> = env.iter().map(|v| oracle.lang.show_value(v)).collect();
                if !sem.in_x(oracle, &o, &want, Some(&node_exit)) {
                    return Some(format!(
                        "{} with x0.. = [{}] gives {:?}, not a {:?}",
                        oracle.lang.show_term(&node),
                        vals.join(", "),
                        o,
                        want
                    ));
                }
                for ((v, b), p) in env.iter().zip(&before).zip(&premises) {
                    if oracle.lang.same(v, b) {
                        continue;
                    }
                    sem.forget(v);
                    if !sem.holds(oracle, v, p) {
                        return Some(format!(
                            "{} with x0.. = [{}] leaves a child no longer a {:?}",
                            oracle.lang.show_term(&node),
                            vals.join(", "),
                            p
                        ));
                    }
                }
            }
        }
    }
    None
}
