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
    /// Selection stops when no rule gains this share of all the weight
    /// the candidates can cover.
    pub min_gain: f64,
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
            min_gain: 0.1,
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

pub struct Observation<V> {
    pub node: Term,
    pub outcome: Outcome<V>,
    /// Per child, the universe indices of its bound variables' types.
    pub beta: Vec<Vec<usize>>,
    /// Per child, the universe indices of the types it has; `None` if a
    /// run of it got stuck.
    pub kid_types: Vec<Option<Vec<usize>>>,
    /// Types the binder flow fixed: per child, and for the node.
    pub kid_fixed: Vec<Option<usize>>,
    pub res_fixed: Option<usize>,
}

pub struct ConSearch {
    pub con: usize,
    pub sources: Vec<Vec<Source>>,
    pub observations: usize,
    pub candidates: usize,
    pub refuted: usize,
    /// Candidates the greedy cover picked but `falsify` refuted.
    pub falsified: usize,
    pub chosen: Vec<Schema>,
    /// The most general refuted candidate, and why.
    pub best_refuted: Option<(Schema, String)>,
}

/// The pools children are drawn from.
pub struct Pools {
    /// Small closed terms covering the universe's types.
    pub reps: Vec<Term>,
    /// Open terms by how many variables they may use.
    pub open: HashMap<usize, Vec<Term>>,
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
    let obs = observe(oracle, sem, pools, con, &sources, cfg, rng);
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
        ground.extend(instances(oracle, sem, &obs[i], con, rng));
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
    candidates.extend(simple_rules(oracle.lang.signature(), sem, con, &sources));
    candidates.retain(|r| faithful(sem, r));
    lap(&format!("proposed {}", candidates.len()));
    // Refute by observation.
    let mut s = ConSearch {
        con,
        sources,
        observations: obs.len(),
        candidates: candidates.len(),
        refuted: 0,
        falsified: 0,
        chosen: Vec::new(),
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
    let coverable: f64 = {
        let mut any = vec![false; obs.len()];
        for (_, c) in &sound {
            for (i, _) in c {
                any[*i] = true;
            }
        }
        (0..obs.len()).filter(|&i| any[i]).map(|i| weight[i]).sum()
    };
    loop {
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
        let max = gains.iter().cloned().fold(0.0, f64::max);
        if max <= 1e-9 || max < cfg.min_gain * coverable {
            break;
        }
        let at = (0..sound.len())
            .filter(|&i| gains[i] >= cfg.substantial * max && gains[i] >= cfg.min_gain * coverable)
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
        if let Some(why) = falsify(oracle, sem, pools, &best, cfg, rng) {
            if std::env::var_os("TYSEARCH_TRACE").is_some() {
                eprintln!("    falsified {:?}: {why}", best);
            }
            s.falsified += 1;
            refuted.push((best, why));
            continue;
        }
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
    lap("selected");
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
) -> Vec<Schema> {
    let c = &sig[con];
    let positions = c.arity + 1;
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
                    // Parameters: variables, old or new, in order.
                    let mut params: Vec<(Vec<Ty>, u32)> = vec![(Vec::new(), next)];
                    for _ in 0..arity {
                        params = params
                            .into_iter()
                            .flat_map(|(ps, n)| {
                                (0..=n).map(move |v| {
                                    let mut ps = ps.clone();
                                    ps.push(Ty::Var(v));
                                    (ps, n.max(v + 1))
                                })
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
    for tys in tuples {
        let (res, kid_tys) = tys.split_last().unwrap();
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
                        Source::Unknown => {
                            fresh += 1;
                            Ty::Var(fresh - 1)
                        }
                    })
                    .collect(),
                ty: ty.clone(),
            })
            .collect();
        let r = Schema {
            con,
            kids,
            res: res.clone(),
        };
        if ok && r.res_bound() {
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
            Ty::Var(v) => Ty::Var(*v),
            Ty::Ref(s, ps) => Ty::Ref(*s, ps.iter().map(blank).collect()),
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
            })
            .collect(),
        res: blank(&s.res),
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
fn var_con(sig: &[crate::lang::Con]) -> usize {
    sig.iter().position(|c| c.kind == Kind::Var).unwrap()
}

/// Where each bound variable's value comes from, found by making the child
/// the variable itself.
fn binder_sources<L: Language>(
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
                let mut fits = Vec::new();
                for (k, &bk) in c.binds.iter().enumerate() {
                    if bk == 0 && k != i && oracle.eval(&node.kids[k]) == Outcome::Value(v.clone())
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
                        if r == v {
                            fits.push(Source::Node);
                        }
                        for (m, a) in args.iter().enumerate() {
                            if *a == r && args.iter().filter(|x| *x == a).count() == 1 {
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
    let kid_pools: Vec<&[Term]> = c
        .binds
        .iter()
        .map(|b| {
            if *b == 0 {
                pools.reps.as_slice()
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
            m.into_iter().filter(|v| !v.is_empty()).collect()
        };
        let atoms = c.atoms_or_none();
        let mut seen = std::collections::HashSet::new();
        for _ in 0..cfg.nodes * 3 {
            let kids = c
                .binds
                .iter()
                .zip(&kid_pools)
                .map(|(&b, p)| {
                    if b == 0 && !by_sort.is_empty() {
                        let s = &by_sort[rng.below(by_sort.len())];
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
            }
            if nodes.len() >= cfg.nodes {
                break;
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
        for (k, b) in node.kids.iter().zip(&c.binds) {
            closed.push(if *b == 0 {
                match oracle.eval(k) {
                    Outcome::Value(v) => Some(sem.types_of(oracle, &v)),
                    Outcome::Fault(_) | Outcome::Timeout => Some((0..n_u).collect()),
                    Outcome::Stuck { .. } => None,
                }
            } else {
                None
            });
        }
        if flat.is_empty() {
            out.push(Observation {
                node,
                outcome,
                beta: vec![Vec::new(); c.arity],
                kid_types: closed,
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
                    Source::Unknown => Some(rng.below(n_u)),
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
            let mut at = 0;
            for (i, b) in c.binds.iter().enumerate() {
                let mine: Vec<usize> = flat_beta[at..at + b].to_vec();
                at += b;
                kid_types.push(if *b == 0 {
                    closed[i].clone()
                } else {
                    let tys: Vec<Ty> = mine.iter().map(|&u| sem.universe[u].clone()).collect();
                    open_types(oracle, sem, &node.kids[i], &tys, &actual[at - b..at])
                });
                beta.push(mine);
            }
            out.push(Observation {
                node: node.clone(),
                outcome: outcome.clone(),
                beta,
                kid_types,
                kid_fixed,
                res_fixed,
            });
        }
    }
    out
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

/// The universe types every run of open `t` gives, its variables bound to
/// sampled members of `beta` (and to the `actual` values that flow into
/// them, where known); `None` if a run gets stuck.
fn open_types<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    t: &Term,
    beta: &[Ty],
    actual: &[Option<L::Value>],
) -> Option<Vec<usize>> {
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
    let outcomes: Vec<Outcome<L::Value>> = envs.iter().map(|e| oracle.eval_in(t, e)).collect();
    if outcomes.iter().any(Outcome::is_stuck) {
        return None;
    }
    Some(
        (0..sem.universe.len())
            .filter(|&u| {
                let ty = sem.universe[u].clone();
                outcomes.iter().all(|o| sem.in_e(oracle, o, &ty))
            })
            .collect(),
    )
}

/// Ground rule instances an observation supports, a few at random.
fn instances<L: Language>(
    oracle: &mut Oracle<L>,
    sem: &mut Semantics<L::Value>,
    o: &Observation<L::Value>,
    con: usize,
    rng: &mut Rng,
) -> Vec<Schema> {
    let Outcome::Value(v) = &o.outcome else {
        return Vec::new();
    };
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
        out.push(Schema {
            con,
            kids: o
                .beta
                .iter()
                .zip(&pick)
                .map(|(b, &k)| Premise {
                    bound: b.iter().map(|&x| u[x].clone()).collect(),
                    ty: u[k].clone(),
                })
                .collect(),
            res: u[*pick.last().unwrap()].clone(),
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
        for theta in &thetas {
            let p = subst(&cand.res, theta);
            if !sem.in_e(oracle, &o.outcome, &p) {
                return Err(i);
            }
            preds.push(p);
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
    for (k, ts) in cand.kids.iter().zip(&o.kid_types) {
        let Some(ts) = ts else {
            return Vec::new();
        };
        let mut next = Vec::new();
        for th in thetas {
            let p = subst(&k.ty, &th);
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
    cfg: &SearchConfig,
    rng: &mut Rng,
) -> Option<String> {
    let sig = oracle.lang.signature();
    let c = sig[rule.con].clone();
    let var = var_con(sig);
    let vars = rule.vars();
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
    for theta in thetas {
        let mut choices: Vec<Vec<Child<L::Value>>> = Vec::new();
        let mut slot = 0usize;
        for (k, prem) in rule.kids.iter().enumerate() {
            let want = subst(&prem.ty, &theta);
            if c.binds[k] == 0 {
                // A closed child is a variable bound, in the environment, to
                // a member of its type.
                let vals = sem.samples(oracle, &want);
                choices.push(
                    vals.into_iter()
                        .map(|v| (Term::leaf(var, Atom::Int(slot as i64)), Some(v)))
                        .collect(),
                );
                slot += 1;
            } else {
                let beta: Vec<Ty> = prem.bound.iter().map(|b| subst(b, &theta)).collect();
                let es = envs(oracle, sem, &beta);
                let open = &pools.open[&c.binds[k]];
                let mut fit = Vec::new();
                for _ in 0..60 {
                    let t = &open[rng.below(open.len())];
                    let ok = !es.is_empty()
                        && es.iter().all(|e| {
                            let o = oracle.eval_in(t, e);
                            sem.in_e(oracle, &o, &want)
                        });
                    if ok {
                        fit.push((t.clone(), None));
                        if fit.len() >= 3 {
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
        for kids in nodes.into_iter().take(27) {
            // Closed children refer to the environment by slot, under no
            // binders, so unshifted.
            let env: Vec<L::Value> = kids.iter().filter_map(|(_, v)| v.clone()).collect();
            let terms: Vec<Term> = kids.into_iter().map(|(t, _)| t).collect();
            for atom in c.atoms_or_none() {
                let node = Term {
                    con: rule.con,
                    atom,
                    kids: terms.clone(),
                };
                let o = oracle.eval_in(&node, &env);
                if !sem.in_e(oracle, &o, &want) {
                    let vals: Vec<String> = env.iter().map(|v| oracle.lang.show_value(v)).collect();
                    return Some(format!(
                        "{} with x0.. = [{}] gives {:?}, not a {:?}",
                        oracle.lang.show_term(&node),
                        vals.join(", "),
                        o,
                        want
                    ));
                }
            }
        }
    }
    None
}
