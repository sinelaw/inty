//! Which numbers are integers: a type-qualifier analysis.
//!
//! inty has one number type, as JavaScript has. This backend still
//! computes in machine integers where it can: it gives every number-typed
//! place of the program (a variable, a parameter, a function's result, an
//! array's elements, an object's field, an expression's value) a *kind*,
//! `int` or `float`, ordered `int ⊑ float`, and works out the least kinds
//! that hold (Foster, Fähndrich and Aiken, "A Theory of Type Qualifiers",
//! PLDI 1999):
//!
//! * a value flowing into a place makes the place at least its kind (an
//!   `int` stored into a `float` place is converted, never the other way);
//! * a place inside another (an array's elements, a field, a parameter of
//!   a function value) is the same place wherever the outer value flows,
//!   so the kinds there are equal;
//! * an integral literal, `.length`, `indexOf`, the bitwise operators and
//!   `Math.floor` and its kind give `int`; `+ - * %` give the larger of
//!   their operands' kinds; `/`, `**` and fractional literals give `float`.
//!
//! The analysis can't reject a program: `float` everywhere is always a
//! solution. A value whose kind nothing gives (`NaN`, say) is a `float`,
//! and so is a place nothing ever stores a number into.
//! An `int` computes as a Go `int`, which agrees with JavaScript's double
//! up to 2^53 in magnitude; past that the runtime's checked operations
//! stop the program (see `runtime.go`).

/// A kind, ordered `Unknown < Int < Float`. What is still `Unknown` once
/// everything has flowed (nothing flows into it) is `Float`, and flows on
/// as one.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Unknown,
    Int,
    Float,
}

/// Kind variables with their constraints: union-find for equalities,
/// lower bounds for what flows in, and `a ⊑ b` edges.
#[derive(Default, Clone)]
pub struct Kinds {
    parent: Vec<u32>,
    lower: Vec<Kind>,
    edges: Vec<(u32, u32)>,
    /// Places some use needs as integers (see [`Kinds::demand`]).
    demanded: Vec<u32>,
    /// Places compared with each other: one needs integers if the other
    /// does.
    links: Vec<(u32, u32)>,
    /// Functions' parameters: floats unless needed as integers.
    params: Vec<u32>,
    solved: Vec<Kind>,
}

impl Kinds {
    pub fn fresh(&mut self) -> u32 {
        let v = self.parent.len() as u32;
        self.parent.push(v);
        self.lower.push(Kind::Unknown);
        v
    }

    pub fn find(&mut self, v: u32) -> u32 {
        let mut r = v;
        while self.parent[r as usize] != r {
            r = self.parent[r as usize];
        }
        let mut c = v;
        while self.parent[c as usize] != r {
            let next = self.parent[c as usize];
            self.parent[c as usize] = r;
            c = next;
        }
        r
    }

    /// `a` and `b` are one place.
    pub fn union(&mut self, a: u32, b: u32) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb as usize] = ra;
            let k = self.lower[rb as usize];
            self.raise(ra, k);
        }
    }

    /// A value of kind `k` flows into `v`.
    pub fn raise(&mut self, v: u32, k: Kind) {
        let r = self.find(v) as usize;
        if k > self.lower[r] {
            self.lower[r] = k;
        }
    }

    /// `a`'s value flows into `b`: `a ⊑ b`.
    pub fn edge(&mut self, a: u32, b: u32) {
        self.edges.push((a, b));
    }

    /// A use needs `v` as an integer to gain from it: an index, a bitwise
    /// operand, `%`, a store into an integer typed array.
    pub fn demand(&mut self, v: u32) {
        self.demanded.push(v);
    }

    /// `a` and `b` are compared.
    pub fn link(&mut self, a: u32, b: u32) {
        self.links.push((a, b));
    }

    /// `v` is a function's parameter.
    pub fn param(&mut self, v: u32) {
        self.params.push(v);
    }

    /// The least kinds: each place's lower bound, raised along the edges
    /// until nothing changes.
    pub fn solve(&mut self) {
        let n = self.parent.len();
        let mut kind: Vec<Kind> = (0..n as u32)
            .map(|v| {
                let r = self.find(v);
                self.lower[r as usize]
            })
            .collect();
        let edges: Vec<(usize, usize)> = self
            .edges
            .clone()
            .into_iter()
            .map(|(a, b)| (self.find(a) as usize, self.find(b) as usize))
            .collect();
        let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &(a, b) in &edges {
            out[a].push(b);
        }
        let propagate = |kind: &mut Vec<Kind>, mut work: Vec<usize>| {
            while let Some(a) = work.pop() {
                let k = kind[a];
                for &b in &out[a] {
                    if k > kind[b] {
                        kind[b] = k;
                        work.push(b);
                    }
                }
            }
        };
        let roots: Vec<usize> = (0..n).filter(|&v| self.parent[v] as usize == v).collect();
        propagate(&mut kind, roots.clone());
        // What nothing flows into, not even transitively, is a value of no
        // known kind (`NaN`, a built-in's number): a float, which flows on.
        let unknown: Vec<usize> = roots
            .into_iter()
            .filter(|&v| kind[v] == Kind::Unknown)
            .collect();
        for &v in &unknown {
            kind[v] = Kind::Float;
        }
        propagate(&mut kind, unknown);
        // Which integers some use needs: the demanded places, what flows
        // into them, and what is compared with them.
        let mut needed = vec![false; n];
        let mut back: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &(a, b) in &edges {
            back[b].push(a);
        }
        let links: Vec<(usize, usize)> = self
            .links
            .clone()
            .into_iter()
            .map(|(a, b)| (self.find(a) as usize, self.find(b) as usize))
            .collect();
        for &(a, b) in &links {
            back[a].push(b);
            back[b].push(a);
        }
        let mut work: Vec<usize> = Vec::new();
        for v in self.demanded.clone() {
            let r = self.find(v) as usize;
            if !needed[r] {
                needed[r] = true;
                work.push(r);
            }
        }
        while let Some(b) = work.pop() {
            for &a in &back[b] {
                if !needed[a] {
                    needed[a] = true;
                    work.push(a);
                }
            }
        }
        let mut back_edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &(a, b) in &edges {
            back_edges[b].push(a);
        }
        let params: Vec<usize> = self
            .params
            .clone()
            .into_iter()
            .map(|v| self.find(v) as usize)
            .collect();
        // A parameter no use needs as an integer, whose value ends up in a
        // float anyway, is a float (an integer argument converted where it
        // is passed), and so is what it flows into, which no use needs
        // either: a formula on integer arguments computed in floats rather
        // than in checked integer operations whose results are converted.
        // (Once one is, another may meet it: until none changes.)
        loop {
            // Which places' values end up in a float place.
            let mut to_float = vec![false; n];
            let mut work: Vec<usize> = (0..n).filter(|&v| kind[v] == Kind::Float).collect();
            for &v in &work {
                to_float[v] = true;
            }
            while let Some(b) = work.pop() {
                for &a in &back_edges[b] {
                    if !to_float[a] {
                        to_float[a] = true;
                        work.push(a);
                    }
                }
            }
            let mut floats = Vec::new();
            for &r in &params {
                if kind[r] == Kind::Int && !needed[r] && to_float[r] {
                    kind[r] = Kind::Float;
                    floats.push(r);
                }
            }
            if floats.is_empty() {
                break;
            }
            propagate(&mut kind, floats);
        }
        self.solved = (0..n as u32)
            .map(|v| {
                let r = self.find(v) as usize;
                kind[r]
            })
            .collect();
    }

    /// Whether `v` is an `int` in the solution.
    pub fn is_int(&self, v: u32) -> bool {
        self.solved.get(v as usize) == Some(&Kind::Int)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kinds_are_least_and_flow_one_way() {
        let mut k = Kinds::default();
        let (i, f, x, y) = (k.fresh(), k.fresh(), k.fresh(), k.fresh());
        k.raise(i, Kind::Int);
        k.raise(f, Kind::Float);
        k.edge(i, x);
        k.edge(f, y);
        k.edge(x, y);
        k.solve();
        assert!(k.is_int(i) && k.is_int(x));
        assert!(!k.is_int(f) && !k.is_int(y));
    }

    #[test]
    fn a_parameter_is_an_integer_only_where_a_use_needs_one() {
        let mut k = Kinds::default();
        // `f(i)` with an integer `i`: `p` only feeds `r`, which meets a
        // float in `s`; `q` is an index; `o` is only passed on, in `t`.
        let (i, p, r, s, q, o, t) = (
            k.fresh(),
            k.fresh(),
            k.fresh(),
            k.fresh(),
            k.fresh(),
            k.fresh(),
            k.fresh(),
        );
        k.raise(i, Kind::Int);
        k.raise(s, Kind::Float);
        k.edge(i, p);
        k.edge(p, r);
        k.edge(r, s);
        k.edge(i, q);
        k.edge(i, o);
        k.edge(o, t);
        k.param(p);
        k.param(q);
        k.param(o);
        k.demand(q);
        k.solve();
        assert!(!k.is_int(p) && !k.is_int(r));
        assert!(k.is_int(q) && k.is_int(i));
        assert!(k.is_int(o) && k.is_int(t));
    }

    #[test]
    fn equal_places_share_a_kind_and_unknown_is_float() {
        let mut k = Kinds::default();
        let (a, b, c) = (k.fresh(), k.fresh(), k.fresh());
        k.raise(a, Kind::Int);
        k.union(a, b);
        k.raise(b, Kind::Float);
        k.solve();
        assert!(!k.is_int(a));
        assert!(!k.is_int(c));
    }
}
