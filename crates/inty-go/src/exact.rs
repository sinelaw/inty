//! Divisions known to be exact: `a / b` where the program has just
//! tested that `a % b === 0`.
//!
//! `/` gives a fraction in general, so its result is a float (`kinds`).
//! But in
//!
//! ```js
//! if (n % 2 === 0) { n = n / 2; } else { n = 3 * n + 1; }
//! ```
//!
//! the quotient is whole: of two integers (as the kinds have them), the
//! one divisible by the other gives an integer, which a double holds
//! exactly. So such a division is integer arithmetic, an integer from
//! integers, as `+` is. That is path-sensitive: it holds in the branch
//! the test guards, and only while neither `a` nor `b` can have changed.
//! So a division counts as exact here if
//!
//! - it is `a / b` with `a` a name and `b` a positive number, the same
//!   as in the test (`a % b === 0`, `a % b == 0`, `0 === a % b` or
//!   `!(a % b)`, guarding the branch taken when it holds; `!==` / `!=`
//!   guarding the other). A positive number, because `0 / -2` is `-0` in
//!   JavaScript, which an integer can't be, and with `b` zero `!(a % b)`
//!   holds (`a % 0` is `NaN`) though `a / 0` is no integer: a name could
//!   be either;
//! - it is in the guarded branch, not in a function defined there (which
//!   may run later);
//! - nothing that may change `a` runs between the test and it: no
//!   assignment to or update of it, no declaration of its name,
//!   no call (which may assign them, if a closure captures them) before
//!   it in the branch, and none at all in a loop in the branch that
//!   holds it (the next iteration would run it first).
//!
//! It is a conservative, syntactic check: what it misses stays a float.

use std::collections::HashSet;

use inty::ast::*;
use inty::span::Span;

/// The spans of the exact divisions of `program`.
pub fn exact_divisions(program: &Program) -> HashSet<(usize, usize)> {
    let mut out = HashSet::new();
    for s in &program.statements {
        find_stmt(s, &mut out);
    }
    out
}

/// What a test guards: the divisor, the dividend's name, and
/// whether it holds in the branch taken when the test is true.
struct Guard {
    dividend: String,
    divisor: Divisor,
    when_true: bool,
}

/// A divisor: a positive number, by its bits. (A negative one, or a
/// name that may hold one, could make `0 / b` JavaScript's `-0`, which an
/// integer isn't; zero makes no quotient at all.)
#[derive(PartialEq)]
struct Divisor(u64);

fn divisor_of(e: &Expr) -> Option<Divisor> {
    match e {
        Expr::Lit {
            value: Literal::Number(n),
            ..
        } if *n > 0.0 => Some(Divisor(n.to_bits())),
        _ => None,
    }
}

/// `a % b`, as a guard's dividend and divisor.
fn remainder(e: &Expr) -> Option<(String, Divisor)> {
    match e {
        Expr::Binary {
            op: BinOp::Mod,
            left,
            right,
            ..
        } => match &**left {
            Expr::Ident { name, .. } => Some((name.clone(), divisor_of(right)?)),
            _ => None,
        },
        _ => None,
    }
}

fn is_zero(e: &Expr) -> bool {
    matches!(e, Expr::Lit { value: Literal::Number(n), .. } if *n == 0.0)
}

fn guard_of(test: &Expr) -> Option<Guard> {
    match test {
        Expr::Binary {
            op: op @ (BinOp::EqEqEq | BinOp::EqEq | BinOp::NotEqEq | BinOp::NotEq),
            left,
            right,
            ..
        } => {
            let (rem, zero) = if is_zero(right) {
                (left, right)
            } else {
                (right, left)
            };
            if !is_zero(zero) {
                return None;
            }
            let (dividend, divisor) = remainder(rem)?;
            Some(Guard {
                dividend,
                divisor,
                when_true: matches!(op, BinOp::EqEqEq | BinOp::EqEq),
            })
        }
        Expr::Unary {
            op: UnaryOp::Not,
            argument,
            ..
        } => {
            let (dividend, divisor) = remainder(argument)?;
            Some(Guard {
                dividend,
                divisor,
                when_true: true,
            })
        }
        _ => None,
    }
}

// ---- finding the guards -----------------------------------------------------

fn find_stmt(s: &Stmt, out: &mut HashSet<(usize, usize)>) {
    if let Stmt::If {
        test,
        consequent,
        alternate,
        ..
    } = s
    {
        if let Some(g) = guard_of(test) {
            let branch = if g.when_true {
                Some(&**consequent)
            } else {
                alternate.as_deref()
            };
            if let Some(b) = branch {
                let mut r = Region::new(&g);
                r.stmt(b);
                r.finish(out);
            }
        }
    }
    each_child(s, &mut |n| match n {
        Node::Stmt(s) => find_stmt(s, out),
        Node::Expr(e) => find_expr(e, out),
    });
}

fn find_expr(e: &Expr, out: &mut HashSet<(usize, usize)>) {
    if let Expr::Conditional {
        test,
        consequent,
        alternate,
        ..
    } = e
    {
        if let Some(g) = guard_of(test) {
            let branch = if g.when_true { consequent } else { alternate };
            let mut r = Region::new(&g);
            r.expr(branch);
            r.finish(out);
        }
    }
    each_child_expr(e, &mut |n| match n {
        Node::Stmt(s) => find_stmt(s, out),
        Node::Expr(e) => find_expr(e, out),
    });
}

// ---- a guarded branch -------------------------------------------------------

/// The guarded branch: its candidate divisions and what may change the
/// guard's names, each with the outermost loop of the branch around it.
struct Region<'g> {
    guard: &'g Guard,
    divisions: Vec<(Span, Option<Span>)>,
    effects: Vec<(Span, Option<Span>)>,
    /// The outermost loop of the branch being walked.
    in_loop: Option<Span>,
}

impl<'g> Region<'g> {
    fn new(guard: &'g Guard) -> Self {
        Region {
            guard,
            divisions: Vec::new(),
            effects: Vec::new(),
            in_loop: None,
        }
    }

    fn names(&self, name: &str) -> bool {
        name == self.guard.dividend
    }

    fn effect(&mut self, span: Span) {
        self.effects.push((span, self.in_loop));
    }

    fn finish(self, out: &mut HashSet<(usize, usize)>) {
        for (d, lp) in &self.divisions {
            let clear = self.effects.iter().all(|(e, _)| {
                // Not one that runs before it: ending before it starts, or
                // anywhere in a loop around it.
                let before = e.end <= d.start;
                let in_its_loop = lp.is_some_and(|l| l.start <= e.start && e.end <= l.end);
                !before && !in_its_loop
            });
            if clear {
                out.insert((d.start, d.end));
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::While { .. }
            | Stmt::DoWhile { .. }
            | Stmt::For { .. }
            | Stmt::ForIn { .. }
            | Stmt::ForOf { .. }
                if self.in_loop.is_none() =>
            {
                self.in_loop = Some(s.span());
                self.children(s);
                self.in_loop = None;
                return;
            }
            Stmt::Var { declarations, .. } => {
                for d in declarations {
                    if self.names(&d.name) {
                        self.effect(d.span);
                    }
                }
            }
            Stmt::ForIn { left, .. } | Stmt::ForOf { left, .. } => match left {
                ForInLhs::VarDecl(name, _, span, _) if self.names(name) => self.effect(*span),
                ForInLhs::Expr(Expr::Ident { name, span }) if self.names(name) => {
                    self.effect(*span)
                }
                _ => {}
            },
            Stmt::Try {
                handler: Some(h), ..
            } if self.names(&h.param) => self.effect(s.span()),
            // A function declared here is hoisted to the branch's start:
            // its name shadows from there on. (Its body runs only when
            // called, which is an effect of its own.)
            Stmt::FunctionDecl { name, .. } if self.names(name) => self.effect(s.span()),
            Stmt::FunctionDecl { .. } => return,
            Stmt::Import { .. } | Stmt::Export { .. } => self.effect(s.span()),
            _ => {}
        }
        self.children(s);
    }

    fn children(&mut self, s: &Stmt) {
        each_child(s, &mut |n| match n {
            Node::Stmt(s) => self.stmt(s),
            Node::Expr(e) => self.expr(e),
        });
    }

    fn expr(&mut self, e: &Expr) {
        match e {
            // Not run here.
            Expr::Function { .. } => return,
            Expr::Binary {
                op: BinOp::Div,
                left,
                right,
                span,
            } => {
                if let (Expr::Ident { name, .. }, Some(d)) = (&**left, divisor_of(right)) {
                    if *name == self.guard.dividend && d == self.guard.divisor {
                        self.divisions.push((*span, self.in_loop));
                    }
                }
            }
            Expr::Assign { left, span, .. } => {
                if !matches!(&**left, Expr::Ident { name, .. } if !self.names(name)) {
                    // An assignment to the guard's names, or to a place
                    // (a store through a setter-less object can't change a
                    // variable, but its object expression may call).
                    if matches!(&**left, Expr::Ident { .. }) {
                        self.effect(*span);
                    }
                }
            }
            Expr::Unary {
                op: UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec,
                argument,
                span,
            } => {
                if matches!(&**argument, Expr::Ident { name, .. } if self.names(name)) {
                    self.effect(*span);
                }
            }
            Expr::Call { span, .. }
            | Expr::New { span, .. }
            | Expr::OptionalChain { span, .. }
            | Expr::Unary {
                op: UnaryOp::Delete | UnaryOp::Await,
                span,
                ..
            } => self.effect(*span),
            // A getter read may run code; a member read can't be told
            // apart from one here, so it is one too.
            Expr::Member { span, .. } | Expr::ComputedMember { span, .. } => self.effect(*span),
            _ => {}
        }
        each_child_expr(e, &mut |n| match n {
            Node::Stmt(s) => self.stmt(s),
            Node::Expr(e) => self.expr(e),
        });
    }
}

// ---- children -----------------------------------------------------------------

enum Node<'a> {
    Stmt(&'a Stmt),
    Expr(&'a Expr),
}

fn each_child<'a>(s: &'a Stmt, f: &mut dyn FnMut(Node<'a>)) {
    match s {
        Stmt::Block { body, .. } => body.iter().for_each(|s| f(Node::Stmt(s))),
        Stmt::Empty { .. }
        | Stmt::Break { .. }
        | Stmt::Continue { .. }
        | Stmt::Import { .. }
        | Stmt::Export { .. } => {}
        Stmt::Expr { expression, .. } => f(Node::Expr(expression)),
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                if let Some(e) = &d.init {
                    f(Node::Expr(e));
                }
            }
        }
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            f(Node::Expr(test));
            f(Node::Stmt(consequent));
            if let Some(a) = alternate {
                f(Node::Stmt(a));
            }
        }
        Stmt::While { test, body, .. } => {
            f(Node::Expr(test));
            f(Node::Stmt(body));
        }
        Stmt::DoWhile { body, test, .. } => {
            f(Node::Stmt(body));
            f(Node::Expr(test));
        }
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            match init {
                Some(ForInit::VarDecl(ds)) => {
                    for d in ds {
                        if let Some(e) = &d.init {
                            f(Node::Expr(e));
                        }
                    }
                }
                Some(ForInit::Expr(e)) => f(Node::Expr(e)),
                None => {}
            }
            if let Some(t) = test {
                f(Node::Expr(t));
            }
            f(Node::Stmt(body));
            if let Some(u) = update {
                f(Node::Expr(u));
            }
        }
        Stmt::ForIn {
            left, right, body, ..
        }
        | Stmt::ForOf {
            left, right, body, ..
        } => {
            f(Node::Expr(right));
            if let ForInLhs::Expr(t) = left {
                f(Node::Expr(t));
            }
            f(Node::Stmt(body));
        }
        Stmt::Return { argument, .. } => {
            if let Some(e) = argument {
                f(Node::Expr(e));
            }
        }
        Stmt::Throw { argument, .. } => f(Node::Expr(argument)),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            f(Node::Stmt(block));
            if let Some(h) = handler {
                f(Node::Stmt(&h.body));
            }
            if let Some(fin) = finalizer {
                f(Node::Stmt(fin));
            }
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            f(Node::Expr(discriminant));
            for c in cases {
                if let Some(t) = &c.test {
                    f(Node::Expr(t));
                }
                c.consequent.iter().for_each(|s| f(Node::Stmt(s)));
            }
        }
        Stmt::Labeled { body, .. } => f(Node::Stmt(body)),
        Stmt::FunctionDecl { body, .. } => f(Node::Stmt(body)),
    }
}

fn each_child_expr<'a>(e: &'a Expr, f: &mut dyn FnMut(Node<'a>)) {
    match e {
        Expr::Lit { .. } | Expr::This { .. } | Expr::NewTarget { .. } | Expr::Ident { .. } => {}
        Expr::Array { elements, .. } => elements.iter().flatten().for_each(|x| f(Node::Expr(x))),
        Expr::Tuple { elements, .. } => elements.iter().for_each(|x| f(Node::Expr(x))),
        Expr::Object { properties, .. } => {
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => f(Node::Expr(value)),
                    PropDef::Spread { argument, .. } => f(Node::Expr(argument)),
                    PropDef::Getter { body, .. }
                    | PropDef::Setter { body, .. }
                    | PropDef::Method { body, .. } => f(Node::Stmt(body)),
                }
            }
        }
        Expr::Function { body, .. } => f(Node::Stmt(body)),
        Expr::New {
            callee, arguments, ..
        } => {
            f(Node::Expr(callee));
            arguments.iter().for_each(|a| f(Node::Expr(a)));
        }
        Expr::Member { object, .. } => f(Node::Expr(object)),
        Expr::ComputedMember {
            object, property, ..
        } => {
            f(Node::Expr(object));
            f(Node::Expr(property));
        }
        Expr::Call {
            callee,
            arguments,
            keywords,
            ..
        } => {
            f(Node::Expr(callee));
            arguments.iter().for_each(|a| f(Node::Expr(a)));
            keywords.iter().for_each(|(_, a)| f(Node::Expr(a)));
        }
        Expr::Unary { argument, .. } => f(Node::Expr(argument)),
        Expr::Binary { left, right, .. } | Expr::NullishCoalesce { left, right, .. } => {
            f(Node::Expr(left));
            f(Node::Expr(right));
        }
        Expr::Assign { left, right, .. } => {
            f(Node::Expr(left));
            f(Node::Expr(right));
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            f(Node::Expr(test));
            f(Node::Expr(consequent));
            f(Node::Expr(alternate));
        }
        Expr::OptionalChain { head, segments, .. } => {
            f(Node::Expr(head));
            for s in segments {
                match s {
                    ChainSegment::Member { .. } => {}
                    ChainSegment::Computed { property, .. } => f(Node::Expr(property)),
                    ChainSegment::Call { arguments, .. } => {
                        arguments.iter().for_each(|a| f(Node::Expr(a)))
                    }
                }
            }
        }
        Expr::Spread { argument, .. } => f(Node::Expr(argument)),
        Expr::RestArray { source, .. } | Expr::RestRow { source, .. } => f(Node::Expr(source)),
        Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
            expressions.iter().for_each(|x| f(Node::Expr(x)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exact(src: &str) -> usize {
        let p = inty::frontends::javascript::parse_source(src).unwrap();
        exact_divisions(&p).len()
    }

    #[test]
    fn a_division_the_test_guards_is_exact() {
        assert_eq!(exact("if (n % 2 === 0) { n = n / 2; }"), 1);
        assert_eq!(exact("const h = n % 4 === 0 ? n / 4 : 0;"), 1);
        assert_eq!(exact("if (n % 2 !== 0) { x = 1; } else { x = n / 2; }"), 1);
        assert_eq!(exact("if (!(n % 3)) { x = n / 3; }"), 1);
        // A divisor that may be zero (`!(n % 0)` holds) or negative
        // (`0 / -2` is `-0`).
        assert_eq!(exact("if (!(n % k)) { x = n / k; }"), 0);
        assert_eq!(exact("if (n % k === 0) { x = n / k; }"), 0);
        assert_eq!(exact("if (n % -2 === 0) { x = n / -2; }"), 0);
    }

    #[test]
    fn a_change_before_it_or_another_division_isnt() {
        // The other branch, another divisor, a change first.
        assert_eq!(exact("if (n % 2 === 0) { } else { x = n / 2; }"), 0);
        assert_eq!(exact("if (n % 2 === 0) { x = n / 3; }"), 0);
        assert_eq!(exact("if (n % 2 === 0) { n++; x = n / 2; }"), 0);
        assert_eq!(exact("if (n % 2 === 0) { f(); x = n / 2; }"), 0);
        assert_eq!(exact("if (n % 2 === 0) { let n = 3; x = n / 2; }"), 0);
        // In a loop that changes it, or in a function that runs later.
        assert_eq!(
            exact("if (n % 2 === 0) { while (c) { x = n / 2; n = 3; } }"),
            0
        );
        assert_eq!(exact("if (n % 2 === 0) { g = () => n / 2; }"), 0);
        // After it, the assignment holding it: fine.
        assert_eq!(exact("if (n % 2 === 0) { n = n / 2; n = n + 1; }"), 1);
    }
}
