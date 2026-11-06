//! The order declarations are checked in (D65): by what they use, not by
//! where they are in the file.
//!
//! Each declaration has a *head* (a type's constructors, a constant's value,
//! a function's or lemma's signature) and, for functions and lemmas, a
//! *body*. A head needs the heads of the names it mentions; where it
//! mentions a function inside a type (`f~format_type ps`) or in a constant's
//! value, it needs that function's body too, since the type or value may
//! have to be computed. A body needs the heads of what it mentions. Bodies
//! never wait for bodies, so recursion is free. A head that needs itself
//! (through any chain) is an error, except among types, which may be
//! mutually recursive.

use crate::syntax::ast::{self, Block, Constraint, DeclKind, Expr, ExprKind, PatKind, Pattern, Stmt};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Node {
    Head(usize),
    Body(usize),
}

/// The checking order, as groups (a group is several mutually recursive
/// types, or one node), and the cycles that make it impossible.
pub struct Plan {
    pub groups: Vec<Vec<Node>>,
    /// Each a chain of declaration indices, first = last.
    pub cycles: Vec<Vec<usize>>,
}

pub fn plan(m: &ast::Module) -> Plan {
    // Module-level names → declaration index (constructors → their type).
    let mut names: HashMap<&str, usize> = HashMap::new();
    for (k, d) in m.decls.iter().enumerate() {
        match &d.kind {
            DeclKind::Fn { name, .. }
            | DeclKind::Lemma { name, .. }
            | DeclKind::Const { name, .. }
            | DeclKind::Alias { name, .. } => {
                names.insert(&name.name, k);
            }
            DeclKind::Enum { name, ctors, .. } => {
                names.insert(&name.name, k);
                for c in ctors {
                    names.entry(&c.name.name).or_insert(k);
                }
            }
            DeclKind::Record { name, .. } => {
                names.insert(&name.name, k);
            }
            DeclKind::Check { .. } => {}
        }
    }
    let is_type = |k: usize| matches!(m.decls[k].kind, DeclKind::Enum { .. } | DeclKind::Record { .. } | DeclKind::Alias { .. });
    let has_body = |k: usize| matches!(m.decls[k].kind, DeclKind::Fn { .. } | DeclKind::Lemma { .. });

    let mut edges: HashMap<Node, HashSet<Node>> = HashMap::new();
    let mut need = |from: Node, refs: &Refs, computed: bool| {
        let e = edges.entry(from).or_default();
        for (n, in_type) in &refs.0 {
            let Some(&k) = names.get(n.as_str()) else { continue };
            e.insert(Node::Head(k));
            if (computed || *in_type) && has_body(k) {
                e.insert(Node::Body(k));
            }
        }
    };
    for (k, d) in m.decls.iter().enumerate() {
        let mut head = Refs::default();
        let mut body = Refs::default();
        match &d.kind {
            DeclKind::Fn { params, result, constraints, decreasing, body: b, .. } => {
                let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                bound.extend(result.iter().map(|r| r.name.clone()));
                head.constraints(constraints, &bound);
                if let Some(e) = decreasing {
                    head.expr(e, &bound, false);
                }
                body.block(b, &bound);
                need(Node::Head(k), &head, false);
                need(Node::Body(k), &body, false);
            }
            DeclKind::Lemma { params, constraints, lets, ensures, proof, .. } => {
                let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                head.constraints(constraints, &bound);
                for (p, e) in lets {
                    head.expr(e, &bound, false);
                    p.binds(&mut bound);
                }
                head.expr(ensures, &bound, false);
                if let Some(b) = proof {
                    body.block(b, &bound);
                }
                need(Node::Head(k), &head, false);
                need(Node::Body(k), &body, false);
            }
            DeclKind::Const { value, .. } => {
                head.expr(value, &[], false);
                need(Node::Head(k), &head, true);
            }
            DeclKind::Enum { params, constraints, ctors, .. } => {
                let bound: Vec<String> = params.iter().map(|p| p.name.name.clone()).collect();
                head.constraints(constraints, &bound);
                for c in ctors {
                    let mut b = bound.clone();
                    b.extend(c.params.iter().map(|p| p.name.clone()));
                    head.constraints(&c.constraints, &b);
                }
                need(Node::Head(k), &head, false);
            }
            DeclKind::Record { params, constraints, fields, .. } => {
                let mut bound: Vec<String> = params.iter().map(|p| p.name.name.clone()).collect();
                head.constraints(constraints, &bound);
                for f in fields {
                    head.expr(&f.ty, &bound, true);
                    bound.push(f.name.name.clone());
                    for p in &f.preds {
                        head.expr(p, &bound, false);
                    }
                }
                need(Node::Head(k), &head, false);
            }
            DeclKind::Alias { params, constraints, .. } => {
                let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                bound.push("$subject".into());
                head.constraints(constraints, &bound);
                need(Node::Head(k), &head, false);
            }
            DeclKind::Check { .. } => {}
        }
    }
    // A body comes after its own head.
    for k in 0..m.decls.len() {
        if has_body(k) {
            edges.entry(Node::Body(k)).or_default().insert(Node::Head(k));
        }
    }

    // Nodes, in file order (so independent declarations keep it).
    let mut nodes = Vec::new();
    for (k, d) in m.decls.iter().enumerate() {
        if matches!(d.kind, DeclKind::Check { .. }) {
            continue;
        }
        nodes.push(Node::Head(k));
        if has_body(k) {
            nodes.push(Node::Body(k));
        }
    }
    let sccs = tarjan(&nodes, &edges);
    let mut plan = Plan { groups: Vec::new(), cycles: Vec::new() };
    for scc in sccs {
        let cyclic = scc.len() > 1 || edges.get(&scc[0]).is_some_and(|e| e.contains(&scc[0]));
        let all_types = scc.iter().all(|n| matches!(n, Node::Head(k) if is_type(*k)));
        if cyclic && !all_types {
            plan.cycles.push(cycle_in(&scc, &edges));
        }
        // A cycle's members aren't checked: uses of them then have no type,
        // quietly, rather than repeating the error.
        if all_types || !cyclic {
            plan.groups.push(scc);
        }
    }
    plan
}

/// A chain of declarations through an SCC, back to its start.
fn cycle_in(scc: &[Node], edges: &HashMap<Node, HashSet<Node>>) -> Vec<usize> {
    let members: HashSet<Node> = scc.iter().copied().collect();
    let start = *scc.iter().min().unwrap();
    // Breadth-first from start back to start, within the SCC.
    let mut prev: HashMap<Node, Node> = HashMap::new();
    let mut queue = std::collections::VecDeque::from([start]);
    let mut seen = HashSet::from([start]);
    let mut end = None;
    'search: while let Some(n) = queue.pop_front() {
        let mut next: Vec<Node> = edges.get(&n).map(|e| e.iter().copied().filter(|x| members.contains(x)).collect()).unwrap_or_default();
        next.sort();
        for x in next {
            // Prefer a chain through other declarations to a self-reference.
            if x == start && (n != start || scc.len() == 1) {
                end = Some(n);
                break 'search;
            }
            if seen.insert(x) {
                prev.insert(x, n);
                queue.push_back(x);
            }
        }
    }
    let idx = |n: Node| match n {
        Node::Head(k) | Node::Body(k) => k,
    };
    let mut chain = vec![idx(start)];
    let mut n = end.unwrap_or(start);
    let mut back = Vec::new();
    while n != start {
        back.push(idx(n));
        n = prev[&n];
    }
    back.reverse();
    for k in back {
        if chain.last() != Some(&k) {
            chain.push(k);
        }
    }
    chain.push(idx(start));
    chain
}

/// Strongly connected components, dependencies first.
fn tarjan(nodes: &[Node], edges: &HashMap<Node, HashSet<Node>>) -> Vec<Vec<Node>> {
    struct St<'a> {
        edges: &'a HashMap<Node, HashSet<Node>>,
        index: HashMap<Node, usize>,
        low: HashMap<Node, usize>,
        stack: Vec<Node>,
        on: HashSet<Node>,
        next: usize,
        out: Vec<Vec<Node>>,
    }
    fn visit(s: &mut St, v: Node) {
        s.index.insert(v, s.next);
        s.low.insert(v, s.next);
        s.next += 1;
        s.stack.push(v);
        s.on.insert(v);
        let mut succ: Vec<Node> = s.edges.get(&v).map(|e| e.iter().copied().collect()).unwrap_or_default();
        succ.sort();
        for w in succ {
            if !s.index.contains_key(&w) {
                visit(s, w);
                let lw = s.low[&w];
                let lv = s.low.get_mut(&v).unwrap();
                *lv = (*lv).min(lw);
            } else if s.on.contains(&w) {
                let iw = s.index[&w];
                let lv = s.low.get_mut(&v).unwrap();
                *lv = (*lv).min(iw);
            }
        }
        if s.low[&v] == s.index[&v] {
            let mut scc = Vec::new();
            while let Some(w) = s.stack.pop() {
                s.on.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            scc.sort();
            s.out.push(scc);
        }
    }
    let mut s = St { edges, index: HashMap::new(), low: HashMap::new(), stack: Vec::new(), on: HashSet::new(), next: 0, out: Vec::new() };
    for &n in nodes {
        if !s.index.contains_key(&n) {
            visit(&mut s, n);
        }
    }
    s.out
}

/// Names a part of a declaration mentions, and whether inside a type.
#[derive(Default)]
struct Refs(Vec<(String, bool)>);

impl Refs {
    fn constraints(&mut self, cs: &[Constraint], bound: &[String]) {
        let bound: Vec<String> = bound.iter().cloned().chain(cs.iter().filter_map(|c| match c {
            Constraint::Typed { name, .. } => Some(name.name.clone()),
            Constraint::Pred(_) => None,
        })).collect();
        for c in cs {
            match c {
                Constraint::Typed { ty, .. } => self.expr(ty, &bound, true),
                Constraint::Pred(e) => self.expr(e, &bound, false),
            }
        }
    }

    fn block(&mut self, b: &Block, bound: &[String]) {
        let mut bound = bound.to_vec();
        for s in &b.stmts {
            match s {
                Stmt::Let(p, e) | Stmt::Bind(p, e) => {
                    self.expr(e, &bound, false);
                    p.binds(&mut bound);
                }
                Stmt::Have(e) | Stmt::Expr(e) => self.expr(e, &bound, false),
                Stmt::When(w) => {
                    for (x, e) in &w.binds {
                        self.expr(e, &bound, false);
                        bound.push(x.name.clone());
                    }
                    self.block(&w.body, &bound);
                }
            }
        }
        self.expr(&b.result, &bound, false);
    }

    fn expr(&mut self, e: &Expr, bound: &[String], in_type: bool) {
        let go = |s: &mut Self, x: &Expr| s.expr(x, bound, in_type);
        match &e.kind {
            ExprKind::Var(n) | ExprKind::Con(n) => {
                if !bound.iter().any(|b| b == n) {
                    self.0.push((n.clone(), in_type));
                }
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) | ExprKind::Par(xs) => xs.iter().for_each(|x| go(self, x)),
            ExprKind::App(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) | ExprKind::Index(a, b) => {
                go(self, a);
                go(self, b);
            }
            ExprKind::Neg(a) | ExprKind::SectionL(_, a) | ExprKind::SectionR(_, a) | ExprKind::Try(a) => go(self, a),
            // `m.f` names another module's `f`; `x.field` a field.
            ExprKind::Field(a, _) => {
                if !matches!(&a.kind, ExprKind::Var(n) if !bound.iter().any(|b| b == n)) {
                    go(self, a);
                }
            }
            ExprKind::If(c, t, f) => {
                go(self, c);
                go(self, t);
                go(self, f);
            }
            ExprKind::Match(s, arms) => {
                go(self, s);
                for a in arms {
                    let mut b = bound.to_vec();
                    a.pat.binds(&mut b);
                    self.pat_refs(&a.pat, in_type);
                    if let Some(g) = &a.guard {
                        self.expr(g, &b, in_type);
                    }
                    self.expr(&a.body, &b, in_type);
                }
            }
            ExprKind::Lambda(ps, body) => {
                let mut b = bound.to_vec();
                for p in ps {
                    p.binds(&mut b);
                    self.pat_refs(p, in_type);
                }
                self.expr(body, &b, in_type);
            }
            ExprKind::Block(b) => self.block(b, bound),
            ExprKind::Fork(_, b) => self.block(b, bound),
            ExprKind::Join(xs, _, b) => {
                let mut bb = bound.to_vec();
                for (x, e) in xs {
                    self.expr(e, bound, in_type);
                    bb.push(x.name.clone());
                }
                self.block(b, &bb);
            }
            _ => {}
        }
    }

    /// Constructors named in a pattern.
    fn pat_refs(&mut self, p: &Pattern, in_type: bool) {
        match &p.kind {
            PatKind::Con(c, ps) => {
                self.0.push((c.name.clone(), in_type));
                ps.iter().for_each(|q| self.pat_refs(q, in_type));
            }
            PatKind::Record(c, fs) => {
                self.0.push((c.name.clone(), in_type));
                fs.iter().for_each(|(_, q)| self.pat_refs(q, in_type));
            }
            PatKind::Tuple(ps) | PatKind::List(ps) | PatKind::Or(ps) => ps.iter().for_each(|q| self.pat_refs(q, in_type)),
            PatKind::Cons(a, b) => {
                self.pat_refs(a, in_type);
                self.pat_refs(b, in_type);
            }
            _ => {}
        }
    }
}

trait Binds {
    fn binds(&self, out: &mut Vec<String>);
}

impl Binds for Pattern {
    fn binds(&self, out: &mut Vec<String>) {
        match &self.kind {
            PatKind::Var(n) => out.push(n.clone()),
            PatKind::Con(_, ps) | PatKind::Tuple(ps) | PatKind::List(ps) | PatKind::Or(ps) => ps.iter().for_each(|q| q.binds(out)),
            PatKind::Cons(a, b) => {
                a.binds(out);
                b.binds(out);
            }
            PatKind::Record(_, fs) => {
                for (f, q) in fs {
                    if matches!(q.kind, PatKind::Wild) {
                        out.push(f.name.clone());
                    }
                    q.binds(out);
                }
            }
            _ => {}
        }
    }
}
