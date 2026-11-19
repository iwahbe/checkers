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

/// `dicts`: the declarations building instances' dictionaries (D136), which
/// every function and lemma may need, since instances aren't named.
pub fn plan(m: &ast::Module, dicts: &[usize]) -> Plan {
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
            DeclKind::Check { .. } | DeclKind::Class { .. } | DeclKind::Instance { .. } => {}
        }
    }
    // A function whose result type isn't written: its type is known only
    // once its body is checked.
    let inferred = |k: usize| match &m.decls[k].kind {
        DeclKind::Fn { result, constraints, .. } => match result {
            None => true,
            Some(r) => !constraints.iter().any(|c| matches!(c, Constraint::Typed { name, .. } if name.name == r.name)),
        },
        _ => false,
    };
    let is_type = |k: usize| matches!(m.decls[k].kind, DeclKind::Enum { .. } | DeclKind::Record { .. } | DeclKind::Alias { .. });
    let has_body = |k: usize| matches!(m.decls[k].kind, DeclKind::Fn { .. } | DeclKind::Lemma { .. });

    let mut edges: HashMap<Node, HashSet<Node>> = HashMap::new();
    // Soft edges only order checking: a body that uses a function with an
    // inferred result comes after that function's body, where possible.
    let mut soft: HashMap<Node, HashSet<Node>> = HashMap::new();
    let mut need = |from: Node, refs: &Refs, computed: bool| {
        let e = edges.entry(from).or_default();
        for (n, in_type) in &refs.0 {
            let Some(&k) = names.get(n.as_str()) else { continue };
            e.insert(Node::Head(k));
            if (computed || *in_type) && has_body(k) {
                e.insert(Node::Body(k));
            } else if matches!(from, Node::Body(u) if u != k) && inferred(k) {
                soft.entry(from).or_default().insert(Node::Body(k));
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
            DeclKind::Lemma { params, constraints, decreasing, lets, ensures, proof, .. } => {
                let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                head.constraints(constraints, &bound);
                if let Some(e) = decreasing {
                    head.expr(e, &bound, false);
                }
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
            DeclKind::Check { .. } | DeclKind::Class { .. } | DeclKind::Instance { .. } => {}
        }
    }
    // Any function or lemma may use an instance (D136).
    for k in 0..m.decls.len() {
        if has_body(k) && !dicts.contains(&k) {
            for &d in dicts {
                edges.entry(Node::Head(k)).or_default().insert(Node::Head(d));
                edges.entry(Node::Body(k)).or_default().insert(Node::Head(d));
            }
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
    let mut both = edges.clone();
    for (n, ts) in soft {
        both.entry(n).or_default().extend(ts);
    }
    // Order by both kinds of edge; within a group the soft edges make, by
    // the hard ones only (so only those can be cycles).
    let mut sccs = Vec::new();
    for group in tarjan(&nodes, &both) {
        if group.len() == 1 {
            sccs.push(group);
            continue;
        }
        let members: HashSet<Node> = group.iter().copied().collect();
        let inner: HashMap<Node, HashSet<Node>> = group
            .iter()
            .map(|n| (*n, edges.get(n).map(|e| e.iter().copied().filter(|x| members.contains(x)).collect()).unwrap_or_default()))
            .collect();
        let ordered: Vec<Node> = nodes.iter().copied().filter(|n| members.contains(n)).collect();
        sccs.extend(tarjan(&ordered, &inner));
    }
    let is_alias = |n: &Node| matches!(n, Node::Head(k) if matches!(m.decls[*k].kind, DeclKind::Alias { .. }));
    let mut plan = Plan { groups: Vec::new(), cycles: Vec::new() };
    for scc in sccs {
        let cyclic = scc.len() > 1 || edges.get(&scc[0]).is_some_and(|e| e.contains(&scc[0]));
        let all_types = scc.iter().all(|n| matches!(n, Node::Head(k) if is_type(*k)));
        if cyclic && !all_types {
            plan.cycles.push(cycle_in(&scc, &edges));
        }
        // Types may be mutually recursive, but only through an `enum` or a
        // `record`: an alias that needs itself through aliases alone
        // (`type A = x~B`, `type B = x~A`; `type L = x~List L`) would
        // unfold forever.
        if cyclic && all_types {
            let aliases: Vec<Node> = scc.iter().copied().filter(|n| is_alias(n)).collect();
            let alias_edges: HashMap<Node, HashSet<Node>> = aliases
                .iter()
                .map(|n| (*n, edges.get(n).map(|e| e.iter().copied().filter(|x| is_alias(x)).collect()).unwrap_or_default()))
                .collect();
            for group in tarjan(&aliases, &alias_edges) {
                if group.len() > 1 || alias_edges.get(&group[0]).is_some_and(|e| e.contains(&group[0])) {
                    plan.cycles.push(cycle_in(&group, &alias_edges));
                }
            }
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

/// Strongly connected components, dependencies first: those of `nodes` and
/// of what they reach, each node's edges followed in order.
fn tarjan(nodes: &[Node], edges: &HashMap<Node, HashSet<Node>>) -> Vec<Vec<Node>> {
    // Number the nodes: `nodes` first, then the others as they are met.
    let mut all: Vec<Node> = Vec::new();
    let mut number: HashMap<Node, usize> = HashMap::new();
    for &n in nodes {
        number.entry(n).or_insert_with(|| {
            all.push(n);
            all.len() - 1
        });
    }
    let mut numbered: Vec<Vec<usize>> = Vec::new();
    while numbered.len() < all.len() {
        let mut succ: Vec<Node> = edges.get(&all[numbered.len()]).map(|e| e.iter().copied().collect()).unwrap_or_default();
        succ.sort();
        let succ = succ.into_iter().map(|w| {
            *number.entry(w).or_insert_with(|| {
                all.push(w);
                all.len() - 1
            })
        });
        numbered.push(succ.collect());
    }
    let mut out: Vec<Vec<Node>> = sccs(&numbered).into_iter().map(|scc| scc.into_iter().map(|v| all[v]).collect()).collect();
    out.iter_mut().for_each(|scc| scc.sort());
    out
}

/// Strongly connected components (Tarjan's algorithm), dependencies first:
/// `edges[v]` are the nodes `v` depends on.
pub(super) fn sccs(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct St<'a> {
        edges: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(s: &mut St, v: usize) {
        s.index[v] = Some(s.next);
        s.low[v] = s.next;
        s.next += 1;
        s.stack.push(v);
        s.on[v] = true;
        let edges = s.edges;
        for &w in &edges[v] {
            match s.index[w] {
                None => {
                    visit(s, w);
                    s.low[v] = s.low[v].min(s.low[w]);
                }
                Some(iw) if s.on[w] => s.low[v] = s.low[v].min(iw),
                _ => {}
            }
        }
        if Some(s.low[v]) == s.index[v] {
            let mut comp = Vec::new();
            while let Some(w) = s.stack.pop() {
                s.on[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            s.out.push(comp);
        }
    }
    let n = edges.len();
    let mut s = St { edges, index: vec![None; n], low: vec![0; n], on: vec![false; n], stack: vec![], next: 0, out: vec![] };
    for v in 0..n {
        if s.index[v].is_none() {
            visit(&mut s, v);
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
            Constraint::Pred(_) | Constraint::Named(..) => None,
        })).collect();
        for c in cs {
            match c {
                Constraint::Typed { ty, .. } => self.expr(ty, &bound, true),
                Constraint::Pred(e) | Constraint::Named(_, e) => self.expr(e, &bound, false),
            }
        }
    }

    fn block(&mut self, b: &Block, bound: &[String]) {
        let mut bound = bound.to_vec();
        for s in &b.stmts {
            match s {
                Stmt::Let(p, e) => {
                    self.expr(e, &bound, false);
                    p.binds(&mut bound);
                }
                Stmt::Have(e) | Stmt::Expr(e) => self.expr(e, &bound, false),
                // `x` is a local: only the type refers to declarations.
                Stmt::HaveType(_, t) => self.expr(t, &bound, false),
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
            ExprKind::Refine(r) => {
                let mut b = bound.to_vec();
                b.extend(r.binders());
                for t in r.types() {
                    self.expr(t, &b, in_type);
                }
                for p in &r.preds {
                    self.expr(p, &b, false);
                }
            }
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
            ExprKind::Forall(vs, cs) => {
                let mut b = bound.to_vec();
                b.extend(vs.iter().map(|v| v.name.clone()));
                self.constraints(cs, &b);
            }
            ExprKind::Block(b) => self.block(b, bound),
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
