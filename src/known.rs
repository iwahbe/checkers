//! Values known at compile time (§8.9) as graphs: every value is a node of
//! a flat table, its parts nodes before it, equal parts one node
//! (hash-consed). A value of any depth is walked by a loop over the table
//! or an explicit stack, never by recursion, so building, hashing,
//! comparing and showing one takes stack independent of its depth.
//!
//! A known value is a term (`Tm::Known`) and a value (`Val::Known`) of
//! the type checker; matching on one, or reading its field, takes it
//! apart one level at a time (`core::force_meta`). Staging gets them from
//! native code (`native::eval::Evaluator::reify_as`), and native code lays
//! them out as static data (`native::codegen`).

use crate::core::{ConId, Globals, Icit, Lit};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::hash::Hasher;
use std::rc::Rc;
use std::sync::Arc;

/// A fast hasher for the tables of graphs (FxHash's multiply and rotate):
/// deterministic, and much quicker than SipHash on the small keys
/// hash-consing a million nodes looks up.
#[derive(Default, Clone, Copy)]
pub struct Fx(u64);

impl Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for c in words {
            self.write_u64(u64::from_le_bytes(*c));
        }
        for b in rest {
            self.write_u64(*b as u64);
        }
    }

    fn write_u8(&mut self, n: u8) {
        self.write_u64(n as u64)
    }

    fn write_u32(&mut self, n: u32) {
        self.write_u64(n as u64)
    }

    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64)
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }

    /// The state mixed so that every bit of it reaches the low bits, which
    /// a hash table indexes by: a multiplication carries a word's low bits
    /// only upwards, so keys differing only in their high bits (a node's
    /// fields written as one word, its last field's id in the high half)
    /// would all fall in one bucket (murmur3's final mix).
    fn finish(&self) -> u64 {
        let mut x = self.0;
        x ^= x >> 33;
        x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
        x ^= x >> 33;
        x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
        x ^ (x >> 33)
    }
}

/// A map hashed by `Fx`.
pub type FxMap<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<Fx>>;

/// A 128-bit hash of a value's description, from two differently seeded
/// hashers: what tells values apart across graphs.
pub fn hash128(f: impl Fn(&mut dyn Hasher)) -> u128 {
    let mut a = Fx(0x243f_6a88_85a3_08d3);
    let mut b = Fx(0x1319_8a2e_0370_7344);
    f(&mut a);
    f(&mut b);
    // A final mix, so the last word written moves every bit.
    let mix = |x: u64| {
        let x = (x ^ (x >> 33)).wrapping_mul(0xff51_afd7_ed55_8ccd);
        let x = (x ^ (x >> 33)).wrapping_mul(0xc4ce_b9fe_1a85_ec53);
        x ^ (x >> 33)
    };
    (mix(a.finish()) as u128) << 64 | mix(b.finish()) as u128
}

/// A node: a value whose parts are earlier nodes of the same graph.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Int(i128),
    /// An integer outside `i128`'s range (never one inside it).
    Big(BigInt),
    Str(Box<str>),
    Bytes(Box<[u8]>),
    /// `()`, or an erased part (a type, a proof, a `ghost` field).
    Unit,
    /// A constructor applied to its fields (not its type's parameters).
    Con(ConId, Box<[u32]>),
    Tuple(Box<[u32]>),
    /// An array (not of `U8`s: those are `Bytes`), its elements stored by
    /// `layout` (`checkers_rt::array::Layout`'s code).
    Array(u8, Box<[u32]>),
    /// A definition's function, a constructor's, or a lambda's code, as a
    /// value (with no arguments yet). A lambda's closure holding captured
    /// values is its code given them (`Pap`).
    Closure(Code),
    /// A function given some of its arguments: the function's node, then
    /// the arguments'.
    Pap(Box<[u32]>),
    /// An erased value where no type says so (an argument a partial
    /// application holds): the word 0, not `()`'s.
    Erased,
}

/// The code a known closure runs: what names it in every program.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Code {
    Def(crate::core::DefId),
    Con(ConId),
    /// A lambda's, closed: the values it captured are its first parameters.
    Lam(Arc<crate::native::lower::LamCode>),
}

impl Node {
    /// The node's parts.
    pub fn parts(&self) -> &[u32] {
        match self {
            Node::Con(_, xs) | Node::Tuple(xs) | Node::Array(_, xs) | Node::Pap(xs) => xs,
            _ => &[],
        }
    }
}

/// A graph of nodes; a value is a graph and one of its nodes.
pub struct Known {
    nodes: Vec<Node>,
    /// Each node's hash, of its value (not of its position): equal values
    /// in different graphs hash alike.
    hashes: Vec<u128>,
}

impl Known {
    pub fn node(&self, id: u32) -> &Node {
        &self.nodes[id as usize]
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// The hash of node `id`'s value.
    pub fn hash_of(&self, id: u32) -> u128 {
        self.hashes[id as usize]
    }

    /// A graph of one literal.
    pub fn of_lit(l: &Lit) -> (Arc<Known>, u32) {
        let mut b = Builder::default();
        let id = b.lit(l);
        (Arc::new(b.finish()), id)
    }

    /// The nodes `id` reaches, itself included, parts first (in the
    /// table's order).
    pub fn reachable(&self, id: u32) -> Vec<u32> {
        let mut seen = vec![false; id as usize + 1];
        seen[id as usize] = true;
        let mut todo = vec![id];
        while let Some(x) = todo.pop() {
            for &p in self.node(x).parts() {
                if !seen[p as usize] {
                    seen[p as usize] = true;
                    todo.push(p);
                }
            }
        }
        (0..=id).filter(|x| seen[*x as usize]).collect()
    }

    /// Are node `x` of `a` and node `y` of `b` the same value?
    pub fn same(a: &Known, x: u32, b: &Known, y: u32) -> bool {
        if std::ptr::eq(a, b) {
            // One graph: equal values are one node.
            return x == y;
        }
        let mut seen = std::collections::HashSet::new();
        let mut todo = vec![(x, y)];
        while let Some((x, y)) = todo.pop() {
            if a.hash_of(x) != b.hash_of(y) {
                return false;
            }
            if !seen.insert((x, y)) {
                continue;
            }
            let (m, n) = (a.node(x), b.node(y));
            match (m, n) {
                (Node::Con(c, xs), Node::Con(d, ys)) if c == d && xs.len() == ys.len() => todo.extend(xs.iter().copied().zip(ys.iter().copied())),
                (Node::Tuple(xs), Node::Tuple(ys)) if xs.len() == ys.len() => todo.extend(xs.iter().copied().zip(ys.iter().copied())),
                (Node::Array(l, xs), Node::Array(k, ys)) if l == k && xs.len() == ys.len() => todo.extend(xs.iter().copied().zip(ys.iter().copied())),
                (Node::Pap(xs), Node::Pap(ys)) if xs.len() == ys.len() => todo.extend(xs.iter().copied().zip(ys.iter().copied())),
                (Node::Con(..), _) | (Node::Tuple(_), _) | (Node::Array(..), _) | (Node::Pap(_), _) => return false,
                _ if m != n => return false,
                _ => {}
            }
        }
        true
    }

    /// Node `id` as a literal, if it is one.
    pub fn lit(&self, id: u32) -> Option<Lit> {
        Some(match self.node(id) {
            Node::Int(n) => Lit::Num(*n),
            Node::Big(n) => Lit::Big(Rc::new(n.clone())),
            Node::Str(s) => Lit::Str(Rc::from(&**s)),
            Node::Bytes(b) => Lit::Bytes(Rc::from(&**b)),
            _ => return None,
        })
    }

    /// Node `id` shown as the type checker shows the term it is
    /// (`core::show`), at precedence `p`. Iterative: a value of any depth.
    pub fn show(&self, g: &Globals, id: u32, p: u8) -> String {
        enum Task<'a> {
            Text(&'a str),
            Owned(String),
            Node(u32, u8),
        }
        let mut out = String::new();
        let mut todo = vec![Task::Node(id, p)];
        while let Some(t) = todo.pop() {
            let (id, p) = match t {
                Task::Text(s) => {
                    out.push_str(s);
                    continue;
                }
                Task::Owned(s) => {
                    out.push_str(&s);
                    continue;
                }
                Task::Node(id, p) => (id, p),
            };
            match self.node(id) {
                Node::Int(n) => out.push_str(&n.to_string()),
                Node::Big(n) => out.push_str(&n.to_string()),
                Node::Str(s) => out.push_str(&format!("{s:?}")),
                Node::Bytes(b) => out.push_str(&format!("b{:?}", String::from_utf8_lossy(b))),
                Node::Unit | Node::Erased => out.push_str("()"),
                Node::Closure(Code::Def(d)) => out.push_str(&g.defs[d.0 as usize].name),
                Node::Closure(Code::Con(c)) => out.push_str(&g.cons[c.0 as usize].name),
                // A lambda: its code, the values it captured put in.
                Node::Closure(Code::Lam(code)) => out.push_str(&crate::native::ir::show_code(g, &code.ir, &mut Vec::new(), p)),
                Node::Pap(xs) if matches!(self.node(xs[0]), Node::Closure(Code::Lam(c)) if xs.len() - 1 <= c.captured) => {
                    let Node::Closure(Code::Lam(code)) = self.node(xs[0]) else { unreachable!() };
                    let mut names: Vec<String> = xs[1..].iter().map(|x| self.show(g, *x, 2)).collect();
                    let mut body: &crate::native::ir::Ir = &code.ir;
                    for _ in 1..xs.len() {
                        let crate::native::ir::Ir::Lam(_, b) = body else { unreachable!("a lambda per captured value") };
                        body = b;
                    }
                    out.push_str(&crate::native::ir::show_code(g, body, &mut names, p));
                }
                Node::Pap(xs) => {
                    let mut parts = Vec::new();
                    if p > 1 {
                        parts.push(Task::Text("("));
                    }
                    for (k, x) in xs.iter().enumerate() {
                        if k > 0 {
                            parts.push(Task::Text(" "));
                        }
                        parts.push(Task::Node(*x, 2));
                    }
                    if p > 1 {
                        parts.push(Task::Text(")"));
                    }
                    todo.extend(parts.into_iter().rev());
                }
                Node::Array(_, xs) => {
                    let mut parts = vec![Task::Text("[")];
                    for (k, x) in xs.iter().enumerate() {
                        if k > 0 {
                            parts.push(Task::Text(", "));
                        }
                        parts.push(Task::Node(*x, 0));
                    }
                    parts.push(Task::Text("]"));
                    todo.extend(parts.into_iter().rev());
                }
                Node::Tuple(xs) => {
                    // Pushed last first.
                    let mut parts = vec![Task::Text("(")];
                    for (k, x) in xs.iter().enumerate() {
                        if k > 0 {
                            parts.push(Task::Text(", "));
                        }
                        parts.push(Task::Node(*x, 0));
                    }
                    parts.push(Task::Text(")"));
                    todo.extend(parts.into_iter().rev());
                }
                Node::Con(c, xs) => {
                    let ci = &g.cons[c.0 as usize];
                    let mut parts = Vec::new();
                    if Some(*c) == g.well_known.cons && xs.len() == 2 {
                        if p > 0 {
                            parts.push(Task::Text("("));
                        }
                        parts.extend([Task::Node(xs[0], 3), Task::Text(" :: "), Task::Node(xs[1], 1)]);
                        if p > 0 {
                            parts.push(Task::Text(")"));
                        }
                    } else {
                        let explicit: Vec<u32> = xs.iter().zip(&ci.fields).filter(|(_, f)| f.2 == Icit::Expl).map(|(x, _)| *x).collect();
                        if explicit.is_empty() {
                            out.push_str(if Some(*c) == g.well_known.nil { "[]" } else { &ci.name });
                            continue;
                        }
                        if p > 1 {
                            parts.push(Task::Text("("));
                        }
                        parts.push(Task::Owned(ci.name.to_string()));
                        for x in explicit {
                            parts.push(Task::Text(" "));
                            parts.push(Task::Node(x, 2));
                        }
                        if p > 1 {
                            parts.push(Task::Text(")"));
                        }
                    }
                    todo.extend(parts.into_iter().rev());
                }
            }
        }
        out
    }
}

/// A known value: a graph and one of its nodes. Shown for debugging (and
/// in keys made from terms' `Debug` form) by its hash, so equal values
/// print alike, and a value of any size in a few characters.
#[derive(Clone)]
pub struct Value {
    pub graph: Arc<Known>,
    pub id: u32,
}

impl Value {
    pub fn new(graph: Arc<Known>, id: u32) -> Value {
        Value { graph, id }
    }

    pub fn node(&self) -> &Node {
        self.graph.node(self.id)
    }

    /// Its part `id` (a node of the same graph).
    pub fn at(&self, id: u32) -> Value {
        Value { graph: self.graph.clone(), id }
    }

    pub fn same(&self, other: &Value) -> bool {
        Known::same(&self.graph, self.id, &other.graph, other.id)
    }

    pub fn lit(&self) -> Option<Lit> {
        self.graph.lit(self.id)
    }

    pub fn hash(&self) -> u128 {
        self.graph.hash_of(self.id)
    }

    pub fn show(&self, g: &Globals, p: u8) -> String {
        self.graph.show(g, self.id, p)
    }

    /// Whether `f` holds of a constructor in this value.
    pub fn any_con(&self, mut f: impl FnMut(ConId) -> bool) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut todo = vec![self.id];
        while let Some(x) = todo.pop() {
            if !seen.insert(x) {
                continue;
            }
            let n = self.graph.node(x);
            if let Node::Con(c, _) = n {
                if f(*c) {
                    return true;
                }
            }
            todo.extend_from_slice(n.parts());
        }
        false
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Known#{:032x}", self.hash())
    }
}

impl std::fmt::Debug for Known {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Known({} nodes)", self.nodes.len())
    }
}

/// Builds a graph, node by node, parts first: a node equal to one already
/// added is that one.
#[derive(Default)]
pub struct Builder {
    nodes: Vec<Node>,
    ids: FxMap<Node, u32>,
}

impl Builder {
    pub fn add(&mut self, n: Node) -> u32 {
        debug_assert!(n.parts().iter().all(|&p| (p as usize) < self.nodes.len()));
        if let Some(&id) = self.ids.get(&n) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(n.clone());
        self.ids.insert(n, id);
        id
    }

    pub fn lit(&mut self, l: &Lit) -> u32 {
        self.add(match l {
            Lit::Num(n) => Node::Int(*n),
            Lit::Big(n) => Node::Big((**n).clone()),
            Lit::Str(s) => Node::Str(Box::from(&**s)),
            Lit::Bytes(b) => Node::Bytes(Box::from(&**b)),
        })
    }

    pub fn finish(self) -> Known {
        let mut hashes: Vec<u128> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let v = hash128(|s: &mut dyn Hasher| match n {
                Node::Con(c, xs) => {
                    s.write_u8(0);
                    s.write_u32(c.0);
                    for x in xs.iter() {
                        s.write(&hashes[*x as usize].to_le_bytes());
                    }
                }
                Node::Tuple(xs) => {
                    s.write_u8(1);
                    for x in xs.iter() {
                        s.write(&hashes[*x as usize].to_le_bytes());
                    }
                }
                Node::Int(n) => {
                    s.write_u8(2);
                    s.write(&n.to_le_bytes());
                }
                Node::Big(n) => {
                    s.write_u8(3);
                    s.write(&n.to_signed_bytes_le());
                }
                Node::Str(t) => {
                    s.write_u8(4);
                    s.write_usize(t.len());
                    s.write(t.as_bytes());
                }
                Node::Bytes(b) => {
                    s.write_u8(5);
                    s.write_usize(b.len());
                    s.write(b);
                }
                Node::Unit => s.write_u8(6),
                Node::Erased => s.write_u8(8),
                Node::Closure(Code::Def(d)) => {
                    s.write_u8(9);
                    s.write_u32(d.0);
                }
                Node::Closure(Code::Con(c)) => {
                    s.write_u8(10);
                    s.write_u32(c.0);
                }
                Node::Closure(Code::Lam(code)) => {
                    s.write_u8(12);
                    s.write(&code.hash().to_le_bytes());
                }
                Node::Pap(xs) => {
                    s.write_u8(11);
                    s.write_usize(xs.len());
                    for x in xs.iter() {
                        s.write(&hashes[*x as usize].to_le_bytes());
                    }
                }
                Node::Array(l, xs) => {
                    s.write_u8(7);
                    s.write_u8(*l);
                    s.write_usize(xs.len());
                    for x in xs.iter() {
                        s.write(&hashes[*x as usize].to_le_bytes());
                    }
                }
            });
            hashes.push(v);
        }
        Known { nodes: self.nodes, hashes }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A chain of `n` constructors around `Unit`, each holding its depth's
    /// parity: built bottom up, as `reify` builds one.
    fn chain(n: u32) -> (Arc<Known>, u32) {
        let mut b = Builder::default();
        let mut id = b.add(Node::Unit);
        for k in 0..n {
            let x = b.add(Node::Int((k % 2) as i128));
            id = b.add(Node::Con(ConId(1), Box::new([id, x])));
        }
        (Arc::new(b.finish()), id)
    }

    #[test]
    fn equal_parts_are_one_node() {
        let (k, _) = chain(1000);
        // `Unit`, the two numbers, and one node per link.
        assert_eq!(k.len(), 3 + 1000);
    }

    #[test]
    fn values_compare_across_graphs_at_any_depth() {
        let (a, x) = chain(1_000_000);
        let (b, y) = chain(1_000_000);
        let (c, z) = chain(999_999);
        assert_eq!(a.hash_of(x), b.hash_of(y));
        assert!(Known::same(&a, x, &b, y));
        assert!(!Known::same(&a, x, &c, z));
        assert_eq!(a.reachable(x).len(), a.len());
    }
}
