//! A persistent map: a copy shares the entries with the original, so
//! keeping a copy costs O(1) however many entries there are, and changing
//! either copies only the path to the entry changed. A treap (a binary
//! search tree, kept a heap by each key's hash), so each operation takes
//! O(log n) expected. The elaborator's contexts count the locals of each
//! name this way, so a context kept for later stays free to keep.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

struct Node<K, V> {
    key: K,
    val: V,
    /// The key's hash: a node's is at least its children's.
    pri: u64,
    left: Option<Rc<Node<K, V>>>,
    right: Option<Rc<Node<K, V>>>,
}

type Link<K, V> = Option<Rc<Node<K, V>>>;

pub struct PMap<K, V> {
    root: Link<K, V>,
    len: usize,
}

impl<K, V> Clone for PMap<K, V> {
    fn clone(&self) -> Self {
        PMap { root: self.root.clone(), len: self.len }
    }
}

impl<K, V> Default for PMap<K, V> {
    fn default() -> Self {
        PMap { root: None, len: 0 }
    }
}

fn priority<Q: Hash + ?Sized>(k: &Q) -> u64 {
    // The default hasher's keys are fixed: the same map for the same keys.
    let mut h = std::collections::hash_map::DefaultHasher::new();
    k.hash(&mut h);
    h.finish()
}

impl<K: Ord + Hash + Clone, V: Clone> PMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get<Q: Ord + ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        let mut node = self.root.as_deref();
        while let Some(n) = node {
            node = match k.cmp(n.key.borrow()) {
                Ordering::Less => n.left.as_deref(),
                Ordering::Greater => n.right.as_deref(),
                Ordering::Equal => return Some(&n.val),
            };
        }
        None
    }

    /// Set `k` to `v`.
    pub fn insert(&mut self, k: K, v: V) {
        let pri = priority(&k);
        let mut added = false;
        self.root = Some(insert(self.root.take(), k, v, pri, &mut added));
        self.len += usize::from(added);
    }

    /// Remove `k`, if it is there.
    pub fn remove<Q: Ord + ?Sized>(&mut self, k: &Q)
    where
        K: Borrow<Q>,
    {
        if self.get(k).is_some() {
            self.root = remove(self.root.take(), k);
            self.len -= 1;
        }
    }
}

fn node<K: Clone, V: Clone>(n: &Node<K, V>, left: Link<K, V>, right: Link<K, V>) -> Node<K, V> {
    Node { key: n.key.clone(), val: n.val.clone(), pri: n.pri, left, right }
}

fn insert<K: Ord + Clone, V: Clone>(t: Link<K, V>, k: K, v: V, pri: u64, added: &mut bool) -> Rc<Node<K, V>> {
    let Some(n) = t else {
        *added = true;
        return Rc::new(Node { key: k, val: v, pri, left: None, right: None });
    };
    match k.cmp(&n.key) {
        Ordering::Equal => Rc::new(Node { key: k, val: v, pri: n.pri, left: n.left.clone(), right: n.right.clone() }),
        Ordering::Less => {
            let l = insert(n.left.clone(), k, v, pri, added);
            if l.pri > n.pri {
                // Rotate right: the new left child is the root.
                let down = node(&n, l.right.clone(), n.right.clone());
                Rc::new(node(&l, l.left.clone(), Some(Rc::new(down))))
            } else {
                Rc::new(node(&n, Some(l), n.right.clone()))
            }
        }
        Ordering::Greater => {
            let r = insert(n.right.clone(), k, v, pri, added);
            if r.pri > n.pri {
                let down = node(&n, n.left.clone(), r.left.clone());
                Rc::new(node(&r, Some(Rc::new(down)), r.right.clone()))
            } else {
                Rc::new(node(&n, n.left.clone(), Some(r)))
            }
        }
    }
}

fn remove<K: Ord + Clone + Borrow<Q>, V: Clone, Q: Ord + ?Sized>(t: Link<K, V>, k: &Q) -> Link<K, V> {
    let n = t?;
    match k.cmp(n.key.borrow()) {
        Ordering::Less => Some(Rc::new(node(&n, remove(n.left.clone(), k), n.right.clone()))),
        Ordering::Greater => Some(Rc::new(node(&n, n.left.clone(), remove(n.right.clone(), k)))),
        Ordering::Equal => merge(n.left.clone(), n.right.clone()),
    }
}

/// Two trees, every key of `a` before every key of `b`, as one.
fn merge<K: Clone, V: Clone>(a: Link<K, V>, b: Link<K, V>) -> Link<K, V> {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(a), Some(b)) if a.pri >= b.pri => Some(Rc::new(node(&a, a.left.clone(), merge(a.right.clone(), Some(b))))),
        (Some(a), Some(b)) => Some(Rc::new(node(&b, merge(Some(a), b.left.clone()), b.right.clone()))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agrees_with_a_btree_map_and_keeps_copies() {
        let mut m: PMap<u32, u32> = PMap::new();
        let mut b = std::collections::BTreeMap::new();
        let mut kept = Vec::new();
        for i in 0..2000u32 {
            let k = (i * 7919) % 613;
            if i % 3 == 2 {
                m.remove(&k);
                b.remove(&k);
            } else {
                m.insert(k, i);
                b.insert(k, i);
            }
            if i % 97 == 0 {
                kept.push((m.clone(), b.clone()));
            }
            assert_eq!(m.len(), b.len());
        }
        for (m, b) in kept.iter().chain([(m, b)].iter()) {
            for k in 0..613 {
                assert_eq!(m.get(&k), b.get(&k));
            }
        }
    }
}
