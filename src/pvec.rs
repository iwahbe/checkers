//! A persistent vector: a copy shares the elements with the original, so
//! keeping a copy costs O(1) however long it is, and changing either copies
//! only what the change touches (a trie of 32-element leaves and the last,
//! partial one): O(log n) to read or change an element, amortized O(1) to
//! push or pop. The elaborator's contexts are kept this way, one for each
//! constraint left for later.

use std::rc::Rc;

const BITS: u32 = 5;
const WIDTH: usize = 1 << BITS;
const MASK: usize = WIDTH - 1;

#[derive(Clone)]
enum Node<T> {
    Branch(Vec<Rc<Node<T>>>),
    Leaf(Vec<T>),
}

pub struct PVec<T> {
    len: usize,
    /// The root's level: a leaf is at 0, a branch over leaves at `BITS`.
    shift: u32,
    /// The full leaves, first `len - tail.len()` elements; `None` if none.
    root: Option<Rc<Node<T>>>,
    /// The last elements, at most `WIDTH`.
    tail: Rc<Vec<T>>,
}

impl<T> Clone for PVec<T> {
    fn clone(&self) -> Self {
        PVec { len: self.len, shift: self.shift, root: self.root.clone(), tail: self.tail.clone() }
    }
}

impl<T> Default for PVec<T> {
    fn default() -> Self {
        PVec { len: 0, shift: 0, root: None, tail: Rc::new(Vec::new()) }
    }
}

impl<T: Clone> PVec<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// How many elements are in the trie, not the tail.
    fn trie_len(&self) -> usize {
        self.len - self.tail.len()
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        if i >= self.len {
            return None;
        }
        let t = self.trie_len();
        if i >= t {
            return Some(&self.tail[i - t]);
        }
        let mut node = self.root.as_deref()?;
        let mut shift = self.shift;
        loop {
            match node {
                Node::Branch(ch) => {
                    node = &ch[(i >> shift) & MASK];
                    shift -= BITS;
                }
                Node::Leaf(v) => return Some(&v[i & MASK]),
            }
        }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        if i >= self.len {
            return None;
        }
        let t = self.trie_len();
        if i >= t {
            return Some(&mut Rc::make_mut(&mut self.tail)[i - t]);
        }
        let mut node = Rc::make_mut(self.root.as_mut()?);
        let mut shift = self.shift;
        loop {
            match node {
                Node::Branch(ch) => {
                    node = Rc::make_mut(&mut ch[(i >> shift) & MASK]);
                    shift -= BITS;
                }
                Node::Leaf(v) => return Some(&mut v[i & MASK]),
            }
        }
    }

    pub fn last(&self) -> Option<&T> {
        self.len.checked_sub(1).and_then(|i| self.get(i))
    }

    pub fn push(&mut self, x: T) {
        if self.tail.len() == WIDTH {
            let at = self.trie_len();
            let full = std::mem::replace(&mut self.tail, Rc::new(Vec::with_capacity(WIDTH)));
            let leaf = Rc::new(Node::Leaf(Rc::try_unwrap(full).unwrap_or_else(|v| (*v).clone())));
            self.push_leaf(at, leaf);
        }
        Rc::make_mut(&mut self.tail).push(x);
        self.len += 1;
    }

    /// Adds a full leaf after the trie's `at` elements.
    fn push_leaf(&mut self, at: usize, leaf: Rc<Node<T>>) {
        let Some(root) = &mut self.root else {
            self.root = Some(leaf);
            self.shift = 0;
            return;
        };
        if at == WIDTH << self.shift {
            // Full: a new root over the old one and a path to the leaf.
            let old = root.clone();
            *root = Rc::new(Node::Branch(vec![old, path(self.shift, leaf)]));
            self.shift += BITS;
            return;
        }
        let mut node = root;
        let mut shift = self.shift;
        loop {
            let Node::Branch(ch) = Rc::make_mut(node) else { unreachable!("a leaf above the last level") };
            let k = (at >> shift) & MASK;
            if shift == BITS || k == ch.len() {
                ch.push(path(shift - BITS, leaf));
                return;
            }
            node = &mut ch[k];
            shift -= BITS;
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        if self.tail.is_empty() {
            let leaf = self.pop_leaf();
            self.tail = Rc::new(match Rc::try_unwrap(leaf).unwrap_or_else(|n| (*n).clone()) {
                Node::Leaf(v) => v,
                Node::Branch(_) => unreachable!("a branch at the last level"),
            });
        }
        self.len -= 1;
        Rc::make_mut(&mut self.tail).pop()
    }

    /// Takes the trie's last leaf away; the tail is empty.
    fn pop_leaf(&mut self) -> Rc<Node<T>> {
        let root = self.root.as_mut().expect("elements in the trie");
        if self.shift == 0 {
            return self.root.take().unwrap();
        }
        fn go<T: Clone>(node: &mut Rc<Node<T>>, shift: u32) -> (Rc<Node<T>>, bool) {
            let Node::Branch(ch) = Rc::make_mut(node) else { unreachable!("a leaf above the last level") };
            let leaf = if shift == BITS {
                ch.pop().unwrap()
            } else {
                let (leaf, empty) = go(ch.last_mut().unwrap(), shift - BITS);
                if empty {
                    ch.pop();
                }
                leaf
            };
            (leaf, ch.is_empty())
        }
        let (leaf, _) = go(root, self.shift);
        // A root with one child is that child.
        while self.shift > 0 {
            let Some(Node::Branch(ch)) = self.root.as_deref() else { break };
            if ch.len() != 1 {
                break;
            }
            let only = ch[0].clone();
            self.root = Some(only);
            self.shift -= BITS;
        }
        leaf
    }

    pub fn truncate(&mut self, n: usize) {
        while self.len > n {
            self.pop();
        }
    }

    /// First to last; reversible.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> + ExactSizeIterator + Clone + '_ {
        (0..self.len).map(move |i| &self[i])
    }
}

/// `leaf` under branches down from level `shift`.
fn path<T>(shift: u32, leaf: Rc<Node<T>>) -> Rc<Node<T>> {
    let mut node = leaf;
    let mut s = 0;
    while s < shift {
        node = Rc::new(Node::Branch(vec![node]));
        s += BITS;
    }
    node
}

impl<T: Clone> std::ops::Index<usize> for PVec<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        let len = self.len;
        self.get(i).unwrap_or_else(|| panic!("index {i} out of range for a vector of {len}"))
    }
}

impl<T: Clone> std::ops::IndexMut<usize> for PVec<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        let len = self.len;
        self.get_mut(i).unwrap_or_else(|| panic!("index {i} out of range for a vector of {len}"))
    }
}

impl<T: Clone> FromIterator<T> for PVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        let mut v = PVec::new();
        for x in it {
            v.push(x);
        }
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pushes, pops, changes and copies, against a `Vec` doing the same.
    #[test]
    fn behaves_as_a_vec() {
        let mut v: PVec<usize> = PVec::new();
        let mut w: Vec<usize> = Vec::new();
        let mut kept: Vec<(PVec<usize>, Vec<usize>)> = Vec::new();
        let mut seed = 12345u64;
        let mut next = |m: u64| {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 33) % m) as usize
        };
        // Growing on the whole, past three levels, popping across leaves.
        for step in 0..200_000 {
            match next(1000) {
                0..=549 => {
                    v.push(step);
                    w.push(step);
                }
                550..=749 => assert_eq!(v.pop(), w.pop()),
                750..=949 if !w.is_empty() => {
                    let i = next(w.len() as u64);
                    v[i] = step;
                    w[i] = step;
                }
                950 => {
                    let n = w.len().saturating_sub(next(200));
                    v.truncate(n);
                    w.truncate(n);
                }
                _ if step % 4000 == 0 => kept.push((v.clone(), w.clone())),
                _ => {}
            }
            assert_eq!(v.len(), w.len());
            if !w.is_empty() {
                let i = next(w.len() as u64);
                assert_eq!(v.get(i), w.get(i));
            }
        }
        assert!(w.len() > 40_000, "{}", w.len());
        kept.push((v, w));
        for (v, w) in &kept {
            assert!(v.iter().eq(w.iter()));
            assert!(v.iter().rev().eq(w.iter().rev()));
        }
        // Thousands deep: several levels, grown and shrunk again.
        let mut v: PVec<usize> = (0..100_000).collect();
        let copy = v.clone();
        v.truncate(10);
        assert!(v.iter().copied().eq(0..10));
        assert!(copy.iter().copied().eq(0..100_000));
    }
}
