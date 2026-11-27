//! Evaluation environments: the values of the locals in scope, as a
//! persistent list (`List`, also what native code's compiler knows of
//! each local). Adding a value, or dropping the innermost ones, shares
//! everything already there, so an environment a closure holds is never
//! copied when it is extended: a call of a closure made under n locals adds
//! one value in O(1), where copying them took O(n), and a chain of n `let`s
//! of closures took O(n²) time and memory. A value is found by its index in
//! O(log n).
//!
//! The list is Okasaki's skew-binary random-access list: a list of complete
//! binary trees whose sizes, 2^k − 1, increase strictly, except that the
//! first two may be equal. The innermost local is the first tree's root.

use crate::core::Val;
use std::rc::Rc;

/// The values of locals, outermost (level 0) to innermost.
pub type Env = List<Val>;

enum Tree<T> {
    Leaf(T),
    /// A root and two subtrees of equal size.
    Node(T, Rc<Tree<T>>, Rc<Tree<T>>),
}

struct Cell<T> {
    /// The number of values in `tree`.
    size: usize,
    tree: Rc<Tree<T>>,
    rest: Option<Rc<Cell<T>>>,
}

/// A persistent list, indexed by level (from the outermost) or by de
/// Bruijn index (from the innermost).
pub struct List<T> {
    len: usize,
    top: Option<Rc<Cell<T>>>,
}

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        List { len: self.len, top: self.top.clone() }
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        List { len: 0, top: None }
    }
}

impl<T> Tree<T> {
    /// Value `i` in preorder, of a tree of `size` values.
    fn get(&self, mut i: usize, mut size: usize) -> &T {
        let mut t = self;
        loop {
            match t {
                Tree::Leaf(v) => return v,
                Tree::Node(v, l, r) => {
                    if i == 0 {
                        return v;
                    }
                    size /= 2;
                    if i <= size {
                        i -= 1;
                        t = l;
                    } else {
                        i -= 1 + size;
                        t = r;
                    }
                }
            }
        }
    }

    /// Every value, in preorder.
    fn each<'a>(&'a self, out: &mut Vec<&'a T>) {
        match self {
            Tree::Leaf(v) => out.push(v),
            Tree::Node(v, l, r) => {
                out.push(v);
                l.each(out);
                r.each(out);
            }
        }
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Add `v` as the innermost value.
    pub fn push(&mut self, v: T) {
        let top = self.top.take();
        self.top = Some(Rc::new(match top {
            Some(a) if matches!(&a.rest, Some(b) if b.size == a.size) => {
                let b = a.rest.as_ref().unwrap();
                Cell { size: 2 * a.size + 1, tree: Rc::new(Tree::Node(v, a.tree.clone(), b.tree.clone())), rest: b.rest.clone() }
            }
            rest => Cell { size: 1, tree: Rc::new(Tree::Leaf(v)), rest },
        }));
        self.len += 1;
    }

    /// `self` with `v` added.
    pub fn with(&self, v: T) -> Self {
        let mut e = self.clone();
        e.push(v);
        e
    }

    /// Drop the innermost `k` values.
    fn drop_inner(&mut self, mut k: usize) {
        assert!(k <= self.len, "dropping {k} of {} values", self.len);
        self.len -= k;
        let mut top = self.top.take();
        while k > 0 {
            let cell = top.expect("an environment holds its length");
            if k >= cell.size {
                k -= cell.size;
                top = cell.rest.clone();
                continue;
            }
            // `k < size`, so the tree is a node: drop its root, keep its halves.
            let Tree::Node(_, l, r) = &*cell.tree else { unreachable!("a leaf is one value") };
            let half = cell.size / 2;
            k -= 1;
            let right = Rc::new(Cell { size: half, tree: r.clone(), rest: cell.rest.clone() });
            top = Some(Rc::new(Cell { size: half, tree: l.clone(), rest: Some(right) }));
        }
        self.top = top;
    }

    pub fn pop(&mut self) {
        if self.len > 0 {
            self.drop_inner(1);
        }
    }

    /// Keep the outermost `n` values.
    pub fn truncate(&mut self, n: usize) {
        if n < self.len {
            self.drop_inner(self.len - n);
        }
    }

    /// The outermost `n` values.
    pub fn prefix(&self, n: usize) -> Self {
        let mut e = self.clone();
        e.truncate(n);
        e
    }

    /// The value of de Bruijn index `i`: the `i`th from the innermost.
    pub fn var(&self, mut i: usize) -> &T {
        let mut c = self.top.as_deref();
        while let Some(cell) = c {
            if i < cell.size {
                return cell.tree.get(i, cell.size);
            }
            i -= cell.size;
            c = cell.rest.as_deref();
        }
        panic!("index {} out of an environment of {}", i, self.len)
    }

    /// The `i`th value from the innermost, if there are that many.
    pub fn nth(&self, i: usize) -> Option<&T> {
        (i < self.len).then(|| self.var(i))
    }

    /// The value at level `l`.
    pub fn get(&self, l: usize) -> Option<&T> {
        (l < self.len).then(|| self.var(self.len - 1 - l))
    }

    /// The innermost value.
    pub fn last(&self) -> Option<&T> {
        (self.len > 0).then(|| self.var(0))
    }

    /// The values, outermost first.
    pub fn iter(&self) -> std::vec::IntoIter<&T> {
        let mut out = Vec::with_capacity(self.len);
        let mut c = self.top.as_deref();
        while let Some(cell) = c {
            cell.tree.each(&mut out);
            c = cell.rest.as_deref();
        }
        out.reverse();
        out.into_iter()
    }

    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }
}

impl<T> std::ops::Index<usize> for List<T> {
    type Output = T;
    /// The value at level `l`.
    fn index(&self, l: usize) -> &T {
        assert!(l < self.len, "level {l} out of an environment of {}", self.len);
        self.var(self.len - 1 - l)
    }
}

impl<T> From<Vec<T>> for List<T> {
    fn from(vs: Vec<T>) -> Self {
        vs.into_iter().collect()
    }
}

impl<T: Clone> From<&[T]> for List<T> {
    fn from(vs: &[T]) -> Self {
        vs.iter().cloned().collect()
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        let mut e = List::new();
        for v in it {
            e.push(v);
        }
        e
    }
}

impl<T> Extend<T> for List<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, it: I) {
        for v in it {
            self.push(v);
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Lit;

    fn int(i: usize) -> Val {
        Val::Lit(Lit::Num(i as i128))
    }
    fn at(e: &Env, l: usize) -> i128 {
        match &e[l] {
            Val::Lit(Lit::Num(n)) => *n,
            _ => unreachable!(),
        }
    }

    #[test]
    fn push_index_truncate_agree_with_a_vector() {
        let mut e = Env::new();
        let mut v: Vec<usize> = Vec::new();
        let mut kept = Vec::new();
        for i in 0..300 {
            e.push(int(i));
            v.push(i);
            if i % 7 == 3 {
                let n = v.len() * 2 / 3;
                e.truncate(n);
                v.truncate(n);
            }
            if i % 11 == 0 {
                kept.push((e.clone(), v.clone()));
            }
            assert_eq!(e.len(), v.len());
            for (l, x) in v.iter().enumerate() {
                assert_eq!(at(&e, l), *x as i128);
            }
        }
        for (e, v) in kept {
            assert_eq!(e.iter().count(), v.len());
            for (l, x) in v.iter().enumerate() {
                assert_eq!(at(&e, l), *x as i128);
                assert_eq!(at(&e.prefix(l + 1), l), *x as i128);
            }
        }
    }
}
