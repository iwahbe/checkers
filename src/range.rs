//! Constant bounds of integers (D135): what the elaborator's intervals
//! compute for arithmetic (`elab::interval`), and what native code knows of
//! a value whose type bounds it, carried past erasure (`Globals::bounds`).

use crate::core::Prim;

/// Constant bounds, each possibly absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: Option<i128>,
    pub hi: Option<i128>,
}

impl Range {
    pub const ANY: Range = Range { lo: None, hi: None };

    pub fn exact(n: i128) -> Range {
        Range { lo: Some(n), hi: Some(n) }
    }

    /// The smallest range holding both.
    pub fn hull(self, o: Range) -> Range {
        Range { lo: self.lo.zip(o.lo).map(|(x, y)| x.min(y)), hi: self.hi.zip(o.hi).map(|(x, y)| x.max(y)) }
    }

    /// Does `self` hold every value of `o`?
    pub fn holds(self, o: Range) -> bool {
        let lo = match (self.lo, o.lo) {
            (None, _) => true,
            (Some(a), Some(b)) => a <= b,
            (Some(_), None) => false,
        };
        let hi = match (self.hi, o.hi) {
            (None, _) => true,
            (Some(a), Some(b)) => a >= b,
            (Some(_), None) => false,
        };
        lo && hi
    }

    pub fn meet(self, o: Range) -> Range {
        let lo = match (self.lo, o.lo) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
        let hi = match (self.hi, o.hi) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        Range { lo, hi }
    }
}

fn add(a: Option<i128>, b: Option<i128>) -> Option<i128> {
    a?.checked_add(b?)
}

fn sub(a: Option<i128>, b: Option<i128>) -> Option<i128> {
    a?.checked_sub(b?)
}

/// The range of `a op b` (D135 a); `nat_sub` for `Nat` subtraction, whose
/// obligation `a >= b` makes it non-negative.
pub fn combine(op: Prim, a: Range, b: Range, nat_sub: bool) -> Range {
    match op {
        Prim::Add => Range { lo: add(a.lo, b.lo), hi: add(a.hi, b.hi) },
        Prim::Sub => {
            let lo = sub(a.lo, b.hi);
            let lo = if nat_sub { Some(lo.map_or(0, |l| l.max(0))) } else { lo };
            Range { lo, hi: sub(a.hi, b.lo) }
        }
        Prim::Mul => match (a.lo, a.hi, b.lo, b.hi) {
            (Some(a0), Some(a1), Some(b0), Some(b1)) => {
                let ps = [a0.checked_mul(b0), a0.checked_mul(b1), a1.checked_mul(b0), a1.checked_mul(b1)];
                if ps.iter().any(|p| p.is_none()) {
                    return Range::ANY;
                }
                let ps = ps.map(|p| p.unwrap_or(0));
                Range { lo: ps.iter().min().copied(), hi: ps.iter().max().copied() }
            }
            // Both non-negative: at least the product of the lower bounds.
            (Some(a0), _, Some(b0), _) if a0 >= 0 && b0 >= 0 => {
                Range { lo: a0.checked_mul(b0), hi: a.hi.and_then(|x| b.hi.and_then(|y| x.checked_mul(y))) }
            }
            _ => Range::ANY,
        },
        // Euclidean division by a divisor known to be at least 1.
        Prim::Div => match (a.lo, b.lo) {
            (Some(a0), Some(b0)) if a0 >= 0 && b0 >= 1 => {
                Range { lo: Some(b.hi.map_or(0, |b1| a0 / b1)), hi: a.hi.map(|a1| a1 / b0) }
            }
            _ => Range::ANY,
        },
        // Euclidean remainder: `0 … |b| - 1`, never more than a
        // non-negative dividend.
        Prim::Rem => {
            let c = match (b.lo, b.hi) {
                (Some(b0), Some(b1)) if !(b0 <= 0 && 0 <= b1) => b0.checked_abs().zip(b1.checked_abs()).map(|(x, y)| x.max(y)),
                _ => None,
            };
            let hi = c.map(|c| c - 1);
            let hi = match (a.lo, a.hi) {
                (Some(a0), Some(a1)) if a0 >= 0 => Some(hi.map_or(a1, |h| h.min(a1))),
                _ => hi,
            };
            Range { lo: Some(0), hi }
        }
        _ => Range::ANY,
    }
}
