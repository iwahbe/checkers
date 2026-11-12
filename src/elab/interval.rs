//! Arithmetic keeps constant bounds (D135): the result of `+ - * / %` on
//! operands whose bounds are constants is that range, an anonymous
//! refinement `(n~Nat, 1 <= n, n <= 256)`, laid out in arrays by the
//! narrowest layout that holds it (D133 e).

use super::*;
use checkers_rt::array::Layout;

/// The branches of an `if` or `match` whose type is inferred, so far.
#[derive(Clone, Copy, Debug)]
pub enum Join {
    Empty,
    /// Every branch so far is a number with constant bounds: their hull.
    Range(Range),
    /// A branch that isn't.
    Other,
}

/// Constant bounds, each possibly absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: Option<i128>,
    pub hi: Option<i128>,
}

impl Range {
    const ANY: Range = Range { lo: None, hi: None };

    fn exact(n: i128) -> Range {
        Range { lo: Some(n), hi: Some(n) }
    }

    fn meet(self, o: Range) -> Range {
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

/// The narrowest array layout holding `r` (D135 d), as `Layout`'s code.
pub fn layout_for(r: Range) -> u8 {
    let (Some(lo), Some(hi)) = (r.lo, r.hi) else { return Layout::Words as u8 };
    let fits = |a: i128, b: i128| a <= lo && hi <= b;
    let l = if fits(0, 255) {
        Layout::U8
    } else if fits(-128, 127) {
        Layout::I8
    } else if fits(0, 65535) {
        Layout::U16
    } else if fits(0, u32::MAX as i128) {
        Layout::U32
    } else if fits(i32::MIN as i128, i32::MAX as i128) {
        Layout::I32
    } else if fits(0, u64::MAX as i128) {
        Layout::U64
    } else if fits(i64::MIN as i128, i64::MAX as i128) {
        Layout::I64
    } else {
        Layout::Words
    };
    l as u8
}

/// A constant term: a literal, or a negated one.
fn constant(t: &Tm) -> Option<i128> {
    match t {
        Tm::Lit(Lit::Num(n)) => Some(*n),
        Tm::PrimApp(Prim::Neg, a) => constant(a.first()?).and_then(|n| n.checked_neg()),
        _ => None,
    }
}

/// What a predicate about the subject (`Var(0)`) says of its bounds.
fn pred_range(t: &Tm) -> Range {
    let Tm::PrimApp(p, args) = t else { return Range::ANY };
    let (Some(a), Some(b)) = (args.first(), args.get(1)) else { return Range::ANY };
    let subject = |x: &Tm| matches!(x, Tm::Var(0));
    // Put it as `n op c`.
    let (op, c) = match (subject(a), subject(b), constant(a), constant(b)) {
        (true, _, _, Some(c)) => (p.clone(), c),
        (_, true, Some(c), _) => (
            match p {
                Prim::Lt => Prim::Gt,
                Prim::Le => Prim::Ge,
                Prim::Gt => Prim::Lt,
                Prim::Ge => Prim::Le,
                other => other.clone(),
            },
            c,
        ),
        _ => return Range::ANY,
    };
    match op {
        Prim::Lt => Range { lo: None, hi: c.checked_sub(1) },
        Prim::Le => Range { lo: None, hi: Some(c) },
        Prim::Gt => Range { lo: c.checked_add(1), hi: None },
        Prim::Ge => Range { lo: Some(c), hi: None },
        Prim::Eq => Range::exact(c),
        _ => Range::ANY,
    }
}

impl Elab {
    /// The constant bounds of a number type, if it is one: its aliases'
    /// predicates, down to `Int`.
    pub fn type_range(&self, ty: &Val) -> Option<Range> {
        let mut r = Range::ANY;
        let mut v = crate::core::force_meta(&self.g, ty.clone());
        for _ in 0..64 {
            if let Val::Neutral(Head::Def(d), sp) = &v {
                if sp.is_empty() {
                    if let Some(preds) = self.alias_preds.get(d) {
                        for p in preds {
                            r = r.meet(pred_range(&p.tm));
                        }
                    }
                }
            }
            match crate::core::unfold(&self.g, &v) {
                Some(u) => v = crate::core::force_meta(&self.g, u),
                None => break,
            }
        }
        match v {
            Val::TyCon(id, _) if Some(id) == self.g.well_known.int => Some(r),
            _ => None,
        }
    }

    /// An operand's bounds: a constant's own, else its type's.
    pub fn operand_range(&self, t: &Tm, ty: &Val) -> Option<Range> {
        match constant(t) {
            Some(c) => Some(Range::exact(c)),
            None => self.type_range(ty),
        }
    }

    /// The type of a range (D135 c): `Nat`, `Int`, or an anonymous
    /// refinement of one, made once per range.
    pub fn range_type(&mut self, r: Range) -> Val {
        let nat = r.lo.is_some_and(|l| l >= 0);
        if r == (Range { lo: if nat { Some(0) } else { None }, hi: None }) {
            return if nat { self.nat() } else { self.int() };
        }
        if let Some(d) = self.ranges.get(&(r.lo, r.hi)) {
            return eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(*d));
        }
        let mut preds = Vec::new();
        let lit = |n: i128| if n < 0 { Tm::PrimApp(Prim::Neg, vec![Tm::Lit(Lit::Num(-n))]) } else { Tm::Lit(Lit::Num(n)) };
        let mut pred = |tm: Tm, text: String| {
            preds.push(Pred { tm, text, span: Span::default(), is_post: false, alias: None });
        };
        match (r.lo, r.hi) {
            // One value: `n == c`.
            (Some(lo), Some(hi)) if lo == hi => pred(Tm::PrimApp(Prim::Eq, vec![Tm::Var(0), lit(lo)]), format!("n == {lo}")),
            _ => {
                if let Some(lo) = r.lo.filter(|l| !nat || *l > 0) {
                    pred(Tm::PrimApp(Prim::Le, vec![lit(lo), Tm::Var(0)]), format!("{lo} <= n"));
                }
                if let Some(hi) = r.hi {
                    pred(Tm::PrimApp(Prim::Le, vec![Tm::Var(0), lit(hi)]), format!("n <= {hi}"));
                }
            }
        }
        let (base, base_text) = match (nat, self.g.well_known.nat, self.g.well_known.int) {
            (true, Some(n), _) => (Tm::Def(n), "Nat"),
            (_, _, Some(i)) => (Tm::TyCon(i), "Int"),
            _ => return self.int(),
        };
        let text = format!("(n~{base_text}, {})", preds.iter().map(|p| p.text.as_str()).collect::<Vec<_>>().join(", "));
        let did = self.new_def(&text);
        let info = &mut self.g.defs[did.0 as usize];
        info.body = Some(base);
        info.ty = Tm::Univ(0);
        self.alias_preds.insert(did, preds);
        self.alias_subject.insert(did, Rc::from("n"));
        self.g.well_known.layouts.push((did, layout_for(r)));
        self.ranges.insert((r.lo, r.hi), did);
        eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(did))
    }

    /// The join placeholder `expected` is, if it is one (before the first
    /// branch decides it).
    pub fn join_of(&self, expected: &Val) -> Option<MetaId> {
        match expected {
            Val::Neutral(Head::Meta(m), _) if self.joins.contains_key(m) => Some(*m),
            _ => None,
        }
    }

    pub fn join_branch(&mut self, m: MetaId, r: Option<Range>) {
        let j = match (self.joins.get(&m).copied(), r) {
            (Some(Join::Empty), Some(r)) => Join::Range(r),
            (Some(Join::Range(a)), Some(b)) => Join::Range(Range {
                lo: a.lo.zip(b.lo).map(|(x, y)| x.min(y)),
                hi: a.hi.zip(b.hi).map(|(x, y)| x.max(y)),
            }),
            _ => Join::Other,
        };
        self.joins.insert(m, j);
    }

    /// Is `ty` a range this rule made (D135)?
    pub fn is_range(&self, ty: &Val) -> bool {
        matches!(crate::core::force_meta(&self.g, ty.clone()), Val::Neutral(Head::Def(d), _) if self.ranges.values().any(|r| *r == d))
    }

    /// The type an operator's other operand is checked against: a range's
    /// base, so ranges don't spread through it (D135).
    pub fn shared_operand_type(&self, ty: &Val) -> Val {
        if self.is_range(ty) { self.arith_base(ty) } else { ty.clone() }
    }

    /// The type of `lt op rt` (D134, D135): `ty` is the operands' shared
    /// type, `lty` and `rty` their own.
    pub fn arith_type(&mut self, op: Prim, lt: &Tm, rt: &Tm, ty: &Val, lty: &Val, rty: &Val) -> Val {
        let nat_sub = op == Prim::Sub && crate::core::is_nat(&self.g, ty);
        match (self.operand_range(lt, lty), self.operand_range(rt, rty)) {
            (Some(a), Some(b)) => {
                let r = combine(op, a, b, nat_sub);
                // Never wider than D134's base: `Nat` stays `Nat`.
                let base_nat = crate::core::is_nat(&self.g, ty);
                let r = if base_nat { r.meet(Range { lo: Some(0), hi: None }) } else { r };
                self.range_type(r)
            }
            _ => self.arith_base(ty),
        }
    }
}
