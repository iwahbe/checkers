//! Results returned as their parts (SPEC §14): an optimization over
//! closure-converted code, after `tailrec` and before reference counting.
//! A function whose every result is a constructor value it builds, which
//! its callers take apart at once (`match p xs | Ok (v, rest) -> …`), need
//! not build it: it can return the constructor and its fields in registers,
//! and the caller can use them where it would have read them from the
//! value. This is constructed product result analysis (Baker-Finch, Glynn
//! and Peyton Jones, "Constructed Product Result Analysis for Haskell",
//! JFP 2004) with sums and nesting, as GHC's worker/wrapper split does it.
//!
//! - **A value's layout** (`Shape`) is what is known of every value an
//!   expression can give: built by a constructor (and which), a tuple, or
//!   unknown (`Boxed`). A constructor's layout is a word naming it (the
//!   word its value would be if it had no fields) followed by its fields'
//!   layouts; the constructors of a type share the words after the first.
//!   A field built in place is laid out in turn: `Ok (v, rest)` is three
//!   words, `Ok`, `v` and `rest`. Words a constructor doesn't use are 0.
//! - **Functions** (`f`): when every path of `f` ends in a constructor or
//!   tuple it builds, a failure, or a call in tail position of another such
//!   function, and some caller takes `f`'s result apart, `f`'s code moves to
//!   `f.parts`, which returns the parts. Functions calling each other in
//!   tail position share one layout. `f` itself calls `f.parts` and builds
//!   the value from them, for the callers that need it as a value
//!   (closures, other functions' tail calls). A caller's `let` taking
//!   apart both values it builds and such functions' results (`match`
//!   on an inlined function that tail-calls one) gives those functions a
//!   layout with room for the values built there.
//! - **Callers**: `let x = e` where every value `e` can give is built there
//!   or returned as parts by a call, and the code after it only takes `x`
//!   apart (`match x`, a field, a tuple's components), binds the parts to
//!   variables instead; `match x` chooses by the word naming the
//!   constructor. A field that is itself laid out is taken apart the same
//!   way, or built where it is needed whole.
//!
//! Each part is owned, as the field of a value no one else holds would be,
//! so reference counting treats the parts as it treats any variables. It
//! changes no result, failure, or order of effects: the parts are computed
//! in the order the fields were, and nothing can tell a value built anew
//! from the one that wasn't built.

use super::lower::*;
use std::collections::HashMap;
use std::sync::Arc;

/// At most this many words returned: what the `tail` calling convention
/// returns in registers on x86-64 and ARM64.
pub const MAX_PARTS: usize = 8;

/// What is known of every value an expression can give.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Shape {
    /// None: it fails.
    Bottom,
    /// A value, nothing known: one word.
    Boxed,
    /// Built by one of these constructors (sorted), with its fields' layouts.
    Con(Vec<(u32, Vec<Shape>)>),
    /// A tuple of these components.
    Tuple(Vec<Shape>),
}

impl Shape {
    /// How many words it takes.
    pub fn size(&self) -> usize {
        match self {
            Shape::Bottom => 0,
            Shape::Boxed => 1,
            Shape::Con(cs) => 1 + cs.iter().map(|(_, fs)| fs.iter().map(Shape::size).sum::<usize>()).max().unwrap_or(0),
            Shape::Tuple(xs) => xs.iter().map(Shape::size).sum(),
        }
    }

    /// What is known of a value that is one or the other.
    fn join(self, o: Shape) -> Shape {
        match (self, o) {
            (Shape::Bottom, x) | (x, Shape::Bottom) => x,
            (Shape::Con(mut out), Shape::Con(b)) => {
                for (c, fs) in b {
                    match out.iter_mut().find(|(d, _)| *d == c) {
                        Some((_, gs)) => {
                            if gs.len() != fs.len() {
                                return Shape::Boxed;
                            }
                            let old = std::mem::take(gs);
                            *gs = old.into_iter().zip(fs).map(|(x, y)| x.join(y)).collect();
                        }
                        None => out.push((c, fs)),
                    }
                }
                out.sort_by_key(|(c, _)| *c);
                Shape::Con(out)
            }
            (Shape::Tuple(a), Shape::Tuple(b)) if a.len() == b.len() => Shape::Tuple(a.into_iter().zip(b).map(|(x, y)| x.join(y)).collect()),
            _ => Shape::Boxed,
        }
    }

    /// Parts nested more than `d` deep boxed (the outermost is 1 deep).
    fn prune(&self, d: usize) -> Shape {
        match self {
            Shape::Con(_) | Shape::Tuple(_) if d == 0 => Shape::Boxed,
            Shape::Con(cs) => Shape::Con(cs.iter().map(|(c, fs)| (*c, fs.iter().map(|f| f.prune(d - 1)).collect())).collect()),
            Shape::Tuple(xs) => Shape::Tuple(xs.iter().map(|x| x.prune(d - 1)).collect()),
            other => other.clone(),
        }
    }

    /// The layout to return or bind: as deep as fits in `MAX_PARTS` words,
    /// if that is worth it (a constructor with fields, or a tuple).
    fn fit(&self) -> Option<Shape> {
        if !matches!(self, Shape::Con(_) | Shape::Tuple(_)) {
            return None;
        }
        let s = (1..=4).rev().map(|d| self.prune(d)).find(|s| s.size() <= MAX_PARTS)?;
        (s.size() >= 2).then_some(s)
    }

    /// Where constructor `k`'s fields start, and each field's layout.
    fn fields(&self, k: usize) -> Vec<(usize, &Shape)> {
        let Shape::Con(cs) = self else { unreachable!("fields of a constructor layout") };
        let mut at = 1;
        cs[k].1.iter().map(|f| {
            let r = (at, f);
            at += f.size();
            r
        }).collect()
    }

    /// Where each tuple component starts, and its layout.
    fn components(&self) -> Vec<(usize, &Shape)> {
        let Shape::Tuple(xs) = self else { unreachable!("components of a tuple layout") };
        let mut at = 0;
        xs.iter().map(|f| {
            let r = (at, f);
            at += f.size();
            r
        }).collect()
    }
}

/// The constructor a word names, if it names one without fields.
fn nullary_con(w: u64) -> Option<u32> {
    (w & 7 == 2).then_some((w >> 3) as u32)
}

fn static_shape(s: &Static) -> Shape {
    match s {
        Static::Word(w) => nullary_con(*w).map_or(Shape::Boxed, |c| Shape::Con(vec![(c, Vec::new())])),
        Static::Con(c, xs) => Shape::Con(vec![(*c, xs.iter().map(|x| static_shape(x)).collect())]),
        Static::Tuple(xs) => tuple_shape(xs.iter().map(|x| static_shape(x)).collect()),
        _ => Shape::Boxed,
    }
}

/// A tuple's layout. Its last component is kept whole when it is a tuple:
/// at run time, `(a, (b, c))` is `(a, b, c)`.
fn tuple_shape(mut xs: Vec<Shape>) -> Shape {
    if let Some(l @ Shape::Tuple(_)) = xs.last_mut() {
        *l = Shape::Boxed;
    }
    Shape::Tuple(xs)
}

/// What is known of the value of `e`, an expression that is a field.
fn value_shape(e: &E) -> Shape {
    match e {
        E::Con { con, fields, reuse: None } => Shape::Con(vec![(*con, fields.iter().map(value_shape).collect())]),
        E::Tuple(xs) if xs.len() >= 2 => tuple_shape(xs.iter().map(value_shape).collect()),
        E::Static(s) => static_shape(s),
        _ => Shape::Boxed,
    }
}

/// The expressions in tail position of `e`: the values it can give.
fn leaves<'a>(e: &'a E, f: &mut dyn FnMut(&'a E)) {
    match e {
        E::Let(_, _, b) | E::LetMulti(_, _, b) | E::At(_, b) => leaves(b, f),
        E::Case { arms, lits, default, .. } => {
            for a in arms {
                leaves(&a.body, f);
            }
            for (_, b) in lits {
                leaves(b, f);
            }
            if let Some(d) = default {
                leaves(d, f);
            }
        }
        _ => f(e),
    }
}

/// A word as an expression.
fn word_expr(w: u64) -> E {
    use checkers_rt::word as rw;
    if w == rw::ERASED {
        E::Erased
    } else if w == rw::UNIT {
        E::Unit
    } else if rw::is_int(w) {
        E::Int(rw::int_of(w))
    } else if let Some(c) = nullary_con(w) {
        E::Con { con: c, fields: Vec::new(), reuse: None }
    } else {
        E::Static(Arc::new(Static::Word(w)))
    }
}

fn static_expr(s: &Arc<Static>) -> E {
    match &**s {
        Static::Word(w) => word_expr(*w),
        _ => E::Static(s.clone()),
    }
}

/// The parts of `e`, a value laid out as `s`, in order.
fn flatten(e: E, s: &Shape, out: &mut Vec<E>) {
    match s {
        Shape::Boxed => out.push(e),
        Shape::Bottom => unreachable!("a value laid out as nothing"),
        Shape::Con(cs) => {
            let start = out.len();
            let (con, fields): (u32, Vec<E>) = match e {
                E::Con { con, fields, reuse: None } => (con, fields),
                E::Static(st) => match &*st {
                    Static::Con(c, xs) => (*c, xs.iter().map(static_expr).collect()),
                    Static::Word(w) => (nullary_con(*w).expect("a constructor's word"), Vec::new()),
                    _ => unreachable!("a static constructor"),
                },
                _ => unreachable!("a constructor laid out"),
            };
            let k = cs.iter().position(|(c, _)| *c == con).expect("a constructor of the layout");
            out.push(E::Con { con, fields: Vec::new(), reuse: None });
            for (f, fs) in fields.into_iter().zip(&cs[k].1) {
                flatten(f, fs, out);
            }
            out.resize(start + s.size(), E::Erased);
        }
        Shape::Tuple(ss) => {
            let xs: Vec<E> = match e {
                E::Tuple(xs) => xs,
                E::Static(st) => match &*st {
                    Static::Tuple(xs) => xs.iter().map(static_expr).collect(),
                    _ => unreachable!("a static tuple"),
                },
                _ => unreachable!("a tuple laid out"),
            };
            for (x, xs) in xs.into_iter().zip(ss) {
                flatten(x, xs, out);
            }
        }
    }
}

/// The value laid out as `s` in the variables `vs`, built.
fn rebox(s: &Shape, vs: &[V]) -> E {
    match s {
        Shape::Boxed => E::Var(vs[0]),
        Shape::Bottom => unreachable!("a value laid out as nothing"),
        Shape::Tuple(_) => E::Tuple(s.components().into_iter().map(|(at, f)| rebox(f, &vs[at..at + f.size()])).collect()),
        Shape::Con(cs) => {
            if cs.iter().all(|(_, fs)| fs.is_empty()) {
                return E::Var(vs[0]);
            }
            let build = |k: usize| {
                let fields = s.fields(k).into_iter().map(|(at, f)| rebox(f, &vs[at..at + f.size()])).collect();
                E::Con { con: cs[k].0, fields, reuse: None }
            };
            if cs.len() == 1 {
                return build(0);
            }
            // A constructor without fields is its word.
            let arms: Vec<Arm> = (0..cs.len()).filter(|k| !cs[*k].1.is_empty()).map(|k| Arm { con: cs[k].0, fields: Vec::new(), body: build(k) }).collect();
            let default = (arms.len() < cs.len()).then(|| Box::new(E::Var(vs[0])));
            E::Case { scrut: vs[0], arms, lits: Vec::new(), default }
        }
    }
}

/// The part of a value laid out as `s` (in `vs`) that `op` reads, if it
/// reads one: a constructor's field, or a tuple's component (the last
/// only as the rest from it: a tuple whose last component is a tuple has
/// more components at run time).
fn part<'a>(s: &'a Shape, vs: &'a [V], op: &BOp) -> Option<(&'a Shape, &'a [V])> {
    let (at, f) = match (s, op) {
        (Shape::Con(cs), BOp::Field(i)) if cs.len() == 1 && *i < cs[0].1.len() => s.fields(0)[*i],
        (Shape::Tuple(xs), BOp::Proj(i)) if i + 1 < xs.len() => s.components()[*i],
        (Shape::Tuple(xs), BOp::ProjRest(i)) if i + 1 == xs.len() => s.components()[*i],
        _ => return None,
    };
    Some((f, vs.get(at..at + f.size())?))
}

/// `Let(y, op(x), b)` reading a part of `x`: `op` and `y`.
fn reads(e: &E, x: V) -> Option<(&BOp, V, &E)> {
    let E::Let(y, a, b) = e else { return None };
    let E::Borrow { op, args, .. } = &**a else { return None };
    matches!(args.as_slice(), [E::Var(v)] if *v == x).then_some((op, *y, b))
}

/// Whether `e` only takes `x` (laid out as `s`) apart.
fn taken_apart(x: V, s: &Shape, e: &E) -> bool {
    if let Some((op, _, b)) = reads(e, x) {
        return part(s, &[0; MAX_PARTS], op).is_some() && taken_apart(x, s, b);
    }
    let ok = |e: &E| taken_apart(x, s, e);
    match e {
        E::Var(v) => *v != x,
        E::Let(_, a, b) | E::LetMulti(_, a, b) => ok(a) && ok(b),
        E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => args.iter().all(ok),
        E::Apply { f, args, .. } => ok(f) && args.iter().all(ok),
        E::MkClo { captured, .. } => !captured.contains(&x),
        E::Con { fields, reuse, .. } => *reuse != Some(x) && fields.iter().all(ok),
        E::Borrow { args, drops, .. } => !drops.contains(&x) && args.iter().all(ok),
        E::Case { scrut, arms, lits, default } => {
            (*scrut != x || matches!(s, Shape::Con(_)) && lits.is_empty())
                && arms.iter().all(|a| ok(&a.body))
                && lits.iter().all(|(l, b)| ok(l) && ok(b))
                && default.as_deref().is_none_or(ok)
        }
        E::At(_, b) => ok(b),
        E::Dup(v, b) | E::Drop(v, b) => *v != x && ok(b),
        E::DropReuse(v, t, _, b) => *v != x && *t != x && ok(b),
        E::Int(_) | E::BigLit(_) | E::Str(_) | E::Bytes(_) | E::Static(_) | E::Erased | E::Unit | E::Global(_) | E::ConFn(_) | E::Fail(_) => true,
    }
}

/// Rewrites one function's code.
struct Rw<'a> {
    workers: &'a HashMap<u32, (u32, Shape)>,
    next: V,
}

impl Rw<'_> {
    fn fresh(&mut self, n: usize) -> Vec<V> {
        let vs = (self.next..self.next + n as V).collect();
        self.next += n as V;
        vs
    }

    /// The layout for `let x = a`, if every value `a` gives is built there
    /// or returned as parts; and whether all of them are returned as parts.
    fn let_shape(&self, a: &E) -> Option<(Shape, bool)> {
        let mut j = Shape::Bottom;
        let mut calls = Vec::new();
        let mut built = false;
        let mut bad = false;
        leaves(a, &mut |l| match l {
            E::Call { f, .. } => match self.workers.get(f) {
                Some((_, s)) => calls.push(s),
                None => bad = true,
            },
            E::Fail(_) => {}
            E::Con { .. } | E::Tuple(_) | E::Static(_) => {
                built = true;
                j = std::mem::replace(&mut j, Shape::Bottom).join(value_shape(l));
            }
            _ => bad = true,
        });
        if bad {
            return None;
        }
        for s in &calls {
            j = j.join((*s).clone());
        }
        let s = j.fit()?;
        calls.iter().all(|c| **c == s).then_some((s, !built && !calls.is_empty()))
    }

    /// `e`'s values, laid out as `s`, as parts: built ones as `Multi`,
    /// calls to the functions returning parts.
    fn to_parts(&self, e: E, s: &Shape, tail: bool) -> E {
        match e {
            E::Let(x, a, b) => E::Let(x, a, Box::new(self.to_parts(*b, s, tail))),
            E::LetMulti(xs, a, b) => E::LetMulti(xs, a, Box::new(self.to_parts(*b, s, tail))),
            E::At(o, b) => E::At(o, Box::new(self.to_parts(*b, s, tail))),
            E::Case { scrut, arms, lits, default } => E::Case {
                scrut,
                arms: arms.into_iter().map(|a| Arm { body: self.to_parts(a.body, s, tail), ..a }).collect(),
                lits: lits.into_iter().map(|(l, b)| (l, self.to_parts(b, s, tail))).collect(),
                default: default.map(|d| Box::new(self.to_parts(*d, s, tail))),
            },
            E::Call { f, args, .. } => {
                let (w, ws) = &self.workers[&f];
                debug_assert_eq!(ws, s);
                E::Call { f: *w, args, tail }
            }
            E::Fail(m) => E::Fail(m),
            leaf => {
                let mut out = Vec::new();
                flatten(leaf, s, &mut out);
                E::Multi(out)
            }
        }
    }

    /// `x`, laid out as `s` in `vs`, bound for `body`: taken apart there,
    /// or built.
    fn bind(&mut self, x: V, s: &Shape, vs: &[V], body: E) -> E {
        match s {
            Shape::Boxed => E::Let(x, Box::new(E::Var(vs[0])), Box::new(body)),
            _ if taken_apart(x, s, &body) => self.subst(x, s, vs, body),
            _ => E::Let(x, Box::new(rebox(s, vs)), Box::new(body)),
        }
    }

    /// `e`, which only takes `x` apart, reading `x`'s parts from `vs`.
    fn subst(&mut self, x: V, s: &Shape, vs: &[V], e: E) -> E {
        if let Some((op, y, _)) = reads(&e, x) {
            let (op, y) = (*op, y);
            let E::Let(_, _, b) = e else { unreachable!() };
            let (fs, fvs) = part(s, vs, &op).expect("a part taken apart");
            let (fs, fvs) = (fs.clone(), fvs.to_vec());
            let b = self.subst(x, s, vs, *b);
            return self.bind(y, &fs, &fvs, b);
        }
        match e {
            E::Case { scrut, arms, lits: _, default } if scrut == x => {
                let Shape::Con(cs) = s else { unreachable!("a match on a constructor layout") };
                let mut arms2 = Vec::new();
                for a in arms {
                    // A constructor the value is never built by: never chosen.
                    let Some(k) = cs.iter().position(|(c, _)| *c == a.con) else { continue };
                    let mut body = self.subst(x, s, vs, a.body);
                    let fields = s.fields(k);
                    for (i, f) in a.fields.iter().enumerate().rev() {
                        if let Some(v) = f {
                            let (at, fs) = fields[i];
                            body = self.bind(*v, fs, &vs[at..at + fs.size()], body);
                        }
                    }
                    arms2.push(Arm { con: a.con, fields: Vec::new(), body });
                }
                let default = default.map(|d| Box::new(self.subst(x, s, vs, *d)));
                if cs.len() == 1 && arms2.len() == 1 {
                    return arms2.pop().unwrap().body;
                }
                if arms2.is_empty() {
                    if let Some(d) = default {
                        return *d;
                    }
                }
                E::Case { scrut: vs[0], arms: arms2, lits: Vec::new(), default }
            }
            other => map_children(other, &mut |c| self.subst(x, s, vs, c)),
        }
    }

    /// Callers' code: `let`s whose values are taken apart bind their
    /// parts; other calls of functions returning parts build the value.
    fn local(&mut self, e: E, tail: bool) -> E {
        match e {
            E::Let(x, a, b) => {
                // Calls `a` ends in stay calls, to be taken apart here.
                let a = self.local(*a, true);
                let b = self.local(*b, tail);
                if let Some((s, all_calls)) = self.let_shape(&a) {
                    if taken_apart(x, &s, &b) {
                        let vs = self.fresh(s.size());
                        let a = self.to_parts(a, &s, false);
                        let b = self.subst(x, &s, &vs, b);
                        return E::LetMulti(vs, Box::new(a), Box::new(b));
                    }
                    if all_calls {
                        let vs = self.fresh(s.size());
                        let a = self.to_parts(a, &s, false);
                        return E::LetMulti(vs.clone(), Box::new(a), Box::new(E::Let(x, Box::new(rebox(&s, &vs)), Box::new(b))));
                    }
                }
                E::Let(x, Box::new(a), Box::new(b))
            }
            // A call whose value is needed: its parts, built (what `f`
            // itself would do). A tail call stays one.
            E::Call { f, args, tail: t } if !tail && self.workers.contains_key(&f) => {
                let args = args.into_iter().map(|a| self.local(a, false)).collect();
                let (w, s) = self.workers[&f].clone();
                let vs = self.fresh(s.size());
                E::LetMulti(vs.clone(), Box::new(E::Call { f: w, args, tail: t }), Box::new(rebox(&s, &vs)))
            }
            E::LetMulti(xs, a, b) => E::LetMulti(xs, Box::new(self.local(*a, false)), Box::new(self.local(*b, tail))),
            E::At(o, b) => E::At(o, Box::new(self.local(*b, tail))),
            E::Case { scrut, arms, lits, default } => E::Case {
                scrut,
                arms: arms.into_iter().map(|a| Arm { body: self.local(a.body, tail), ..a }).collect(),
                lits: lits.into_iter().map(|(l, b)| (l, self.local(b, tail))).collect(),
                default: default.map(|d| Box::new(self.local(*d, tail))),
            },
            other => map_children(other, &mut |c| self.local(c, false)),
        }
    }
}

/// `e` with `f` applied to each child expression.
fn map_children(e: E, f: &mut dyn FnMut(E) -> E) -> E {
    match e {
        E::Let(x, a, b) => {
            let a = f(*a);
            E::Let(x, Box::new(a), Box::new(f(*b)))
        }
        E::LetMulti(xs, a, b) => {
            let a = f(*a);
            E::LetMulti(xs, Box::new(a), Box::new(f(*b)))
        }
        E::Call { f: g, args, tail } => E::Call { f: g, args: args.into_iter().map(&mut *f).collect(), tail },
        E::Apply { f: g, args, tail } => {
            let g = f(*g);
            E::Apply { f: Box::new(g), args: args.into_iter().map(&mut *f).collect(), tail }
        }
        E::Con { con, fields, reuse } => E::Con { con, fields: fields.into_iter().map(&mut *f).collect(), reuse },
        E::Tuple(xs) => E::Tuple(xs.into_iter().map(&mut *f).collect()),
        E::Multi(xs) => E::Multi(xs.into_iter().map(&mut *f).collect()),
        E::Par(xs) => E::Par(xs.into_iter().map(&mut *f).collect()),
        E::Borrow { op, args, drops } => E::Borrow { op, args: args.into_iter().map(&mut *f).collect(), drops },
        E::Case { scrut, arms, lits, default } => E::Case {
            scrut,
            arms: arms.into_iter().map(|a| Arm { body: f(a.body), ..a }).collect(),
            lits: lits.into_iter().map(|(l, b)| (l, f(b))).collect(),
            default: default.map(|d| Box::new(f(*d))),
        },
        E::At(o, b) => E::At(o, Box::new(f(*b))),
        E::Dup(v, b) => E::Dup(v, Box::new(f(*b))),
        E::Drop(v, b) => E::Drop(v, Box::new(f(*b))),
        E::DropReuse(v, t, n, b) => E::DropReuse(v, t, n, Box::new(f(*b))),
        leaf => leaf,
    }
}

/// What one function's paths end in.
enum Ends {
    /// Values it builds (joined), and functions it calls in tail position.
    Built(Shape, Vec<u32>),
    /// Something else: it can't return parts.
    Other,
}

fn ends(f: &Func) -> Ends {
    if !matches!(f.kind, FnKind::Global) || f.rets != 1 {
        return Ends::Other;
    }
    let mut s = Shape::Bottom;
    let mut calls = Vec::new();
    let mut other = false;
    leaves(&f.body, &mut |l| match l {
        E::Call { f, .. } => calls.push(*f),
        E::Fail(_) => {}
        E::Con { .. } | E::Tuple(_) | E::Static(_) => s = std::mem::replace(&mut s, Shape::Bottom).join(value_shape(l)),
        _ => other = true,
    });
    if other {
        Ends::Other
    } else {
        Ends::Built(s, calls)
    }
}

fn find(up: &mut [usize], i: usize) -> usize {
    let mut r = i;
    while up[r] != r {
        r = up[r];
    }
    let mut j = i;
    while up[j] != r {
        let n = up[j];
        up[j] = r;
        j = n;
    }
    r
}

/// Rewrite the functions in `p.funcs[from..]`, adding `.parts` functions.
pub fn program(p: &mut Program, from: usize) {
    let end = p.funcs.len();
    let n = end - from;
    let local = |i: u32| (i as usize) >= from && (i as usize) < end;
    // Which functions can return parts: every path ends in a value built
    // there or a tail call of another that can (the greatest such set).
    let info: Vec<Ends> = p.funcs[from..end].iter().map(ends).collect();
    let mut can: Vec<bool> = info.iter().map(|e| matches!(e, Ends::Built(..))).collect();
    loop {
        let mut changed = false;
        for k in 0..n {
            if let (true, Ends::Built(_, calls)) = (can[k], &info[k]) {
                if calls.iter().any(|c| !local(*c) || !can[*c as usize - from]) {
                    can[k] = false;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // Functions calling each other in tail position share a layout.
    let mut up: Vec<usize> = (0..n).collect();
    for k in 0..n {
        if let (true, Ends::Built(_, calls)) = (can[k], &info[k]) {
            for c in calls {
                let (a, b) = (find(&mut up, k), find(&mut up, *c as usize - from));
                up[a] = b;
            }
        }
    }
    let class_shapes = |up: &mut [usize], extra: &[(usize, Shape)]| {
        let mut shapes: HashMap<usize, Shape> = HashMap::new();
        let built = (0..n).filter_map(|k| match (can[k], &info[k]) {
            (true, Ends::Built(s, _)) => Some((k, s)),
            _ => None,
        });
        for (k, s) in built.chain(extra.iter().map(|(k, s)| (*k, s))) {
            let r = find(up, k);
            let old = shapes.remove(&r).unwrap_or(Shape::Bottom);
            shapes.insert(r, old.join(s.clone()));
        }
        shapes
    };
    // A caller's `let` taking apart what such functions return and values
    // it builds itself: those functions share a layout that has room for
    // the values built there.
    let mut extra: Vec<(usize, Shape)> = Vec::new();
    {
        let shapes = class_shapes(&mut up, &[]);
        let mut joins: Vec<(Vec<usize>, Shape)> = Vec::new();
        for f in &p.funcs[from..end] {
            lets(&f.body, &mut |x, a, b| {
                let (mut ks, mut built, mut ok) = (Vec::new(), Shape::Bottom, true);
                leaves(a, &mut |l| match l {
                    E::Call { f, .. } if local(*f) && can[*f as usize - from] => ks.push(*f as usize - from),
                    E::Fail(_) => {}
                    E::Con { .. } | E::Tuple(_) | E::Static(_) => built = std::mem::replace(&mut built, Shape::Bottom).join(value_shape(l)),
                    _ => ok = false,
                });
                if !ok || ks.is_empty() || built == Shape::Bottom {
                    return;
                }
                let mut s = built.clone();
                for k in &ks {
                    let mut u = up.clone();
                    s = s.join(shapes.get(&find(&mut u, *k)).cloned().unwrap_or(Shape::Bottom));
                }
                if s.fit().is_some_and(|s| taken_apart(x, &s, b)) {
                    joins.push((ks, built));
                }
            });
        }
        for (ks, built) in joins {
            for k in &ks[1..] {
                let (a, b) = (find(&mut up, *k), find(&mut up, ks[0]));
                up[a] = b;
            }
            extra.push((ks[0], built));
        }
    }
    let shapes = class_shapes(&mut up, &extra);
    let shapes: HashMap<usize, Shape> = shapes.into_iter().filter_map(|(r, s)| s.fit().map(|s| (r, s))).collect();
    // The candidates, as if each returned parts; those some caller takes
    // apart are kept.
    let mut cands: HashMap<u32, (u32, Shape)> = p.workers.clone();
    for (k, c) in can.iter().enumerate() {
        if let (true, Some(s)) = (*c, shapes.get(&find(&mut up, k))) {
            cands.insert((from + k) as u32, (0, s.clone()));
        }
    }
    let mut wanted = std::collections::HashSet::new();
    {
        let rw = Rw { workers: &cands, next: 0 };
        for f in &p.funcs[from..end] {
            wants(&rw, &f.body, &mut |g| {
                if local(g) && cands.contains_key(&g) {
                    wanted.insert(find(&mut up, g as usize - from));
                }
            });
        }
    }
    // The `.parts` functions, with the code of the functions they replace:
    // every function of a layout some caller takes apart.
    let mut workers = Vec::new();
    for k in 0..n {
        let i = from + k;
        if !wanted.contains(&find(&mut up, k)) {
            continue;
        }
        let Some((_, s)) = cands.get(&(i as u32)) else { continue };
        let w = p.funcs.len() as u32;
        let f = &p.funcs[i];
        let worker = Func { name: format!("{}.parts", f.name), rets: s.size(), ..f.clone() };
        p.funcs.push(worker);
        p.workers.insert(i as u32, (w, s.clone()));
        workers.push(i);
    }
    let layouts: HashMap<u32, Shape> = p.workers.values().map(|(w, s)| (*w, s.clone())).collect();
    for i in from..p.funcs.len() {
        if workers.contains(&i) {
            continue;
        }
        let mut rw = Rw { workers: &p.workers, next: p.funcs[i].nvars };
        let body = std::mem::replace(&mut p.funcs[i].body, E::Erased);
        let mut body = rw.local(body, true);
        if p.funcs[i].rets > 1 {
            body = rw.to_parts(body, &layouts[&(i as u32)], true);
        }
        p.funcs[i].body = body;
        p.funcs[i].nvars = rw.next;
    }
    // Each replaced function: its `.parts`, built.
    for i in workers {
        let (w, s) = p.workers[&(i as u32)].clone();
        let f = &mut p.funcs[i];
        let vs: Vec<V> = (f.nvars..f.nvars + s.size() as V).collect();
        f.nvars += s.size() as V;
        let call = E::Call { f: w, args: f.params.iter().map(|v| E::Var(*v)).collect(), tail: false };
        f.body = E::LetMulti(vs.clone(), Box::new(call), Box::new(rebox(&s, &vs)));
    }
}

/// Each `let x = a in b` in `e`.
fn lets(e: &E, f: &mut dyn FnMut(V, &E, &E)) {
    if let E::Let(x, a, b) = e {
        f(*x, a, b);
    }
    visit_children(e, &mut |c| lets(c, f));
}

/// Calls of candidates whose values `e`'s `let`s take apart.
fn wants(rw: &Rw, e: &E, out: &mut dyn FnMut(u32)) {
    if let E::Let(x, a, b) = e {
        if let Some((s, _)) = rw.let_shape(a) {
            if taken_apart(*x, &s, b) {
                leaves(a, &mut |l| {
                    if let E::Call { f, .. } = l {
                        out(*f);
                    }
                });
            }
        }
    }
    visit_children(e, &mut |c| wants(rw, c, out));
}

fn visit_children(e: &E, f: &mut dyn FnMut(&E)) {
    match e {
        E::Let(_, a, b) | E::LetMulti(_, a, b) => {
            f(a);
            f(b)
        }
        E::Call { args, .. } | E::Tuple(args) | E::Multi(args) | E::Par(args) | E::Con { fields: args, .. } | E::Borrow { args, .. } => {
            args.iter().for_each(f)
        }
        E::Apply { f: g, args, .. } => {
            f(g);
            args.iter().for_each(f)
        }
        E::Case { arms, lits, default, .. } => {
            arms.iter().for_each(|a| f(&a.body));
            lits.iter().for_each(|(_, b)| f(b));
            if let Some(d) = default {
                f(d)
            }
        }
        E::At(_, b) | E::Dup(_, b) | E::Drop(_, b) | E::DropReuse(_, _, _, b) => f(b),
        _ => {}
    }
}
