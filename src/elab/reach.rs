//! What a value of a type can hold: the types of its parts, fields and
//! elements, however deep. A walk (`Holds`) says what it looks for; this
//! finds it, with a worklist rather than recursion, and never stops early
//! because the types went deep.
//!
//! A type can hold infinitely many types: `Nest a` with a field of type
//! `Nest (Option a)` holds `Nest (Option (Option a))` and so on. Where a
//! type constructor comes back inside itself at other arguments, what it
//! holds is read from its summary instead: what it holds at any arguments
//! (a hit, or which of its parameters it holds), found once, with its
//! parameters as variables. A summary that depends on more than its
//! parameters (a field's type computed from one, `pick n`, or a hit that
//! depends on a parameter) is unsure: the walk says so rather than guess.

use super::*;
use std::collections::BTreeSet;

/// What a walk does at one type.
pub(super) enum Look {
    /// What the walk looks for.
    Hit,
    /// Nothing here, and nothing below.
    Leaf,
    /// A type variable at this level: the walk records it.
    Var(usize),
    /// Look at these types.
    Parts(Vec<Val>),
    /// Look at the fields of this type constructor at these arguments.
    Fields(TyId, Vec<Val>),
}

/// A walk over the types a value of a type holds.
pub(super) trait Holds {
    /// What to do at `t`, forced.
    fn look(&self, e: &Elab, t: &Val) -> Look;
    /// Whether field `k` of constructor `c` is held.
    fn field(&self, e: &Elab, c: ConId, k: usize) -> bool;
    /// Whether `look`'s `Hit` and `Leaf` depend only on a type's head, not
    /// on its arguments: then a summary can tell them with the type's
    /// parameters as variables.
    fn by_head(&self) -> bool;
}

/// What a walk found.
pub(super) enum Found {
    /// Nothing it looks for.
    Nothing,
    /// A type it looks for.
    Hit(Val),
    /// A type holding types that can't all be known (see the module's
    /// comment): this one.
    Unsure(Val),
}

/// What a type constructor holds at any arguments.
#[derive(Clone, Default, PartialEq)]
struct Summary {
    hit: bool,
    unsure: bool,
    /// The parameters whose arguments it holds.
    params: BTreeSet<usize>,
}

/// The type constructors a type is inside, innermost first.
struct Path {
    id: TyId,
    up: Option<Rc<Path>>,
}

fn on_path(p: &Option<Rc<Path>>, id: TyId) -> bool {
    let mut p = p.as_deref();
    while let Some(q) = p {
        if q.id == id {
            return true;
        }
        p = q.up.as_deref();
    }
    false
}

/// The summaries found so far, and those being found.
#[derive(Default)]
struct Summaries {
    found: HashMap<TyId, Summary>,
    done: HashSet<TyId>,
    finding: Vec<TyId>,
}

/// What one walk found: as `Found`, and the type variables and (finding a
/// summary) the parameters it met.
struct Walked {
    found: Found,
    vars: BTreeSet<usize>,
    params: BTreeSet<usize>,
}

impl Elab {
    /// What a value of type `ty` (at level `lvl`) holds, as walk `w` sees
    /// it: what it found, and the type variables it met.
    pub(super) fn reach(&self, w: &dyn Holds, lvl: usize, ty: &Val) -> (Found, BTreeSet<usize>) {
        let mut sums = Summaries::default();
        let r = self.walk_holds(w, lvl, ty, None, &mut sums);
        (r.found, r.vars)
    }

    /// The walk: depth first, in the order of the parts and fields, so the
    /// first hit is the one a recursive walk would meet first. With
    /// `generic` (the number of a type constructor's parameters, which are
    /// the variables below it), finding a summary.
    fn walk_holds(&self, w: &dyn Holds, lvl: usize, ty: &Val, generic: Option<usize>, sums: &mut Summaries) -> Walked {
        let mut out = Walked { found: Found::Nothing, vars: BTreeSet::new(), params: BTreeSet::new() };
        let mut seen: Vec<(TyId, Vec<Tm>)> = Vec::new();
        let mut work: Vec<(Val, Option<Rc<Path>>)> = vec![(ty.clone(), None)];
        let mentions = |t: &Val| {
            let mut free = BTreeSet::new();
            crate::core::free_vars(&quote(&self.g, lvl, t), 0, &mut free);
            !free.is_empty()
        };
        while let Some((t, path)) = work.pop() {
            let t = self.force(&t);
            if let Some(n) = generic {
                match &t {
                    Val::Neutral(Head::Var(l), sp) if sp.is_empty() && *l < n => {
                        out.params.insert(*l);
                        continue;
                    }
                    // Computed from a parameter: what it is depends on the arguments.
                    Val::Neutral(..) if mentions(&t) => {
                        out.found = Found::Unsure(t);
                        return out;
                    }
                    _ => {}
                }
            }
            let look = w.look(self, &t);
            if generic.is_some() && !w.by_head() && matches!(look, Look::Hit | Look::Leaf) && mentions(&t) {
                out.found = Found::Unsure(t);
                return out;
            }
            match look {
                Look::Hit => {
                    out.found = Found::Hit(t);
                    return out;
                }
                Look::Leaf => {}
                Look::Var(l) => {
                    out.vars.insert(l);
                }
                Look::Parts(ps) => work.extend(ps.into_iter().rev().map(|p| (p, path.clone()))),
                Look::Fields(id, args) => {
                    let key: Vec<Tm> = args.iter().map(|a| quote(&self.g, lvl, a)).collect();
                    if seen.iter().any(|(i, k)| *i == id && k.len() == key.len() && k.iter().zip(&key).all(|(a, b)| tm_eq(a, b))) {
                        continue;
                    }
                    seen.push((id, key));
                    if on_path(&path, id) {
                        // Inside itself at other arguments: what it holds
                        // at any arguments.
                        let s = self.holds_summary(w, id, sums);
                        if s.hit {
                            out.found = Found::Hit(self.first_hit(w, lvl, &t).unwrap_or(t));
                            return out;
                        }
                        if s.unsure {
                            out.found = Found::Unsure(t);
                            return out;
                        }
                        work.extend(s.params.iter().rev().filter_map(|k| args.get(*k)).map(|a| (a.clone(), path.clone())));
                        continue;
                    }
                    let inner = Some(Rc::new(Path { id, up: path }));
                    let mut fields = Vec::new();
                    for c in self.g.tys[id.0 as usize].ctors.clone() {
                        for (i, f) in self.g.cons[c.0 as usize].fields.iter().enumerate() {
                            if !w.field(self, c, i) {
                                continue;
                            }
                            let mut env = args.clone();
                            env.extend(std::iter::repeat_n(Val::Error, i));
                            fields.push(eval(&self.g, &crate::core::Env::from(env), &f.3));
                        }
                    }
                    work.extend(fields.into_iter().rev().map(|f| (f, inner.clone())));
                }
            }
        }
        out
    }

    /// What type constructor `id` holds at any arguments: its fields
    /// walked with its parameters as variables. Type constructors that
    /// hold each other are found together, by repeating until nothing
    /// changes (each summary only grows, so this ends).
    fn holds_summary(&self, w: &dyn Holds, id: TyId, sums: &mut Summaries) -> Summary {
        if sums.done.contains(&id) || sums.finding.contains(&id) {
            return sums.found.get(&id).cloned().unwrap_or_default();
        }
        let n = self.g.tys[id.0 as usize].params.len();
        let generic = Val::TyCon(id, (0..n).map(Val::var).collect::<Vec<_>>().into());
        sums.finding.push(id);
        loop {
            let r = self.walk_holds(w, n, &generic, Some(n), sums);
            let s = Summary { hit: matches!(r.found, Found::Hit(_)), unsure: matches!(r.found, Found::Unsure(_)), params: r.params };
            let before = sums.found.insert(id, s.clone());
            if before.as_ref() == Some(&s) {
                break;
            }
        }
        sums.finding.pop();
        if sums.finding.is_empty() {
            // Found from the others' summaries as they were: only the
            // outermost is final, the others are found again if needed.
            let s = sums.found.remove(&id).unwrap_or_default();
            sums.found.clear();
            sums.found.insert(id, s);
            sums.done.insert(id);
        }
        sums.found.get(&id).cloned().unwrap_or_default()
    }

    /// The first hit in `ty`, breadth first: a summary says there is one,
    /// at some finite depth, so this finds it even where the types held
    /// never end.
    fn first_hit(&self, w: &dyn Holds, lvl: usize, ty: &Val) -> Option<Val> {
        let mut seen: Vec<(TyId, Vec<Tm>)> = Vec::new();
        let mut work = std::collections::VecDeque::from([ty.clone()]);
        while let Some(t) = work.pop_front() {
            let t = self.force(&t);
            match w.look(self, &t) {
                Look::Hit => return Some(t),
                Look::Leaf | Look::Var(_) => {}
                Look::Parts(ps) => work.extend(ps),
                Look::Fields(id, args) => {
                    let key: Vec<Tm> = args.iter().map(|a| quote(&self.g, lvl, a)).collect();
                    if seen.iter().any(|(i, k)| *i == id && k.len() == key.len() && k.iter().zip(&key).all(|(a, b)| tm_eq(a, b))) {
                        continue;
                    }
                    seen.push((id, key));
                    for c in self.g.tys[id.0 as usize].ctors.clone() {
                        for (i, f) in self.g.cons[c.0 as usize].fields.iter().enumerate() {
                            if w.field(self, c, i) {
                                let mut env = args.clone();
                                env.extend(std::iter::repeat_n(Val::Error, i));
                                work.push_back(eval(&self.g, &crate::core::Env::from(env), &f.3));
                            }
                        }
                    }
                }
            }
        }
        None
    }
}
