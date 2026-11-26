//! Arithmetic keeps constant bounds (D135): the result of `+ - * / %` on
//! operands whose bounds are constants is that range, an anonymous
//! refinement `(n~Nat, 1 <= n, n <= 256)`, laid out in arrays by the
//! narrowest layout that holds it (D133 e).

use super::*;
pub use crate::range::{combine, Range};
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

/// What a predicate says of the bounds of `Var(subject)`: a comparison of
/// it with a constant, an integer known at compile time (`constant`).
fn subject_range(t: &Tm, subject: usize, constant: &dyn Fn(&Tm) -> Option<i128>) -> Range {
    let Tm::PrimApp(p, args) = t else { return Range::ANY };
    let (Some(a), Some(b)) = (args.first(), args.get(1)) else { return Range::ANY };
    let subject = |x: &Tm| matches!(x, Tm::Var(v) if *v == subject);
    // Put it as `n op c`.
    let constant = |x: &Tm| if subject(x) { None } else { constant(x) };
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

/// The most function entries and loop iterations native code may make in a
/// development build computing a constant that only code generation wants
/// (§8.9, `checkers_rt::prog::ck_tick`): a cost bound, which changes only
/// the code generated. Types and proofs compute their values to completion.
pub const CODEGEN_WORK: u64 = 10_000_000;

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
                            r = r.meet(subject_range(&p.tm, 0, &|t| self.constant(t)));
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

    /// The constant bounds of each of a function signature's binders, then
    /// of its result (`Globals::bounds`): its type's, met with what its
    /// preconditions (postconditions, for the result) say of it alone.
    /// `preds` are over the binders and then the result.
    pub fn signature_bounds(&self, binders: &[(Name, Mult, Icit, Tm)], result: &Tm, preds: &[Pred]) -> Vec<Option<Range>> {
        let nb = binders.len();
        (0..=nb)
            .map(|k| {
                let ty = if k < nb { &binders[k].3 } else { result };
                let env = Rc::new((0..k).map(Val::var).collect::<Vec<_>>());
                let mut r = self.type_range(&eval(&self.g, &env, ty))?;
                for p in preds.iter().filter(|p| p.is_post == (k == nb)) {
                    r = r.meet(subject_range(&p.tm, nb - k, &|t| self.constant(t)));
                }
                (r != Range::ANY).then_some(r)
            })
            .collect()
    }

    /// An operand's value as a constant, in context `cx`: an integer known
    /// at compile time (§8.9). An operation's range is its type's (D135):
    /// it isn't evaluated again, which would walk every operator chained
    /// below it.
    pub fn known_int(&self, cx: &Cx, t: &Tm) -> Option<i128> {
        match t {
            Tm::Lit(Lit::Num(n)) => Some(*n),
            Tm::PrimApp(Prim::Neg, a) => self.known_int(cx, a.first()?).and_then(|n| n.checked_neg()),
            Tm::PrimApp(..) | Tm::Lit(_) => None,
            // A `let` bound to a known value stands for it.
            _ => match &*self.known_term(cx, cx.lvl(), t)? {
                Tm::Lit(Lit::Num(n)) => Some(*n),
                _ => None,
            },
        }
    }

    /// What local `l` is known to be at compile time (§8.9), as a term over
    /// the locals before it: a literal, a closed term, or a tuple,
    /// constructor or function whose parts are known as far as they are;
    /// `None` if it depends on a runtime value some other way. Decided once,
    /// from the term that defined it (`Local::def`), and kept
    /// (`Local::known`): what a local is known to be takes work in
    /// proportion to its term, not to its value, which may hold every
    /// value computed before it.
    pub fn known_local(&self, cx: &Cx, l: usize) -> Option<Rc<Tm>> {
        // Each local undecided that `l`'s term reaches, lowest first: one's
        // term mentions only locals before it, decided by then. A loop, not
        // recursion, however long the chain of locals.
        let mut todo = vec![l];
        let mut undecided = std::collections::BTreeSet::new();
        while let Some(m) = todo.pop() {
            let local = &cx.locals[m];
            if local.known.get().is_some() || !undecided.insert(m) {
                continue;
            }
            if let Some(t) = &local.def {
                let mut free = std::collections::BTreeSet::new();
                crate::core::free_vars(t, 0, &mut free);
                todo.extend(free.into_iter().filter_map(|i| m.checked_sub(1 + i)));
            }
        }
        for m in undecided {
            let local = &cx.locals[m];
            let known = match &local.def {
                Some(t) => self.known_term(cx, m, t),
                // A parameter, or a variable a `match` binds.
                None if local.bound => None,
                // Defined by a value alone.
                None => self.known_in(cx, &cx.env[m]).map(|l| Rc::new(Tm::Lit(l))),
            };
            let _ = local.known.set(known);
        }
        cx.locals[l].known.get().cloned().flatten()
    }

    /// What `t`, a term over the first `depth` locals, is known to be at
    /// compile time, as `known_local` says of a local: `t` with each local
    /// it mentions replaced by what that is known to be, evaluated with the
    /// rest as variables. A value that depends on a runtime value is never
    /// looked into.
    fn known_term(&self, cx: &Cx, depth: usize, t: &Tm) -> Option<Rc<Tm>> {
        fn subst(t: &Tm, n: usize, f: &dyn Fn(usize, usize) -> Tm) -> Tm {
            match t {
                Tm::Var(i) if *i >= n => f(i - n, n),
                _ => t.map_sub(|x, k| subst(x, n + k, f)),
            }
        }
        // A known local's term is over the locals before it: under `n`
        // binders of `t`, its variables move out past `i + 1` locals.
        let t = subst(t, 0, &|i, n| match depth.checked_sub(1 + i).and_then(|m| self.known_local(cx, m)) {
            Some(k) => crate::core::rename_free(&k, 0, &|x| x + i + 1 + n),
            None => Tm::Var(i + n),
        });
        // The variables left, renumbered `0..k`: evaluating needs `k`
        // values, not one for every local in scope.
        let mut free = std::collections::BTreeSet::new();
        crate::core::free_vars(&t, 0, &mut free);
        let levels: Vec<usize> = free.iter().rev().map(|i| depth - 1 - i).collect();
        let k = levels.len();
        let dense = |i: usize| k - 1 - levels.binary_search(&(depth - 1 - i)).unwrap();
        let env = Rc::new((0..k).map(Val::var).collect::<Vec<_>>());
        let v = eval(&self.g, &env, &crate::core::rename_free(&t, 0, &dense));
        if let Some(l) = crate::core::known_lit(&self.g, v.clone()) {
            return Some(Rc::new(Tm::Lit(l)));
        }
        let t = quote(&self.g, k, &v);
        if let Some(l) = self.known_value(&t) {
            return Some(Rc::new(Tm::Lit(l)));
        }
        if let Some(c) = runtime_closed(&self.g, &t) {
            return Some(Rc::new(c));
        }
        // Open, but a structure: a part of it may be known.
        match t.head() {
            Tm::Tuple(_) | Tm::ConApp(..) | Tm::Con(_) | Tm::Lam(..) => {
                Some(Rc::new(crate::core::rename_free(&t, 0, &|j| depth - 1 - levels[k - 1 - j])))
            }
            _ => None,
        }
    }

    /// A closed term's value as a constant: an integer known at compile time.
    pub fn constant(&self, t: &Tm) -> Option<i128> {
        match t {
            Tm::Lit(Lit::Num(n)) => Some(*n),
            Tm::PrimApp(Prim::Neg, a) => self.constant(a.first()?).and_then(|n| n.checked_neg()),
            _ => match self.known_value(t)? {
                Lit::Num(n) => Some(n),
                _ => None,
            },
        }
    }

    /// The literal value `v` (in context `cx`) is known to be at compile
    /// time, if it depends on no runtime value (`known_value`).
    pub fn known_in(&self, cx: &Cx, v: &Val) -> Option<Lit> {
        if let Some(l) = crate::core::known_lit(&self.g, v.clone()) {
            return Some(l);
        }
        self.known_value(&quote(&self.g, cx.lvl(), v))
    }

    /// The literal a closed term is known to be at compile time (§8.9): a
    /// literal, a named constant, or a call of total functions on known
    /// values, sealed or not. The type checker's evaluation computes it
    /// where it can, within its steps; else it runs as native code, as
    /// staging runs compile-time code, once every function it reaches is
    /// total and its module proved, and the preconditions of the calls in
    /// `t` hold: then it ends (§8.9). A computation that fails, or that
    /// can't run yet, isn't known: never an error. Results are kept per
    /// term (per function and arguments).
    pub fn known_value(&self, t: &Tm) -> Option<Lit> {
        self.known_value_within(t, u64::MAX)
    }

    /// `known_value`, giving up after `work` function entries and loop
    /// iterations of native code (`CODEGEN_WORK`); a value given up on
    /// isn't kept, so it is computed again if asked for without a limit.
    pub fn known_value_within(&self, t: &Tm, work: u64) -> Option<Lit> {
        match self.known_term_within(t, None, work)? {
            Tm::Lit(l) => Some(l),
            _ => None,
        }
    }

    /// The value closed term `t` is known to be at compile time, of any
    /// type that has a term (§8.9): a literal, `()`, or a known value
    /// (`Tm::Known`). `ty`, the closed type it has where it is known, tells
    /// how to read it back (a type stored as its one field, a string). As
    /// `known_value` computes it; `work` as `known_value_within`.
    pub fn known_term_within(&self, t: &Tm, ty: Option<&Tm>, work: u64) -> Option<Tm> {
        self.known_term_in(t, ty, work, &mut None)
    }

    /// `known_term_within`, running native code in `ev` (made on first
    /// use): many values computed together share its compiled code.
    pub fn known_term_in<'g>(&'g self, t: &Tm, ty: Option<&Tm>, work: u64, ev: &mut Option<crate::native::eval::Evaluator<'g>>) -> Option<Tm> {
        if let Tm::Lit(_) | Tm::Known(_) = t {
            return Some(t.clone());
        }
        let t = &runtime_closed(&self.g, t)?;
        let key = format!("{t:?}|{ty:?}");
        if let Some(k) = self.known_cache.borrow().get(&key) {
            return k.clone();
        }
        if !self.functions_proved(t) {
            // Not known yet, however it would be computed: a function it
            // calls runs only once its module is proved.
            return None;
        }
        if let Some(l) = crate::core::known_lit(&self.g, eval(&self.g, &Rc::new(Vec::new()), t)) {
            self.known_cache.borrow_mut().insert(key, Some(Tm::Lit(l.clone())));
            return Some(Tm::Lit(l));
        }
        if !self.runnable(t) {
            // Not known yet: a function it needs may be checked later.
            return None;
        }
        if !self.preconditions_hold(t, 0, work) {
            // A total function ends where its preconditions hold: outside
            // them its value isn't known, and the call's precondition is
            // reported where it is proved.
            self.known_cache.borrow_mut().insert(key, None);
            return None;
        }
        let ev = ev.get_or_insert_with(|| crate::native::eval::Evaluator::plain(&self.g));
        let k = match ev.eval_limited(t, work) {
            Ok(v) => {
                let r = match ty {
                    Some(ty) => ev.reify_as(v, ty),
                    None => ev.reify(v),
                };
                ev.release(v);
                r
            }
            Err(e) if e.contains(checkers_rt::prog::WORK_LIMIT) => return None,
            // A runtime error: not known.
            Err(_) => None,
        };
        self.known_cache.borrow_mut().insert(key, k.clone());
        k
    }

    /// Do the preconditions of every call in closed term `t` (outside
    /// lambdas: those calls' preconditions are their caller's to prove)
    /// hold for its arguments, as values known at compile time? `depth`
    /// counts preconditions of preconditions; `work`, as `known_value_within`.
    fn preconditions_hold(&self, t: &Tm, depth: usize, work: u64) -> bool {
        fn calls(t: &Tm, out: &mut Vec<Tm>) {
            match t {
                Tm::App(..) => {
                    let (h, args) = t.spine();
                    if let Tm::Def(_) = h {
                        out.push(t.clone());
                    }
                    for a in args {
                        calls(a, out);
                    }
                }
                Tm::Lam(..) => {}
                _ => t.each_sub(|x, n| {
                    if n == 0 {
                        calls(x, out)
                    }
                }),
            }
        }
        let mut found = Vec::new();
        calls(t, &mut found);
        let empty = Rc::new(Vec::new());
        for c in &found {
            let (h, args) = c.spine();
            let Tm::Def(d) = h else { continue };
            let Some(spec) = self.specs.get(d) else { continue };
            if args.len() < spec.n_binders {
                continue;
            }
            // The spine's arguments, first to last; the result isn't
            // mentioned by a precondition.
            let mut env: Vec<Val> = args.iter().rev().take(spec.n_binders).map(|a| eval(&self.g, &empty, a)).collect();
            env.push(Val::Error);
            for p in spec.preds.iter().filter(|p| !p.is_post) {
                let goal = quote(&self.g, 0, &self.inst_pred(p, env.clone()));
                if self.known_bool(&goal, depth, work) != Some(true) {
                    return false;
                }
            }
        }
        true
    }

    /// The truth of closed `t` at compile time, computed as `known_value`
    /// computes a number.
    fn known_bool(&self, t: &Tm, depth: usize, work: u64) -> Option<bool> {
        let wk = &self.g.well_known;
        let saved = self.g.fuel.replace(crate::core::DEFAULT_FUEL);
        let forced = crate::core::force(&self.g, eval(&self.g, &Rc::new(Vec::new()), t));
        self.g.fuel.set(saved);
        match forced {
            Val::Con(c, _) if Some(c) == wk.true_con => return Some(true),
            Val::Con(c, _) if Some(c) == wk.false_con => return Some(false),
            _ => {}
        }
        let t = &runtime_closed(&self.g, t)?;
        if depth > 8 || !self.runnable(t) || !self.preconditions_hold(t, depth + 1, work) {
            return None;
        }
        let mut ev = crate::native::eval::Evaluator::plain(&self.g);
        let v = ev.eval_limited(t, work).ok()?;
        let b = !ev.is_false(v);
        ev.release(v);
        Some(b)
    }

    /// Is module `m` proved, with no errors (§8.9)? An imported module is
    /// proved the first time one of its functions would run; the module
    /// being checked, or being proved, isn't yet.
    pub fn module_proved(&self, m: &str) -> bool {
        // A module with errors isn't proved: its broken declarations'
        // obligations are set aside only once the program is checked.
        if self.loading.iter().any(|l| l == m) || self.proving.borrow().contains(m) || self.diags.iter().any(|(at, d)| at == m && d.is_error()) {
            return false;
        }
        !crate::verify::proved(self, m).diags.iter().any(|d| d.is_error())
    }

    /// Is definition `d` proved (§8.9)? One of an imported module, once that
    /// module is proved with no errors (`module_proved`); one of the module
    /// being checked, once it and everything it reaches are, on demand
    /// (`settle`).
    pub fn def_proved(&self, d: DefId) -> bool {
        let m = &self.g.defs[d.0 as usize].module;
        if **m == *self.cur && self.loading.iter().any(|l| *l == **m) {
            return self.settle(d);
        }
        self.module_proved(m)
    }

    /// Is every function `t` reaches, through constants and functions'
    /// bodies, proved (`def_proved`, §8.9)? Constants, and
    /// builtins, which have no body, needn't be.
    fn functions_proved(&self, t: &Tm) -> bool {
        let mut todo = Vec::new();
        crate::core::defs_in(t, &mut todo);
        let mut seen = HashSet::new();
        while let Some(d) = todo.pop() {
            if self.runnable_defs.borrow().contains(&d) || !seen.insert(d) {
                continue;
            }
            let Some(info) = self.g.defs.get(d.0 as usize) else { return false };
            let Some(b) = &info.body else { continue };
            if matches!(info.ty, Tm::Pi(..)) && !self.def_proved(d) {
                return false;
            }
            crate::core::defs_in(b, &mut todo);
        }
        true
    }

    /// Can `t` run at compile time now? Every definition it reaches has
    /// code (a body, or a builtin of the runtime), is total (not
    /// `partial`), and is proved (`def_proved`), so it ends and calls only
    /// what its callees accept; and nothing in it waits on a cown.
    fn runnable(&self, t: &Tm) -> bool {
        let mut todo = Vec::new();
        crate::core::defs_in(t, &mut todo);
        if has_when(t) {
            return false;
        }
        let mut seen = HashSet::new();
        while let Some(d) = todo.pop() {
            if self.runnable_defs.borrow().contains(&d) || !seen.insert(d) {
                continue;
            }
            let Some(info) = self.g.defs.get(d.0 as usize) else { return false };
            // A `partial` function has a body and is opaque; a builtin has
            // none (its code is the runtime's).
            if info.opaque && info.body.is_some() || !self.def_proved(d) {
                return false;
            }
            match &info.body {
                Some(b) => {
                    if has_when(b) {
                        return false;
                    }
                    crate::core::defs_in(b, &mut todo);
                }
                None => {
                    let full = format!("{}.{}", info.module, info.name);
                    if checkers_rt::builtins::symbol(&full).is_none() && !is_type_former(&info.ty) {
                        return false;
                    }
                }
            }
        }
        // Each definition reached is in a proved module: it stays runnable.
        self.runnable_defs.borrow_mut().extend(seen);
        true
    }

    /// An operand's bounds: a constant's own, else its type's.
    pub fn operand_range(&self, c: Option<i128>, ty: &Val) -> Option<Range> {
        match c {
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
        // `n < 0` is `-(-n)`, and `-i128::MIN` is a `Big` literal.
        let lit = |n: i128| if n < 0 { Tm::PrimApp(Prim::Neg, vec![Tm::Lit(Lit::int(-num_bigint::BigInt::from(n)))]) } else { Tm::Lit(Lit::Num(n)) };
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
            (Some(Join::Range(a)), Some(b)) => Join::Range(a.hull(b)),
            _ => Join::Other,
        };
        self.joins.insert(m, j);
    }

    /// The type of values that are each an `a` or a `b`, for a type
    /// parameter several values decide together: numbers' ranges joined
    /// (D135), a type constructor's arguments joined one by one, and
    /// otherwise the type without its refinement. Where `a` and `b` differ
    /// in more than refinements, `a`'s type: the value of type `b` is then
    /// reported where it is checked against it.
    pub fn join_types(&mut self, a: &Val, b: &Val) -> Val {
        let (pa, pb) = (self.peel(a), self.peel(b));
        if matches!(pb, Val::Neutral(Head::Meta(_), _)) {
            return a.clone();
        }
        if matches!(pa, Val::Neutral(Head::Meta(_), _)) {
            return b.clone();
        }
        if self.same_type(&pa, &pb) {
            return a.clone();
        }
        if let (Some(x), Some(y)) = (self.type_range(&pa), self.type_range(&pb)) {
            return self.range_type(x.hull(y));
        }
        match (self.force(&pa), self.force(&pb)) {
            (Val::TyCon(t1, x1), Val::TyCon(t2, x2)) if t1 == t2 && x1.len() == x2.len() => {
                Val::TyCon(t1, x1.iter().zip(x2.iter()).map(|(x, y)| self.join_types(x, y)).collect())
            }
            (Val::TupleTy(x1), Val::TupleTy(x2)) if x1.len() == x2.len() => Val::TupleTy(x1.iter().zip(x2.iter()).map(|(x, y)| self.join_types(x, y)).collect()),
            // A number's base is `Nat` or `Int`, not their representation.
            _ if self.type_range(&pa).is_some() => self.arith_base(&pa),
            (fa, _) => fa,
        }
    }

    /// Is `ty` a range this rule made (D135)?
    pub fn is_range(&self, ty: &Val) -> bool {
        matches!(crate::core::force_meta(&self.g, ty.clone()), Val::Neutral(Head::Def(d), _) if self.ranges.values().any(|r| *r == d))
    }

    /// The type an operator's other operand is checked against: a range's
    /// base, so ranges don't spread through it (D135).
    pub fn shared_operand_type(&self, ty: &Val) -> Val {
        if self.is_range(ty) {
            return self.arith_base(ty);
        }
        // A class's type with a base type (#360): its operators are the base's.
        crate::core::class_type_base(&self.g, ty).unwrap_or_else(|| ty.clone())
    }

    /// The type of `lt op rt` (D134, D135): `ty` is the operands' shared
    /// type, `lty` and `rty` their own.
    pub fn arith_type(&mut self, op: Prim, lc: Option<i128>, rc: Option<i128>, ty: &Val, lty: &Val, rty: &Val) -> Val {
        let nat_sub = op == Prim::Sub && crate::core::is_nat(&self.g, ty);
        match (self.operand_range(lc, lty), self.operand_range(rc, rty)) {
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

/// Does `t` wait on a cown (`when`), which compile time can't?
fn has_when(t: &Tm) -> bool {
    matches!(t, Tm::PrimApp(Prim::When, _)) || t.any_sub(|x, _| has_when(x))
}

/// `t` as a closed term, if what it computes depends on no variable: its
/// solved unknowns filled in, and each erased argument (a type, a proof)
/// that mentions a variable or an unknown replaced by a type, since none
/// is there at run time (`Univ(0)`; a call's type arguments may still be
/// unknowns while a signature is checked).
fn runtime_closed(g: &Globals, t: &Tm) -> Option<Tm> {
    fn erase(g: &Globals, t: &Tm, depth: usize) -> Tm {
        let Tm::App(..) = t else { return t.map_sub(|x, n| erase(g, x, depth + n)) };
        let mut args = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, i, m) = h {
            args.push((a, *i, *m));
            h = f;
        }
        args.reverse();
        // A definition's parameters say which arguments are erased (quoting
        // doesn't keep multiplicities).
        let mut ty = match h {
            Tm::Def(d) => g.defs.get(d.0 as usize).map(|i| i.ty.clone()),
            _ => None,
        };
        let mut out = erase(g, h, depth);
        for (a, i, m) in args {
            let m = match &ty {
                Some(Tm::Pi(_, pm, _, _, b)) => {
                    let pm = *pm;
                    ty = Some((**b).clone());
                    pm
                }
                _ => {
                    ty = None;
                    m
                }
            };
            let mut free = std::collections::BTreeSet::new();
            crate::core::free_vars(a, depth, &mut free);
            let a = if m == Mult::Zero && (!free.is_empty() || has_meta(a)) { Tm::Univ(0) } else { erase(g, a, depth) };
            out = Tm::App(Rc::new(out), Rc::new(a), i, m);
        }
        out
    }
    fn has_meta(t: &Tm) -> bool {
        matches!(t, Tm::Meta(_)) || t.any_sub(|x, _| has_meta(x))
    }
    let l = crate::core::max_var(t).map_or(0, |m| m + 1);
    let t = erase(g, &crate::core::zonk_metas(g, l, t), 0);
    (crate::core::max_var(&t).is_none() && !has_meta(&t)).then_some(t)
}
