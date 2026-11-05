//! Usage checking (QTT, §2 and §4): `own` values are used exactly once on
//! every path; `ghost` values never at runtime.

use crate::core::{CaseTm, DefId, Mult, Prim, Tm};
use crate::diag::Diagnostic;
use crate::elab::Elab;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Count {
    Zero,
    One,
    Many,
}

impl Count {
    fn add(self, o: Count) -> Count {
        match (self, o) {
            (Count::Zero, x) | (x, Count::Zero) => x,
            _ => Count::Many,
        }
    }
    fn scale(self, m: Mult) -> Count {
        match (self, m) {
            (_, Mult::Zero) | (Count::Zero, _) => Count::Zero,
            (c, Mult::One) => c,
            (_, Mult::Many) => Count::Many,
        }
    }
}

struct Binder {
    name: String,
    mult: Mult,
}

struct U<'a> {
    e: &'a mut Elab,
    did: DefId,
    binders: Vec<Binder>,
    reported: bool,
}

type Counts = Vec<Count>;

fn add(a: &mut Counts, b: &Counts) {
    for (x, y) in a.iter_mut().zip(b) {
        *x = x.add(*y);
    }
}

impl U<'_> {
    fn zero(&self) -> Counts {
        vec![Count::Zero; self.binders.len()]
    }

    fn report(&mut self, lvl: usize, c: Count, mixed: bool) {
        let b = &self.binders[lvl];
        let meta = self.e.fn_meta.get(&self.did).cloned().unwrap_or_default();
        let span = meta
            .params
            .iter()
            .find(|p| p.0 == b.name)
            .map(|p| p.2)
            .unwrap_or(meta.span);
        let fname = meta.name.clone();
        let name = b.name.clone();
        let d = match (b.mult, mixed, c) {
            (Mult::Zero, _, _) => Diagnostic::error(
                "E0403",
                format!("`{name}` is `ghost`: it may only appear in types and constraints, but `{fname}` uses it at runtime"),
                span,
            )
            .with_help("remove `ghost` if the value is needed at runtime"),
            (_, true, _) => Diagnostic::error(
                "E0402",
                format!("`{name}` is `own`, but `{fname}` uses it on some paths and not on others"),
                span,
            )
            .with_help("an owned resource must be used exactly once on every path, e.g. closed in every branch"),
            (_, false, Count::Zero) => Diagnostic::error(
                "E0401",
                format!("`{name}` is `own`, so it must be used exactly once, but `{fname}` never uses it"),
                span,
            )
            .with_help("close or pass on the resource"),
            _ => Diagnostic::error(
                "E0401",
                format!("`{name}` is `own`, so it must be used exactly once, but `{fname}` may use it more than once"),
                span,
            )
            .with_help("an owned resource can't be copied; thread it with `<-` so each use gets the new one"),
        };
        self.e.err(d);
        self.reported = true;
    }

    /// Check a binder's own usage when it goes out of scope.
    fn close(&mut self, counts: &Counts) {
        let lvl = self.binders.len() - 1;
        let c = counts[lvl];
        match self.binders[lvl].mult {
            Mult::One if c != Count::One => self.report(lvl, c, false),
            Mult::Zero if c != Count::Zero => self.report(lvl, c, false),
            _ => {}
        }
    }

    fn under(&mut self, name: &str, mult: Mult, body: &Tm) -> Counts {
        self.binders.push(Binder { name: name.to_string(), mult });
        let c = self.go(body);
        self.close(&c);
        self.binders.pop();
        let mut c = c;
        c.pop();
        c
    }

    fn go(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Var(i) => {
                let mut c = self.zero();
                let lvl = self.binders.len() - 1 - i;
                c[lvl] = Count::One;
                c
            }
            Tm::App(f, a, _, m) => {
                let mut c = self.go(f);
                let ca: Counts = self.go(a).into_iter().map(|x| x.scale(*m)).collect();
                add(&mut c, &ca);
                c
            }
            Tm::Lam(x, m, _, b) => {
                // A closure may run any number of times.
                self.under(x, *m, b).into_iter().map(|c| c.scale(Mult::Many)).collect()
            }
            Tm::Let(x, m, _, v, b) => {
                let mut c: Counts = self.go(v).into_iter().map(|c| c.scale(if *m == Mult::Zero { Mult::Zero } else { Mult::One })).collect();
                let cb = self.under(x, *m, b);
                add(&mut c, &cb);
                c
            }
            Tm::Tuple(v) => {
                let mut c = self.zero();
                for x in v {
                    let cx = self.go(x);
                    add(&mut c, &cx);
                }
                c
            }
            Tm::ConApp(cid, v) => {
                let g = &self.e.g;
                let ci = &g.cons[cid.0 as usize];
                let np = g.arity_ty(ci.ty);
                let mults: Vec<Mult> =
                    std::iter::repeat_n(Mult::Zero, np).chain(ci.fields.iter().map(|f| f.1)).collect();
                let mut c = self.zero();
                for (x, m) in v.iter().zip(mults) {
                    let cx: Counts = self.go(x).into_iter().map(|c| c.scale(if m == Mult::Zero { Mult::Zero } else { Mult::One })).collect();
                    add(&mut c, &cx);
                }
                c
            }
            Tm::PrimApp(p, v) => {
                let mut c = self.zero();
                for x in v {
                    // Behaviour bodies run once: a resource may move into them.
                    let cx = match (p, x) {
                        (Prim::Fork | Prim::Join | Prim::When, Tm::Lam(..)) => self.lam_once(x),
                        _ => self.go(x),
                    };
                    add(&mut c, &cx);
                }
                c
            }
            Tm::Proj(x, _) | Tm::Field(x, _, _) => self.go(x),
            Tm::Case(s, c) => {
                let mut cs = self.go(s);
                let cb = self.case(c);
                add(&mut cs, &cb);
                cs
            }
            // Types and globals are erased or contain no locals.
            _ => self.zero(),
        }
    }

    fn lam_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(x, m, _, b) => {
                self.binders.push(Binder { name: x.to_string(), mult: *m });
                let c = self.lam_once(b);
                self.close(&c);
                self.binders.pop();
                let mut c = c;
                c.pop();
                c
            }
            other => self.go(other),
        }
    }

    fn case(&mut self, c: &CaseTm) -> Counts {
        let mut results: Vec<Counts> = Vec::new();
        for (_, n, body) in &c.branches {
            if matches!(body, Tm::Error) {
                continue;
            }
            let start = self.binders.len();
            for k in 0..*n {
                self.binders.push(Binder { name: format!("$field{k}"), mult: Mult::Many });
            }
            let mut r = self.go(body);
            self.binders.truncate(start);
            r.truncate(start);
            results.push(r);
        }
        for (_, body) in &c.lits {
            if !matches!(body, Tm::Error) {
                results.push(self.go(body));
            }
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
            results.push(self.go(d));
        }
        // Branches without code (errors already reported) don't constrain usage.
        let mut out = self.zero();
        let Some(first) = results.first() else { return out };
        for lvl in 0..out.len() {
            let mult = self.binders[lvl].mult;
            let all: Vec<Count> = results.iter().map(|r| r[lvl]).collect();
            if mult == Mult::One && all.iter().any(|x| *x != first[lvl]) && !self.reported {
                let has_one = all.contains(&Count::One);
                let has_zero = all.contains(&Count::Zero);
                if has_one && has_zero {
                    self.report(lvl, Count::One, true);
                }
            }
            out[lvl] = all.iter().copied().fold(Count::Zero, |a, b| match (a, b) {
                (Count::Many, _) | (_, Count::Many) => Count::Many,
                (Count::One, _) | (_, Count::One) => Count::One,
                _ => Count::Zero,
            });
        }
        out
    }
}

/// Check the body (a λ over the function's parameters) of `did`.
pub fn check_fn(e: &mut Elab, did: DefId, body: &Tm) {
    let mut u = U { e, did, binders: Vec::new(), reported: false };
    let mut t = body;
    let mut n = 0;
    while let Tm::Lam(x, m, _, b) = t {
        u.binders.push(Binder { name: x.to_string(), mult: *m });
        t = b;
        n += 1;
    }
    let c = u.go(t);
    for lvl in (0..n).rev() {
        let mult = u.binders[lvl].mult;
        let k = c[lvl];
        let bad = match mult {
            Mult::One => k != Count::One,
            Mult::Zero => k != Count::Zero,
            Mult::Many => false,
        };
        if bad && !u.reported {
            u.report(lvl, k, false);
        }
    }
}
