//! Maximal partial evaluation (§8.9): each function's code, once small
//! functions are inlined and calls specialized, is folded from the inside
//! out. An operation on static data alone is computed when compiling and
//! replaced by its value, as static data: a primitive, a field or
//! component, a `match` on a constructor (its arm), a `let` of static data
//! (its value), and a call of a function or builtin with all its
//! arguments. The compiler computes arithmetic and comparisons of numbers
//! itself; anything else runs as compile-time evaluation runs code
//! (`eval`), once per operation and arguments.
//!
//! An operation that can't be computed is *kept*, with the reason: it
//! fails (its runtime error stays the program's, at the same point), its
//! value has no static form yet, its function is `partial` or reaches an
//! effect, or the program relies on an `admit`, so its calls
//! might be outside their preconditions. `check` verifies that every
//! operation on static data alone that is left was kept so
//! (`CHECKERS_RESIDUAL_CHECK=1`); `CHECKERS_NATIVE_DUMP=1` lists those kept.
//! `CHECKERS_NO_FOLD=1` turns folding off, to measure it and to test the
//! check.

use super::ir::{shift, Ir, IrCase, Lit, Op};
use super::lower::{SNode, Static};
use crate::core::{DefId, Globals, Tm};
use checkers_rt::word as w;
use std::collections::HashMap;
use std::sync::Arc;

/// Why an operation on static data alone is left to run.
#[derive(Clone, Debug)]
pub enum Kept {
    /// Computing it fails: a runtime error, which stays the program's.
    Fails(String),
    /// Its value has no static form yet.
    NoForm,
    /// It calls a `partial` function, which may not end.
    Partial,
    /// It reaches a builtin that runs only when the program does: one with
    /// effects, or `blackbox` (§8.9).
    RunTime,
    /// The program relies on an `admit`: a call might be outside
    /// its function's preconditions.
    Unproved,
}

impl Kept {
    pub fn why(&self) -> String {
        match self {
            Kept::Fails(e) => format!("fails when compiling ({e})"),
            Kept::NoForm => "its value has no static form yet".into(),
            Kept::Partial => "it calls a `partial` function".into(),
            Kept::RunTime => "it reaches a builtin that runs only when the program does (one with effects, or `blackbox`)".into(),
            Kept::Unproved => "the program relies on an `admit`".into(),
        }
    }
}

/// Whether folding is on: off with `CHECKERS_NO_FOLD=1`.
pub fn off() -> bool {
    std::env::var_os("CHECKERS_NO_FOLD").is_some()
}

/// Whether the check is on (`CHECKERS_RESIDUAL_CHECK=1`).
pub fn checking() -> bool {
    std::env::var_os("CHECKERS_RESIDUAL_CHECK").is_some()
}

/// Folds code: one per program, so each operation is computed once.
pub struct Folder<'g> {
    g: &'g Globals,
    staged: Option<&'g crate::stage::Staged>,
    /// Runs calls; made when the first one is folded.
    ev: Option<crate::native::eval::Evaluator<'g>>,
    /// Each operation computed, by its key: its value, or why it is kept.
    memo: HashMap<String, Result<Arc<Ir>, Kept>>,
    /// Whether each definition reaches neither an effect nor a `partial`
    /// function (`Ok`), or which it reaches.
    pure: HashMap<DefId, Result<(), Kept>>,
    /// The operations kept in the code folded last: each node, and why.
    pub kept: Vec<(Arc<Ir>, Kept)>,
}

impl<'g> Folder<'g> {
    pub fn new(g: &'g Globals, staged: Option<&'g crate::stage::Staged>) -> Folder<'g> {
        Folder { g, staged, ev: None, memo: HashMap::new(), pure: HashMap::new(), kept: Vec::new() }
    }

    /// `ir` folded, for a program whose copies are `specs`.
    pub fn fold_def(&mut self, ir: &Arc<Ir>, specs: &crate::native::spec::Specs) -> Arc<Ir> {
        self.kept.clear();
        if let Some(ev) = &mut self.ev {
            ev.mirror(specs);
        }
        self.fold(ir, specs)
    }

    fn fold(&mut self, ir: &Arc<Ir>, specs: &crate::native::spec::Specs) -> Arc<Ir> {
        let g = self.g;
        match &**ir {
            Ir::Var(_) | Ir::Global(_) | Ir::Erased | Ir::Lit(_) | Ir::ConFn(_) | Ir::Fail(_) | Ir::Static(..) => ir.clone(),
            Ir::Lam(o, b) => Arc::new(Ir::Lam(*o, self.fold(b, specs))),
            Ir::At(o, x) => {
                let x = self.fold(x, specs);
                // Static data can't fail: it has no error to name.
                if is_static(g, &x) {
                    return x;
                }
                Arc::new(Ir::At(*o, x))
            }
            Ir::Let(v, b) => {
                let v = self.fold(v, specs);
                if is_static(g, &v) {
                    return self.fold(&Arc::new(subst0(b, &v)), specs);
                }
                Arc::new(Ir::Let(v, self.fold(b, specs)))
            }
            Ir::Tuple(xs) => Arc::new(Ir::Tuple(xs.iter().map(|x| self.fold(x, specs)).collect())),
            Ir::Con(c, xs) => Arc::new(Ir::Con(*c, xs.iter().map(|x| self.fold(x, specs)).collect())),
            Ir::Par(xs) => Arc::new(Ir::Par(xs.iter().map(|x| self.fold(x, specs)).collect())),
            Ir::Proj(e, i, rest) => {
                let e = self.fold(e, specs);
                match components(g, &e) {
                    Some(xs) if !*rest && *i < xs.len() => xs[*i].clone(),
                    _ => Arc::new(Ir::Proj(e, *i, *rest)),
                }
            }
            Ir::Field(e, i) => {
                let e = self.fold(e, specs);
                match con_fields(g, &e) {
                    Some((_, xs)) if *i < xs.len() => xs[*i].clone(),
                    _ => Arc::new(Ir::Field(e, *i)),
                }
            }
            Ir::Case(s, c) => {
                let s = self.fold(s, specs);
                if let Some(arm) = choose(g, &s, c) {
                    return self.fold(&Arc::new(arm), specs);
                }
                let branches = c.branches.iter().map(|(con, n, b)| (*con, *n, self.fold(b, specs))).collect();
                let lits = c.lits.iter().map(|(l, b)| (l.clone(), self.fold(b, specs))).collect();
                let default = c.default.as_ref().map(|d| self.fold(d, specs));
                Arc::new(Ir::Case(s, Arc::new(IrCase { branches, lits, default })))
            }
            Ir::Prim(op, args, nat) => {
                let args: Vec<Arc<Ir>> = args.iter().map(|a| self.fold(a, specs)).collect();
                let node = Arc::new(Ir::Prim(*op, args, *nat));
                let Ir::Prim(_, args, _) = &*node else { unreachable!() };
                if !foldable_op(*op) || !args.iter().all(|a| is_static(g, a)) {
                    return node;
                }
                let r = match arith(self.g, *op, args, *nat) {
                    Some(r) => r,
                    None => self.run(&node, specs),
                };
                self.settle(node, r)
            }
            Ir::Call(h, args) => {
                let h = self.fold(h, specs);
                let args: Vec<Arc<Ir>> = args.iter().map(|a| self.fold(a, specs)).collect();
                let node = Arc::new(Ir::Call(h, args));
                let Ir::Call(h, args) = &*node else { unreachable!() };
                // The definitions the function runs: a definition's, or
                // those a closure known when compiling holds.
                let defs = match &**h {
                    Ir::Global(d) => vec![d.0],
                    Ir::Static(v, id) => match v.globals(*id) {
                        Some(ds) => ds,
                        None => return node,
                    },
                    Ir::ConFn(_) => Vec::new(),
                    _ => return node,
                };
                if !args.iter().all(|a| is_static(g, a)) {
                    return node;
                }
                let r = match self.g.fold_work.get() {
                    None => Err(Kept::Unproved),
                    Some(_) => match defs.iter().try_for_each(|d| self.pure_def(DefId(specs.origin(*d)))) {
                        Err(k) => Err(k),
                        Ok(()) => self.run(&node, specs),
                    },
                };
                self.settle(node, r)
            }
        }
    }

    /// `node`'s value where it has one, else `node`, kept.
    fn settle(&mut self, node: Arc<Ir>, r: Result<Arc<Ir>, Kept>) -> Arc<Ir> {
        match r {
            Ok(v) => v,
            Err(k) => {
                self.kept.push((node.clone(), k));
                node
            }
        }
    }

    /// The value of closed `node`, computed by running it.
    fn run(&mut self, node: &Ir, specs: &crate::native::spec::Specs) -> Result<Arc<Ir>, Kept> {
        // Code with a part a key can't name exactly isn't remembered.
        let key = key(node);
        if let Some(r) = key.as_ref().and_then(|k| self.memo.get(k)) {
            return r.clone();
        }
        let work = self.g.fold_work.get().unwrap_or(crate::elab::CODEGEN_WORK);
        let (g, staged) = (self.g, self.staged);
        let ev = self.ev.get_or_insert_with(|| {
            let mut ev = crate::native::eval::Evaluator::for_folding(g, staged);
            ev.mirror(specs);
            ev
        });
        let r = match ev.eval_ir_limited(node, work) {
            Ok(v) => {
                let out = ev.within_program(|| from_word(v)).map(|(s, id)| Arc::new(Static::ir(&Arc::new(s), id))).ok_or(Kept::NoForm);
                ev.release(v);
                out
            }
            Err(e) => Err(Kept::Fails(e)),
        };
        if let Some(key) = key {
            self.memo.insert(key, r.clone());
        }
        r
    }

    /// Whether definition `d` and every definition it reaches can run when
    /// compiling: none is `partial` or a builtin that runs only when the
    /// program does, and no code waits on a cown.
    fn pure_def(&mut self, d: DefId) -> Result<(), Kept> {
        if let Some(r) = self.pure.get(&d) {
            return r.clone();
        }
        let g = self.g;
        let mut todo = vec![d];
        let mut seen = std::collections::HashSet::new();
        let mut r = Ok(());
        while let Some(x) = todo.pop() {
            if !seen.insert(x) {
                continue;
            }
            if let Some(known) = self.pure.get(&x) {
                if known.is_err() {
                    r = known.clone();
                    break;
                }
                continue;
            }
            let body = crate::native::ir::body_of(g, self.staged, x);
            let Some(info) = g.defs.get(x.0 as usize) else {
                // A staged definition: its body's.
                if let Some(b) = &body {
                    crate::core::defs_in(b, &mut todo);
                }
                continue;
            };
            if info.opaque && info.body.is_some() {
                r = Err(Kept::Partial);
                break;
            }
            if g.run_time_only.borrow().contains(&x) {
                r = Err(Kept::RunTime);
                break;
            }
            if let Some(b) = &body {
                if waits(b) {
                    r = Err(Kept::RunTime);
                    break;
                }
                crate::core::defs_in(b, &mut todo);
            }
        }
        self.pure.insert(d, r.clone());
        r
    }
}

/// Does `t` wait on a cown (`when`)?
fn waits(t: &Tm) -> bool {
    matches!(t, Tm::PrimApp(crate::core::Prim::When, _)) || t.any_sub(|x, _| waits(x))
}

/// Primitives computed when compiling: all but running in parallel,
/// waiting on cowns and building descriptors.
fn foldable_op(op: Op) -> bool {
    !matches!(op, Op::Par | Op::When | Op::TypeApply)
}

/// Data known when compiling: a literal, static data, an erased value, a
/// definition's or constructor's function (whose closure is static data),
/// or a constructor or tuple of such.
pub fn is_static(g: &Globals, ir: &Ir) -> bool {
    match ir {
        Ir::Lit(_) | Ir::Static(..) | Ir::Erased | Ir::ConFn(_) => true,
        Ir::Global(d) => g.defs.get(d.0 as usize).is_some_and(|i| matches!(i.ty, Tm::Pi(..)) && i.body.as_ref().is_none_or(|b| matches!(b, Tm::Lam(..)))),
        Ir::Con(_, xs) | Ir::Tuple(xs) => xs.iter().all(|x| is_static(g, x)),
        Ir::At(_, x) => is_static(g, x),
        _ => false,
    }
}

/// A static tuple's slots as it is laid out at run time, which a
/// projection's index counts: a last component that is a tuple is laid
/// out in place (`(a, (b, c))` is `(a, b, c)`).
fn components(g: &Globals, e: &Arc<Ir>) -> Option<Vec<Arc<Ir>>> {
    match &**e {
        Ir::Tuple(xs) if xs.iter().all(|x| is_static(g, x)) => {
            let mut out = xs.clone();
            // A static tuple of two or more as the last: its own slots.
            while let Some(more) = out.last().and_then(|l| match &**l {
                Ir::Tuple(ys) if ys.len() >= 2 => Some(ys.clone()),
                Ir::Static(v, id) => match v.node(*id) {
                    SNode::Obj { kind, fields, .. } if *kind == w::K_TUPLE && fields.len() >= 2 => {
                        Some(fields.iter().map(|f| Arc::new(Static::ir(v, *f))).collect())
                    }
                    _ => None,
                },
                _ => None,
            }) {
                out.pop();
                out.extend(more);
            }
            Some(out)
        }
        Ir::Static(v, id) => match v.node(*id) {
            SNode::Obj { kind, fields, .. } if *kind == w::K_TUPLE => Some(fields.iter().map(|f| Arc::new(Static::ir(v, *f))).collect()),
            _ => None,
        },
        _ => None,
    }
}

/// A static constructor's constructor and fields.
fn con_fields(g: &Globals, e: &Arc<Ir>) -> Option<(crate::core::ConId, Vec<Arc<Ir>>)> {
    match &**e {
        Ir::Con(c, xs) if xs.iter().all(|x| is_static(g, x)) => Some((*c, xs.clone())),
        Ir::Static(v, id) => Static::open_con(v, *id),
        _ => None,
    }
}

/// The arm of `match s` that static `s` takes, its fields bound in order.
fn choose(g: &Globals, s: &Arc<Ir>, c: &IrCase) -> Option<Ir> {
    if let Some((con, fields)) = con_fields(g, s) {
        return Some(match c.branches.iter().find(|(b, _, _)| *b == con) {
            Some((_, n, arm)) if *n == fields.len() => {
                let mut out = shift(arm, 0, 0);
                for (j, x) in fields.iter().enumerate().rev() {
                    out = Ir::Let(Arc::new(shift(x, j, 0)), Arc::new(out));
                }
                out
            }
            Some(_) => return None,
            None => shift(c.default.as_ref()?, fields.len(), 0),
        });
    }
    if let Ir::Lit(l) = &**s {
        let arm = c.lits.iter().find(|(x, _)| same_lit(x, l)).map(|(_, b)| b).or(c.default.as_ref())?;
        return Some(shift(arm, 0, 0));
    }
    None
}

fn same_lit(a: &Lit, b: &Lit) -> bool {
    match (a, b) {
        (Lit::Num(x), Lit::Num(y)) => x == y,
        (Lit::Big(x), Lit::Big(y)) => x == y,
        (Lit::Str(x), Lit::Str(y)) => x == y,
        (Lit::Bytes(x), Lit::Bytes(y)) => x == y,
        _ => false,
    }
}

/// Arithmetic and comparisons of numbers that fit in `i128`, computed
/// here; `None` for anything else (run instead).
fn arith(g: &Globals, op: Op, args: &[Arc<Ir>], nat: bool) -> Option<Result<Arc<Ir>, Kept>> {
    let num = |x: &Arc<Ir>| match &**x {
        Ir::Lit(Lit::Num(n)) => Some(*n),
        _ => None,
    };
    let wk = &g.well_known;
    let boolean = |b: bool| Some(Ok(Arc::new(Ir::Con(if b { wk.true_con? } else { wk.false_con? }, Vec::new()))));
    let n = |v: Option<i128>| v.map(|v| Ok(Arc::new(Ir::Lit(Lit::Num(v)))));
    match (op, args) {
        (Op::Neg, [a]) => n(num(a)?.checked_neg()),
        (_, [a, b]) => {
            let (a, b) = (num(a)?, num(b)?);
            match op {
                Op::Add => n(a.checked_add(b)),
                Op::Sub if nat && a < b => Some(Err(Kept::Fails("`Nat` subtraction below zero".into()))),
                Op::Sub => n(a.checked_sub(b)),
                Op::Mul => n(a.checked_mul(b)),
                Op::Eq => boolean(a == b),
                Op::Ne => boolean(a != b),
                Op::Lt => boolean(a < b),
                Op::Le => boolean(a <= b),
                Op::Gt => boolean(a > b),
                Op::Ge => boolean(a >= b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `b` with variable 0 replaced by closed `v`.
fn subst0(b: &Ir, v: &Arc<Ir>) -> Ir {
    fn go(b: &Ir, v: &Arc<Ir>, depth: usize) -> Ir {
        match b {
            Ir::Var(i) if *i == depth => shift(v, 0, 0),
            Ir::Var(i) if *i > depth => Ir::Var(i - 1),
            Ir::Var(i) => Ir::Var(*i),
            _ => b.map_subterms(|s, k| go(s, v, depth + k)),
        }
    }
    go(b, v, 0)
}

/// A key for closed code: equal keys, equal code. `None` for code with a
/// part it doesn't name exactly.
fn key(ir: &Ir) -> Option<String> {
    let mut out = String::new();
    write_key(ir, &mut out).then_some(out)
}

fn write_key(ir: &Ir, out: &mut String) -> bool {
    use std::fmt::Write;
    match ir {
        Ir::Lit(Lit::Num(n)) => write!(out, "{n}").unwrap(),
        Ir::Lit(Lit::Big(s)) => write!(out, "{s}").unwrap(),
        Ir::Lit(Lit::Str(s)) => write!(out, "{s:?}").unwrap(),
        Ir::Lit(Lit::Bytes(b)) => write!(out, "b{b:?}").unwrap(),
        Ir::Static(v, id) => write!(out, "#{:x}", v.hash_of(*id)).unwrap(),
        Ir::Erased => out.push('_'),
        Ir::Global(d) => write!(out, "g{}", d.0).unwrap(),
        Ir::Con(c, xs) => {
            write!(out, "c{}(", c.0).unwrap();
            for x in xs {
                if !write_key(x, out) {
                    return false;
                }
                out.push(',');
            }
            out.push(')');
        }
        Ir::Tuple(xs) => {
            out.push('(');
            for x in xs {
                if !write_key(x, out) {
                    return false;
                }
                out.push(',');
            }
            out.push(')');
        }
        Ir::At(_, x) => return write_key(x, out),
        Ir::Prim(op, xs, nat) => {
            write!(out, "{op:?}{nat}(").unwrap();
            for x in xs {
                if !write_key(x, out) {
                    return false;
                }
                out.push(',');
            }
            out.push(')');
        }
        Ir::Call(h, xs) => {
            if !write_key(h, out) {
                return false;
            }
            out.push('(');
            for x in xs {
                if !write_key(x, out) {
                    return false;
                }
                out.push(',');
            }
            out.push(')');
        }
        Ir::ConFn(c) => write!(out, "f{}", c.0).unwrap(),
        // Only closed code of the forms above is remembered.
        _ => return false,
    }
    true
}

/// A runtime value as static data, where it has a static form: numbers,
/// bytes, arrays, constructors and tuples of such. Walked with a stack of its own,
/// so a value of any depth takes the same stack.
pub fn from_word(v: w::W) -> Option<(Static, u32)> {
    let mut s = Static::default();
    let mut done: HashMap<w::W, u32> = HashMap::new();
    // Each object's parts, as first read.
    let mut parts: HashMap<w::W, Vec<w::W>> = HashMap::new();
    let mut stack: Vec<(w::W, bool)> = vec![(v, false)];
    while let Some((x, ready)) = stack.pop() {
        if done.contains_key(&x) {
            continue;
        }
        if !w::is_ptr(x) {
            done.insert(x, s.add(SNode::Word(x)));
            continue;
        }
        let k = w::kind(x);
        let id = match k {
            w::K_BYTES => s.add(SNode::Bytes(Arc::from(w::blob(x)))),
            w::K_BIG => {
                let n = checkers_rt::obj::num_of(x);
                let big: num_bigint::BigInt = n.to_string().parse().ok()?;
                s.add(SNode::Big(big))
            }
            w::K_CON | w::K_TUPLE => {
                let n = w::nfields(x);
                let part = |i: usize| if k == w::K_CON { w::field(x, i) } else { w::slot(x, i) };
                if !ready {
                    let ps: Vec<w::W> = (0..n).map(part).collect();
                    stack.push((x, true));
                    stack.extend(ps.iter().copied().filter(|p| !done.contains_key(p)).map(|p| (p, false)));
                    parts.insert(x, ps);
                    continue;
                }
                let fields: Box<[u32]> = parts[&x].iter().map(|p| done[p]).collect();
                let tag = if k == w::K_CON { w::con_of(x)? as u64 } else { 0 };
                s.add(SNode::Obj { kind: k, tag, fields })
            }
            checkers_rt::array::K_ARRAY => {
                use checkers_rt::array as a;
                let (layout, n) = (a::layout(x), a::len(x));
                let words = layout == a::Layout::Words;
                // An array of words that is a slice of another: no static form.
                if words && a::is_slice(x) {
                    return None;
                }
                // Each element: a word held (not a new reference), or a
                // packed element's word.
                // (Read once: a packed element past a word is a new object
                // each time it is read.)
                let part = |i: usize| if words { w::slot(x, i + 2) } else { a::get(x, i) };
                if !ready {
                    let ps: Vec<w::W> = (0..n).map(part).collect();
                    stack.push((x, true));
                    stack.extend(ps.iter().copied().filter(|p| !done.contains_key(p)).map(|p| (p, false)));
                    parts.insert(x, ps);
                    continue;
                }
                let elems: Box<[u32]> = parts[&x].iter().map(|p| done[p]).collect();
                s.add(SNode::Array { layout: layout as u8, elems })
            }
            _ => return None,
        };
        done.insert(x, id);
    }
    let root = done[&v];
    Some((s, root))
}

/// Each operation in `ir` on static data alone that `kept` doesn't keep:
/// a primitive computed when compiling, or a call of a definition or of
/// another function known when compiling.
pub fn residuals<'i>(g: &Globals, ir: &'i Ir, kept: &[(Arc<Ir>, Kept)], out: &mut Vec<&'i Ir>) {
    let is_kept = |x: &Ir| kept.iter().any(|(k, _)| std::ptr::eq(x, Arc::as_ptr(k)));
    let mut stack = vec![ir];
    while let Some(x) = stack.pop() {
        let operation = match x {
            Ir::Prim(op, args, _) => foldable_op(*op) && args.iter().all(|a| is_static(g, a)),
            Ir::Call(h, args) => matches!(&**h, Ir::Global(_) | Ir::Static(..) | Ir::ConFn(_)) && args.iter().all(|a| is_static(g, a)),
            _ => false,
        };
        if operation && !is_kept(x) {
            out.push(x);
        }
        stack.extend(x.subterms().into_iter().map(|(s, _)| s));
    }
}

/// An operation, for messages: its operator or function and its operands.
pub fn describe(g: &Globals, ir: &Ir) -> String {
    let arg = |a: &Ir| match a {
        Ir::Lit(Lit::Num(n)) => n.to_string(),
        Ir::Lit(Lit::Big(s)) => s.to_string(),
        Ir::Lit(Lit::Str(s)) => format!("{s:?}"),
        _ => "…".to_string(),
    };
    match ir {
        Ir::Prim(op, args, _) => {
            let sym = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Div => "/",
                Op::Rem => "%",
                Op::Neg => "-",
                Op::Eq => "==",
                Op::Ne => "!=",
                Op::Lt => "<",
                Op::Le => "<=",
                Op::Gt => ">",
                Op::Ge => ">=",
                Op::Concat => "++",
                Op::Len => "len",
                Op::Index => "indexing",
                Op::Par => "par",
                Op::When => "when",
                Op::TypeApply => "a type's descriptor",
            };
            match &args[..] {
                [a, b] if !matches!(op, Op::Index) && sym.len() <= 2 => format!("`{} {sym} {}`", arg(a), arg(b)),
                [a] if matches!(op, Op::Neg) => format!("`-{}`", arg(a)),
                _ => format!("`{sym}` of {}", args.iter().map(|a| arg(a)).collect::<Vec<_>>().join(", ")),
            }
        }
        Ir::Call(h, args) => {
            let f = match &**h {
                Ir::Global(d) => format!("`{}`", g.defs.get(d.0 as usize).map_or_else(|| format!("#{}", d.0), |i| i.name.to_string())),
                _ => "a closure".to_string(),
            };
            format!("a call of {f} on {}", args.iter().map(|a| arg(a)).collect::<Vec<_>>().join(", "))
        }
        _ => "an operation".to_string(),
    }
}
