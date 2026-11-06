//! The interpreter (M2, SPEC §13): runs erased core terms.
//!
//! Evaluation is strict. Calls in tail position (a function body's result,
//! the body of a `let`, a `match` arm) reuse the evaluator loop instead of
//! recursing, so tail-recursive loops run in constant stack space.

mod builtins;
pub mod ir;
mod sched;
pub use checkers_rt::num;
pub mod value;

use crate::core::{ConId, DefId, Globals, Mult, Tm};
use ir::{Compiler, Ir, IrCase, Op};
use num::Num;
use std::collections::VecDeque;
use std::io::{BufRead, Write};
use std::sync::{Arc, Mutex};
use value::{env_get, env_push, BuiltinFn, Cap, Env, Value};

/// A runtime error: an unproven obligation that failed (§13.3), or a bug.
#[derive(Debug)]
pub struct RtError {
    pub msg: String,
    pub in_fn: Option<String>,
}

impl std::fmt::Display for RtError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.in_fn {
            Some(n) => write!(f, "runtime error in `{n}`: {}", self.msg),
            None => write!(f, "runtime error: {}", self.msg),
        }
    }
}

pub type R<T> = Result<T, RtError>;

/// Standard streams, replaceable for tests.
pub struct Io {
    pub stdin: Box<dyn BufRead + Send>,
    pub stdout: Box<dyn Write + Send>,
    pub stderr: Box<dyn Write + Send>,
}

impl Io {
    pub fn process() -> Io {
        Io {
            stdin: Box::new(std::io::BufReader::new(std::io::stdin())),
            stdout: Box::new(std::io::BufWriter::new(std::io::stdout())),
            stderr: Box::new(std::io::stderr()),
        }
    }
}

pub(crate) enum Behaviour {
    When(Vec<Arc<value::Held<Value>>>, Value),
    Fork(Arc<value::Held<Option<Value>>>, Value),
    Join(Vec<Arc<value::Held<Option<Value>>>>, Value, Arc<value::Held<Option<Value>>>),
}

/// Constructors the runtime builds values with.
#[derive(Default, Clone, Copy)]
pub struct Known {
    true_con: Option<ConId>,
    false_con: Option<ConId>,
    some: Option<ConId>,
    none: Option<ConId>,
    ok: Option<ConId>,
    err: Option<ConId>,
    nil: Option<ConId>,
    cons: Option<ConId>,
    parsed: Option<ConId>,
    system: Option<ConId>,
    success: Option<ConId>,
    failure: Option<ConId>,
}

/// What the runtime needs of the checked program, shareable between
/// threads (M7): compiled code, builtins, and constructor tables.
pub struct Rt {
    pub names: Vec<String>,
    builtins: Vec<Option<Arc<BuiltinFn>>>,
    code: std::sync::RwLock<Vec<Option<Arc<Ir>>>>,
    pub cons: Vec<value::ConRt>,
    pub known: Known,
    system_fields: Vec<String>,
}

/// The evaluator: one per thread, sharing `Rt`, the standard streams and
/// the scheduler.
pub struct Machine {
    pub rt: Arc<Rt>,
    cache: Vec<Option<Value>>,
    true_v: Value,
    false_v: Value,
    pub io: Arc<Mutex<Io>>,
    queue: VecDeque<Behaviour>,
    current: Option<DefId>,
    known: Known,
    /// The multi-threaded scheduler, when running with more than one thread.
    pub(crate) sched: Option<Arc<sched::Shared>>,
    /// On a worker: where its pool will be, once started.
    pool_cell: Option<Arc<std::sync::OnceLock<Arc<sched::Shared>>>>,
}

/// A `Machine` plus the checked program, which it compiles code from.
pub struct Interp<'g> {
    pub g: &'g Globals,
    m: Machine,
    /// The staged program (§8.9), if staging ran: replacement bodies, and
    /// generated functions numbered after `g.defs`.
    staged: Option<std::rc::Rc<crate::stage::Staged>>,
}

impl<'g> std::ops::Deref for Interp<'g> {
    type Target = Machine;
    fn deref(&self) -> &Machine {
        &self.m
    }
}

impl<'g> std::ops::DerefMut for Interp<'g> {
    fn deref_mut(&mut self) -> &mut Machine {
        &mut self.m
    }
}

impl<'g> Interp<'g> {
    pub fn new(g: &'g Globals, io: Io) -> Interp<'g> {
        let wk = &g.well_known;
        let find = |module: &str, name: &str| {
            g.cons.iter().position(|c| {
                &*c.name == name && &*g.tys[c.ty.0 as usize].module == module
            }).map(|i| ConId(i as u32))
        };
        let known = Known {
            true_con: wk.true_con,
            false_con: wk.false_con,
            some: wk.some,
            none: wk.none,
            ok: wk.ok,
            err: wk.err,
            nil: wk.nil,
            cons: wk.cons,
            parsed: find("cursor", "Parsed"),
            system: find("system", "System"),
            success: find("system", "Success"),
            failure: find("system", "Failure"),
        };
        let mut builtins = Vec::new();
        for info in &g.defs {
            builtins.push(if info.body.is_none() {
                let mut keep = Vec::new();
                let mut t = &info.ty;
                while let Tm::Pi(_, m, _, _, b) = t {
                    keep.push(*m != Mult::Zero);
                    t = b;
                }
                Some(Arc::new(BuiltinFn { name: format!("{}.{}", info.module, info.name), keep }))
            } else {
                None
            });
        }
        let cons = g
            .cons
            .iter()
            .enumerate()
            .map(|(k, ci)| value::ConRt {
                name: ci.name.to_string(),
                arity: g.arity_con(ConId(k as u32)),
                np: g.arity_ty(ci.ty),
                erased: ci.fields.iter().map(|f| f.1 == Mult::Zero).collect(),
                shown: ci.fields.iter().map(|f| f.2 == crate::core::Icit::Expl && f.1 != Mult::Zero).collect(),
            })
            .collect();
        let system_fields = known.system.map(|c| g.cons[c.0 as usize].fields.iter().map(|f| f.0.to_string()).collect()).unwrap_or_default();
        let rt = Rt {
            names: g.defs.iter().map(|d| d.name.to_string()).collect(),
            builtins,
            code: std::sync::RwLock::new(vec![None; g.defs.len()]),
            cons,
            known,
            system_fields,
        };
        Interp { g, m: Machine::new(Arc::new(rt), Arc::new(Mutex::new(io))), staged: None }
    }

    /// Run the staged program rather than the elaborated one.
    pub fn with_staged(mut self, s: std::rc::Rc<crate::stage::Staged>) -> Self {
        let rt = Arc::get_mut(&mut self.m.rt).expect("staging is set before running");
        rt.names.extend(s.extra.iter().map(|e| e.0.clone()));
        rt.builtins.resize(self.g.defs.len() + s.extra.len(), None);
        rt.code.get_mut().unwrap().resize(self.g.defs.len() + s.extra.len(), None);
        self.m.cache.resize(self.g.defs.len() + s.extra.len(), None);
        self.staged = Some(s);
        self
    }

    /// The body to run for `d`: staged, generated, or elaborated.
    fn body_of(&self, d: DefId) -> Option<Tm> {
        body_of(self.g, self.staged.as_deref(), d)
    }

    /// Compile `d` and everything its code refers to, so that running it
    /// never needs the checked program (worker threads don't have it).
    fn prepare(&mut self, roots: Vec<DefId>) {
        let mut todo = roots;
        while let Some(d) = todo.pop() {
            if self.m.rt.code.read().unwrap().get(d.0 as usize).is_none_or(|c| c.is_some()) {
                continue;
            }
            let Some(body) = self.body_of(d) else { continue };
            if std::env::var_os("CHECKERS_DUMP").is_some() {
                eprintln!("{} = {}", self.m.def_name(d), crate::core::show(self.g, &[], &body));
            }
            let c = Compiler { g: self.g, owner: Some(d) }.compile(&body);
            globals_in(&c, &mut todo);
            self.m.rt.code.write().unwrap()[d.0 as usize] = Some(c);
        }
    }

    /// Evaluate a closed core term (a `check`, say).
    pub fn eval_closed(&mut self, t: &Tm) -> R<Value> {
        let ir = Compiler { g: self.g, owner: None }.compile(t);
        let mut roots = Vec::new();
        globals_in(&ir, &mut roots);
        self.prepare(roots);
        self.m.current = None;
        self.m.eval(&ir, &None)
    }

    /// Call `main` and return the process exit code (§13.4). With more than
    /// one thread, behaviours run on a pool as soon as they are runnable (D66).
    pub fn run_main(&mut self, main: DefId, args: &[String], threads: usize) -> R<u8> {
        self.prepare(vec![main]);
        if threads > 1 {
            self.m.sched = Some(sched::start(self.m.rt.clone(), self.m.io.clone(), threads));
        }
        let r = self.m.run_main(main, args);
        if let Some(s) = self.m.sched.clone() {
            let waited = s.finish(&mut self.m);
            self.m.sched = None;
            let r = r?;
            waited?;
            return self.m.exit_code(r);
        }
        let r = r?;
        self.m.exit_code(r)
    }
}

/// The body to run for `d`: staged, generated (numbered after `g.defs`), or
/// elaborated. Shared with native code (§14).
pub fn body_of(g: &Globals, staged: Option<&crate::stage::Staged>, d: DefId) -> Option<Tm> {
    let n = g.defs.len();
    if let Some(s) = staged {
        if (d.0 as usize) >= n {
            return s.extra.get(d.0 as usize - n).map(|e| e.1.clone());
        }
        if let Some(b) = s.bodies.get(&d) {
            return Some(b.clone());
        }
    }
    g.defs.get(d.0 as usize).and_then(|i| i.body.clone())
}

/// The definitions compiled code refers to.
pub fn globals_in(ir: &Ir, out: &mut Vec<DefId>) {
    match ir {
        Ir::Global(d) => out.push(*d),
        Ir::Lam(_, b) => globals_in(b, out),
        Ir::Call(h, xs) => {
            globals_in(h, out);
            xs.iter().for_each(|x| globals_in(x, out));
        }
        Ir::Let(a, b) => {
            globals_in(a, out);
            globals_in(b, out);
        }
        Ir::Tuple(xs) | Ir::Con(_, xs) | Ir::Prim(_, xs, _) | Ir::Par(xs) => xs.iter().for_each(|x| globals_in(x, out)),
        Ir::Proj(x, _) | Ir::Field(x, _) => globals_in(x, out),
        Ir::Case(s, c) => {
            globals_in(s, out);
            c.branches.iter().for_each(|(_, _, b)| globals_in(b, out));
            c.lits.iter().for_each(|(_, b)| globals_in(b, out));
            if let Some(d) = &c.default {
                globals_in(d, out);
            }
        }
        _ => {}
    }
}

impl Machine {
    pub fn new(rt: Arc<Rt>, io: Arc<Mutex<Io>>) -> Machine {
        let known = rt.known;
        let mk = |c: Option<ConId>| match c {
            Some(c) => Value::Con(c, Arc::from(Vec::new())),
            None => Value::Erased,
        };
        let n = rt.names.len();
        Machine {
            cache: vec![None; n],
            true_v: mk(known.true_con),
            false_v: mk(known.false_con),
            rt,
            io,
            queue: VecDeque::new(),
            current: None,
            known,
            sched: None,
            pool_cell: None,
        }
    }

    pub fn def_name(&self, d: DefId) -> String {
        self.rt.names.get(d.0 as usize).cloned().unwrap_or_default()
    }

    pub fn error(&self, msg: impl Into<String>) -> RtError {
        RtError { msg: msg.into(), in_fn: self.current.map(|d| self.def_name(d)) }
    }

    fn con(&self, c: Option<ConId>, fields: Vec<Value>) -> Value {
        Value::Con(c.expect("standard library constructor"), Arc::from(fields))
    }

    pub fn bool(&self, b: bool) -> Value {
        if b {
            self.true_v.clone()
        } else {
            self.false_v.clone()
        }
    }

    pub fn some(&self, v: Value) -> Value {
        self.con(self.known.some, vec![v])
    }

    pub fn none(&self) -> Value {
        self.con(self.known.none, vec![])
    }

    pub fn ok(&self, v: Value) -> Value {
        self.con(self.known.ok, vec![v])
    }

    pub fn err(&self, v: Value) -> Value {
        self.con(self.known.err, vec![v])
    }

    pub fn list(&self, items: Vec<Value>) -> Value {
        let mut l = self.con(self.known.nil, vec![]);
        for v in items.into_iter().rev() {
            l = self.con(self.known.cons, vec![v, l]);
        }
        l
    }

    pub fn list_items(&self, mut v: &Value) -> R<Vec<Value>> {
        let mut out = Vec::new();
        loop {
            match v {
                Value::Con(c, f) if Some(*c) == self.known.cons => {
                    out.push(f[0].clone());
                    v = &f[1];
                }
                Value::Con(c, _) if Some(*c) == self.known.nil => return Ok(out),
                other => return Err(self.error(format!("expected a list, found a {}", other.kind()))),
            }
        }
    }

    /// A `Parsed` record (cursor.ck): the value and the index after it.
    pub fn parsed(&self, v: Value, stop: usize) -> Value {
        self.con(self.known.parsed, vec![v, Value::nat(stop)])
    }

    pub fn is_false(&self, v: &Value) -> bool {
        matches!(v, Value::Con(c, _) if Some(*c) == self.known.false_con)
    }

    // ── globals ─────────────────────────────────────────────────────────────

    fn global(&mut self, d: DefId) -> R<Value> {
        if let Some(Some(v)) = self.cache.get(d.0 as usize) {
            return Ok(v.clone());
        }
        // This machine's own copy of the code (`ir::private`).
        let code = self.rt.code.read().unwrap().get(d.0 as usize).cloned().flatten().map(|c| ir::private(&c));
        let v = match code {
            Some(ir) => {
                let saved = self.current;
                self.current = Some(d);
                let v = self.eval(&ir, &None)?;
                self.current = saved;
                v
            }
            None => {
                let Some(b) = self.rt.builtins.get(d.0 as usize).cloned().flatten() else {
                    return Err(self.error(format!("`{}` was not compiled (a bug)", self.def_name(d))));
                };
                if !builtins::exists(&b.name) {
                    return Err(self.error(format!("`{}` has no implementation in this interpreter yet", b.name)));
                }
                if b.keep.is_empty() {
                    builtins::call(self, &b.name, vec![])?
                } else {
                    Value::Builtin(b, Arc::new(Vec::new()))
                }
            }
        };
        if let Some(slot) = self.cache.get_mut(d.0 as usize) {
            *slot = Some(v.clone());
        }
        Ok(v)
    }

    // ── evaluation ──────────────────────────────────────────────────────────

    pub fn eval(&mut self, ir: &Arc<Ir>, env: &Env) -> R<Value> {
        let saved = self.current;
        let r = self.run(ir.clone(), env.clone());
        if r.is_ok() {
            self.current = saved;
        }
        r
    }

    fn run(&mut self, mut ir: Arc<Ir>, mut env: Env) -> R<Value> {
        loop {
            let (next, next_env) = match &*ir {
                Ir::Var(i) => return Ok(env_get(&env, *i).clone()),
                Ir::Global(d) => return self.global(*d),
                Ir::Erased => return Ok(Value::Erased),
                Ir::Lit(v) => return Ok(v.clone()),
                Ir::Fail(m) => return Err(self.error(format!("reached {m}"))),
                Ir::Lam(owner, b) => {
                    return Ok(Value::Clo(Arc::new(value::Closure { body: b.clone(), env: env.clone(), owner: *owner })))
                }
                Ir::Call(h, spine) => {
                    // Evaluate the head, then every argument left to right (§13.2),
                    // then enter the body without building intermediate closures.
                    let mut fv = self.eval(h, &env)?;
                    let mut args = Vec::with_capacity(spine.len());
                    for a in spine {
                        args.push(self.eval(a, &env)?);
                    }
                    let mut args = args.into_iter();
                    loop {
                        let Some(av) = args.next() else { return Ok(fv) };
                        match fv {
                            Value::Clo(c) => {
                                if c.owner.is_some() {
                                    self.current = c.owner;
                                }
                                let mut body = c.body.clone();
                                let mut e = env_push(&c.env, av);
                                // Further arguments go straight into nested lambdas.
                                while args.len() > 0 {
                                    let Ir::Lam(_, b) = &*body else { break };
                                    let b = b.clone();
                                    e = env_push(&e, args.next().unwrap_or(Value::Erased));
                                    body = b;
                                }
                                if args.len() == 0 {
                                    break (body, e);
                                }
                                fv = self.eval(&body, &e)?;
                            }
                            other => fv = self.apply(other, av)?,
                        }
                    }
                }
                Ir::Let(v, b) => {
                    let vv = self.eval(v, &env)?;
                    (b.clone(), env_push(&env, vv))
                }
                Ir::Case(s, c) => {
                    let sv = self.eval(s, &env)?;
                    let (body, n) = self.select(&sv, c)?;
                    let mut e = env.clone();
                    if n > 0 {
                        if let Value::Con(_, fields) = &sv {
                            for k in 0..n {
                                e = env_push(&e, fields.get(k).cloned().unwrap_or(Value::Erased));
                            }
                        }
                    }
                    (body, e)
                }
                Ir::Tuple(xs) => {
                    let mut vs = Vec::with_capacity(xs.len());
                    for x in xs {
                        vs.push(self.eval(x, &env)?);
                    }
                    return Ok(Value::Tuple(Arc::from(vs)));
                }
                Ir::Proj(x, i) => {
                    return match self.eval(x, &env)? {
                        Value::Tuple(vs) => Ok(vs[*i].clone()),
                        other => Err(self.error(format!("expected a tuple, found a {}", other.kind()))),
                    }
                }
                Ir::Field(x, i) => {
                    return match self.eval(x, &env)? {
                        Value::Con(_, fs) => Ok(fs[*i].clone()),
                        other => Err(self.error(format!("expected a record, found a {}", other.kind()))),
                    }
                }
                Ir::Con(c, xs) => {
                    let mut vs = Vec::with_capacity(xs.len());
                    for x in xs {
                        vs.push(self.eval(x, &env)?);
                    }
                    return Ok(Value::Con(*c, Arc::from(vs)));
                }
                Ir::ConFn(c) => {
                    return Ok(if self.rt.cons[c.0 as usize].arity == 0 {
                        Value::Con(*c, Arc::from(Vec::new()))
                    } else {
                        Value::ConFn(*c, Arc::new(Vec::new()))
                    })
                }
                Ir::Par(xs) => return self.par(xs, &env),
                Ir::Prim(p, args, nat) => {
                    let mut vs = Vec::with_capacity(args.len());
                    for a in args {
                        vs.push(self.eval(a, &env)?);
                    }
                    return self.prim(p, vs, *nat);
                }
            };
            ir = next;
            env = next_env;
        }
    }

    /// The arm for `v`, and how many fields it binds.
    fn select(&self, v: &Value, c: &IrCase) -> R<(Arc<Ir>, usize)> {
        match v {
            Value::Con(con, _) => {
                for (bc, n, body) in &c.branches {
                    if bc == con {
                        return Ok((body.clone(), *n));
                    }
                }
            }
            Value::Num(_) | Value::Str(_) | Value::Bytes(_) => {
                for (l, body) in &c.lits {
                    if value::equal(l, v).unwrap_or(false) {
                        return Ok((body.clone(), 0));
                    }
                }
            }
            _ => {}
        }
        match &c.default {
            Some(d) => Ok((d.clone(), 0)),
            None => Err(self.error(format!("no `match` arm for this {}", v.kind()))),
        }
    }

    /// Apply a function value to one argument.
    pub fn apply(&mut self, f: Value, a: Value) -> R<Value> {
        match f {
            Value::Clo(c) => {
                let saved = self.current;
                if c.owner.is_some() {
                    self.current = c.owner;
                }
                let r = self.run(c.body.clone(), env_push(&c.env, a));
                if r.is_ok() {
                    self.current = saved;
                }
                r
            }
            Value::Builtin(b, args) => {
                let mut v = (*args).clone();
                v.push(a);
                if v.len() < b.keep.len() {
                    return Ok(Value::Builtin(b, Arc::new(v)));
                }
                let kept: Vec<Value> = v.into_iter().zip(&b.keep).filter(|(_, k)| **k).map(|(x, _)| x).collect();
                builtins::call(self, &b.name, kept)
            }
            Value::ConFn(c, args) => {
                let mut v = (*args).clone();
                v.push(a);
                let ci = &self.rt.cons[c.0 as usize];
                if v.len() < ci.arity {
                    return Ok(Value::ConFn(c, Arc::new(v)));
                }
                let fields: Vec<Value> = v
                    .into_iter()
                    .skip(ci.np)
                    .zip(&ci.erased)
                    .map(|(x, erased)| if *erased { Value::Erased } else { x })
                    .collect();
                Ok(Value::Con(c, Arc::from(fields)))
            }
            Value::Erased => Ok(Value::Erased),
            other => Err(self.error(format!("applied a {} as a function", other.kind()))),
        }
    }

    pub fn apply_n(&mut self, f: Value, args: Vec<Value>) -> R<Value> {
        let mut v = f;
        for a in args {
            v = self.apply(v, a)?;
        }
        Ok(v)
    }

    fn num<'a>(&self, v: &'a Value) -> R<&'a Num> {
        match v {
            Value::Num(n) => Ok(n),
            other => Err(self.error(format!("expected a number, found a {}", other.kind()))),
        }
    }

    fn prim(&mut self, p: &Op, args: Vec<Value>, nat: bool) -> R<Value> {
        let a = || &args[0];
        let b = || &args[1];
        Ok(match p {
            Op::Add => Value::Num(self.num(a())?.add(self.num(b())?)),
            Op::Sub => {
                let (x, y) = (self.num(a())?, self.num(b())?);
                if nat && x < y {
                    return Err(self.error(format!("`-` on `Nat` would go below zero ({x} - {y})")));
                }
                Value::Num(x.sub(y))
            }
            Op::Mul => Value::Num(self.num(a())?.mul(self.num(b())?)),
            Op::Div | Op::Rem => {
                let (x, y) = (self.num(a())?, self.num(b())?);
                if y.is_zero() {
                    let op = if *p == Op::Div { "/" } else { "%" };
                    return Err(self.error(format!("`{op}` by zero ({x} {op} 0)")));
                }
                Value::Num(if *p == Op::Div { x.div(y) } else { x.rem(y) })
            }
            Op::Neg => Value::Num(self.num(a())?.neg()),
            Op::Eq | Op::Ne => {
                let e = value::equal(a(), b()).map_err(|what| self.error(format!("`==` can't compare {what}")))?;
                self.bool(if *p == Op::Eq { e } else { !e })
            }
            Op::Lt => self.bool(self.num(a())? < self.num(b())?),
            Op::Le => self.bool(self.num(a())? <= self.num(b())?),
            Op::Gt => self.bool(self.num(a())? > self.num(b())?),
            Op::Ge => self.bool(self.num(a())? >= self.num(b())?),
            Op::Concat => match (a(), b()) {
                (Value::Str(x), Value::Str(y)) => Value::Str(Arc::from(format!("{x}{y}"))),
                (Value::Bytes(x), Value::Bytes(y)) => Value::Bytes(x.iter().chain(y.iter()).copied().collect()),
                (x, y) => {
                    let mut items = self.list_items(x)?;
                    items.extend(self.list_items(y)?);
                    self.list(items)
                }
            },
            Op::Len => match a() {
                Value::Str(s) => Value::nat(s.len()),
                Value::Bytes(b) => Value::nat(b.len()),
                other => Value::nat(self.list_items(other)?.len()),
            },
            Op::Index => {
                let Value::Bytes(src) = a() else { return Err(self.error("indexing needs `Bytes`")) };
                let i = self.num(b())?;
                match i.to_usize().filter(|i| *i < src.len()) {
                    Some(i) => Value::nat(src[i] as usize),
                    None => return Err(self.error(format!("index {i} out of bounds for {} bytes", src.len()))),
                }
            }
            Op::Format => Value::Str(Arc::from(value::format(&self.rt, a()))),
            Op::Par => a().clone(),
            Op::When => {
                let Value::Tuple(cs) = b() else { return Err(self.error("`when` needs cowns")) };
                let mut cowns = Vec::new();
                for c in cs.iter() {
                    match c {
                        Value::Cown(r) => cowns.push(r.clone()),
                        other => return Err(self.error(format!("`when` needs cowns, found a {}", other.kind()))),
                    }
                }
                self.schedule(Behaviour::When(cowns, args[2].clone()));
                Value::unit()
            }
            Op::Fork => {
                let fut = value::Held::new(None);
                self.schedule(Behaviour::Fork(fut.clone(), b().clone()));
                Value::Future(fut)
            }
            Op::Join => {
                let Value::Tuple(fs) = b() else { return Err(self.error("`join` needs futures")) };
                let mut futs = Vec::new();
                for f in fs.iter() {
                    match f {
                        Value::Future(r) => futs.push(r.clone()),
                        other => return Err(self.error(format!("`join` needs futures, found a {}", other.kind()))),
                    }
                }
                let out = value::Held::new(None);
                self.schedule(Behaviour::Join(futs, args[2].clone(), out.clone()));
                Value::Future(out)
            }
        })
    }

    // ── behaviours (D44, D66) ───────────────────────────────────────────────

    /// Schedule a behaviour: on the pool if there is one, else on the FIFO queue.
    fn schedule(&mut self, b: Behaviour) {
        if self.sched.is_none() {
            self.sched = self.pool_cell.as_ref().and_then(|c| c.get().cloned());
        }
        match &self.sched {
            Some(s) => {
                let res: Vec<&checkers_rt::sched::Resource> = match &b {
                    Behaviour::When(cs, _) => cs.iter().map(|c| &c.res).collect(),
                    Behaviour::Fork(f, _) => vec![&f.res],
                    Behaviour::Join(fs, _, out) => fs.iter().map(|c| &c.res).chain(std::iter::once(&out.res)).collect(),
                };
                // The behaviour holds its cells, so they outlive their queues.
                let res: Vec<&'static checkers_rt::sched::Resource> =
                    res.into_iter().map(|r| unsafe { &*(r as *const checkers_rt::sched::Resource) }).collect();
                s.submit(&res, b)
            }
            None => self.queue.push_back(b),
        }
    }

    /// Run one behaviour. `ready`: the scheduler guarantees its futures are
    /// filled; on the FIFO queue a `join` may have to wait its turn.
    pub(crate) fn run_behaviour(&mut self, b: Behaviour, ready: bool) -> R<Option<Behaviour>> {
        match b {
            Behaviour::When(cowns, f) => {
                let contents: Vec<Value> = cowns.iter().map(|c| c.lock().unwrap().clone()).collect();
                let r = self.apply_n(f, contents)?;
                if cowns.len() == 1 {
                    *cowns[0].lock().unwrap() = r;
                } else {
                    let Value::Tuple(vs) = r else { return Err(self.error("`when` body must return a tuple")) };
                    for (c, v) in cowns.iter().zip(vs.iter()) {
                        *c.lock().unwrap() = v.clone();
                    }
                }
            }
            Behaviour::Fork(fut, f) => {
                let v = self.apply(f, Value::unit())?;
                *fut.lock().unwrap() = Some(v);
            }
            Behaviour::Join(futs, f, out) => {
                if !ready && futs.iter().any(|x| x.lock().unwrap().is_none()) {
                    return Ok(Some(Behaviour::Join(futs, f, out)));
                }
                let vals: Vec<Value> = futs.iter().map(|x| x.lock().unwrap().take().unwrap_or(Value::Erased)).collect();
                let v = self.apply_n(f, vals)?;
                *out.lock().unwrap() = Some(v);
            }
        }
        Ok(None)
    }

    /// Run the FIFO queue until it is empty (D44, `--threads 1`).
    pub fn run_queue(&mut self) -> R<()> {
        let mut stalled = 0;
        while let Some(b) = self.queue.pop_front() {
            match self.run_behaviour(b, false)? {
                // Causal order makes this unreachable with FIFO scheduling (D44).
                Some(waiting) => {
                    stalled += 1;
                    if stalled > self.queue.len() + 1 {
                        return Err(self.error("a `join` waits on a future that is never filled"));
                    }
                    self.queue.push_back(waiting);
                }
                None => stalled = 0,
            }
        }
        Ok(())
    }

    /// `par (e1, …, en)` (D69): components on threads while the pool has
    /// room, the rest here; the result is the same tuple either way.
    fn par(&mut self, xs: &[Arc<Ir>], env: &Env) -> R<Value> {
        let sched = self.sched.clone();
        let take = |n: usize| sched.as_ref().map_or(0, |s| s.take_par(n));
        let spawned = take(xs.len().saturating_sub(1));
        if spawned == 0 {
            let mut vs = Vec::with_capacity(xs.len());
            for x in xs {
                vs.push(self.eval(x, env)?);
            }
            return Ok(Value::Tuple(Arc::from(vs)));
        }
        let (rt, io, current) = (self.rt.clone(), self.io.clone(), self.current);
        let results: Vec<R<Value>> = std::thread::scope(|sc| {
            let mut handles = Vec::new();
            for x in &xs[..spawned] {
                let (rt, io, sched, env) = (rt.clone(), io.clone(), sched.clone(), env.clone());
                let h = std::thread::Builder::new()
                    .stack_size(256 << 20)
                    .spawn_scoped(sc, move || {
                        let mut m = Machine::new(rt, io);
                        m.sched = sched;
                        m.current = current;
                        m.eval(x, &env)
                    })
                    .expect("spawn a `par` thread");
                handles.push(h);
            }
            let mut rest = Vec::new();
            for x in &xs[spawned..] {
                rest.push(self.eval(x, env));
            }
            let mut out: Vec<R<Value>> = handles.into_iter().map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e))).collect();
            out.extend(rest);
            out
        });
        if let Some(s) = &sched {
            s.give_par(spawned);
        }
        let mut vs = Vec::with_capacity(xs.len());
        for r in results {
            vs.push(r?);
        }
        Ok(Value::Tuple(Arc::from(vs)))
    }

    // ── main ────────────────────────────────────────────────────────────────

    pub fn system(&self) -> Value {
        let Some(c) = self.known.system else { return Value::Erased };
        let fields = self
            .rt
            .system_fields
            .iter()
            .map(|f| match f.as_str() {
                "term" => Value::Cap(Cap::Term),
                "fs" => Value::Cap(Cap::Fs(None)),
                "env" => Value::Cap(Cap::Env),
                "proc" => Value::Cap(Cap::Proc),
                "net" => Value::Cap(Cap::Net),
                "clock" => Value::Cap(Cap::Clock),
                "sched" => Value::Cap(Cap::Sched),
                _ => Value::Erased,
            })
            .collect::<Vec<_>>();
        Value::Con(c, Arc::from(fields))
    }

    /// Call `main`; with the FIFO scheduler, also run its behaviours.
    pub fn run_main(&mut self, main: DefId, args: &[String]) -> R<Value> {
        let argv = self.list(args.iter().map(|a| Value::str(a)).collect());
        let sys = self.system();
        let f = self.global(main)?;
        self.current = Some(main);
        let r = self.apply_n(f, vec![argv, sys])?;
        if self.sched.is_none() {
            self.run_queue()?;
        }
        self.current = Some(main);
        Ok(r)
    }

    /// The process exit code `main`'s result stands for (§13.4).
    pub fn exit_code(&mut self, mut r: Value) -> R<u8> {
        if let Value::Future(fut) = &r {
            let v = fut.lock().unwrap().take();
            r = v.ok_or_else(|| self.error("`main`'s future was never filled"))?;
        }
        match &r {
            Value::Con(c, _) if Some(*c) == self.known.success => Ok(0),
            Value::Con(c, f) if Some(*c) == self.known.failure => {
                let n = self.num(&f[0])?;
                match n.to_u32().filter(|n| (1..=255).contains(n)) {
                    Some(n) => Ok(n as u8),
                    None => Err(self.error(format!("`Failure {n}`: an exit code must be between 1 and 255"))),
                }
            }
            other => Err(self.error(format!("`main` returned a {}, not an `ExitCode`", other.kind()))),
        }
    }

    pub fn flush(&mut self) {
        let mut io = self.io.lock().unwrap();
        let _ = io.stdout.flush();
        let _ = io.stderr.flush();
    }
}

/// Run `f` on a thread with a large stack: non-tail recursion (over a long
/// list, say) nests Rust frames.
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("spawn interpreter thread")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}
