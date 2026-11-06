//! The interpreter (M2, SPEC §13): runs erased core terms.
//!
//! Evaluation is strict. Calls in tail position (a function body's result,
//! the body of a `let`, a `match` arm) reuse the evaluator loop instead of
//! recursing, so tail-recursive loops run in constant stack space.

mod builtins;
pub mod ir;
pub mod num;
pub mod value;

use crate::core::{ConId, DefId, Globals, Mult, Prim, Tm};
use ir::{Compiler, Ir, IrCase};
use num::Num;
use std::collections::{HashMap, VecDeque};
use std::io::{BufRead, Write};
use std::rc::Rc;
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
    pub stdin: Box<dyn BufRead>,
    pub stdout: Box<dyn Write>,
    pub stderr: Box<dyn Write>,
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

enum Behaviour {
    When(Vec<Rc<std::cell::RefCell<Value>>>, Value),
    Fork(Rc<std::cell::RefCell<Option<Value>>>, Value),
    Join(Vec<Rc<std::cell::RefCell<Option<Value>>>>, Value, Rc<std::cell::RefCell<Option<Value>>>),
}

/// Constructors the runtime builds values with.
#[derive(Default)]
struct Known {
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

pub struct Interp<'g> {
    pub g: &'g Globals,
    code: HashMap<DefId, Rc<Ir>>,
    cache: Vec<Option<Value>>,
    true_v: Value,
    false_v: Value,
    pub io: Io,
    queue: VecDeque<Behaviour>,
    current: Option<DefId>,
    known: Known,
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
        let mk = |c: Option<ConId>| match c {
            Some(c) => Value::Con(c, Rc::from(Vec::new())),
            None => Value::Erased,
        };
        Interp {
            g,
            code: HashMap::new(),
            cache: vec![None; g.defs.len()],
            true_v: mk(known.true_con),
            false_v: mk(known.false_con),
            io,
            queue: VecDeque::new(),
            current: None,
            known,
        }
    }

    // ── errors ──────────────────────────────────────────────────────────────

    pub fn error(&self, msg: impl Into<String>) -> RtError {
        RtError { msg: msg.into(), in_fn: self.current.map(|d| self.g.defs[d.0 as usize].name.to_string()) }
    }

    // ── value helpers ───────────────────────────────────────────────────────

    fn con(&self, c: Option<ConId>, fields: Vec<Value>) -> Value {
        Value::Con(c.expect("standard library constructor"), Rc::from(fields))
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
        let info = &self.g.defs[d.0 as usize];
        let v = match &info.body {
            None => {
                let mut keep = Vec::new();
                let mut t = &info.ty;
                while let Tm::Pi(_, m, _, _, b) = t {
                    keep.push(*m != Mult::Zero);
                    t = b;
                }
                let name = format!("{}.{}", info.module, info.name);
                if !builtins::exists(&name) {
                    return Err(self.error(format!("`{name}` has no implementation in this interpreter yet")));
                }
                let b = Rc::new(BuiltinFn { name, keep });
                if b.keep.is_empty() {
                    builtins::call(self, &b.name, vec![])?
                } else {
                    Value::Builtin(b, Rc::new(Vec::new()))
                }
            }
            Some(body) => {
                let ir = self.code_of(d, body);
                let saved = self.current;
                self.current = Some(d);
                let v = self.eval(&ir, &None)?;
                self.current = saved;
                v
            }
        };
        if let Some(slot) = self.cache.get_mut(d.0 as usize) {
            *slot = Some(v.clone());
        }
        Ok(v)
    }

    fn code_of(&mut self, d: DefId, body: &Tm) -> Rc<Ir> {
        if let Some(c) = self.code.get(&d) {
            return c.clone();
        }
        // Staging (§8.9): compile-time calls are expanded before erasure. If
        // it fails, `checkers check` has reported why; running the unstaged
        // body computes the same values.
        let staged = if crate::stage::needs_staging(self.g, body) { crate::stage::stage(self.g, body).ok() } else { None };
        let body = staged.as_ref().unwrap_or(body);
        if std::env::var_os("CHECKERS_DUMP").is_some() {
            eprintln!("{} = {}", self.g.defs[d.0 as usize].name, crate::core::show(self.g, &[], body));
        }
        let c = Compiler { g: self.g, owner: Some(d) }.compile(body);
        self.code.insert(d, c.clone());
        c
    }

    /// Evaluate a closed core term (a `check`, say).
    pub fn eval_closed(&mut self, t: &Tm) -> R<Value> {
        let staged = if crate::stage::needs_staging(self.g, t) { crate::stage::stage(self.g, t).ok() } else { None };
        let t = staged.as_ref().unwrap_or(t);
        let ir = Compiler { g: self.g, owner: None }.compile(t);
        self.current = None;
        self.eval(&ir, &None)
    }

    // ── evaluation ──────────────────────────────────────────────────────────

    pub fn eval(&mut self, ir: &Rc<Ir>, env: &Env) -> R<Value> {
        let saved = self.current;
        let r = self.run(ir.clone(), env.clone());
        if r.is_ok() {
            self.current = saved;
        }
        r
    }

    fn run(&mut self, mut ir: Rc<Ir>, mut env: Env) -> R<Value> {
        loop {
            let (next, next_env) = match &*ir {
                Ir::Var(i) => return Ok(env_get(&env, *i).clone()),
                Ir::Global(d) => return self.global(*d),
                Ir::Erased => return Ok(Value::Erased),
                Ir::Lit(v) => return Ok(v.clone()),
                Ir::Fail(m) => return Err(self.error(format!("reached {m}"))),
                Ir::Lam(owner, b) => {
                    return Ok(Value::Clo(Rc::new(value::Closure { body: b.clone(), env: env.clone(), owner: *owner })))
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
                    return Ok(Value::Tuple(Rc::from(vs)));
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
                    return Ok(Value::Con(*c, Rc::from(vs)));
                }
                Ir::ConFn(c) => {
                    return Ok(if self.g.arity_con(*c) == 0 {
                        Value::Con(*c, Rc::from(Vec::new()))
                    } else {
                        Value::ConFn(*c, Rc::new(Vec::new()))
                    })
                }
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
    fn select(&self, v: &Value, c: &IrCase) -> R<(Rc<Ir>, usize)> {
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
                    return Ok(Value::Builtin(b, Rc::new(v)));
                }
                let kept: Vec<Value> = v.into_iter().zip(&b.keep).filter(|(_, k)| **k).map(|(x, _)| x).collect();
                builtins::call(self, &b.name, kept)
            }
            Value::ConFn(c, args) => {
                let mut v = (*args).clone();
                v.push(a);
                if v.len() < self.g.arity_con(c) {
                    return Ok(Value::ConFn(c, Rc::new(v)));
                }
                let ci = &self.g.cons[c.0 as usize];
                let np = self.g.arity_ty(ci.ty);
                let fields: Vec<Value> = v
                    .into_iter()
                    .skip(np)
                    .zip(&ci.fields)
                    .map(|(x, f)| if f.1 == Mult::Zero { Value::Erased } else { x })
                    .collect();
                Ok(Value::Con(c, Rc::from(fields)))
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

    fn prim(&mut self, p: &Prim, args: Vec<Value>, nat: bool) -> R<Value> {
        let a = || &args[0];
        let b = || &args[1];
        Ok(match p {
            Prim::Add => Value::Num(self.num(a())?.add(self.num(b())?)),
            Prim::Sub => {
                let (x, y) = (self.num(a())?, self.num(b())?);
                if nat && x < y {
                    return Err(self.error(format!("`-` on `Nat` would go below zero ({x} - {y})")));
                }
                Value::Num(x.sub(y))
            }
            Prim::Mul => Value::Num(self.num(a())?.mul(self.num(b())?)),
            Prim::Div | Prim::Rem => {
                let (x, y) = (self.num(a())?, self.num(b())?);
                if y.is_zero() {
                    let op = if *p == Prim::Div { "/" } else { "%" };
                    return Err(self.error(format!("`{op}` by zero ({x} {op} 0)")));
                }
                Value::Num(if *p == Prim::Div { x.div(y) } else { x.rem(y) })
            }
            Prim::Neg => Value::Num(self.num(a())?.neg()),
            Prim::Eq | Prim::Ne => {
                let e = value::equal(a(), b()).map_err(|what| self.error(format!("`==` can't compare {what}")))?;
                self.bool(if *p == Prim::Eq { e } else { !e })
            }
            Prim::Lt => self.bool(self.num(a())? < self.num(b())?),
            Prim::Le => self.bool(self.num(a())? <= self.num(b())?),
            Prim::Gt => self.bool(self.num(a())? > self.num(b())?),
            Prim::Ge => self.bool(self.num(a())? >= self.num(b())?),
            Prim::Concat => match (a(), b()) {
                (Value::Str(x), Value::Str(y)) => Value::Str(Rc::from(format!("{x}{y}"))),
                (Value::Bytes(x), Value::Bytes(y)) => Value::Bytes(x.iter().chain(y.iter()).copied().collect()),
                (x, y) => {
                    let mut items = self.list_items(x)?;
                    items.extend(self.list_items(y)?);
                    self.list(items)
                }
            },
            Prim::Len => match a() {
                Value::Str(s) => Value::nat(s.len()),
                Value::Bytes(b) => Value::nat(b.len()),
                other => Value::nat(self.list_items(other)?.len()),
            },
            Prim::Index => {
                let Value::Bytes(src) = a() else { return Err(self.error("indexing needs `Bytes`")) };
                let i = self.num(b())?;
                match i.to_usize().filter(|i| *i < src.len()) {
                    Some(i) => Value::nat(src[i] as usize),
                    None => return Err(self.error(format!("index {i} out of bounds for {} bytes", src.len()))),
                }
            }
            Prim::Format => Value::Str(Rc::from(value::format(self.g, a()))),
            Prim::Par => a().clone(),
            Prim::When => {
                let Value::Tuple(cs) = b() else { return Err(self.error("`when` needs cowns")) };
                let mut cowns = Vec::new();
                for c in cs.iter() {
                    match c {
                        Value::Cown(r) => cowns.push(r.clone()),
                        other => return Err(self.error(format!("`when` needs cowns, found a {}", other.kind()))),
                    }
                }
                self.queue.push_back(Behaviour::When(cowns, args[2].clone()));
                Value::unit()
            }
            Prim::Fork => {
                let fut = Rc::new(std::cell::RefCell::new(None));
                self.queue.push_back(Behaviour::Fork(fut.clone(), b().clone()));
                Value::Future(fut)
            }
            Prim::Join => {
                let Value::Tuple(fs) = b() else { return Err(self.error("`join` needs futures")) };
                let mut futs = Vec::new();
                for f in fs.iter() {
                    match f {
                        Value::Future(r) => futs.push(r.clone()),
                        other => return Err(self.error(format!("`join` needs futures, found a {}", other.kind()))),
                    }
                }
                let out = Rc::new(std::cell::RefCell::new(None));
                self.queue.push_back(Behaviour::Join(futs, args[2].clone(), out.clone()));
                Value::Future(out)
            }
            Prim::Builtin(n) => return Err(self.error(format!("unexpected primitive `{n}`"))),
        })
    }

    // ── behaviours (D44) ────────────────────────────────────────────────────

    /// Run scheduled behaviours until none remain.
    pub fn run_queue(&mut self) -> R<()> {
        let mut stalled = 0;
        while let Some(b) = self.queue.pop_front() {
            match b {
                Behaviour::When(cowns, f) => {
                    let contents: Vec<Value> = cowns.iter().map(|c| c.borrow().clone()).collect();
                    let r = self.apply_n(f, contents)?;
                    if cowns.len() == 1 {
                        *cowns[0].borrow_mut() = r;
                    } else {
                        let Value::Tuple(vs) = r else { return Err(self.error("`when` body must return a tuple")) };
                        for (c, v) in cowns.iter().zip(vs.iter()) {
                            *c.borrow_mut() = v.clone();
                        }
                    }
                    stalled = 0;
                }
                Behaviour::Fork(fut, f) => {
                    let v = self.apply(f, Value::unit())?;
                    *fut.borrow_mut() = Some(v);
                    stalled = 0;
                }
                Behaviour::Join(futs, f, out) => {
                    if futs.iter().any(|x| x.borrow().is_none()) {
                        // Causal order makes this unreachable with FIFO scheduling (D44).
                        stalled += 1;
                        if stalled > self.queue.len() + 1 {
                            return Err(self.error("a `join` waits on a future that is never filled"));
                        }
                        self.queue.push_back(Behaviour::Join(futs, f, out));
                        continue;
                    }
                    let vals: Vec<Value> = futs.iter().map(|x| x.borrow_mut().take().unwrap_or(Value::Erased)).collect();
                    let v = self.apply_n(f, vals)?;
                    *out.borrow_mut() = Some(v);
                    stalled = 0;
                }
            }
        }
        Ok(())
    }

    // ── main ────────────────────────────────────────────────────────────────

    pub fn system(&self) -> Value {
        let Some(c) = self.known.system else { return Value::Erased };
        let fields = self.g.cons[c.0 as usize]
            .fields
            .iter()
            .map(|f| match &*f.0 {
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
        Value::Con(c, Rc::from(fields))
    }

    /// Call `main` and return the process exit code (§13.4).
    pub fn run_main(&mut self, main: DefId, args: &[String]) -> R<u8> {
        let argv = self.list(args.iter().map(|a| Value::str(a)).collect());
        let sys = self.system();
        let f = self.global(main)?;
        self.current = Some(main);
        let mut r = self.apply_n(f, vec![argv, sys])?;
        self.run_queue()?;
        if let Value::Future(fut) = &r {
            let v = fut.borrow_mut().take();
            r = v.ok_or_else(|| self.error("`main`'s future was never filled"))?;
        }
        self.current = Some(main);
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
        let _ = self.io.stdout.flush();
        let _ = self.io.stderr.flush();
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
