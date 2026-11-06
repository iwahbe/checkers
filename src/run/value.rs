//! Runtime values (§13.1): what is left after erasure.

use super::ir::Ir;
use super::num::{Decimal, Num};
use crate::core::{ConId, DefId};
use std::sync::Mutex;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::PathBuf;
use std::sync::Arc;

/// A persistent environment: index 0 is the innermost binder.
pub type Env = Option<Arc<EnvNode>>;

pub struct EnvNode {
    pub v: Value,
    pub next: Env,
}

pub fn env_push(env: &Env, v: Value) -> Env {
    Some(Arc::new(EnvNode { v, next: env.clone() }))
}

pub fn env_get(env: &Env, mut i: usize) -> &Value {
    let mut cur = env.as_ref().expect("unbound variable at run time");
    while i > 0 {
        cur = cur.next.as_ref().expect("unbound variable at run time");
        i -= 1;
    }
    &cur.v
}

pub struct Closure {
    pub body: Arc<Ir>,
    pub env: Env,
    /// The definition this code belongs to, for error messages.
    pub owner: Option<DefId>,
}

/// A builtin waiting for more arguments.
pub struct BuiltinFn {
    pub name: String,
    /// One entry per parameter: false for erased (`ghost`, implicit) parameters.
    pub keep: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cap {
    Term,
    /// The file system, optionally confined to a directory (`files.within`).
    Fs(Option<Arc<PathBuf>>),
    Env,
    Proc,
    Net,
    Clock,
    Sched,
}

pub enum FileState {
    Read(BufReader<File>),
    Write(BufWriter<File>),
}

#[derive(Clone)]
pub enum Value {
    Num(Num),
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
    /// A constructor with its fields (type parameters dropped; erased fields are `Erased`).
    Con(ConId, Arc<[Value]>),
    Tuple(Arc<[Value]>),
    Clo(Arc<Closure>),
    /// A constructor applied to fewer arguments (parameters + fields) than it takes.
    ConFn(ConId, Arc<Vec<Value>>),
    Builtin(Arc<BuiltinFn>, Arc<Vec<Value>>),
    /// A type, proof or ghost value.
    Erased,
    Cap(Cap),
    /// An open file; `None` once closed.
    File(Arc<Mutex<Option<FileState>>>),
    IoErr(Arc<str>),
    Decimal(Arc<Decimal>),
    /// A multiset of integers (D47): sorted (value, count) pairs.
    Bag(Arc<Vec<(Num, usize)>>),
    Cown(Arc<Held<Value>>),
    Future(Arc<Held<Option<Value>>>),
}

/// A cown's or future's contents, and its queue in the scheduler (D66).
pub struct Held<T> {
    pub res: checkers_rt::sched::Resource,
    pub v: Mutex<T>,
}

impl<T> Held<T> {
    pub fn new(v: T) -> Arc<Held<T>> {
        Arc::new(Held { res: checkers_rt::sched::Resource::default(), v: Mutex::new(v) })
    }
}

impl<T> std::ops::Deref for Held<T> {
    type Target = Mutex<T>;
    fn deref(&self) -> &Mutex<T> {
        &self.v
    }
}

impl Value {
    pub fn unit() -> Value {
        Value::Tuple(Arc::from(Vec::new()))
    }

    pub fn str(s: &str) -> Value {
        Value::Str(Arc::from(s))
    }

    pub fn nat(n: usize) -> Value {
        Value::Num(Num::from(n))
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Value::Num(_) => "number",
            Value::Str(_) => "string",
            Value::Bytes(_) => "bytes",
            Value::Con(..) => "constructor",
            Value::Tuple(_) => "tuple",
            Value::Clo(_) | Value::ConFn(..) | Value::Builtin(..) => "function",
            Value::Erased => "erased value",
            Value::Cap(_) => "capability",
            Value::File(_) => "file",
            Value::IoErr(_) => "I/O error",
            Value::Decimal(_) => "decimal",
            Value::Bag(_) => "bag",
            Value::Cown(_) => "cown",
            Value::Future(_) => "future",
        }
    }
}

/// Structural equality (§13.2). `Err` names what can't be compared.
pub fn equal(a: &Value, b: &Value) -> Result<bool, &'static str> {
    Ok(match (a, b) {
        (Value::Num(x), Value::Num(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Bytes(x), Value::Bytes(y)) => x == y,
        (Value::Decimal(x), Value::Decimal(y)) => x == y,
        (Value::Bag(x), Value::Bag(y)) => x == y,
        (Value::IoErr(x), Value::IoErr(y)) => x == y,
        (Value::Erased, _) | (_, Value::Erased) => true,
        (Value::Con(c1, f1), Value::Con(c2, f2)) => {
            if c1 != c2 {
                return Ok(false);
            }
            for (x, y) in f1.iter().zip(f2.iter()) {
                if !equal(x, y)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Tuple(x), Value::Tuple(y)) => {
            for (a, b) in x.iter().zip(y.iter()) {
                if !equal(a, b)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Clo(_) | Value::ConFn(..) | Value::Builtin(..), _) => return Err("functions"),
        (Value::Cap(_), _) => return Err("capabilities"),
        (Value::File(_), _) => return Err("files"),
        (Value::Cown(_) | Value::Future(_), _) => return Err("cowns and futures"),
        _ => false,
    })
}

/// What the runtime knows of a constructor (M7: no `Globals` on workers).
pub struct ConRt {
    pub name: String,
    /// Parameters + fields: the arguments it takes.
    pub arity: usize,
    /// Type parameters.
    pub np: usize,
    /// Per field: erased (`ghost`)?
    pub erased: Vec<bool>,
    /// Per field: printed by `format` (explicit and not erased)?
    pub shown: Vec<bool>,
}

/// The explicit, runtime fields of a constructor value, for printing.
fn shown_fields<'a>(g: &super::Rt, c: ConId, fields: &'a [Value]) -> Vec<&'a Value> {
    let ci = &g.cons[c.0 as usize];
    ci.shown.iter().zip(fields).filter(|(s, _)| **s).map(|(_, v)| v).collect()
}

/// `format` (D42).
pub fn format(g: &super::Rt, v: &Value) -> String {
    match v {
        Value::Str(s) => s.to_string(),
        other => show(g, other, 0),
    }
}

fn paren(b: bool, s: String) -> String {
    if b {
        format!("({s})")
    } else {
        s
    }
}

/// Render as Checkers source; `p > 0` means "in argument position".
pub fn show(g: &super::Rt, v: &Value, p: u8) -> String {
    let wk = &g.known;
    match v {
        Value::Num(n) => {
            let s = n.to_string();
            paren(p > 0 && n.is_negative(), s)
        }
        Value::Str(s) => format!("{:?}", &**s),
        Value::Bytes(b) => show_bytes(b),
        Value::Con(c, fields) => {
            if Some(*c) == wk.nil || Some(*c) == wk.cons {
                let mut items = Vec::new();
                let mut cur = v;
                while let Value::Con(c, f) = cur {
                    if Some(*c) == wk.cons && f.len() == 2 {
                        items.push(show(g, &f[0], 0));
                        cur = &f[1];
                    } else {
                        break;
                    }
                }
                return format!("[{}]", items.join(", "));
            }
            let name = g.cons[c.0 as usize].name.to_string();
            let args = shown_fields(g, *c, fields);
            if args.is_empty() {
                name
            } else {
                let parts: Vec<String> = args.iter().map(|a| show(g, a, 1)).collect();
                paren(p > 0, format!("{name} {}", parts.join(" ")))
            }
        }
        Value::Tuple(xs) => {
            if xs.is_empty() {
                "()".into()
            } else {
                format!("({})", xs.iter().map(|x| show(g, x, 0)).collect::<Vec<_>>().join(", "))
            }
        }
        Value::Clo(_) | Value::ConFn(..) | Value::Builtin(..) => "<function>".into(),
        Value::Erased => "_".into(),
        Value::Cap(c) => match c {
            Cap::Term => "<Term>".into(),
            Cap::Fs(_) => "<Fs>".into(),
            Cap::Env => "<Env>".into(),
            Cap::Proc => "<Proc>".into(),
            Cap::Net => "<Net>".into(),
            Cap::Clock => "<Clock>".into(),
            Cap::Sched => "<Sched>".into(),
        },
        Value::File(_) => "<File>".into(),
        Value::IoErr(m) => format!("<IoError: {m}>"),
        Value::Decimal(d) => d.render(),
        Value::Bag(b) => {
            let items: Vec<String> =
                b.iter().flat_map(|(v, n)| std::iter::repeat_n(v.to_string(), *n)).collect();
            format!("<Bag {{{}}}>", items.join(", "))
        }
        Value::Cown(_) => "<Cown>".into(),
        Value::Future(_) => "<Future>".into(),
    }
}

/// A `Bytes` literal: `b"hi\n"`.
pub fn show_bytes(b: &[u8]) -> String {
    let mut s = String::from("b\"");
    for &c in b.iter() {
        match c {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'\n' => s.push_str("\\n"),
            b'\t' => s.push_str("\\t"),
            b'\r' => s.push_str("\\r"),
            0x20..=0x7e => s.push(c as char),
            _ => s.push_str(&format!("\\x{c:02x}")),
        }
    }
    s.push('"');
    s
}

// Values are shared between worker threads (M7, D66).
#[allow(dead_code)]
fn assert_thread_safe() {
    fn check<T: Send + Sync>() {}
    check::<Value>();
    check::<Ir>();
}
