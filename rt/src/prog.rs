//! What the runtime knows of the program: constructors (for `format` and the
//! values builtins build), definition names (for error messages), and how
//! to call compiled code. Native code passes it as a text descriptor.

use crate::word::*;
use std::io::Write;
use std::sync::OnceLock;

pub struct ConInfo {
    pub name: String,
    /// Parameters + fields.
    pub arity: usize,
    /// Type parameters.
    pub np: usize,
    /// Per field: printed by `format`?
    pub shown: Vec<bool>,
}

#[derive(Default, Clone, Copy)]
pub struct Known {
    pub true_con: Option<u32>,
    pub false_con: Option<u32>,
    pub some: Option<u32>,
    pub none: Option<u32>,
    pub ok: Option<u32>,
    pub err: Option<u32>,
    pub nil: Option<u32>,
    pub cons: Option<u32>,
    pub parsed: Option<u32>,
    pub system: Option<u32>,
    pub success: Option<u32>,
    pub failure: Option<u32>,
}

/// Compiled code's entry for calls from Rust: `invoke(code, env, args, n)`
/// calls `code(env, args[0], …, args[n-1])` in the `tail` convention.
pub type Invoke = extern "C" fn(u64, W, *const W, u64) -> W;

pub struct Prog {
    pub cons: Vec<ConInfo>,
    pub names: Vec<String>,
    pub known: Known,
    pub system_fields: Vec<String>,
    pub invoke: Invoke,
}

static PROG: OnceLock<Prog> = OnceLock::new();

pub fn prog() -> &'static Prog {
    PROG.get().unwrap_or_else(|| fatal("the program was not set up"))
}

/// The descriptor (one item per line):
/// `con NAME ARITY NP SHOWN` (SHOWN: a string of 0/1 per field),
/// `def NAME`, `known KEY ID`, `system FIELD`.
pub fn install(desc: &str, invoke: Invoke) {
    let mut p = Prog { cons: Vec::new(), names: Vec::new(), known: Known::default(), system_fields: Vec::new(), invoke };
    for line in desc.lines() {
        let mut it = line.split(' ');
        match it.next() {
            Some("con") => {
                let name = it.next().unwrap_or("").to_string();
                let arity = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
                let np = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
                let shown = it.next().unwrap_or("").bytes().map(|b| b == b'1').collect();
                p.cons.push(ConInfo { name, arity, np, shown });
            }
            Some("def") => p.names.push(it.next().unwrap_or("").to_string()),
            Some("known") => {
                let key = it.next().unwrap_or("");
                let id = it.next().and_then(|x| x.parse().ok());
                let k = &mut p.known;
                let slot = match key {
                    "true" => &mut k.true_con,
                    "false" => &mut k.false_con,
                    "some" => &mut k.some,
                    "none" => &mut k.none,
                    "ok" => &mut k.ok,
                    "err" => &mut k.err,
                    "nil" => &mut k.nil,
                    "cons" => &mut k.cons,
                    "parsed" => &mut k.parsed,
                    "system" => &mut k.system,
                    "success" => &mut k.success,
                    "failure" => &mut k.failure,
                    _ => continue,
                };
                *slot = id;
            }
            Some("system") => p.system_fields.push(it.next().unwrap_or("").to_string()),
            _ => {}
        }
    }
    let _ = PROG.set(p);
}

// ── values the runtime builds ───────────────────────────────────────────────

fn known_con(c: Option<u32>) -> u32 {
    c.unwrap_or_else(|| fatal("a standard library constructor is missing"))
}

pub fn bool_w(b: bool) -> W {
    let k = &prog().known;
    nullary(known_con(if b { k.true_con } else { k.false_con }))
}

pub fn is_true(w: W) -> bool {
    w == bool_w(true)
}

pub fn some(v: W) -> W {
    new_con(known_con(prog().known.some), &[v])
}

pub fn none() -> W {
    nullary(known_con(prog().known.none))
}

pub fn ok(v: W) -> W {
    new_con(known_con(prog().known.ok), &[v])
}

pub fn err(v: W) -> W {
    new_con(known_con(prog().known.err), &[v])
}

/// A list of owned words.
pub fn list(items: Vec<W>) -> W {
    let k = &prog().known;
    let (nil, cons) = (known_con(k.nil), known_con(k.cons));
    let mut l = nullary(nil);
    for v in items.into_iter().rev() {
        l = new_con(cons, &[v, l]);
    }
    l
}

/// The items of a list (borrowed).
pub fn list_items(mut w: W) -> Vec<W> {
    let k = &prog().known;
    let mut out = Vec::new();
    loop {
        match con_of(w) {
            Some(c) if Some(c) == k.cons => {
                out.push(field(w, 0));
                w = field(w, 1);
            }
            Some(c) if Some(c) == k.nil => return out,
            _ => bug("expected a list"),
        }
    }
}

pub fn parsed(v: W, stop: usize) -> W {
    new_con(known_con(prog().known.parsed), &[v, crate::obj::nat(stop)])
}

// ── errors ──────────────────────────────────────────────────────────────────

/// Owner of code with no definition (a `check`, say).
pub const NO_OWNER: u32 = u32::MAX;

/// Stop with a runtime error, as the interpreter reports it (D76): flush
/// standard output, print the message, exit with code 70.
pub fn error(owner: u32, msg: &str) -> ! {
    crate::io::flush();
    let name = PROG.get().and_then(|p| p.names.get(owner as usize));
    let mut e = std::io::stderr().lock();
    let _ = match name {
        Some(n) => writeln!(e, "runtime error in `{n}`: {msg}"),
        None => writeln!(e, "runtime error: {msg}"),
    };
    let _ = e.flush();
    std::process::exit(70)
}

#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_fail(owner: u64, msg: *const u8, len: u64) -> W {
    let m = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(msg, len as usize)) };
    error(owner as u32, &format!("reached {m}"))
}

/// A runtime error with a message of its own (from native code).
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_error(owner: u64, msg: *const u8, len: u64) -> W {
    let m = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(msg, len as usize)) };
    error(owner as u32, m)
}

/// No `match` arm for this value.
#[no_mangle]
pub extern "C" fn ck_nomatch(w: W, owner: u64) -> W {
    let kind = if crate::obj::is_num(w) {
        "number"
    } else if is_kind(w, K_STR) {
        "string"
    } else if is_kind(w, K_BYTES) {
        "bytes"
    } else if con_of(w).is_some() {
        "constructor"
    } else {
        "value"
    };
    error(owner as u32, &format!("no `match` arm for this {kind}"))
}

/// A constant's value, computed on first use (`slot` holds `UNSET` until
/// then) by `code`, a function of no arguments. The slot keeps one
/// reference for good; the caller gets another.
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_caf(slot: *const std::sync::atomic::AtomicU64, code: u64) -> W {
    let slot = unsafe { &*slot };
    let v = (prog().invoke)(code, ERASED, std::ptr::null(), 0);
    match slot.compare_exchange(UNSET, v, std::sync::atomic::Ordering::AcqRel, std::sync::atomic::Ordering::Acquire) {
        Ok(_) => dup(v),
        Err(existing) => {
            drop_w(v);
            dup(existing)
        }
    }
}

/// A broken internal invariant (never in a checked program).
pub fn bug(msg: &str) -> ! {
    error(NO_OWNER, &format!("internal error: {msg}"))
}

pub fn fatal(msg: &str) -> ! {
    crate::io::flush();
    eprintln!("checkers runtime: {msg}");
    std::process::exit(70)
}
