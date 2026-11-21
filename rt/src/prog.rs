//! What the runtime knows of the program: constructors (for `debug` and the
//! values builtins build), definition names (for error messages), and how
//! to call compiled code. Native code passes it as a text descriptor.

use crate::word::*;
use std::io::Write;
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct ConInfo {
    pub name: String,
    /// Parameters + fields.
    pub arity: usize,
    /// Type parameters.
    pub np: usize,
    /// Per field: printed by `debug`?
    pub shown: Vec<bool>,
    /// Its type's hand-written `debug` (#126): an index into `Prog::debug`.
    pub debug: Option<usize>,
    /// Its type's number (#170).
    pub ty: Option<u32>,
    /// Per field: its type, from the type's parameters (#170).
    pub templates: Vec<crate::desc::Template>,
}

/// What `debug` needs to know of a type to show it by its descriptor (#170).
#[derive(Clone, Debug, Default)]
pub struct TyInfo {
    pub kind: TyKind,
    /// Stored as its one kept field: the constructor and the field.
    pub unboxed: Option<(u32, usize)>,
    /// Its hand-written `debug`: an index into `Prog::debug`, and how many
    /// type parameters that function takes before the value.
    pub debug: Option<(usize, usize)>,
}

/// Types shown otherwise than by their constructors.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TyKind {
    #[default]
    Other,
    List,
    Array,
    String,
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
    pub system: Option<u32>,
    pub success: Option<u32>,
    pub failure: Option<u32>,
    pub entry: Option<u32>,
    pub output: Option<u32>,
    pub spawned: Option<u32>,
    pub inherit: Option<u32>,
    pub pipe: Option<u32>,
    pub discard: Option<u32>,
}

/// Compiled code's entry for calls from Rust: `invoke(code, env, args, n)`
/// calls `code(env, args[0], …, args[n-1])` in the `tail` convention.
pub type Invoke = extern "C" fn(u64, W, *const W, u64) -> W;

pub struct Prog {
    pub cons: Vec<ConInfo>,
    pub names: Vec<String>,
    pub known: Known,
    pub system_fields: Vec<String>,
    /// Types by number (#170).
    pub tys: Vec<TyInfo>,
    pub invoke: Invoke,
    /// The hand-written `Debug` instances' functions (#126), set once
    /// after `install` (`set_debug`); kept for good.
    pub debug: std::sync::OnceLock<Vec<W>>,
}

impl Prog {
    /// Type `id`'s entry, made if it isn't there yet.
    fn ty_mut(&mut self, id: u32) -> &mut TyInfo {
        let i = id as usize;
        if self.tys.len() <= i {
            self.tys.resize(i + 1, TyInfo::default());
        }
        &mut self.tys[i]
    }
}

/// The current program. `checkers check` installs one per file it
/// evaluates `check`s in; the old ones are kept (never freed), since values
/// computed under them may still be read.
static PROG: AtomicPtr<Prog> = AtomicPtr::new(std::ptr::null_mut());

pub fn prog() -> &'static Prog {
    let p = PROG.load(Ordering::Acquire);
    if p.is_null() {
        fatal("the program was not set up");
    }
    unsafe { &*p }
}

fn prog_opt() -> Option<&'static Prog> {
    let p = PROG.load(Ordering::Acquire);
    (!p.is_null()).then(|| unsafe { &*p })
}

/// The descriptor (one item per line):
/// `con NAME ARITY NP SHOWN TY TEMPLATES` (SHOWN: a string of 0/1 per
/// field; TY: its type's number; TEMPLATES: each field's type, `;` between
/// them, `-` for none), `ty ID KIND UNBOXED` (KIND: `list`, `array`,
/// `string` or `-`; UNBOXED: `CON:FIELD` or `-`), `def NAME`, `known KEY
/// ID`, `system FIELD`, `debug TY INDEX NTYPES` (after the types).
pub fn install(desc: &str, invoke: Invoke) {
    let mut p = Prog {
        cons: Vec::new(),
        names: Vec::new(),
        known: Known::default(),
        system_fields: Vec::new(),
        tys: Vec::new(),
        invoke,
        debug: std::sync::OnceLock::new(),
    };
    for line in desc.lines() {
        let mut it = line.split(' ');
        match it.next() {
            Some("con") => {
                let name = it.next().unwrap_or("").to_string();
                let arity = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
                let np = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
                let shown = it.next().unwrap_or("").bytes().map(|b| b == b'1').collect();
                let ty = it.next().and_then(|x| x.parse().ok());
                let templates = match it.next() {
                    None | Some("-") => Vec::new(),
                    Some(ts) => ts.split(';').map(crate::desc::Template::parse).collect(),
                };
                p.cons.push(ConInfo { name, arity, np, shown, debug: None, ty, templates });
            }
            Some("ty") => {
                let Some(id) = it.next().and_then(|x| x.parse().ok()) else { continue };
                let kind = match it.next() {
                    Some("list") => TyKind::List,
                    Some("array") => TyKind::Array,
                    Some("string") => TyKind::String,
                    _ => TyKind::Other,
                };
                let unboxed = it.next().and_then(|x| x.split_once(':')).and_then(|(c, f)| Some((c.parse().ok()?, f.parse().ok()?)));
                *p.ty_mut(id) = TyInfo { kind, unboxed, debug: None };
            }
            Some("debug") => {
                let ty: Option<u32> = it.next().and_then(|x| x.parse().ok());
                let k: Option<usize> = it.next().and_then(|x| x.parse().ok());
                let n: usize = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
                let (Some(ty), Some(k)) = (ty, k) else { continue };
                p.ty_mut(ty).debug = Some((k, n));
                for ci in p.cons.iter_mut().filter(|c| c.ty == Some(ty)) {
                    ci.debug = Some(k);
                }
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
                    "system" => &mut k.system,
                    "success" => &mut k.success,
                    "failure" => &mut k.failure,
                    "entry" => &mut k.entry,
                    "output" => &mut k.output,
                    "spawned" => &mut k.spawned,
                    "inherit" => &mut k.inherit,
                    "pipe" => &mut k.pipe,
                    "discard" => &mut k.discard,
                    _ => continue,
                };
                *slot = id;
            }
            Some("system") => p.system_fields.push(it.next().unwrap_or("").to_string()),
            _ => {}
        }
    }
    PROG.store(Box::into_raw(Box::new(p)), Ordering::Release);
}

/// The hand-written `Debug` instances' functions (#126): `fs`, an owned
/// list of them, in the order of the descriptor's indices.
pub fn set_debug(fs: W) {
    let items: Vec<W> = list_items(fs).into_iter().map(dup).collect();
    drop_w(fs);
    let _ = prog().debug.set(items);
}

/// The hand-written `debug` of constructor `c`'s type, if it has one, and
/// how many type parameters it takes before the value.
pub fn debug_fn(c: u32) -> Option<(W, usize)> {
    let p = prog();
    let ci = p.cons.get(c as usize)?;
    let k = ci.debug?;
    let n = ci.ty.and_then(|t| p.tys.get(t as usize)).and_then(|t| t.debug).map_or(0, |d| d.1);
    Some((*p.debug.get()?.get(k)?, n))
}

/// The hand-written `debug` of type `ty`, if it has one, and how many type
/// parameters it takes before the value.
pub fn debug_fn_of_type(ty: u32) -> Option<(W, usize)> {
    let p = prog();
    let (k, n) = p.tys.get(ty as usize)?.debug?;
    Some((*p.debug.get()?.get(k)?, n))
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
    list_onto(items, nullary(known_con(prog().known.nil)))
}

/// Owned words in front of the owned list `tail`, which is shared, not copied.
pub fn list_onto(items: Vec<W>, tail: W) -> W {
    let cons = known_con(prog().known.cons);
    items.into_iter().rev().fold(tail, |l, v| new_con(cons, &[v, l]))
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

/// A `files.Entry`.
pub fn entry(name: &str, dir: bool) -> W {
    new_con(known_con(prog().known.entry), &[new_str(name), bool_w(dir)])
}

/// A `proc.Output`.
pub fn output(code: usize, stdout: &[u8], stderr: &[u8]) -> W {
    new_con(known_con(prog().known.output), &[crate::obj::nat(code), new_bytes(stdout), new_bytes(stderr)])
}

/// A `proc.Spawned`: the child, then each stream's end (a `File` or unit).
pub fn spawned(child: W, ends: [W; 3]) -> W {
    new_con(known_con(prog().known.spawned), &[child, ends[0], ends[1], ends[2]])
}

/// How a `proc.Stream` connects a child's stream.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Conn {
    Inherit,
    Pipe,
    Discard,
}

pub fn conn(w: W) -> Conn {
    let k = &prog().known;
    match con_of(w) {
        Some(c) if Some(c) == k.pipe => Conn::Pipe,
        Some(c) if Some(c) == k.discard => Conn::Discard,
        Some(c) if Some(c) == k.inherit => Conn::Inherit,
        _ => bug("expected a proc.Stream"),
    }
}

// ── errors ──────────────────────────────────────────────────────────────────

/// Owner of code with no definition (a `check`, say).
pub const NO_OWNER: u32 = u32::MAX;

/// Stop with a runtime error, as the interpreter reports it (D76): flush
/// standard output, print the message, exit with code 70.
pub fn error(owner: u32, msg: &str) -> ! {
    let name = prog_opt().and_then(|p| p.names.get(owner as usize));
    // Compile-time evaluation: report to the compiler, stop this thread.
    if let Some(tx) = TRAP.with(|t| t.borrow().clone()) {
        let text = match name {
            Some(n) => format!("runtime error in `{n}`: {msg}"),
            None => format!("runtime error: {msg}"),
        };
        let _ = tx.send(Err(text));
        loop {
            std::thread::park();
        }
    }
    crate::io::flush();
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

thread_local! {
    /// Where a runtime error goes during compile-time evaluation (D80).
    pub static TRAP: std::cell::RefCell<Option<std::sync::mpsc::Sender<Result<W, String>>>> =
        const { std::cell::RefCell::new(None) };
}

/// Run compiled code for the compiler (a `check`, a value staging needs):
/// on a thread of its own with a large stack. A runtime error doesn't exit
/// the process: it comes back as `Err` with the message `checkers run`
/// would print, and that thread stays parked.
pub fn eval_trapped(f: impl FnOnce() -> W + Send + 'static) -> Result<W, String> {
    let (tx, rx) = std::sync::mpsc::channel();
    let tx2 = tx.clone();
    let spawned = std::thread::Builder::new().stack_size(1 << 30).spawn(move || {
        TRAP.with(|t| *t.borrow_mut() = Some(tx2.clone()));
        let w = f();
        let _ = tx2.send(Ok(w));
    });
    if let Err(e) = spawned {
        return Err(format!("could not start evaluation: {e}"));
    }
    drop(tx);
    rx.recv().unwrap_or_else(|_| Err("evaluation stopped".into()))
}

/// This thread's trap, for threads it starts (`par`).
pub fn current_trap() -> Option<std::sync::mpsc::Sender<Result<W, String>>> {
    TRAP.with(|t| t.borrow().clone())
}

pub fn set_trap(tx: Option<std::sync::mpsc::Sender<Result<W, String>>>) {
    TRAP.with(|t| *t.borrow_mut() = tx);
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
    } else if is_kind(w, K_BYTES) {
        "bytes or a string"
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
