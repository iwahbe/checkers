//! The standard library's `__builtin` functions for native code, one file
//! per module. Runtime errors are reported as D76 describes.

use crate::num::{Decimal, Num};
use crate::obj::*;
use crate::prog::*;
use crate::word::*;
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::sync::Mutex;

macro_rules! builtin {
    ($name:ident, |$a:ident| $body:expr) => {
        #[no_mangle]
        pub extern "C" fn $name(p: *const W, n: u64) -> W {
            let $a = args(p, n);
            $body
        }
    };
}

pub mod terminal;
pub mod files;
pub mod bytes;
pub mod string;
pub mod utf8;
#[path = "char.rs"]
pub mod chars;
pub mod decimal;
pub mod bag;
pub mod cown;
pub mod future;
pub mod env;
pub mod proc;

/// A builtin: its standard-library name (`std.terminal.print_line`), its
/// symbol, and its function. Each takes its kept (non-erased) arguments as
/// a borrowed array and returns an owned word.
pub type Builtin = (&'static str, &'static str, extern "C" fn(*const W, u64) -> W);

/// Every module's builtins (SPEC §16.3).
pub const MODULES: &[&[Builtin]] = &[
    terminal::TABLE,
    files::TABLE,
    bytes::TABLE,
    string::TABLE,
    utf8::TABLE,
    chars::TABLE,
    decimal::TABLE,
    bag::TABLE,
    cown::TABLE,
    future::TABLE,
    env::TABLE,
    proc::TABLE,
];

/// Every builtin.
pub fn all() -> impl Iterator<Item = &'static Builtin> {
    MODULES.iter().flat_map(|t| t.iter())
}

/// The symbol of the builtin called `name`.
pub fn symbol(name: &str) -> Option<&'static str> {
    all().find(|b| b.0 == name).map(|b| b.1)
}

/// The address of each builtin, for the JIT.
pub fn addresses() -> Vec<(&'static str, *const u8)> {
    let mut v: Vec<(&'static str, *const u8)> = all().map(|b| (b.1, b.2 as *const u8)).collect();
    v.sort_by_key(|x| x.0);
    v.dedup_by_key(|x| x.0);
    v
}

pub(crate) fn args<'a>(p: *const W, n: u64) -> &'a [W] {
    if n == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(p, n as usize) }
    }
}

pub(crate) fn s(w: W) -> &'static str {
    if !is_kind(w, K_STR) {
        bug("expected a string");
    }
    str_of(w)
}

pub(crate) fn b(w: W) -> &'static [u8] {
    if !is_kind(w, K_BYTES) {
        bug("expected bytes");
    }
    blob(w)
}

pub(crate) fn n(w: W) -> usize {
    to_usize(w).unwrap_or_else(|| bug("a number out of range"))
}

pub(crate) fn ch(w: W) -> char {
    u32::try_from(n(w)).ok().and_then(char::from_u32).unwrap_or_else(|| bug("not a Unicode scalar value"))
}

/// The operating system's message, without Rust's " (os error N)" suffix.
pub(crate) fn describe_io(e: &std::io::Error) -> W {
    let s = e.to_string();
    let s = match s.find(" (os error") {
        Some(k) => s[..k].to_string(),
        None => s,
    };
    new_obj(Obj::IoErr(s))
}

pub(crate) fn io_err(m: &str) -> W {
    new_obj(Obj::IoErr(m.to_string()))
}

/// Resolve a path against an `Fs` capability (§13.4).
pub(crate) fn path(fs: W, p: &str) -> Result<PathBuf, W> {
    let root = match obj(fs) {
        Some(Obj::Fs(d)) => Some(d.clone()),
        _ if fs == CAP_FS => None,
        _ => return Err(io_err("not a file system capability")),
    };
    match root {
        None => Ok(PathBuf::from(p)),
        Some(dir) => {
            let rel = Path::new(p);
            let escapes = rel.is_absolute()
                || rel.components().any(|c| matches!(c, Component::ParentDir | Component::RootDir | Component::Prefix(_)));
            if escapes {
                Err(io_err("Permission denied (outside the directory this capability allows)"))
            } else {
                Ok(dir.join(rel))
            }
        }
    }
}

pub(crate) fn file_result(r: std::io::Result<std::fs::File>, write: bool) -> W {
    match r {
        Ok(f) => {
            let st = if write {
                FileState::Write(Box::new(std::io::BufWriter::new(f)))
            } else {
                FileState::Read(Box::new(std::io::BufReader::new(f)))
            };
            ok(new_file(st))
        }
        Err(e) => err(describe_io(&e)),
    }
}

/// Using a `File` the way it wasn't opened for.
fn misuse(m: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, m)
}

/// For operations whose type has no error: misuse is a runtime error, any
/// other error the end of input (reading) or nothing (writing), as before.
pub(crate) fn fail_on(op: &str, e: &std::io::Error) {
    if e.kind() == std::io::ErrorKind::InvalidInput {
        error(NO_OWNER, &format!("`{op}`: {e}"))
    }
}

pub(crate) fn new_file(st: FileState) -> W {
    new_obj(Obj::File(Mutex::new(Some(st))))
}

/// Read from a `File` (or report why it can't be read).
pub(crate) fn reading<T>(w: W, f: impl FnOnce(&mut dyn std::io::BufRead) -> std::io::Result<T>) -> std::io::Result<T> {
    let mut g = file(w).lock().unwrap_or_else(|e| e.into_inner());
    match &mut *g {
        Some(FileState::Read(r)) => f(&mut **r),
        Some(FileState::Stdin) => {
            let mut io = crate::io::std_io();
            // What was written so far comes before waiting for input.
            let _ = io.out.flush();
            f(&mut io.inp)
        }
        Some(_) => Err(misuse("this file is open for writing, not reading")),
        None => Err(misuse("this file is closed")),
    }
}

/// Write to a `File` (or report why it can't be written).
pub(crate) fn writing<T>(w: W, f: impl FnOnce(&mut dyn Write) -> std::io::Result<T>) -> std::io::Result<T> {
    let mut g = file(w).lock().unwrap_or_else(|e| e.into_inner());
    match &mut *g {
        Some(FileState::Write(wr)) => f(&mut **wr),
        Some(FileState::Stdout) => {
            let mut io = crate::io::std_io();
            f(&mut io.out)
        }
        Some(FileState::Stderr) => {
            let mut io = crate::io::std_io();
            let _ = io.out.flush();
            f(&mut std::io::stderr())
        }
        Some(_) => Err(misuse("this file is open for reading, not writing")),
        None => Err(misuse("this file is closed")),
    }
}

pub(crate) fn file<'a>(w: W) -> &'a Mutex<Option<FileState>> {
    match obj(w) {
        Some(Obj::File(f)) => f,
        _ => bug("expected a file"),
    }
}
