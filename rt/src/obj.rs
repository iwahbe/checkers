//! Values that live as Rust data behind a `K_RUST` object, and numbers.

use crate::num::{Decimal, Num};
use crate::word::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::sync::atomic::AtomicPtr;
use std::sync::{Arc, Mutex};

/// What a `File` is open on (D112): a reader or a writer (a file on disk, a
/// child's pipe), or one of the standard streams, whose buffers it shares
/// with `std.terminal`.
pub enum FileState {
    Read(Box<dyn BufRead + Send>),
    Write(Box<dyn Write + Send>),
    Stdin,
    Stdout,
    Stderr,
}

/// A resource for the scheduler (D66): a cown or a future.
pub struct Cell {
    pub res: crate::sched::Resource,
    pub v: Mutex<W>,
}

/// A child process and whether it has been reaped. A `kill` holds `reaped`'s
/// lock while it signals, and the child is reaped only under that lock, so a
/// signal never reaches a process that has reused the child's id.
pub struct ChildCell {
    pub pid: i32,
    pub child: Mutex<Option<std::process::Child>>,
    pub reaped: Mutex<bool>,
}

pub enum Obj {
    Decimal(Decimal),
    /// Sorted (value, count) pairs (D47, D138), each value by how it is
    /// shown (a bag is only made by `check`s on specifications).
    Bag(Vec<(String, usize)>),
    File(Mutex<Option<FileState>>),
    /// A child process, until it is waited for.
    Child(Arc<ChildCell>),
    /// A way to end a child, shared freely (`proc.killer`).
    Killer(Arc<ChildCell>),
    IoErr(String),
    /// A file system capability confined to a directory (`files.within`).
    Fs(PathBuf),
    Cown(Arc<Cell>),
    /// `UNSET` until filled.
    Future(Arc<Cell>),
}

impl Drop for Cell {
    fn drop(&mut self) {
        let v = *self.v.get_mut().unwrap();
        if v != UNSET {
            drop_w(v);
        }
    }
}

pub fn new_obj(o: Obj) -> W {
    let w = alloc_obj(info(K_RUST, 0, 0), HDR + 8);
    set_slot(w, 0, Box::into_raw(Box::new(o)) as u64);
    w
}

pub fn obj<'a>(w: W) -> Option<&'a Obj> {
    if is_kind(w, K_RUST) {
        Some(unsafe { &*(slot(w, 0) as *const Obj) })
    } else {
        None
    }
}

pub fn new_cell(v: W) -> Arc<Cell> {
    Arc::new(Cell { res: crate::sched::Resource { last: AtomicPtr::new(std::ptr::null_mut()) }, v: Mutex::new(v) })
}

// ── numbers ─────────────────────────────────────────────────────────────────

pub fn big_of<'a>(w: W) -> &'a BigInt {
    unsafe { &*(slot(w, 0) as *const BigInt) }
}

pub fn is_num(w: W) -> bool {
    is_int(w) || is_kind(w, K_BIG)
}

pub fn num_of(w: W) -> Num {
    if is_int(w) {
        Num::S(int_of(w) as i128)
    } else if is_kind(w, K_BIG) {
        Num::from_big(big_of(w).clone())
    } else {
        crate::bug("expected a number")
    }
}

pub fn of_num(n: Num) -> W {
    match n {
        Num::S(s) if fits(s) => mk_int(s as i64),
        Num::S(s) => of_big(BigInt::from(s)),
        Num::B(b) => match b.to_i64() {
            Some(s) if fits(s as i128) => mk_int(s),
            _ => of_big((*b).clone()),
        },
    }
}

fn of_big(b: BigInt) -> W {
    let w = alloc_obj(info(K_BIG, 0, 0), HDR + 8);
    set_slot(w, 0, Box::into_raw(Box::new(b)) as u64);
    w
}

pub fn nat(n: usize) -> W {
    of_num(Num::from(n))
}

/// A number as a `usize` (a length or an index), if it is one.
pub fn to_usize(w: W) -> Option<usize> {
    if is_int(w) {
        usize::try_from(int_of(w)).ok()
    } else {
        num_of(w).to_usize()
    }
}
