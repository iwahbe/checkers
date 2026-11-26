//! Values that live as Rust data behind a `K_RUST` object, and numbers.

use crate::num::{Decimal, Num};
use crate::word::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::io::{BufRead, Write};
use std::sync::atomic::AtomicPtr;
use std::sync::{Arc, Mutex};

/// What a `File` is open on (D112): a reader or a writer (a file on disk, a
/// child's pipe), or one of the standard streams, whose buffers it shares
/// with `std.terminal`.
pub enum FileState {
    Read(Box<dyn BufRead + Send>),
    Write(Box<dyn Sink>),
    Stdin,
    Stdout,
    Stderr,
}

/// A `File` open for writing: a buffer before a descriptor.
pub trait Sink: Write + Send {
    /// Write out what is buffered, then close the descriptor: the first
    /// error of the two (`files.close`, §13.4).
    fn finish(self: Box<Self>) -> std::io::Result<()>;
}

/// What writes to a descriptor of its own, and gives it up to be closed.
pub trait IntoFd {
    fn into_fd(self) -> std::os::fd::OwnedFd;
}

impl<T: Write + Send + IntoFd> Sink for std::io::BufWriter<T> {
    fn finish(self: Box<Self>) -> std::io::Result<()> {
        match (*self).into_inner() {
            Ok(inner) => close_fd(inner.into_fd()),
            Err(e) => {
                // Taken apart, the writer is dropped without trying again;
                // the descriptor is closed with it.
                let (e, w) = e.into_parts();
                drop(w.into_parts());
                Err(e)
            }
        }
    }
}

/// Close a descriptor, reporting the error `close` gives. After `EINTR` the
/// descriptor is closed (Linux, macOS) and nothing is lost: not an error.
pub fn close_fd(fd: std::os::fd::OwnedFd) -> std::io::Result<()> {
    use std::os::fd::IntoRawFd;
    let raw = fd.into_raw_fd();
    // Closing can wait on a network file system: not on a behaviour's thread.
    crate::fiber::blocking(move || {
        if unsafe { libc::close(raw) } == 0 {
            return Ok(());
        }
        let e = std::io::Error::last_os_error();
        if e.kind() == std::io::ErrorKind::Interrupted {
            Ok(())
        } else {
            Err(e)
        }
    })
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

/// One value of a bag: its text (what equal values share), the value (one
/// reference, to show it by its type, #170), and how many times it is there.
pub struct BagEntry {
    pub key: String,
    pub value: W,
    pub count: usize,
}

impl Clone for BagEntry {
    fn clone(&self) -> BagEntry {
        BagEntry { key: self.key.clone(), value: dup(self.value), count: self.count }
    }
}

impl Drop for BagEntry {
    fn drop(&mut self) {
        drop_w(self.value);
    }
}

impl PartialEq for BagEntry {
    fn eq(&self, o: &BagEntry) -> bool {
        self.key == o.key && self.count == o.count
    }
}

pub enum Obj {
    Decimal(Decimal),
    /// Sorted by the values' text (D47, D138): equal values have equal
    /// text, whatever their type.
    Bag(Vec<BagEntry>),
    File(Mutex<Option<FileState>>),
    /// A child process, until it is waited for.
    Child(Arc<ChildCell>),
    /// A way to end a child, shared freely (`proc.killer`).
    Killer(Arc<ChildCell>),
    IoErr(String),
    /// A file system capability confined to a directory (`files.within`).
    Fs(Arc<crate::confine::Root>),
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

/// A `K_BIG` object whose number fits in an `i128` holds it in its two
/// words (tag 1); a larger one holds a `BigInt` (tag 0). Numbers past 63
/// bits but within 127 then take one small allocation, and arithmetic on
/// them none of `BigInt`'s. Native code reads and makes these objects
/// itself (§14): their header's `info` word is `INFO_I128`, the number's low
/// word is first.
pub const BIG_I128: u64 = 1;
pub const INFO_I128: u64 = info(K_BIG, 0, BIG_I128);

/// Whether `w` (a `K_BIG` object) holds its number in its words.
#[inline]
pub fn big_inline(w: W) -> bool {
    tag(w) as u64 == BIG_I128
}

/// The number of a `K_BIG` object holding a `BigInt`.
pub fn big_of<'a>(w: W) -> &'a BigInt {
    unsafe { &*(slot(w, 0) as *const BigInt) }
}

#[inline]
fn big_i128(w: W) -> i128 {
    ((slot(w, 1) as u128) << 64 | slot(w, 0) as u128) as i128
}

pub fn is_num(w: W) -> bool {
    is_int(w) || is_kind(w, K_BIG)
}

pub fn num_of(w: W) -> Num {
    if is_int(w) {
        Num::S(int_of(w) as i128)
    } else if is_kind(w, K_BIG) {
        if big_inline(w) {
            Num::S(big_i128(w))
        } else {
            Num::from_big(big_of(w).clone())
        }
    } else {
        crate::bug("expected a number")
    }
}

pub fn of_num(n: Num) -> W {
    match n {
        Num::S(s) if fits(s) => mk_int(s as i64),
        Num::S(s) => of_i128(s),
        Num::B(b) => match b.to_i128() {
            Some(s) if fits(s) => mk_int(s as i64),
            Some(s) => of_i128(s),
            None => of_big(std::sync::Arc::try_unwrap(b).unwrap_or_else(|b| (*b).clone())),
        },
    }
}

fn of_i128(s: i128) -> W {
    let w = alloc_obj(INFO_I128, HDR + 16);
    set_slot(w, 0, s as u128 as u64);
    set_slot(w, 1, ((s as u128) >> 64) as u64);
    w
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::fd::{FromRawFd, OwnedFd};

    fn sink(w: impl Write + Send + IntoFd + 'static) -> Box<dyn Sink> {
        Box::new(std::io::BufWriter::new(w))
    }

    #[test]
    fn finish_writes_out_and_closes() {
        let p = std::env::temp_dir().join(format!("checkers-finish-{}", std::process::id()));
        let mut s = sink(crate::fiber::BlockingWrite(std::fs::File::create(&p).unwrap()));
        s.write_all(b"kept").unwrap();
        s.finish().unwrap();
        assert_eq!(std::fs::read(&p).unwrap(), b"kept");
        std::fs::remove_file(&p).unwrap();
    }

    /// What is buffered for a pipe nobody reads any more can't be written:
    /// `finish` says so.
    #[test]
    fn finish_reports_a_broken_pipe() {
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let (r, w) = unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) };
        drop(r);
        let mut s = sink(crate::poll::PollFd::new(w));
        s.write_all(b"lost").unwrap();
        assert_eq!(s.finish().unwrap_err().kind(), std::io::ErrorKind::BrokenPipe);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn finish_reports_a_full_device() {
        let f = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
        let mut s = sink(crate::fiber::BlockingWrite(f));
        s.write_all(b"lost").unwrap();
        assert_eq!(s.finish().unwrap_err().raw_os_error(), Some(libc::ENOSPC));
    }
}
