//! Values as 64-bit words (D73, SPEC §14).
//!
//! | word                 | value                                        |
//! |----------------------|----------------------------------------------|
//! | `2n + 1`             | an integer `n` of up to 63 bits              |
//! | `0`                  | an erased value (type, proof, ghost)         |
//! | `8k + 2`             | constructor `k` without fields (`True`, `[]`) |
//! | `8k + 4`             | an immediate: unit, or a capability          |
//! | `8k + 6`             | reserved (`UNSET`: a constant not yet computed) |
//! | other multiples of 8 | a pointer to a heap object                   |
//!
//! A heap object starts with a header: a reference count, then `info`
//! (kind in bits 0–7, field count in bits 8–31, constructor or arity in
//! bits 32–63). Fields follow, one word each.

use std::alloc::{alloc, dealloc, Layout};
use std::sync::atomic::{fence, AtomicBool, AtomicI64, Ordering};

/// `CHECKERS_RC_CHECK=1`: count live objects, to find leaks (D74).
pub static TRACK: AtomicBool = AtomicBool::new(false);
pub static LIVE: AtomicI64 = AtomicI64::new(0);

pub type W = u64;

pub const ERASED: W = 0;
pub const UNIT: W = 4;
/// A constant (CAF) slot that hasn't been computed.
pub const UNSET: W = 6;

/// Reference count of objects in the program's data (literals, global
/// closures): never reaches zero.
pub const STATIC_RC: i64 = 1 << 60;

pub const K_CON: u64 = 1;
pub const K_TUPLE: u64 = 2;
/// A closure: arity in `tag`, free variables in the fields; the code
/// pointer is the first word after the header.
pub const K_CLO: u64 = 3;
/// A partial application: the function is the first word after the
/// header, then the arguments it holds.
pub const K_PAP: u64 = 4;
/// Bytes, and strings, which are stored as their bytes (#170). (Kind 5
/// was strings' own.)
pub const K_BYTES: u64 = 6;
pub const K_BIG: u64 = 7;
/// A Rust value (`Obj`): decimals, bags, files, cowns, futures, …
pub const K_RUST: u64 = 8;

/// Immediates (`8k + 4`).
pub const CAP_TERM: W = 8 + 4;
pub const CAP_FS: W = 16 + 4;
pub const CAP_ENV: W = 24 + 4;
pub const CAP_PROC: W = 32 + 4;
pub const CAP_NET: W = 40 + 4;
pub const CAP_CLOCK: W = 48 + 4;
pub const CAP_SCHED: W = 56 + 4;

#[repr(C)]
pub struct Hdr {
    pub rc: AtomicI64,
    pub info: u64,
}

pub const HDR: usize = 16;

#[inline]
pub fn is_ptr(w: W) -> bool {
    w != 0 && w & 7 == 0
}

#[inline]
pub fn is_int(w: W) -> bool {
    w & 1 == 1
}

#[inline]
pub fn int_of(w: W) -> i64 {
    (w as i64) >> 1
}

pub const INT_MIN: i64 = -(1 << 62);
pub const INT_MAX: i64 = (1 << 62) - 1;

#[inline]
pub fn fits(n: i128) -> bool {
    n >= INT_MIN as i128 && n <= INT_MAX as i128
}

#[inline]
pub fn mk_int(n: i64) -> W {
    ((n << 1) | 1) as u64
}

#[inline]
pub fn nullary(con: u32) -> W {
    ((con as u64) << 3) | 2
}

#[inline]
pub fn is_nullary(w: W) -> bool {
    w & 7 == 2
}

#[inline]
pub const fn info(kind: u64, n: u64, tag: u64) -> u64 {
    kind | (n << 8) | (tag << 32)
}

#[inline]
pub fn hdr<'a>(w: W) -> &'a Hdr {
    unsafe { &*(w as *const Hdr) }
}

#[inline]
pub fn kind(w: W) -> u64 {
    hdr(w).info & 0xff
}

#[inline]
pub fn nfields(w: W) -> usize {
    ((hdr(w).info >> 8) & 0xff_ffff) as usize
}

#[inline]
pub fn tag(w: W) -> u32 {
    (hdr(w).info >> 32) as u32
}

/// Word `i` after the header.
#[inline]
pub fn slot(w: W, i: usize) -> W {
    unsafe { *((w as usize + HDR + 8 * i) as *const W) }
}

#[inline]
pub fn set_slot(w: W, i: usize, v: W) {
    unsafe { *((w as usize + HDR + 8 * i) as *mut W) = v }
}

/// The constructor of a constructor value (with or without fields).
pub fn con_of(w: W) -> Option<u32> {
    if is_nullary(w) {
        Some((w >> 3) as u32)
    } else if is_ptr(w) && kind(w) == K_CON {
        Some(tag(w))
    } else {
        None
    }
}

/// Field `i` of a constructor value.
pub fn field(w: W, i: usize) -> W {
    slot(w, i)
}

fn size_of(w: W) -> usize {
    let n = nfields(w);
    match kind(w) {
        K_CON | K_TUPLE => HDR + 8 * n,
        K_CLO | K_PAP => HDR + 8 + 8 * n,
        K_BYTES | crate::array::K_ARRAY => crate::array::size(w),
        K_BIG if crate::obj::big_inline(w) => HDR + 16,
        _ => HDR + 8,
    }
}

// ── small objects' memory ───────────────────────────────────────────────────
//
// Each thread keeps the memory of the small objects it frees, a list per
// size, and allocates from it first: most objects are a header and a few
// words, made and freed at a high rate. Memory freed on one thread may be
// used by another; it all came from the system allocator with its size.

/// Sizes kept: `HDR + 8k` for `k < SMALL`.
const SMALL: usize = 16;
/// At most this many blocks kept per size and thread; more are released.
const KEEP: u32 = 4096;

struct Free {
    head: [std::cell::Cell<*mut u8>; SMALL],
    len: [std::cell::Cell<u32>; SMALL],
}

thread_local! {
    static FREE: Free = const {
        Free { head: [const { std::cell::Cell::new(std::ptr::null_mut()) }; SMALL], len: [const { std::cell::Cell::new(0) }; SMALL] }
    };
}

/// The list for blocks of `size` bytes, if they are kept.
#[inline]
fn class(size: usize) -> Option<usize> {
    let k = size.wrapping_sub(HDR) / 8;
    (size >= HDR && size.is_multiple_of(8) && k < SMALL).then_some(k)
}

#[inline]
fn take_block(size: usize) -> *mut u8 {
    let Some(k) = class(size) else { return std::ptr::null_mut() };
    FREE.try_with(|f| {
        let p = f.head[k].get();
        if !p.is_null() {
            f.head[k].set(unsafe { *(p as *mut *mut u8) });
            f.len[k].set(f.len[k].get() - 1);
        }
        p
    })
    .unwrap_or(std::ptr::null_mut())
}

/// Keep `p`, a block of `size` bytes; false if it isn't kept.
#[inline]
fn keep_block(p: *mut u8, size: usize) -> bool {
    let Some(k) = class(size) else { return false };
    FREE.try_with(|f| {
        if f.len[k].get() >= KEEP {
            return false;
        }
        unsafe { *(p as *mut *mut u8) = f.head[k].get() };
        f.head[k].set(p);
        f.len[k].set(f.len[k].get() + 1);
        true
    })
    .unwrap_or(false)
}

/// A new object with reference count 1; its words are uninitialised. If
/// it can't be allocated, the program ends: `out of memory` (§13.3, D184).
pub fn alloc_obj(info_word: u64, size: usize) -> W {
    // A size above what an allocation can be has no layout (D184).
    let Ok(layout) = Layout::from_size_align(size.max(HDR), 8) else { crate::fatal("out of memory") };
    let p = take_block(layout.size());
    let p = if p.is_null() { unsafe { alloc(layout) } } else { p };
    if p.is_null() {
        crate::fatal("out of memory");
    }
    if TRACK.load(Ordering::Relaxed) {
        LIVE.fetch_add(1, Ordering::Relaxed);
    }
    let h = p as *mut Hdr;
    unsafe {
        (*h).rc = AtomicI64::new(1);
        (*h).info = info_word;
    }
    p as W
}

#[no_mangle]
pub extern "C" fn ck_alloc(info_word: u64, size: u64) -> W {
    alloc_obj(info_word, size as usize)
}

pub fn new_con(con: u32, fields: &[W]) -> W {
    if fields.is_empty() {
        return nullary(con);
    }
    let w = alloc_obj(info(K_CON, fields.len() as u64, con as u64), HDR + 8 * fields.len());
    for (i, f) in fields.iter().enumerate() {
        set_slot(w, i, *f);
    }
    w
}

pub fn new_tuple(items: &[W]) -> W {
    if items.is_empty() {
        return UNIT;
    }
    let w = alloc_obj(info(K_TUPLE, items.len() as u64, 0), HDR + 8 * items.len());
    for (i, f) in items.iter().enumerate() {
        set_slot(w, i, *f);
    }
    w
}

fn new_blob(kind: u64, b: &[u8]) -> W {
    let w = alloc_obj(info(kind, 0, 0), HDR + 16 + b.len().div_ceil(8) * 8);
    set_slot(w, 0, b.len() as u64);
    set_slot(w, 1, 0);
    unsafe { std::ptr::copy_nonoverlapping(b.as_ptr(), (w as usize + HDR + 16) as *mut u8, b.len()) };
    w
}

/// A bytes object of one byte in the program's data, never freed: its
/// header, its length, `0` (not a slice), its byte.
#[repr(C, align(8))]
struct OneByte {
    rc: AtomicI64,
    words: [u64; 4],
}

/// The strings of one ASCII character, shared: making one allocates
/// nothing, and dropping it frees nothing.
static ASCII: [OneByte; 128] = {
    let mut a = [const { OneByte { rc: AtomicI64::new(STATIC_RC), words: [K_BYTES, 1, 0, 0] } }; 128];
    let mut i = 0;
    while i < 128 {
        a[i].words[3] = u64::from_ne_bytes([i as u8, 0, 0, 0, 0, 0, 0, 0]);
        i += 1;
    }
    a
};

/// The string of the character `c`, if it is ASCII: shared, so no memory
/// is allocated.
#[inline]
pub fn ascii_str(c: u32) -> Option<W> {
    ASCII.get(c as usize).map(|o| o as *const OneByte as W)
}

/// A string: a bytes object (#170).
pub fn new_str(s: &str) -> W {
    new_blob(K_BYTES, s.as_bytes())
}

pub fn new_bytes(b: &[u8]) -> W {
    new_blob(K_BYTES, b)
}

/// The bytes of a bytes object (a string's too).
pub fn blob<'a>(w: W) -> &'a [u8] {
    let n = slot(w, 0) as usize;
    unsafe { std::slice::from_raw_parts(crate::array::data(w) as *const u8, n) }
}

/// The text of a string: a bytes object that a `String` is, so UTF-8.
pub fn str_of<'a>(w: W) -> &'a str {
    unsafe { std::str::from_utf8_unchecked(blob(w)) }
}

pub fn is_kind(w: W, k: u64) -> bool {
    is_ptr(w) && kind(w) == k
}

// ── reference counts (D74) ──────────────────────────────────────────────────

#[inline]
pub fn dup(w: W) -> W {
    if is_ptr(w) {
        hdr(w).rc.fetch_add(1, Ordering::Relaxed);
    }
    w
}

#[inline]
pub fn drop_w(w: W) {
    if is_ptr(w) && hdr(w).rc.fetch_sub(1, Ordering::Release) == 1 {
        fence(Ordering::Acquire);
        free(w);
    }
}

#[no_mangle]
pub extern "C" fn ck_dup(w: W) -> W {
    dup(w)
}

#[no_mangle]
pub extern "C" fn ck_drop(w: W) {
    drop_w(w)
}

/// Is this the only reference? (Then it may be reused in place.)
pub fn unique(w: W) -> bool {
    is_ptr(w) && hdr(w).rc.load(Ordering::Acquire) == 1
}

/// Free an object whose count reached zero, and drop what it holds. Uses a
/// work list rather than recursion: a long list is a deep chain. The list's
/// top is kept apart, so freeing allocates only when an object frees two.
#[no_mangle]
pub extern "C" fn ck_free(w: W) {
    // Most objects freed hold no references: bytes and strings, numbers.
    // Their memory goes straight back.
    let k = kind(w);
    if k == K_BYTES && slot(w, 1) == 0 || k == K_BIG && crate::obj::big_inline(w) {
        give_back(w);
        return;
    }
    free_held(w)
}

/// Free `w` and what it holds.
#[inline(never)]
fn free_held(w: W) {
    let mut todo = Vec::new();
    let mut next = Some(w);
    while let Some(w) = next.take().or_else(|| todo.pop()) {
        let n = nfields(w);
        let mut release = |c: W| {
            if is_ptr(c) && hdr(c).rc.fetch_sub(1, Ordering::Release) == 1 {
                fence(Ordering::Acquire);
                // The top of the stack is `next`.
                if let Some(p) = next.replace(c) {
                    todo.push(p);
                }
            }
        };
        match kind(w) {
            K_CON | K_TUPLE => (0..n).for_each(|i| release(slot(w, i))),
            K_CLO => (0..n).for_each(|i| release(slot(w, i + 1))),
            K_PAP => (0..=n).for_each(|i| release(slot(w, i))),
            K_BIG if !crate::obj::big_inline(w) => unsafe { drop(Box::from_raw(slot(w, 0) as *mut num_bigint::BigInt)) },
            K_RUST => unsafe { drop(Box::from_raw(slot(w, 0) as *mut crate::obj::Obj)) },
            // Bytes and packed arrays hold nothing unless they are slices.
            K_BYTES if slot(w, 1) == 0 => {}
            K_BYTES | crate::array::K_ARRAY => crate::array::held(w).for_each(&mut release),
            _ => {}
        }
        give_back(w);
    }
}

/// Give back the memory of `w`, whose references are released.
#[inline(always)]
fn give_back(w: W) {
    if TRACK.load(Ordering::Relaxed) {
        LIVE.fetch_sub(1, Ordering::Relaxed);
    }
    let size = size_of(w).max(HDR);
    if !keep_block(w as *mut u8, size) {
        unsafe { dealloc(w as *mut u8, Layout::from_size_align(size, 8).unwrap()) };
    }
}

pub fn free(w: W) {
    ck_free(w)
}

/// A reference the runtime holds while it works with a borrowed word, so a
/// value stored into a new object is counted.
pub fn keep(w: W) -> W {
    dup(w)
}
