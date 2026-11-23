//! Arrays (D133, SPEC §14): `Array a`, its elements stored by layout.
//!
//! An array of `U8` is a bytes object (`K_BYTES`), so `Bytes` is unchanged.
//! Any other array is a `K_ARRAY` object: its layout in the header's tag,
//! its length in the first word, then `0` and its elements, one word each
//! for `WORDS`, packed otherwise. A slice (#169) has, after its length, a
//! pointer to its first element and the array whose elements they are,
//! which it holds a reference to: slicing takes constant time. Reading goes by the header; code that creates
//! an array is given the layout of its element type (a type argument's
//! word, `layout_word`).

use crate::num::Num;
use crate::obj::*;
use crate::prog::*;
use crate::word::*;

pub const K_ARRAY: u64 = 9;

/// How an array's elements are stored. The compiler passes one as a type
/// argument's word (`2n + 1`, an integer), so the numbers are fixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Layout {
    Words = 0,
    U8 = 1,
    I8 = 2,
    Bool = 3,
    U16 = 4,
    U32 = 5,
    I32 = 6,
    U64 = 7,
    I64 = 8,
}

use Layout::*;

impl Layout {
    pub fn of_code(c: u64) -> Layout {
        match c {
            1 => U8,
            2 => I8,
            3 => Bool,
            4 => U16,
            5 => U32,
            6 => I32,
            7 => U64,
            8 => I64,
            _ => Words,
        }
    }

    /// The layout a type argument's word names: its layout or its type's
    /// descriptor (`desc`, #170); an erased argument (`0`, or anything else
    /// that is neither) is `Words`.
    pub fn of_word(w: W) -> Layout {
        crate::desc::Ty::of_word(w).layout()
    }

    pub fn width(self) -> usize {
        match self {
            U8 | I8 | Bool => 1,
            U16 => 2,
            U32 | I32 => 4,
            U64 | I64 | Words => 8,
        }
    }

    /// The numbers it holds, for a numeric layout.
    fn range(self) -> Option<(i128, i128)> {
        Some(match self {
            U8 => (0, 255),
            I8 => (-128, 127),
            U16 => (0, 65535),
            U32 => (0, u32::MAX as i128),
            I32 => (i32::MIN as i128, i32::MAX as i128),
            U64 => (0, u64::MAX as i128),
            I64 => (i64::MIN as i128, i64::MAX as i128),
            Words | Bool => return None,
        })
    }

    /// The narrowest layout holding the elements of both (for `++`, and a
    /// `set` whose element doesn't fit).
    pub fn join(self, o: Layout) -> Layout {
        if self == o {
            return self;
        }
        let (Some((a0, a1)), Some((b0, b1))) = (self.range(), o.range()) else { return Words };
        let (lo, hi) = (a0.min(b0), a1.max(b1));
        for l in [U8, I8, U16, U32, I32, U64, I64] {
            let (x, y) = l.range().unwrap();
            if x <= lo && hi <= y {
                return l;
            }
        }
        Words
    }

    /// Can this layout hold `w`?
    pub fn holds(self, w: W) -> bool {
        match self {
            Words => true,
            Bool => w == bool_w(true) || w == bool_w(false),
            _ => {
                let (lo, hi) = self.range().unwrap();
                match num_of_opt(w) {
                    Some(Num::S(n)) => lo <= n && n <= hi,
                    _ => false,
                }
            }
        }
    }
}

fn num_of_opt(w: W) -> Option<Num> {
    is_num(w).then(|| num_of(w))
}

pub fn is_array(w: W) -> bool {
    is_kind(w, K_ARRAY) || is_kind(w, K_BYTES)
}

/// How `a` (an array) stores its elements.
pub fn layout(a: W) -> Layout {
    if is_kind(a, K_BYTES) {
        U8
    } else {
        Layout::of_code(tag(a) as u64)
    }
}

pub fn len(a: W) -> usize {
    slot(a, 0) as usize
}

/// Whether `a` (an array, or bytes) is a slice of another array.
pub fn is_slice(a: W) -> bool {
    slot(a, 1) != 0
}

/// Where `a`'s elements are: after its header, or another array's.
pub fn data(a: W) -> *mut u8 {
    match slot(a, 1) {
        0 => (a as usize + HDR + 16) as *mut u8,
        p => p as *mut u8,
    }
}

/// The size of an array or bytes object, for freeing.
pub fn size(a: W) -> usize {
    if is_slice(a) {
        HDR + 24
    } else {
        HDR + 16 + (len(a) * layout(a).width()).div_ceil(8) * 8
    }
}

/// The references an array or bytes object holds, for freeing: a slice's
/// array, or the elements of an array of words.
pub fn held(a: W) -> impl Iterator<Item = W> {
    let (owner, n) = match (is_slice(a), layout(a)) {
        (true, _) => (Some(slot(a, 2)), 0),
        (false, Words) => (None, len(a)),
        (false, _) => (None, 0),
    };
    owner.into_iter().chain((0..n).map(move |i| slot(a, i + 2)))
}

/// A new array of `n` elements laid out as `l`, its elements unset. A size
/// no machine word holds is one no machine has: out of memory (D184).
fn alloc_array(l: Layout, n: usize) -> W {
    let bytes = n.checked_mul(l.width()).and_then(|b| b.checked_next_multiple_of(8)).and_then(|b| b.checked_add(HDR + 16));
    let Some(size) = bytes else { crate::fatal("out of memory") };
    let w = if l == U8 { alloc_obj(info(K_BYTES, 0, 0), size) } else { alloc_obj(info(K_ARRAY, 0, l as u64), size) };
    set_slot(w, 0, n as u64);
    set_slot(w, 1, 0);
    w
}

/// Element `i` (in bounds), a new reference.
pub fn get(a: W, i: usize) -> W {
    let l = layout(a);
    let p = data(a);
    unsafe {
        match l {
            Words => dup(*(p as *const W).add(i)),
            U8 => mk_int(*p.add(i) as i64),
            I8 => mk_int(*(p as *const i8).add(i) as i64),
            Bool => bool_w(*p.add(i) != 0),
            U16 => mk_int((p as *const u16).add(i).read_unaligned() as i64),
            U32 => mk_int((p as *const u32).add(i).read_unaligned() as i64),
            I32 => mk_int((p as *const i32).add(i).read_unaligned() as i64),
            U64 => of_num(Num::S((p as *const u64).add(i).read_unaligned() as i128)),
            I64 => of_num(Num::S((p as *const i64).add(i).read_unaligned() as i128)),
        }
    }
}

/// Store `w` (owned; held by `l`) as element `i` of a new array.
fn put(a: W, l: Layout, i: usize, w: W) {
    let p = data(a);
    let n = || match num_of(w) {
        Num::S(n) => n,
        Num::B(_) => 0,
    };
    unsafe {
        match l {
            Words => *(p as *mut W).add(i) = w,
            U8 => *p.add(i) = n() as u8,
            I8 => *(p as *mut i8).add(i) = n() as i8,
            Bool => *p.add(i) = (w == bool_w(true)) as u8,
            U16 => (p as *mut u16).add(i).write_unaligned(n() as u16),
            U32 => (p as *mut u32).add(i).write_unaligned(n() as u32),
            I32 => (p as *mut i32).add(i).write_unaligned(n() as i32),
            U64 => (p as *mut u64).add(i).write_unaligned(n() as u64),
            I64 => (p as *mut i64).add(i).write_unaligned(n() as i64),
        }
    }
    if l != Words {
        drop_w(w);
    }
}

/// A new array laid out as `l` (or the narrowest layout holding every
/// element, if `l` can't) of `items` (owned).
pub fn from_items(l: Layout, items: Vec<W>) -> W {
    let l = if items.iter().all(|w| l.holds(*w)) { l } else { Words };
    let a = alloc_array(l, items.len());
    for (i, w) in items.into_iter().enumerate() {
        put(a, l, i, w);
    }
    a
}

/// A new array of `n` copies of `x` (borrowed), laid out as `l` (or with
/// one word per element, if `l` can't hold `x`): one allocation.
pub fn repeat(l: Layout, n: usize, x: W) -> W {
    let l = if l.holds(x) { l } else { Words };
    let a = alloc_array(l, n);
    for i in 0..n {
        put(a, l, i, dup(x));
    }
    a
}

/// A new array of `n` elements laid out as `l`, element `i` being
/// `next(i)` (owned), written in place as it comes: one allocation. If an
/// element doesn't fit `l` (a program that type checks never does that),
/// the array is rebuilt with one word per element.
pub fn build(l: Layout, n: usize, mut next: impl FnMut(usize) -> W) -> W {
    let a = alloc_array(l, n);
    for i in 0..n {
        let w = next(i);
        if !l.holds(w) {
            let mut v: Vec<W> = (0..i).map(|k| get(a, k)).collect();
            v.push(w);
            v.extend((i + 1..n).map(&mut next));
            // `a` is packed (every word fits `Words`), so it holds no
            // references: freeing it releases nothing.
            drop_w(a);
            return from_items(Words, v);
        }
        put(a, l, i, w);
    }
    a
}

/// The elements of `a` (borrowed), as new references.
pub fn items(a: W) -> Vec<W> {
    (0..len(a)).map(|i| get(a, i)).collect()
}

/// Elements `i..j` of `a` (borrowed), in `a`'s layout: a slice sharing
/// its storage, in constant time (#169). A slice of a slice is one of the
/// same array; an empty one shares nothing.
pub fn slice(a: W, i: usize, j: usize) -> W {
    let l = layout(a);
    if i == j {
        return alloc_array(l, 0);
    }
    if i == 0 && j == len(a) {
        return dup(a);
    }
    let owner = if is_slice(a) { slot(a, 2) } else { a };
    let r = if l == U8 { alloc_obj(info(K_BYTES, 0, 0), HDR + 24) } else { alloc_obj(info(K_ARRAY, 0, l as u64), HDR + 24) };
    set_slot(r, 0, (j - i) as u64);
    set_slot(r, 1, unsafe { data(a).add(i * l.width()) } as W);
    set_slot(r, 2, dup(owner));
    r
}

/// `a ++ b` (both borrowed): the narrowest layout holding both.
pub fn concat(a: W, b: W) -> W {
    let (la, lb) = (layout(a), layout(b));
    if la == lb && la != Words {
        let w = la.width();
        let (n, m) = (len(a), len(b));
        let r = alloc_array(la, n + m);
        unsafe {
            std::ptr::copy_nonoverlapping(data(a), data(r), n * w);
            std::ptr::copy_nonoverlapping(data(b), data(r).add(n * w), m * w);
        }
        return r;
    }
    let mut v = items(a);
    v.extend(items(b));
    from_items(la.join(lb), v)
}

/// `a ++ b`, `a` owned and `b` borrowed: when `a` is the only reference to
/// its storage (not a slice, not `b`) and `b` has its layout, `b`'s elements
/// are written after `a`'s in place, its memory grown if they don't fit;
/// otherwise a new array, and `a` dropped.
pub fn concat_own(a: W, b: W) -> W {
    let l = layout(a);
    if l != layout(b) || a == b || !unique(a) || is_slice(a) {
        let r = concat(a, b);
        drop_w(a);
        return r;
    }
    let w = l.width();
    let (n, m) = (len(a), len(b));
    let old = size(a);
    let Some(new) = (n + m).checked_mul(w).and_then(|b| b.checked_next_multiple_of(8)).and_then(|b| b.checked_add(HDR + 16)) else {
        crate::fatal("out of memory")
    };
    let a = if new > old {
        // The old layout is the one it was allocated with: its size is
        // computed from its length, like `size`.
        let p = unsafe { std::alloc::realloc(a as *mut u8, std::alloc::Layout::from_size_align(old, 8).unwrap(), new) };
        if p.is_null() {
            crate::fatal("out of memory");
        }
        p as W
    } else {
        a
    };
    if l == Words {
        let (src, dst) = (data(b) as *const W, data(a) as *mut W);
        for i in 0..m {
            unsafe { *dst.add(n + i) = dup(*src.add(i)) };
        }
    } else {
        unsafe { std::ptr::copy_nonoverlapping(data(b), data(a).add(n * w), m * w) };
    }
    set_slot(a, 0, (n + m) as u64);
    a
}

/// `a` (borrowed) with element `i` (in bounds) replaced by `x` (borrowed).
/// In place if `a` has no other reference and can hold `x`: the caller must
/// then own `a` (`std.array.set` is called through its wrapper, which does).
pub fn set(a: W, i: usize, x: W) -> W {
    let l = layout(a);
    // A slice's elements are its array's, which others may see.
    if unique(a) && !is_slice(a) && l.holds(x) {
        if l == Words {
            let p = unsafe { (data(a) as *mut W).add(i) };
            unsafe {
                drop_w(*p);
                *p = dup(x);
            }
        } else {
            put(a, l, i, dup(x));
        }
        return dup(a);
    }
    let mut v = items(a);
    drop_w(std::mem::replace(&mut v[i], dup(x)));
    from_items(l, v)
}

/// The elements of `a` (borrowed) in reverse order, in `a`'s layout.
pub fn reverse(a: W) -> W {
    let mut v = items(a);
    v.reverse();
    from_items(layout(a), v)
}

pub fn equal(a: W, b: W, eq: &dyn Fn(W, W) -> Result<bool, &'static str>) -> Result<bool, &'static str> {
    let (n, la, lb) = (len(a), layout(a), layout(b));
    if n != len(b) {
        return Ok(false);
    }
    if la == lb && la != Words {
        let w = la.width();
        return Ok(unsafe { std::slice::from_raw_parts(data(a), n * w) == std::slice::from_raw_parts(data(b), n * w) });
    }
    for i in 0..n {
        let (x, y) = (get(a, i), get(b, i));
        let e = eq(x, y);
        drop_w(x);
        drop_w(y);
        if !e? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// A type argument's word for an element type: its layout.
pub fn layout_word(l: Layout) -> W {
    mk_int(l as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widths() {
        assert_eq!([U8, I8, Bool, U16, U32, I32, U64, I64, Words].map(Layout::width), [1, 1, 1, 2, 4, 4, 8, 8, 8]);
    }

    #[test]
    fn type_argument_words() {
        // The compiler passes `2n + 1` for layout `n`; an erased argument is 0.
        assert_eq!(Layout::of_word(layout_word(I32)), I32);
        assert_eq!(Layout::of_word(ERASED), Words);
        // A descriptor's tag keeps the layout in its low four bits (#170).
        assert_eq!(Layout::of_word(mk_int(crate::desc::tag(Some(5), U16 as u8) as i64)), U16);
        assert_eq!(Layout::of_word(mk_int(-3)), Words);
    }

    #[test]
    fn joins() {
        assert_eq!(U8.join(U8), U8);
        assert_eq!(U8.join(U32), U32);
        // `[-128, 255]`: with no `I16`, the narrowest is `I32`.
        assert_eq!(U8.join(I8), I32);
        assert_eq!(U32.join(I32), I64);
        assert_eq!(U64.join(I8), Words);
        assert_eq!(Bool.join(U8), Words);
    }

    #[test]
    fn packed_size() {
        let a = from_items(U16, (0..5).map(|n| mk_int(n * 1000)).collect());
        assert_eq!(size(a), HDR + 16 + 16);
        assert_eq!((0..5).map(|i| int_of(get(a, i))).collect::<Vec<_>>(), [0, 1000, 2000, 3000, 4000]);
        let s = slice(a, 1, 3);
        assert_eq!((layout(s), len(s), int_of(get(s, 1))), (U16, 2, 2000));
        drop_w(s);
        drop_w(a);
    }
}
