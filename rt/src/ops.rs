//! Primitive operations (§13.2). Arguments are borrowed; results are owned.
//! Native code handles small integers inline and calls these otherwise.

use crate::num::Num;
use crate::obj::*;
use crate::prog::*;
use crate::word::*;
use crate::desc::Ty;
use std::rc::Rc;

fn num2(a: W, b: W) -> (Num, Num) {
    (num_of(a), num_of(b))
}

#[no_mangle]
pub extern "C" fn ck_add(a: W, b: W) -> W {
    let (x, y) = num2(a, b);
    of_num(x.add(&y))
}

#[no_mangle]
pub extern "C" fn ck_sub(a: W, b: W) -> W {
    let (x, y) = num2(a, b);
    of_num(x.sub(&y))
}

/// `-` on `Nat`: checked (D41).
#[no_mangle]
pub extern "C" fn ck_natsub(a: W, b: W, owner: u64) -> W {
    let (x, y) = num2(a, b);
    if x < y {
        error(owner as u32, &format!("`-` on `Nat` would go below zero ({x} - {y})"));
    }
    of_num(x.sub(&y))
}

#[no_mangle]
pub extern "C" fn ck_mul(a: W, b: W) -> W {
    let (x, y) = num2(a, b);
    of_num(x.mul(&y))
}

fn divide(a: W, b: W, owner: u64, rem: bool) -> W {
    let (x, y) = num2(a, b);
    if y.is_zero() {
        let op = if rem { "%" } else { "/" };
        error(owner as u32, &format!("`{op}` by zero ({x} {op} 0)"));
    }
    of_num(if rem { x.rem(&y) } else { x.div(&y) })
}

#[no_mangle]
pub extern "C" fn ck_div(a: W, b: W, owner: u64) -> W {
    divide(a, b, owner, false)
}

#[no_mangle]
pub extern "C" fn ck_rem(a: W, b: W, owner: u64) -> W {
    divide(a, b, owner, true)
}

#[no_mangle]
pub extern "C" fn ck_neg(a: W) -> W {
    of_num(num_of(a).neg())
}

/// -1, 0 or 1.
#[no_mangle]
pub extern "C" fn ck_cmp(a: W, b: W) -> i64 {
    if is_int(a) && is_int(b) {
        return (int_of(a).cmp(&int_of(b))) as i64;
    }
    num_of(a).cmp(&num_of(b)) as i64
}

/// Structural equality (§13.2). `Err` names what can't be compared.
///
/// Values are compared depth first, left to right, so the first difference
/// or the first thing that can't be compared decides. What is left to
/// compare is a list on the heap, not the stack: comparing takes stack
/// independent of the values' shape and size (§13.3).
pub fn equal(a: W, b: W) -> Result<bool, &'static str> {
    let mut todo = Todo { near: [Pending::Pair(0, 0); NEAR], n: 0, far: Vec::new() };
    let r = equal_from(a, b, &mut todo);
    // Stopped early: the array elements still held.
    while let Some(e) = todo.pop() {
        if let Pending::Release(x, y) = e {
            drop_w(x);
            drop_w(y);
        }
    }
    r
}

/// How much of `equal`'s work list is kept on the stack: comparing a small
/// value allocates nothing.
const NEAR: usize = 8;

/// `equal`'s work list: its first `NEAR` entries in `near`, the rest in `far`.
struct Todo {
    near: [Pending; NEAR],
    n: usize,
    far: Vec<Pending>,
}

impl Todo {
    #[inline]
    fn push(&mut self, p: Pending) {
        if self.n < NEAR {
            self.near[self.n] = p;
            self.n += 1;
        } else {
            self.far.push(p);
        }
    }

    #[inline]
    fn pop(&mut self) -> Option<Pending> {
        if let Some(p) = self.far.pop() {
            return Some(p);
        }
        if self.n == 0 {
            return None;
        }
        self.n -= 1;
        Some(self.near[self.n])
    }
}

/// What `equal` has left to do.
#[derive(Clone, Copy)]
enum Pending {
    /// Compare these.
    Pair(W, W),
    /// Compare two arrays' elements from this index on.
    Elems(W, W, usize),
    /// Drop these elements (new references), compared now.
    Release(W, W),
}

/// What one step of `equal` finds.
enum Step {
    Equal(bool),
    /// Equal so far: two constructors or tuples alike with this many fields.
    Fields(usize),
    /// Arrays of one length stored differently: element by element.
    Elems,
}

fn equal_from(a: W, b: W, todo: &mut Todo) -> Result<bool, &'static str> {
    // The next pair, kept out of `todo`: walking a list pushes nothing.
    let mut next = Some((a, b));
    loop {
        let (a, b) = match next.take() {
            Some(p) => p,
            None => match todo.pop() {
                None => return Ok(true),
                Some(Pending::Pair(a, b)) => (a, b),
                Some(Pending::Release(x, y)) => {
                    drop_w(x);
                    drop_w(y);
                    continue;
                }
                Some(Pending::Elems(a, b, i)) => {
                    if i == crate::array::len(a) {
                        continue;
                    }
                    todo.push(Pending::Elems(a, b, i + 1));
                    let (x, y) = (crate::array::get(a, i), crate::array::get(b, i));
                    todo.push(Pending::Release(x, y));
                    (x, y)
                }
            },
        };
        match equal_step(a, b)? {
            Step::Equal(true) => {}
            Step::Equal(false) => return Ok(false),
            Step::Elems => todo.push(Pending::Elems(a, b, 0)),
            Step::Fields(n) => {
                // The first field next, the others after it in order; equal
                // words that aren't references or capabilities can be skipped.
                for i in (0..n).rev() {
                    let (x, y) = (slot(a, i), slot(b, i));
                    if x == y && !is_ptr(x) && !is_cap(x) {
                        continue;
                    }
                    if let Some((p, q)) = next.replace((x, y)) {
                        todo.push(Pending::Pair(p, q));
                    }
                }
            }
        }
    }
}

/// Compare `a` and `b` as far as they can be without their parts.
fn equal_step(a: W, b: W) -> Result<Step, &'static str> {
    if a == ERASED || b == ERASED {
        return Ok(Step::Equal(true));
    }
    if a == b && !is_ptr(a) {
        if is_cap(a) {
            return Err("capabilities");
        }
        return Ok(Step::Equal(true));
    }
    if is_num(a) && is_num(b) {
        return Ok(Step::Equal(num_of(a) == num_of(b)));
    }
    if is_cap(a) || is_cap(b) {
        return Err("capabilities");
    }
    if !is_ptr(a) || !is_ptr(b) {
        // Different immediates, or an immediate and an object of another kind.
        if is_ptr(a) && is_fn(a) || is_ptr(b) && is_fn(b) {
            return Err("functions");
        }
        return Ok(Step::Equal(false));
    }
    let (ka, kb) = (kind(a), kind(b));
    if matches!(ka, K_CLO | K_PAP) {
        return Err("functions");
    }
    // Arrays of one type may be stored differently (an `Array U8` used as
    // an `Array U32`, D133): compared element by element.
    if crate::array::is_array(a) && crate::array::is_array(b) && (ka == crate::array::K_ARRAY || kb == crate::array::K_ARRAY) {
        return Ok(crate::array::equal_flat(a, b).map_or(Step::Elems, Step::Equal));
    }
    if ka != kb {
        return Ok(Step::Equal(false));
    }
    Ok(Step::Equal(match ka {
        K_BYTES => blob(a) == blob(b),
        K_CON | K_TUPLE => {
            if ka == K_CON && tag(a) != tag(b) || nfields(a) != nfields(b) {
                return Ok(Step::Equal(false));
            }
            return Ok(Step::Fields(nfields(a)));
        }
        K_RUST => match (obj(a), obj(b)) {
            (Some(Obj::Decimal(x)), Some(Obj::Decimal(y))) => x == y,
            (Some(Obj::Bag(x)), Some(Obj::Bag(y))) => x == y,
            (Some(Obj::IoErr(x)), Some(Obj::IoErr(y))) => x == y,
            (Some(Obj::File(_)), _) => return Err("files"),
            (Some(Obj::Fs(_)), _) => return Err("capabilities"),
            (Some(Obj::Cown(_) | Obj::Future(_)), _) => return Err("cowns and futures"),
            (Some(Obj::Child(_) | Obj::Killer(_)), _) => return Err("process handles"),
            _ => false,
        },
        _ => false,
    }))
}

fn is_cap(w: W) -> bool {
    w & 7 == 4 && w != UNIT || matches!(obj(w), Some(Obj::Fs(_)))
}

fn is_fn(w: W) -> bool {
    matches!(kind(w), K_CLO | K_PAP)
}

#[no_mangle]
pub extern "C" fn ck_eq(a: W, b: W, owner: u64) -> W {
    match equal(a, b) {
        Ok(e) => bool_w(e),
        Err(what) => error(owner as u32, &format!("`==` can't compare {what}")),
    }
}

#[no_mangle]
pub extern "C" fn ck_ne(a: W, b: W, owner: u64) -> W {
    match equal(a, b) {
        Ok(e) => bool_w(!e),
        Err(what) => error(owner as u32, &format!("`==` can't compare {what}")),
    }
}

#[no_mangle]
pub extern "C" fn ck_concat(a: W, b: W) -> W {
    // Strings and bytes are arrays of `U8`: one allocation.
    if crate::array::is_array(a) {
        return crate::array::concat(a, b);
    }
    list_onto(list_items(a).into_iter().map(dup).collect(), dup(b))
}

/// `a ++ b` where this is `a`'s last use: `a` is owned (consumed), `b`
/// borrowed. An array or string with no other reference is appended to in
/// place.
#[no_mangle]
pub extern "C" fn ck_concat_own(a: W, b: W) -> W {
    if let Some(r) = crate::array::append_in_room(a, b) {
        return r;
    }
    concat_own(a, b)
}

#[inline(never)]
fn concat_own(a: W, b: W) -> W {
    if crate::array::is_array(a) {
        return crate::array::concat_own(a, b);
    }
    let r = ck_concat(a, b);
    drop_w(a);
    r
}

#[no_mangle]
pub extern "C" fn ck_len(a: W) -> W {
    if is_kind(a, K_BYTES) {
        return nat(blob(a).len());
    }
    if is_kind(a, crate::array::K_ARRAY) {
        return nat(crate::array::len(a));
    }
    nat(list_items(a).len())
}

#[no_mangle]
pub extern "C" fn ck_index(a: W, b: W, owner: u64) -> W {
    let n = crate::array::len(a);
    match to_usize(b).filter(|i| *i < n) {
        Some(i) => crate::array::get(a, i),
        None if is_kind(a, K_BYTES) => error(owner as u32, &format!("index {} out of bounds for {n} bytes", num_of(b))),
        None => error(owner as u32, &format!("index {} out of bounds for an array of {n} elements", num_of(b))),
    }
}

/// A number literal that doesn't fit in a word, from its decimal digits.
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_big_lit(p: *const u8, len: u64) -> W {
    let s = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(p, len as usize)) };
    let b: num_bigint::BigInt = s.parse().unwrap_or_default();
    of_num(Num::from_big(b))
}

// ── `debug` (#126): values as Checkers source ──────────────────────────────

fn paren(b: bool, s: String) -> String {
    if b {
        format!("({s})")
    } else {
        s
    }
}

/// Render as Checkers source, as `debug` does (#126): a type's hand-written
/// `Debug` where it has one, else the derived form. `p > 0` means "in
/// argument position".
pub fn show(w: W, p: u8) -> String {
    render(w, p, true)
}

/// The derived form only, at every level: a value's structure (a bag's
/// key, which must not depend on code the program writes).
pub fn show_derived(w: W, p: u8) -> String {
    render(w, p, false)
}

/// `show`, for a value of the type `ty` describes (#170): what the type
/// says and the value doesn't (a type stored as its one field, a string)
/// is shown as the type says.
pub fn show_typed(w: W, ty: &Ty, p: u8) -> String {
    render_typed(w, ty, p, true)
}

/// `show_derived`, by type.
pub fn show_typed_derived(w: W, ty: &Ty, p: u8) -> String {
    render_typed(w, ty, p, false)
}

fn render(w: W, p: u8, hand: bool) -> String {
    render_typed(w, &crate::desc::UNKNOWN, p, hand)
}

/// `w` written as Checkers source, by its type where `ty` names one. What
/// is left to write is a list on the heap, not the stack: showing takes
/// stack independent of the value's shape and size (§13.3), except where a
/// hand-written `debug` runs.
fn render_typed(w: W, ty: &Ty, p: u8, hand: bool) -> String {
    let mut s = Shower { out: String::new(), todo: vec![Show::Val(w, p, TyRef::Borrowed(ty))], hand };
    while let Some(next) = s.todo.pop() {
        s.step(next);
    }
    s.out
}

/// A type while showing a value: most are borrowed from the type asked
/// for, or have no arguments; only one built from a field's template with
/// arguments is held.
#[derive(Clone)]
enum TyRef<'a> {
    Borrowed(&'a Ty),
    /// A type without arguments: its tag.
    Tag(u64),
    Held(Rc<Ty>),
}

impl<'a> TyRef<'a> {
    fn of(t: Ty) -> TyRef<'a> {
        match t {
            Ty::Unknown => TyRef::Borrowed(&crate::desc::UNKNOWN),
            Ty::Con { tag, args } if args.is_empty() => TyRef::Tag(tag),
            t => TyRef::Held(Rc::new(t)),
        }
    }

    /// `f` of the type this is.
    fn with<R>(&self, f: impl FnOnce(&Ty) -> R) -> R {
        match self {
            TyRef::Borrowed(t) => f(t),
            TyRef::Tag(tag) => f(&Ty::Con { tag: *tag, args: Vec::new() }),
            TyRef::Held(t) => f(t),
        }
    }

    fn id(&self) -> Option<u32> {
        match self {
            TyRef::Tag(tag) => crate::desc::tag_id(*tag),
            t => t.with(Ty::id),
        }
    }

    /// Argument `i`.
    fn arg(&self, i: usize) -> TyRef<'a> {
        match self {
            TyRef::Borrowed(t) => TyRef::Borrowed(t.arg(i)),
            TyRef::Tag(_) => TyRef::Borrowed(&crate::desc::UNKNOWN),
            TyRef::Held(t) => TyRef::of(t.arg(i).clone()),
        }
    }

    /// A field's type, by its template.
    fn at(&self, t: &crate::desc::Template) -> TyRef<'a> {
        use crate::desc::Template;
        match t {
            Template::Unknown | Template::Fn(_) => TyRef::Borrowed(&crate::desc::UNKNOWN),
            Template::Param(i) => self.arg(*i),
            Template::Con(tag, xs) if xs.is_empty() => TyRef::Tag(*tag),
            t => self.with(|ty| TyRef::of(t.at(ty).into_owned())),
        }
    }
}

/// What showing a value has left to write.
enum Show<'a> {
    /// A value of type `ty`, in argument position if `p > 0`.
    Val(W, u8, TyRef<'a>),
    Text(&'static str),
    /// A list's elements from this cell on; `first`: none written yet.
    List(W, TyRef<'a>, bool),
    /// An array's elements from this index on.
    Elems(W, usize, TyRef<'a>),
    /// A bag's values from entry `i`'s `j`th time on, by type (`None`: by
    /// their keys); `first` as for lists.
    Bag(W, usize, usize, Option<TyRef<'a>>, bool),
    /// A new reference, held until what came before it is written.
    Release(W),
}

struct Shower<'a> {
    out: String,
    todo: Vec<Show<'a>>,
    /// Hand-written `debug`s are used (else the standard library's only).
    hand: bool,
}

impl<'a> Shower<'a> {
    fn step(&mut self, next: Show<'a>) {
        match next {
            Show::Text(t) => self.out.push_str(t),
            Show::Release(w) => drop_w(w),
            Show::Val(w, p, ty) => {
                if !ty.id().is_some_and(|id| self.typed(w, p, &ty, id)) {
                    self.untyped(w, p);
                }
            }
            Show::List(l, elem, first) => {
                let k = &prog().known;
                match con_of(l) {
                    Some(c) if Some(c) == k.cons => {
                        if !first {
                            self.out.push_str(", ");
                        }
                        self.todo.push(Show::List(field(l, 1), elem.clone(), false));
                        self.todo.push(Show::Val(field(l, 0), 0, elem));
                    }
                    Some(c) if Some(c) == k.nil => {}
                    _ => bug("expected a list"),
                }
            }
            Show::Elems(a, i, elem) => {
                if i == crate::array::len(a) {
                    return;
                }
                if i > 0 {
                    self.out.push_str(", ");
                }
                let x = crate::array::get(a, i);
                self.todo.push(Show::Elems(a, i + 1, elem.clone()));
                self.todo.push(Show::Release(x));
                self.todo.push(Show::Val(x, 0, elem));
            }
            Show::Bag(w, i, j, elem, first) => {
                let Some(Obj::Bag(b)) = obj(w) else { return };
                let Some(e) = b.get(i) else { return };
                if j >= e.count {
                    self.todo.push(Show::Bag(w, i + 1, 0, elem, first));
                    return;
                }
                if !first {
                    self.out.push_str(", ");
                }
                match elem {
                    None => {
                        self.out.push_str(&e.key);
                        self.todo.push(Show::Bag(w, i, j + 1, None, false));
                    }
                    Some(elem) => {
                        self.todo.push(Show::Bag(w, i, j + 1, Some(elem.clone()), false));
                        self.todo.push(Show::Val(e.value, 0, elem));
                    }
                }
            }
        }
    }

    /// `(a, b, c)`: a tuple's components, the type of each by `ty`.
    fn tuple(&mut self, w: W, ty: impl Fn(usize) -> TyRef<'a>) {
        self.out.push('(');
        self.todo.push(Show::Text(")"));
        for i in (0..nfields(w)).rev() {
            self.todo.push(Show::Val(slot(w, i), 0, ty(i)));
            if i > 0 {
                self.todo.push(Show::Text(", "));
            }
        }
    }

    /// A constructor applied to its shown fields, each with the type and
    /// the descriptor (a new reference, if one was computed) `ty` gives.
    fn con(&mut self, w: W, c: u32, p: u8, mut ty: impl FnMut(usize) -> (TyRef<'a>, Option<W>)) {
        let ci = &prog().cons[c as usize];
        let n = if is_nullary(w) { 0 } else { nfields(w) };
        let shown = |i: usize| ci.shown.get(i).copied().unwrap_or(false);
        if !(0..n).any(shown) {
            self.out.push_str(&ci.name);
            return;
        }
        if p > 0 {
            self.out.push('(');
            self.todo.push(Show::Text(")"));
        }
        self.out.push_str(&ci.name);
        for i in (0..n).filter(|i| shown(*i)).rev() {
            let (fty, held) = ty(i);
            self.todo.extend(held.map(Show::Release));
            self.todo.push(Show::Val(slot(w, i), 1, fty));
            self.todo.push(Show::Text(" "));
        }
    }

    /// `w` shown as a value of type `id` (with arguments in `ty`), if that
    /// says more than the value does: `false` if not.
    fn typed(&mut self, w: W, p: u8, ty: &TyRef<'a>, id: u32) -> bool {
        let pg = prog();
        if id == crate::desc::TUPLE {
            if !is_kind(w, K_TUPLE) {
                return false;
            }
            self.tuple(w, |i| ty.arg(i));
            return true;
        }
        let other = crate::prog::TyInfo::default();
        let info = pg.tys.get(id as usize).unwrap_or(&other);
        if (self.hand || info.std_debug) && info.debug.is_some() {
            if let Some((f, n)) = crate::prog::debug_fn_of_type(id) {
                let targs = ty.with(|t| (0..n).map(|i| t.arg(i).to_word()).collect());
                let s = custom(f, targs, w, p);
                self.out.push_str(&s);
                return true;
            }
        }
        match info.kind {
            TyKind::List if is_list(w) => {
                self.out.push('[');
                self.todo.push(Show::Text("]"));
                self.todo.push(Show::List(w, ty.arg(0), true));
                return true;
            }
            // A bag's values by its element type, each as many times as it is there.
            TyKind::Bag if matches!(obj(w), Some(Obj::Bag(_))) => {
                self.out.push_str("<Bag {");
                self.todo.push(Show::Text("}>"));
                self.todo.push(Show::Bag(w, 0, 0, Some(ty.arg(0)), true));
                return true;
            }
            TyKind::Array if crate::array::is_array(w) => {
                let elem = ty.arg(0);
                // An array of bytes by its element type, not by how it is stored.
                if elem.with(Ty::layout) == crate::array::Layout::U8 && is_kind(w, K_BYTES) {
                    self.out.push_str(&show_bytes(blob(w)));
                    return true;
                }
                self.out.push('[');
                self.todo.push(Show::Text("]"));
                self.todo.push(Show::Elems(w, 0, elem));
                return true;
            }
            _ => {}
        }
        // Stored as its one kept field: the value is that field.
        if let Some((c, k)) = info.unboxed {
            let ci = &pg.cons[c as usize];
            if !ci.shown.get(k).copied().unwrap_or(false) {
                self.out.push_str(&ci.name);
                return true;
            }
            if p > 0 {
                self.out.push('(');
                self.todo.push(Show::Text(")"));
            }
            self.out.push_str(&ci.name);
            self.out.push(' ');
            match ci.templates.get(k) {
                // Computed from the type's value arguments: the fields before it
                // aren't kept, so they are given as erased.
                Some(crate::desc::Template::Fn(f)) => {
                    let targs = ty.with(|t| (0..ci.np).map(|j| t.arg(j).to_arg()).collect());
                    let d = crate::prog::field_type(*f, targs, &vec![ERASED; k]);
                    self.todo.push(Show::Release(d));
                    self.todo.push(Show::Val(w, 1, TyRef::of(Ty::of_word(d))));
                }
                t => {
                    let fty = t.map_or(TyRef::Borrowed(&crate::desc::UNKNOWN), |t| ty.at(t));
                    self.todo.push(Show::Val(w, 1, fty));
                }
            }
            return true;
        }
        let Some(c) = con_of(w) else { return false };
        let ci = &pg.cons[c as usize];
        if ci.ty != Some(id) {
            return false;
        }
        self.con(w, c, p, |i| match ci.templates.get(i) {
            // A type computed from earlier fields: computed now.
            Some(crate::desc::Template::Fn(f)) => {
                let targs = ty.with(|t| (0..ci.np).map(|j| t.arg(j).to_arg()).collect());
                let before: Vec<W> = (0..i).map(|j| slot(w, j)).collect();
                let d = crate::prog::field_type(*f, targs, &before);
                (TyRef::of(Ty::of_word(d)), Some(d))
            }
            t => (t.map_or(TyRef::Borrowed(&crate::desc::UNKNOWN), |t| ty.at(t)), None),
        });
        true
    }

    /// `w` shown by what it is alone.
    fn untyped(&mut self, w: W, p: u8) {
        let pg = prog();
        let k = &pg.known;
        if is_num(w) {
            let n = num_of(w);
            let s = paren(p > 0 && n.is_negative(), n.to_string());
            self.out.push_str(&s);
            return;
        }
        if w == ERASED {
            self.out.push('_');
            return;
        }
        if w == UNIT {
            self.out.push_str("()");
            return;
        }
        if w & 7 == 4 {
            self.out.push_str(match w {
                CAP_TERM => "<Term>",
                CAP_FS => "<Fs>",
                CAP_ENV => "<Env>",
                CAP_PROC => "<Proc>",
                CAP_NET => "<Net>",
                CAP_CLOCK => "<Clock>",
                CAP_SCHED => "<Sched>",
                _ => "<?>",
            });
            return;
        }
        if let Some(c) = con_of(w) {
            if let Some((f, n, _)) = debug_fn(c).filter(|d| self.hand || d.2) {
                let s = custom(f, vec![ERASED; n], w, p);
                self.out.push_str(&s);
                return;
            }
            if Some(c) == k.nil || Some(c) == k.cons {
                self.out.push('[');
                self.todo.push(Show::Text("]"));
                self.todo.push(Show::List(w, TyRef::Borrowed(&crate::desc::UNKNOWN), true));
                return;
            }
            self.con(w, c, p, |_| (TyRef::Borrowed(&crate::desc::UNKNOWN), None));
            return;
        }
        let text: String = match kind(w) {
            K_BYTES => show_bytes(blob(w)),
            crate::array::K_ARRAY => {
                self.out.push('[');
                self.todo.push(Show::Text("]"));
                self.todo.push(Show::Elems(w, 0, TyRef::Borrowed(&crate::desc::UNKNOWN)));
                return;
            }
            K_TUPLE => {
                self.tuple(w, |_| TyRef::Borrowed(&crate::desc::UNKNOWN));
                return;
            }
            K_CLO | K_PAP => "<function>".into(),
            K_RUST => match obj(w) {
                Some(Obj::Decimal(d)) => d.render(),
                Some(Obj::Bag(_)) => {
                    self.out.push_str("<Bag {");
                    self.todo.push(Show::Text("}>"));
                    self.todo.push(Show::Bag(w, 0, 0, None, true));
                    return;
                }
                Some(Obj::File(_)) => "<File>".into(),
                Some(Obj::Child(_)) => "<Child>".into(),
                Some(Obj::Killer(_)) => "<Killer>".into(),
                Some(Obj::IoErr(m)) => format!("<IoError: {m}>"),
                Some(Obj::Fs(_)) => "<Fs>".into(),
                Some(Obj::Cown(_)) => "<Cown>".into(),
                Some(Obj::Future(_)) => "<Future>".into(),
                None => "<?>".into(),
            },
            _ => "<?>".into(),
        };
        self.out.push_str(&text);
    }
}

/// Whether `w` is a list: `[]` or a cell.
fn is_list(w: W) -> bool {
    let k = &prog().known;
    con_of(w).is_some_and(|c| Some(c) == k.nil || Some(c) == k.cons)
}

/// What a hand-written `debug` gives, in argument position in parentheses
/// if it has a space outside brackets and quotes. `targs` (owned) are its
/// type parameters' words.
fn custom(f: W, targs: Vec<W>, w: W, p: u8) -> String {
    let mut args = targs;
    args.push(dup(w));
    let r = crate::apply::apply(dup(f), args);
    let s = if is_kind(r, K_BYTES) { str_of(r).to_string() } else { bug("a `debug` that didn't give a string") };
    drop_w(r);
    if p == 0 {
        return s;
    }
    let (mut depth, mut quoted, mut escaped, mut spaced) = (0i32, false, false, false);
    for c in s.chars() {
        match c {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            '(' | '[' | '{' if !quoted => depth += 1,
            ')' | ']' | '}' if !quoted => depth -= 1,
            ' ' if !quoted && depth == 0 => spaced = true,
            _ => {}
        }
    }
    paren(spaced, s)
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

// ── tuples (D174) ────────────────────────────────────────────────────────────

/// A tuple just built whose last component is a tuple: one flat tuple, as
/// `(a, (b, c))` is `(a, b, c)`. Consumes `t`.
#[no_mangle]
pub extern "C" fn ck_tuple_flat(t: W) -> W {
    let n = nfields(t);
    let last = slot(t, n - 1);
    if n < 2 || !is_kind(last, K_TUPLE) {
        return t;
    }
    // A tuple that exists is flat already, so one level is enough.
    let mut items: Vec<W> = (0..n - 1).map(|i| dup(slot(t, i))).collect();
    items.extend((0..nfields(last)).map(|i| dup(slot(last, i))));
    drop_w(t);
    new_tuple(&items)
}

/// Component `i` of a tuple and everything after it: the component, if it is
/// the last, else a tuple of the rest (a pattern's last component, D174).
/// Borrows `t`; the result is owned.
#[no_mangle]
pub extern "C" fn ck_tuple_rest(t: W, i: W) -> W {
    let (n, i) = (nfields(t), i as usize);
    if n == i + 1 {
        return dup(slot(t, i));
    }
    let items: Vec<W> = (i..n).map(|k| dup(slot(t, k))).collect();
    new_tuple(&items)
}
