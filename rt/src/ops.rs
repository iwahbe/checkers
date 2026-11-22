//! Primitive operations (§13.2). Arguments are borrowed; results are owned.
//! Native code handles small integers inline and calls these otherwise.

use crate::num::Num;
use crate::obj::*;
use crate::prog::*;
use crate::word::*;
use crate::desc::Ty;

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
pub fn equal(a: W, b: W) -> Result<bool, &'static str> {
    if a == ERASED || b == ERASED {
        return Ok(true);
    }
    if a == b && !is_ptr(a) {
        if is_cap(a) {
            return Err("capabilities");
        }
        return Ok(true);
    }
    if is_num(a) && is_num(b) {
        return Ok(num_of(a) == num_of(b));
    }
    if is_cap(a) || is_cap(b) {
        return Err("capabilities");
    }
    if !is_ptr(a) || !is_ptr(b) {
        // Different immediates, or an immediate and an object of another kind.
        if is_ptr(a) && is_fn(a) || is_ptr(b) && is_fn(b) {
            return Err("functions");
        }
        return Ok(false);
    }
    let (ka, kb) = (kind(a), kind(b));
    if matches!(ka, K_CLO | K_PAP) {
        return Err("functions");
    }
    // Arrays of one type may be stored differently (an `Array U8` used as
    // an `Array U32`, D133): compared element by element.
    if crate::array::is_array(a) && crate::array::is_array(b) && (ka == crate::array::K_ARRAY || kb == crate::array::K_ARRAY) {
        return crate::array::equal(a, b, &equal);
    }
    if ka != kb {
        return Ok(false);
    }
    Ok(match ka {
        K_BYTES => blob(a) == blob(b),
        K_CON | K_TUPLE => {
            if ka == K_CON && tag(a) != tag(b) || nfields(a) != nfields(b) {
                return Ok(false);
            }
            for i in 0..nfields(a) {
                if !equal(slot(a, i), slot(b, i))? {
                    return Ok(false);
                }
            }
            true
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
    })
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
    if is_kind(a, K_BYTES) && is_kind(b, K_BYTES) {
        let mut v = blob(a).to_vec();
        v.extend_from_slice(blob(b));
        return new_bytes(&v);
    }
    if crate::array::is_array(a) {
        return crate::array::concat(a, b);
    }
    list_onto(list_items(a).into_iter().map(dup).collect(), dup(b))
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

fn render_typed(w: W, ty: &Ty, p: u8, hand: bool) -> String {
    let Some(id) = ty.id() else { return render(w, p, hand) };
    let pg = prog();
    if id == crate::desc::TUPLE {
        if !is_kind(w, K_TUPLE) {
            return render(w, p, hand);
        }
        let parts: Vec<String> = (0..nfields(w)).map(|i| render_typed(slot(w, i), ty.arg(i), 0, hand)).collect();
        return format!("({})", parts.join(", "));
    }
    let other = crate::prog::TyInfo::default();
    let info = pg.tys.get(id as usize).unwrap_or(&other);
    if (hand || info.std_debug) && info.debug.is_some() {
        if let Some((f, n)) = crate::prog::debug_fn_of_type(id) {
            return custom(f, (0..n).map(|i| ty.arg(i).to_word()).collect(), w, p);
        }
    }
    match info.kind {
        TyKind::List if is_list(w) => {
            let elem = ty.arg(0);
            let items: Vec<String> = list_items(w).into_iter().map(|x| render_typed(x, elem, 0, hand)).collect();
            return format!("[{}]", items.join(", "));
        }
        // A bag's values by its element type, each as many times as it is there.
        TyKind::Bag => {
            if let Some(Obj::Bag(b)) = obj(w) {
                let elem = ty.arg(0);
                let items: Vec<String> = b.iter().flat_map(|e| std::iter::repeat_n(render_typed(e.value, elem, 0, hand), e.count)).collect();
                return format!("<Bag {{{}}}>", items.join(", "));
            }
        }
        TyKind::Array if crate::array::is_array(w) => {
            let elem = ty.arg(0);
            // An array of bytes by its element type, not by how it is stored.
            if elem.layout() == crate::array::Layout::U8 && is_kind(w, K_BYTES) {
                return show_bytes(blob(w));
            }
            let items: Vec<String> = crate::array::items(w)
                .into_iter()
                .map(|x| {
                    let s = render_typed(x, elem, 0, hand);
                    drop_w(x);
                    s
                })
                .collect();
            return format!("[{}]", items.join(", "));
        }
        _ => {}
    }
    // Stored as its one kept field: the value is that field.
    if let Some((c, k)) = info.unboxed {
        let ci = &pg.cons[c as usize];
        if !ci.shown.get(k).copied().unwrap_or(false) {
            return ci.name.clone();
        }
        let inner = match ci.templates.get(k) {
            // Computed from the type's value arguments: the fields before it
            // aren't kept, so they are given as erased.
            Some(crate::desc::Template::Fn(f)) => {
                let targs = (0..ci.np).map(|j| ty.arg(j).to_arg()).collect();
                let d = crate::prog::field_type(*f, targs, &vec![ERASED; k]);
                let s = render_typed(w, &Ty::of_word(d), 1, hand);
                drop_w(d);
                s
            }
            t => {
                let fty = t.map_or(std::borrow::Cow::Borrowed(&crate::desc::UNKNOWN), |t| t.at(ty));
                render_typed(w, &fty, 1, hand)
            }
        };
        return paren(p > 0, format!("{} {inner}", ci.name));
    }
    let Some(c) = con_of(w) else { return render(w, p, hand) };
    let ci = &pg.cons[c as usize];
    if ci.ty != Some(id) {
        return render(w, p, hand);
    }
    let fields: Vec<W> = if is_nullary(w) { Vec::new() } else { (0..nfields(w)).map(|i| slot(w, i)).collect() };
    let args: Vec<String> = fields
        .iter()
        .enumerate()
        .filter(|(i, _)| ci.shown.get(*i).copied().unwrap_or(false))
        .map(|(i, v)| match ci.templates.get(i) {
            // A type computed from earlier fields: computed now.
            Some(crate::desc::Template::Fn(f)) => {
                let targs = (0..ci.np).map(|j| ty.arg(j).to_arg()).collect();
                let d = crate::prog::field_type(*f, targs, &fields[..i]);
                let s = render_typed(*v, &Ty::of_word(d), 1, hand);
                drop_w(d);
                s
            }
            t => {
                let fty = t.map_or(std::borrow::Cow::Borrowed(&crate::desc::UNKNOWN), |t| t.at(ty));
                render_typed(*v, &fty, 1, hand)
            }
        })
        .collect();
    if args.is_empty() {
        ci.name.clone()
    } else {
        paren(p > 0, format!("{} {}", ci.name, args.join(" ")))
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

fn render(w: W, p: u8, hand: bool) -> String {
    let show = |w: W, p: u8| render(w, p, hand);
    let pg = prog();
    let k = &pg.known;
    if is_num(w) {
        let n = num_of(w);
        return paren(p > 0 && n.is_negative(), n.to_string());
    }
    if w == ERASED {
        return "_".into();
    }
    if w == UNIT {
        return "()".into();
    }
    if w & 7 == 4 {
        return match w {
            CAP_TERM => "<Term>",
            CAP_FS => "<Fs>",
            CAP_ENV => "<Env>",
            CAP_PROC => "<Proc>",
            CAP_NET => "<Net>",
            CAP_CLOCK => "<Clock>",
            CAP_SCHED => "<Sched>",
            _ => "<?>",
        }
        .into();
    }
    if let Some(c) = con_of(w) {
        if let Some((f, n, _)) = debug_fn(c).filter(|d| hand || d.2) {
            return custom(f, vec![ERASED; n], w, p);
        }
        if Some(c) == k.nil || Some(c) == k.cons {
            let items: Vec<String> = list_items(w).into_iter().map(|x| show(x, 0)).collect();
            return format!("[{}]", items.join(", "));
        }
        let ci = &pg.cons[c as usize];
        let fields: Vec<W> = if is_nullary(w) { Vec::new() } else { (0..nfields(w)).map(|i| slot(w, i)).collect() };
        let args: Vec<String> =
            ci.shown.iter().zip(&fields).filter(|(s, _)| **s).map(|(_, v)| show(*v, 1)).collect();
        return if args.is_empty() { ci.name.clone() } else { paren(p > 0, format!("{} {}", ci.name, args.join(" "))) };
    }
    match kind(w) {
        K_BYTES => show_bytes(blob(w)),
        crate::array::K_ARRAY => {
            let items: Vec<String> = crate::array::items(w)
                .into_iter()
                .map(|x| {
                    let s = show(x, 0);
                    drop_w(x);
                    s
                })
                .collect();
            format!("[{}]", items.join(", "))
        }
        K_TUPLE => format!("({})", (0..nfields(w)).map(|i| show(slot(w, i), 0)).collect::<Vec<_>>().join(", ")),
        K_CLO | K_PAP => "<function>".into(),
        K_RUST => match obj(w) {
            Some(Obj::Decimal(d)) => d.render(),
            Some(Obj::Bag(b)) => {
                let items: Vec<String> = b.iter().flat_map(|e| std::iter::repeat_n(e.key.clone(), e.count)).collect();
                format!("<Bag {{{}}}>", items.join(", "))
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
