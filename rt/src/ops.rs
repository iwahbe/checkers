//! Primitive operations (§13.2). Arguments are borrowed; results are owned.
//! Native code handles small integers inline and calls these otherwise.

use crate::num::Num;
use crate::obj::*;
use crate::prog::*;
use crate::word::*;

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
    if ka != kb {
        return Ok(false);
    }
    Ok(match ka {
        K_STR | K_BYTES => blob(a) == blob(b),
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
    if is_kind(a, K_STR) {
        let mut s = str_of(a).to_string();
        s.push_str(str_of(b));
        return new_str(&s);
    }
    if is_kind(a, K_BYTES) {
        let mut v = blob(a).to_vec();
        v.extend_from_slice(blob(b));
        return new_bytes(&v);
    }
    let mut items: Vec<W> = list_items(a).into_iter().map(dup).collect();
    items.extend(list_items(b).into_iter().map(dup));
    list(items)
}

#[no_mangle]
pub extern "C" fn ck_len(a: W) -> W {
    if is_kind(a, K_STR) || is_kind(a, K_BYTES) {
        return nat(blob(a).len());
    }
    nat(list_items(a).len())
}

#[no_mangle]
pub extern "C" fn ck_index(a: W, b: W, owner: u64) -> W {
    let src = blob(a);
    match to_usize(b).filter(|i| *i < src.len()) {
        Some(i) => mk_int(src[i] as i64),
        None => error(owner as u32, &format!("index {} out of bounds for {} bytes", num_of(b), src.len())),
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

#[no_mangle]
pub extern "C" fn ck_format(a: W) -> W {
    new_str(&format(a))
}

// ── `format` (D42), as the interpreter prints values ────────────────────────

pub fn format(w: W) -> String {
    if is_kind(w, K_STR) {
        return str_of(w).to_string();
    }
    show(w, 0)
}

fn paren(b: bool, s: String) -> String {
    if b {
        format!("({s})")
    } else {
        s
    }
}

/// Render as Checkers source; `p > 0` means "in argument position".
pub fn show(w: W, p: u8) -> String {
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
        K_STR => format!("{:?}", str_of(w)),
        K_BYTES => show_bytes(blob(w)),
        K_TUPLE => format!("({})", (0..nfields(w)).map(|i| show(slot(w, i), 0)).collect::<Vec<_>>().join(", ")),
        K_CLO | K_PAP => "<function>".into(),
        K_RUST => match obj(w) {
            Some(Obj::Decimal(d)) => d.render(),
            Some(Obj::Bag(b)) => {
                let items: Vec<String> = b.iter().flat_map(|(v, n)| std::iter::repeat_n(v.to_string(), *n)).collect();
                format!("<Bag {{{}}}>", items.join(", "))
            }
            Some(Obj::File(_)) => "<File>".into(),
            Some(Obj::Child(_)) => "<Child>".into(),
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
