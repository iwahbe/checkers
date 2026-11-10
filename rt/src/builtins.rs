//! The standard library's `__builtin` functions for native code. Each takes
//! its kept (non-erased) arguments as a borrowed array and returns an owned
//! word. Runtime errors are reported as D76 describes.

use crate::num::{Decimal, Num};
use crate::obj::*;
use crate::prog::*;
use crate::word::*;
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::sync::Mutex;

/// The builtins native code may call, by their standard-library names.
pub const NAMES: &[(&str, &str)] = &[
    ("terminal.print_line", "ckb_print_line"),
    ("terminal.eprint_line", "ckb_eprint_line"),
    ("terminal.read_all", "ckb_read_all"),
    ("terminal.read_line", "ckb_read_line"),
    ("files.read", "ckb_files_read"),
    ("files.write", "ckb_files_write"),
    ("files.within", "ckb_files_within"),
    ("files.describe", "ckb_files_describe"),
    ("files.open", "ckb_files_open"),
    ("files.create", "ckb_files_create"),
    ("files.close", "ckb_files_close"),
    ("files.read_line", "ckb_files_read_line"),
    ("files.write_line", "ckb_files_write_line"),
    ("bytes.matches_at", "ckb_matches_at"),
    ("string.from_chars", "ckb_from_chars"),
    ("string.from_char", "ckb_from_char"),
    ("string.concat_map", "ckb_concat_map"),
    ("string.bytes", "ckb_string_bytes"),
    ("utf8.encode", "ckb_string_bytes"),
    ("char.code", "ckb_identity"),
    ("char.from_scalar", "ckb_identity"),
    ("char.from_ascii", "ckb_identity"),
    ("char.from_surrogates", "ckb_from_surrogates"),
    ("utf8.decode_at", "ckb_decode_at"),
    ("decimal.scan_json", "ckb_scan_json"),
    ("decimal.render", "ckb_decimal_render"),
    ("decimal.of_int", "ckb_decimal_of_int"),
    ("bag.of", "ckb_bag_of"),
    ("bag.count", "ckb_bag_count"),
    ("bag.sum", "ckb_bag_sum"),
    ("cown.new", "ckb_cown_new"),
    ("future.ready", "ckb_future_ready"),
    ("terminal.write", "ckb_write"),
    ("terminal.write_bytes", "ckb_write_bytes"),
    ("string.concat", "ckb_string_concat"),
    ("string.from_utf8", "ckb_from_utf8"),
    ("bytes.slice", "ckb_bytes_slice"),
    ("bytes.concat", "ckb_bytes_concat"),
    ("files.list", "ckb_files_list"),
    ("env.get", "ckb_env_get"),
    ("env.executable", "ckb_env_executable"),
    ("proc.exec", "ckb_proc_exec"),
];

/// The address of each builtin, for the JIT.
pub fn addresses() -> Vec<(&'static str, *const u8)> {
    type B = extern "C" fn(*const W, u64) -> W;
    let f = |x: B| x as *const u8;
    vec![
        ("ckb_print_line", f(ckb_print_line)),
        ("ckb_eprint_line", f(ckb_eprint_line)),
        ("ckb_read_all", f(ckb_read_all)),
        ("ckb_read_line", f(ckb_read_line)),
        ("ckb_files_read", f(ckb_files_read)),
        ("ckb_files_write", f(ckb_files_write)),
        ("ckb_files_within", f(ckb_files_within)),
        ("ckb_files_describe", f(ckb_files_describe)),
        ("ckb_files_open", f(ckb_files_open)),
        ("ckb_files_create", f(ckb_files_create)),
        ("ckb_files_close", f(ckb_files_close)),
        ("ckb_files_read_line", f(ckb_files_read_line)),
        ("ckb_files_write_line", f(ckb_files_write_line)),
        ("ckb_matches_at", f(ckb_matches_at)),
        ("ckb_from_chars", f(ckb_from_chars)),
        ("ckb_from_char", f(ckb_from_char)),
        ("ckb_concat_map", f(ckb_concat_map)),
        ("ckb_string_bytes", f(ckb_string_bytes)),
        ("ckb_identity", f(ckb_identity)),
        ("ckb_from_surrogates", f(ckb_from_surrogates)),
        ("ckb_decode_at", f(ckb_decode_at)),
        ("ckb_scan_json", f(ckb_scan_json)),
        ("ckb_decimal_render", f(ckb_decimal_render)),
        ("ckb_decimal_of_int", f(ckb_decimal_of_int)),
        ("ckb_bag_of", f(ckb_bag_of)),
        ("ckb_bag_count", f(ckb_bag_count)),
        ("ckb_bag_sum", f(ckb_bag_sum)),
        ("ckb_cown_new", f(ckb_cown_new)),
        ("ckb_future_ready", f(ckb_future_ready)),
        ("ckb_write", f(ckb_write)),
        ("ckb_write_bytes", f(ckb_write_bytes)),
        ("ckb_string_concat", f(ckb_string_concat)),
        ("ckb_from_utf8", f(ckb_from_utf8)),
        ("ckb_bytes_slice", f(ckb_bytes_slice)),
        ("ckb_bytes_concat", f(ckb_bytes_concat)),
        ("ckb_files_list", f(ckb_files_list)),
        ("ckb_env_get", f(ckb_env_get)),
        ("ckb_env_executable", f(ckb_env_executable)),
        ("ckb_proc_exec", f(ckb_proc_exec)),
    ]
}

fn args<'a>(p: *const W, n: u64) -> &'a [W] {
    if n == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(p, n as usize) }
    }
}

fn s(w: W) -> &'static str {
    if !is_kind(w, K_STR) {
        bug("expected a string");
    }
    str_of(w)
}

fn b(w: W) -> &'static [u8] {
    if !is_kind(w, K_BYTES) {
        bug("expected bytes");
    }
    blob(w)
}

fn n(w: W) -> usize {
    to_usize(w).unwrap_or_else(|| bug("a number out of range"))
}

fn ch(w: W) -> char {
    u32::try_from(n(w)).ok().and_then(char::from_u32).unwrap_or_else(|| bug("not a Unicode scalar value"))
}

/// The operating system's message, without Rust's " (os error N)" suffix.
fn describe_io(e: &std::io::Error) -> W {
    let s = e.to_string();
    let s = match s.find(" (os error") {
        Some(k) => s[..k].to_string(),
        None => s,
    };
    new_obj(Obj::IoErr(s))
}

fn io_err(m: &str) -> W {
    new_obj(Obj::IoErr(m.to_string()))
}

/// Resolve a path against an `Fs` capability (§13.4).
fn path(fs: W, p: &str) -> Result<PathBuf, W> {
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

fn file_result(r: std::io::Result<std::fs::File>, write: bool) -> W {
    match r {
        Ok(f) => {
            let st = if write {
                FileState::Write(std::io::BufWriter::new(f))
            } else {
                FileState::Read(std::io::BufReader::new(f))
            };
            ok(new_obj(Obj::File(Mutex::new(Some(st)))))
        }
        Err(e) => err(describe_io(&e)),
    }
}

fn file<'a>(w: W) -> &'a Mutex<Option<FileState>> {
    match obj(w) {
        Some(Obj::File(f)) => f,
        _ => bug("expected a file"),
    }
}

macro_rules! builtin {
    ($name:ident, |$a:ident| $body:expr) => {
        #[no_mangle]
        pub extern "C" fn $name(p: *const W, n: u64) -> W {
            let $a = args(p, n);
            $body
        }
    };
}

builtin!(ckb_print_line, |a| {
    crate::io::print_line(s(a[0]));
    UNIT
});

builtin!(ckb_eprint_line, |a| {
    crate::io::eprint_line(s(a[0]));
    UNIT
});

builtin!(ckb_read_all, |_a| match crate::io::read_all() {
    Ok(buf) => ok(new_bytes(&buf)),
    Err(e) => err(describe_io(&e)),
});

builtin!(ckb_read_line, |_a| match crate::io::read_line() {
    Some(l) => some(new_str(&l)),
    None => none(),
});

builtin!(ckb_files_read, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => match std::fs::read(p) {
        Ok(bytes) => ok(new_bytes(&bytes)),
        Err(e) => err(describe_io(&e)),
    },
});

builtin!(ckb_files_write, |a| match path(a[2], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => match std::fs::write(p, b(a[1])) {
        Ok(()) => ok(UNIT),
        Err(e) => err(describe_io(&e)),
    },
});

builtin!(ckb_files_within, |a| match path(a[1], s(a[0])) {
    Ok(dir) => new_obj(Obj::Fs(dir)),
    // A directory outside the capability: confine to nothing usable.
    Err(e) => {
        drop_w(e);
        new_obj(Obj::Fs(PathBuf::from("/nonexistent-checkers-confined")))
    }
});

builtin!(ckb_files_describe, |a| match obj(a[0]) {
    Some(Obj::IoErr(m)) => new_str(m),
    _ => bug("expected an IoError"),
});

builtin!(ckb_files_open, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => file_result(std::fs::File::open(p), false),
});

builtin!(ckb_files_create, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => file_result(std::fs::File::create(p), true),
});

builtin!(ckb_files_close, |a| {
    if let Some(FileState::Write(mut w)) = file(a[0]).lock().unwrap().take() {
        let _ = w.flush();
    }
    UNIT
});

builtin!(ckb_files_read_line, |a| {
    let line = match &mut *file(a[0]).lock().unwrap() {
        Some(FileState::Read(r)) => crate::io::read_line_from(r).ok().flatten(),
        Some(FileState::Write(_)) => bug("this file was opened for writing"),
        None => bug("this file is closed"),
    };
    let opt = match line {
        Some(l) => some(new_str(&l)),
        None => none(),
    };
    new_tuple(&[opt, dup(a[0])])
});

builtin!(ckb_files_write_line, |a| {
    match &mut *file(a[1]).lock().unwrap() {
        Some(FileState::Write(w)) => {
            let _ = writeln!(w, "{}", s(a[0]));
        }
        Some(FileState::Read(_)) => bug("this file was opened for reading"),
        None => bug("this file is closed"),
    }
    new_tuple(&[UNIT, dup(a[1])])
});

builtin!(ckb_matches_at, |a| {
    let (src, i, word) = (b(a[0]), n(a[1]), b(a[2]));
    bool_w(i.checked_add(word.len()).is_some_and(|end| end <= src.len() && &src[i..end] == word))
});

builtin!(ckb_from_chars, |a| {
    let st: String = list_items(a[0]).into_iter().map(ch).collect();
    new_str(&st)
});

builtin!(ckb_from_char, |a| new_str(&ch(a[0]).to_string()));

builtin!(ckb_concat_map, |a| {
    let mut out = String::new();
    for c in s(a[1]).chars() {
        let r = crate::apply::apply(dup(a[0]), vec![nat(c as usize)]);
        out.push_str(s(r));
        drop_w(r);
    }
    new_str(&out)
});

builtin!(ckb_string_bytes, |a| new_bytes(s(a[0]).as_bytes()));

builtin!(ckb_identity, |a| dup(a[0]));

builtin!(ckb_from_surrogates, |a| nat(0x10000 + ((n(a[0]) - 0xD800) << 10) + (n(a[1]) - 0xDC00)));

builtin!(ckb_decode_at, |a| {
    let (src, k) = (b(a[0]), n(a[1]));
    let rest = &src[k.min(src.len())..];
    let len = match rest.first() {
        Some(x) if *x < 0x80 => 1,
        Some(x) if *x >> 5 == 0b110 => 2,
        Some(x) if *x >> 4 == 0b1110 => 3,
        Some(x) if *x >> 3 == 0b11110 => 4,
        _ => 0,
    };
    match rest.get(..len).and_then(|x| std::str::from_utf8(x).ok()).and_then(|x| x.chars().next()) {
        Some(c) if len > 0 => some(parsed(nat(c as usize), k + len)),
        _ => none(),
    }
});

builtin!(ckb_scan_json, |a| match Decimal::scan_json(b(a[0]), n(a[1])) {
    Some((d, stop)) => some(parsed(new_obj(Obj::Decimal(d)), stop)),
    None => none(),
});

builtin!(ckb_decimal_render, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => new_str(&d.render()),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_of_int, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), 0))));

builtin!(ckb_bag_of, |a| {
    let mut counts: std::collections::BTreeMap<Num, usize> = std::collections::BTreeMap::new();
    for v in list_items(a[0]) {
        *counts.entry(num_of(v)).or_default() += 1;
    }
    new_obj(Obj::Bag(counts.into_iter().collect()))
});

builtin!(ckb_bag_count, |a| {
    let x = num_of(a[0]);
    match obj(a[1]) {
        Some(Obj::Bag(bag)) => nat(bag.iter().find(|(v, _)| *v == x).map_or(0, |(_, c)| *c)),
        _ => bug("`bag.count` needs a bag"),
    }
});

builtin!(ckb_bag_sum, |a| match (obj(a[0]), obj(a[1])) {
    (Some(Obj::Bag(x)), Some(Obj::Bag(y))) => {
        let mut counts: std::collections::BTreeMap<Num, usize> = x.iter().cloned().collect();
        for (v, c) in y.iter() {
            *counts.entry(v.clone()).or_default() += c;
        }
        new_obj(Obj::Bag(counts.into_iter().collect()))
    }
    _ => bug("`bag.sum` needs bags"),
});

builtin!(ckb_cown_new, |a| new_obj(Obj::Cown(new_cell(dup(a[0])))));

builtin!(ckb_future_ready, |a| new_obj(Obj::Future(new_cell(dup(a[0])))));

builtin!(ckb_write, |a| {
    crate::io::write(s(a[0]).as_bytes());
    UNIT
});

builtin!(ckb_write_bytes, |a| {
    crate::io::write(b(a[0]));
    UNIT
});

builtin!(ckb_string_concat, |a| {
    let parts = list_items(a[0]);
    let mut out = String::with_capacity(parts.iter().map(|p| s(*p).len()).sum());
    for p in parts {
        out.push_str(s(p));
    }
    new_str(&out)
});

builtin!(ckb_from_utf8, |a| match std::str::from_utf8(b(a[0])) {
    Ok(t) => some(new_str(t)),
    Err(_) => none(),
});

builtin!(ckb_bytes_slice, |a| {
    let (src, i, j) = (b(a[0]), n(a[1]), n(a[2]));
    match src.get(i..j) {
        Some(x) => new_bytes(x),
        None => bug("`bytes.slice` out of range"),
    }
});

builtin!(ckb_bytes_concat, |a| {
    let parts = list_items(a[0]);
    let mut out = Vec::with_capacity(parts.iter().map(|p| b(*p).len()).sum());
    for p in parts {
        out.extend_from_slice(b(p));
    }
    new_bytes(&out)
});

builtin!(ckb_files_list, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => match std::fs::read_dir(p) {
        Err(e) => err(describe_io(&e)),
        Ok(rd) => {
            let mut es = Vec::new();
            for e in rd {
                match e {
                    Ok(e) => {
                        let dir = e.file_type().is_ok_and(|t| t.is_dir());
                        es.push((e.file_name().to_string_lossy().into_owned(), dir));
                    }
                    Err(e) => return err(describe_io(&e)),
                }
            }
            es.sort();
            ok(list(es.into_iter().map(|(n, d)| entry(&n, d)).collect()))
        }
    },
});

builtin!(ckb_env_get, |a| match std::env::var(s(a[0])) {
    Ok(v) => some(new_str(&v)),
    Err(_) => none(),
});

builtin!(ckb_env_executable, |_a| match std::env::current_exe() {
    Ok(p) => match p.to_str() {
        Some(t) => some(new_str(t)),
        None => none(),
    },
    Err(_) => none(),
});

builtin!(ckb_proc_exec, |a| {
    let args: Vec<&str> = list_items(a[1]).into_iter().map(s).collect();
    // Output written so far comes first.
    crate::io::flush();
    match std::process::Command::new(s(a[0])).args(args).status() {
        Ok(st) => {
            #[cfg(unix)]
            let signal = std::os::unix::process::ExitStatusExt::signal(&st);
            #[cfg(not(unix))]
            let signal: Option<i32> = None;
            let code = match (st.code(), signal) {
                (Some(c), _) => c as usize,
                (None, Some(sig)) => 128 + sig as usize,
                (None, None) => 1,
            };
            ok(nat(code))
        }
        Err(e) => err(describe_io(&e)),
    }
});
