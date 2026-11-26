//! Builtins of files and directories under an `Fs` capability (`std.files`, §13.4).

#[allow(unused_imports)]
use super::*;
use crate::fiber::blocking;
use std::io::Read;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.files.read", "ckb_files_read", ckb_files_read),
    ("std.files.write", "ckb_files_write", ckb_files_write),
    ("std.files.within", "ckb_files_within", ckb_files_within),
    ("std.files.describe", "ckb_files_describe", ckb_files_describe),
    ("std.files.open", "ckb_files_open", ckb_files_open),
    ("std.files.create", "ckb_files_create", ckb_files_create),
    ("std.files.close", "ckb_files_close", ckb_files_close),
    ("std.files.read_line", "ckb_files_read_line", ckb_files_read_line),
    ("std.files.write_line", "ckb_files_write_line", ckb_files_write_line),
    ("std.files.list", "ckb_files_list", ckb_files_list),
    ("std.files.create_dirs", "ckb_files_create_dirs", ckb_files_create_dirs),
    ("std.files.read_some", "ckb_files_read_some", ckb_files_read_some),
    ("std.files.read_exactly", "ckb_files_read_exactly", ckb_files_read_exactly),
    ("std.files.read_rest", "ckb_files_read_rest", ckb_files_read_rest),
    ("std.files.write_bytes", "ckb_files_write_bytes", ckb_files_write_bytes),
    ("std.files.flush", "ckb_files_flush", ckb_files_flush),
];

// Calls on paths run without holding a behaviour's thread (D113).

builtin!(ckb_files_read, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => blocking(move || match p.open().and_then(|mut f| {
        let mut v = Vec::new();
        f.read_to_end(&mut v).map(|_| v)
    }) {
        Ok(bytes) => ok(new_bytes(&bytes)),
        Err(e) => err(describe_io(&e)),
    }),
});

builtin!(ckb_files_write, |a| match path(a[2], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => {
        let contents = b(a[1]).to_vec();
        blocking(move || match p.create().and_then(|mut f| f.write_all(&contents)) {
            Ok(()) => ok(UNIT),
            Err(e) => err(describe_io(&e)),
        })
    }
});

// `dir` as a path in `fs`, opened beneath it now if it is there, else the
// first time it is used and there; held open after that (`crate::confine`).
builtin!(ckb_files_within, |a| {
    let parent = match obj(a[1]) {
        Some(Obj::Fs(root)) => Some(root.clone()),
        _ if a[1] == CAP_FS => None,
        _ => bug("expected a file system capability"),
    };
    let root = std::sync::Arc::new(Root::new(parent, s(a[0])));
    let r = root.clone();
    blocking(move || r.try_open());
    new_obj(Obj::Fs(root))
});

builtin!(ckb_files_describe, |a| match obj(a[0]) {
    Some(Obj::IoErr(m)) => new_str(m),
    _ => bug("expected an IoError"),
});

builtin!(ckb_files_open, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => blocking(move || file_result(p.open(), false)),
});

builtin!(ckb_files_create, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => blocking(move || file_result(p.create(), true)),
});

builtin!(ckb_files_close, |a| {
    let st = file(a[0]).lock().unwrap_or_else(|e| e.into_inner()).take();
    match st {
        Some(FileState::Write(mut w)) => {
            let _ = w.flush();
        }
        // The stream stays open; what this handle wrote goes out now.
        Some(FileState::Stdout) => crate::io::flush(),
        _ => {}
    }
    UNIT
});

builtin!(ckb_files_read_line, |a| {
    let line = match reading(a[0], crate::io::read_line_from) {
        Ok(l) => l,
        Err(e) => {
            fail_on("files.read_line", &e);
            None
        }
    };
    let opt = match line {
        Some(l) => some(new_str(&l)),
        None => none(),
    };
    new_tuple(&[opt, dup(a[0])])
});

builtin!(ckb_files_write_line, |a| {
    if let Err(e) = writing(a[1], |w| writeln!(w, "{}", s(a[0]))) {
        fail_on("files.write_line", &e);
    }
    new_tuple(&[UNIT, dup(a[1])])
});

/// A result and the file, as `(Result Bytes IoError, File)`.
fn bytes_and(r: std::io::Result<Vec<u8>>, f: W) -> W {
    let r = match r {
        Ok(v) => ok(new_bytes(&v)),
        Err(e) => err(describe_io(&e)),
    };
    new_tuple(&[r, dup(f)])
}

builtin!(ckb_files_read_some, |a| {
    let want = n(a[0]);
    bytes_and(
        reading(a[1], |r| {
            if want == 0 {
                return Ok(Vec::new());
            }
            let buf = loop {
                match r.fill_buf() {
                    Ok(b) => break b,
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(e) => return Err(e),
                }
            };
            let k = buf.len().min(want);
            let v = buf[..k].to_vec();
            r.consume(k);
            Ok(v)
        }),
        a[1],
    )
});

builtin!(ckb_files_read_exactly, |a| {
    let want = n(a[0]);
    bytes_and(
        reading(a[1], |r| {
            let mut v = Vec::with_capacity(want.min(1 << 20));
            r.take(want as u64).read_to_end(&mut v)?;
            Ok(v)
        }),
        a[1],
    )
});

builtin!(ckb_files_read_rest, |a| {
    bytes_and(
        reading(a[0], |r| {
            let mut v = Vec::new();
            r.read_to_end(&mut v)?;
            Ok(v)
        }),
        a[0],
    )
});

builtin!(ckb_files_write_bytes, |a| {
    let r = match writing(a[1], |w| w.write_all(b(a[0]))) {
        Ok(()) => ok(UNIT),
        Err(e) => err(describe_io(&e)),
    };
    new_tuple(&[r, dup(a[1])])
});

builtin!(ckb_files_flush, |a| {
    let r = match writing(a[0], |w| w.flush()) {
        Ok(()) => ok(UNIT),
        Err(e) => err(describe_io(&e)),
    };
    new_tuple(&[r, dup(a[0])])
});

builtin!(ckb_files_create_dirs, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => blocking(move || match p.create_dirs() {
        Ok(()) => ok(UNIT),
        Err(e) => err(describe_io(&e)),
    }),
});

builtin!(ckb_files_list, |a| match path(a[1], s(a[0])) {
    Err(e) => err(e),
    Ok(p) => blocking(move || match p.list() {
        Err(e) => err(describe_io(&e)),
        Ok(mut es) => {
            es.sort();
            ok(list(es.into_iter().map(|(n, d)| entry(&n, d)).collect()))
        }
    }),
});
