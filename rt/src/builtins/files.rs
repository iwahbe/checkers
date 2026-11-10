//! Builtins of files and directories under an `Fs` capability (`std.files`, §13.4).

#[allow(unused_imports)]
use super::*;

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
];

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
