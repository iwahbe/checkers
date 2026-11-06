//! Standard-library functions implemented in Rust (`__builtin` bodies).
//! Arguments arrive with erased parameters already removed.

use super::num::{Decimal, Num};
use super::value::{Cap, FileState, Value};
use super::{Machine, R};
use std::sync::Mutex;
use std::io::{BufRead, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

const NAMES: &[&str] = &[
    "terminal.print_line",
    "terminal.eprint_line",
    "terminal.read_all",
    "terminal.read_line",
    "files.read",
    "files.write",
    "files.within",
    "files.describe",
    "files.open",
    "files.create",
    "files.close",
    "files.read_line",
    "files.write_line",
    "bytes.matches_at",
    "string.from_chars",
    "string.from_char",
    "string.concat_map",
    "string.bytes",
    "char.code",
    "char.from_scalar",
    "char.from_ascii",
    "char.from_surrogates",
    "utf8.decode_at",
    "utf8.encode",
    "decimal.scan_json",
    "decimal.render",
    "decimal.of_int",
    "bag.of",
    "bag.count",
    "bag.sum",
    "cown.new",
    "future.ready",
];

pub fn exists(name: &str) -> bool {
    NAMES.contains(&name)
}

/// The operating system's message, without Rust's " (os error N)" suffix.
fn describe_io(e: &std::io::Error) -> Value {
    let s = e.to_string();
    let s = match s.find(" (os error") {
        Some(k) => s[..k].to_string(),
        None => s,
    };
    Value::IoErr(Arc::from(s))
}

impl Machine {
    fn arg_str<'a>(&self, v: &'a Value) -> R<&'a str> {
        match v {
            Value::Str(s) => Ok(s),
            other => Err(self.error(format!("expected a string, found a {}", other.kind()))),
        }
    }

    fn arg_bytes<'a>(&self, v: &'a Value) -> R<&'a [u8]> {
        match v {
            Value::Bytes(b) => Ok(b),
            other => Err(self.error(format!("expected bytes, found a {}", other.kind()))),
        }
    }

    fn arg_nat(&self, v: &Value) -> R<usize> {
        match v {
            Value::Num(n) => n.to_usize().ok_or_else(|| self.error(format!("{n} is out of range here"))),
            other => Err(self.error(format!("expected a number, found a {}", other.kind()))),
        }
    }

    fn arg_char(&self, v: &Value) -> R<char> {
        let n = self.arg_nat(v)?;
        u32::try_from(n)
            .ok()
            .and_then(char::from_u32)
            .ok_or_else(|| self.error(format!("{n} is not a Unicode scalar value")))
    }

    /// Resolve a path against an `Fs` capability (§13.4).
    fn path(&self, fs: &Value, p: &str) -> Result<PathBuf, Value> {
        let Value::Cap(Cap::Fs(root)) = fs else { return Err(Value::IoErr(Arc::from("not a file system capability"))) };
        match root {
            None => Ok(PathBuf::from(p)),
            Some(dir) => {
                let rel = Path::new(p);
                let escapes = rel.is_absolute()
                    || rel.components().any(|c| matches!(c, Component::ParentDir | Component::RootDir | Component::Prefix(_)));
                if escapes {
                    Err(Value::IoErr(Arc::from("Permission denied (outside the directory this capability allows)")))
                } else {
                    Ok(dir.join(rel))
                }
            }
        }
    }

    fn file_result(&self, r: std::io::Result<std::fs::File>, write: bool) -> Value {
        match r {
            Ok(f) => {
                let st = if write {
                    FileState::Write(std::io::BufWriter::new(f))
                } else {
                    FileState::Read(std::io::BufReader::new(f))
                };
                self.ok(Value::File(Arc::new(Mutex::new(Some(st)))))
            }
            Err(e) => self.err(describe_io(&e)),
        }
    }
}

/// Read one line, without its `\n`; invalid UTF-8 becomes U+FFFD (§13.4).
fn read_line(r: &mut dyn BufRead) -> std::io::Result<Option<String>> {
    let mut buf = Vec::new();
    if r.read_until(b'\n', &mut buf)? == 0 {
        return Ok(None);
    }
    if buf.last() == Some(&b'\n') {
        buf.pop();
    }
    Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

pub fn call(it: &mut Machine, name: &str, a: Vec<Value>) -> R<Value> {
    Ok(match name {
        "terminal.print_line" | "terminal.eprint_line" => {
            let s = it.arg_str(&a[0])?.to_string();
            // One call, one atomic write (D68).
            let mut io = it.io.lock().unwrap();
            let r = if name == "terminal.print_line" {
                writeln!(io.stdout, "{s}")
            } else {
                let _ = io.stdout.flush();
                writeln!(io.stderr, "{s}")
            };
            // A closed pipe is not an error the program can act on.
            let _ = r;
            Value::unit()
        }
        "terminal.read_all" => {
            let mut buf = Vec::new();
            let got = it.io.lock().unwrap().stdin.read_to_end(&mut buf);
            match got {
                Ok(_) => it.ok(Value::Bytes(Arc::from(buf))),
                Err(e) => it.err(describe_io(&e)),
            }
        }
        "terminal.read_line" => {
            let got = {
                let mut io = it.io.lock().unwrap();
                let _ = io.stdout.flush();
                read_line(&mut *io.stdin)
            };
            match got {
                Ok(Some(s)) => it.some(Value::str(&s)),
                _ => it.none(),
            }
        }
        "files.read" => {
            let p = it.arg_str(&a[0])?.to_string();
            match it.path(&a[1], &p) {
                Err(e) => it.err(e),
                Ok(path) => match std::fs::read(path) {
                    Ok(b) => it.ok(Value::Bytes(Arc::from(b))),
                    Err(e) => it.err(describe_io(&e)),
                },
            }
        }
        "files.write" => {
            let p = it.arg_str(&a[0])?.to_string();
            let bytes = it.arg_bytes(&a[1])?.to_vec();
            match it.path(&a[2], &p) {
                Err(e) => it.err(e),
                Ok(path) => match std::fs::write(path, bytes) {
                    Ok(()) => it.ok(Value::unit()),
                    Err(e) => it.err(describe_io(&e)),
                },
            }
        }
        "files.within" => {
            let p = it.arg_str(&a[0])?.to_string();
            match it.path(&a[1], &p) {
                Ok(dir) => Value::Cap(Cap::Fs(Some(Arc::new(dir)))),
                // A directory outside the capability: confine to nothing usable.
                Err(_) => Value::Cap(Cap::Fs(Some(Arc::new(PathBuf::from("/nonexistent-checkers-confined"))))),
            }
        }
        "files.describe" => match &a[0] {
            Value::IoErr(m) => Value::Str(m.clone()),
            other => return Err(it.error(format!("expected an IoError, found a {}", other.kind()))),
        },
        "files.open" | "files.create" => {
            let p = it.arg_str(&a[0])?.to_string();
            match it.path(&a[1], &p) {
                Err(e) => it.err(e),
                Ok(path) => {
                    if name == "files.open" {
                        it.file_result(std::fs::File::open(path), false)
                    } else {
                        it.file_result(std::fs::File::create(path), true)
                    }
                }
            }
        }
        "files.close" => {
            let Value::File(f) = &a[0] else { return Err(it.error("`close` needs a file")) };
            if let Some(FileState::Write(mut w)) = f.lock().unwrap().take() {
                let _ = w.flush();
            }
            Value::unit()
        }
        "files.read_line" => {
            let Value::File(f) = &a[0] else { return Err(it.error("`read_line` needs a file")) };
            let line = match &mut *f.lock().unwrap() {
                Some(FileState::Read(r)) => read_line(r).ok().flatten(),
                Some(FileState::Write(_)) => return Err(it.error("this file was opened for writing")),
                None => return Err(it.error("this file is closed")),
            };
            let opt = match line {
                Some(s) => it.some(Value::str(&s)),
                None => it.none(),
            };
            Value::Tuple(Arc::from(vec![opt, a[0].clone()]))
        }
        "files.write_line" => {
            let s = it.arg_str(&a[0])?.to_string();
            let Value::File(f) = &a[1] else { return Err(it.error("`write_line` needs a file")) };
            match &mut *f.lock().unwrap() {
                Some(FileState::Write(w)) => {
                    let _ = writeln!(w, "{s}");
                }
                Some(FileState::Read(_)) => return Err(it.error("this file was opened for reading")),
                None => return Err(it.error("this file is closed")),
            }
            Value::Tuple(Arc::from(vec![Value::unit(), a[1].clone()]))
        }
        "bytes.matches_at" => {
            let src = it.arg_bytes(&a[0])?;
            let i = it.arg_nat(&a[1])?;
            let word = it.arg_bytes(&a[2])?;
            let m = i.checked_add(word.len()).is_some_and(|end| end <= src.len() && &src[i..end] == word);
            it.bool(m)
        }
        "string.from_chars" => {
            let mut s = String::new();
            for c in it.list_items(&a[0])? {
                s.push(it.arg_char(&c)?);
            }
            Value::str(&s)
        }
        "string.from_char" => Value::str(&it.arg_char(&a[0])?.to_string()),
        "string.concat_map" => {
            let s = it.arg_str(&a[1])?.to_string();
            let mut out = String::new();
            for c in s.chars() {
                let r = it.apply(a[0].clone(), Value::nat(c as usize))?;
                out.push_str(it.arg_str(&r)?);
            }
            Value::str(&out)
        }
        "string.bytes" | "utf8.encode" => Value::Bytes(Arc::from(it.arg_str(&a[0])?.as_bytes())),
        "char.code" | "char.from_scalar" | "char.from_ascii" => a[0].clone(),
        "char.from_surrogates" => {
            let hi = it.arg_nat(&a[0])?;
            let lo = it.arg_nat(&a[1])?;
            Value::nat(0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00))
        }
        "utf8.decode_at" => {
            let src = it.arg_bytes(&a[0])?;
            let k = it.arg_nat(&a[1])?;
            let rest = &src[k.min(src.len())..];
            let len = match rest.first() {
                Some(b) if *b < 0x80 => 1,
                Some(b) if *b >> 5 == 0b110 => 2,
                Some(b) if *b >> 4 == 0b1110 => 3,
                Some(b) if *b >> 3 == 0b11110 => 4,
                _ => 0,
            };
            match rest.get(..len).and_then(|s| std::str::from_utf8(s).ok()).and_then(|s| s.chars().next()) {
                Some(c) if len > 0 => {
                    let v = it.parsed(Value::nat(c as usize), k + len);
                    it.some(v)
                }
                _ => it.none(),
            }
        }
        "decimal.scan_json" => {
            let src = it.arg_bytes(&a[0])?;
            let i = it.arg_nat(&a[1])?;
            match Decimal::scan_json(src, i) {
                Some((d, stop)) => {
                    let v = it.parsed(Value::Decimal(Arc::new(d)), stop);
                    it.some(v)
                }
                None => it.none(),
            }
        }
        "decimal.render" => match &a[0] {
            Value::Decimal(d) => Value::str(&d.render()),
            other => return Err(it.error(format!("expected a Decimal, found a {}", other.kind()))),
        },
        "decimal.of_int" => match &a[0] {
            Value::Num(n) => Value::Decimal(Arc::new(Decimal::new(Num::big(n), 0))),
            other => return Err(it.error(format!("expected a number, found a {}", other.kind()))),
        },
        "bag.of" => {
            let mut counts: std::collections::BTreeMap<Num, usize> = std::collections::BTreeMap::new();
            for v in it.list_items(&a[0])? {
                match v {
                    Value::Num(n) => *counts.entry(n).or_default() += 1,
                    other => return Err(it.error(format!("a bag holds numbers, not a {}", other.kind()))),
                }
            }
            Value::Bag(Arc::new(counts.into_iter().collect()))
        }
        "bag.count" => {
            let Value::Num(x) = &a[0] else { return Err(it.error("`bag.count` needs a number")) };
            let Value::Bag(b) = &a[1] else { return Err(it.error("`bag.count` needs a bag")) };
            Value::nat(b.iter().find(|(v, _)| v == x).map_or(0, |(_, n)| *n))
        }
        "bag.sum" => {
            let (Value::Bag(x), Value::Bag(y)) = (&a[0], &a[1]) else { return Err(it.error("`bag.sum` needs bags")) };
            let mut counts: std::collections::BTreeMap<Num, usize> = x.iter().cloned().collect();
            for (v, n) in y.iter() {
                *counts.entry(v.clone()).or_default() += n;
            }
            Value::Bag(Arc::new(counts.into_iter().collect()))
        }
        "cown.new" => Value::Cown(super::value::Held::new(a[0].clone())),
        "future.ready" => Value::Future(super::value::Held::new(Some(a[0].clone()))),
        other => return Err(it.error(format!("`{other}` has no implementation in this interpreter yet"))),
    })
}
