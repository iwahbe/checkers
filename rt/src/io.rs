//! Standard streams for native programs. Each terminal call holds the lock
//! for its whole write, so calls are atomic (D68).

use std::io::{BufRead, BufReader, BufWriter, Read, Stdin, Stdout, Write};
use std::sync::{Mutex, OnceLock};

pub struct Std {
    pub out: BufWriter<Stdout>,
    pub inp: BufReader<Stdin>,
}

static STD: OnceLock<Mutex<Std>> = OnceLock::new();

pub fn std_io() -> std::sync::MutexGuard<'static, Std> {
    STD.get_or_init(|| Mutex::new(Std { out: BufWriter::new(std::io::stdout()), inp: BufReader::new(std::io::stdin()) }))
        .lock()
        .unwrap_or_else(|e| e.into_inner())
}

pub fn flush() {
    if let Some(m) = STD.get() {
        let mut s = m.lock().unwrap_or_else(|e| e.into_inner());
        let _ = s.out.flush();
    }
}

pub fn print_line(s: &str) {
    let mut io = std_io();
    let _ = writeln!(io.out, "{s}");
}

pub fn write(b: &[u8]) {
    let mut io = std_io();
    let _ = io.out.write_all(b);
}

pub fn eprint_line(s: &str) {
    let mut io = std_io();
    let _ = io.out.flush();
    let _ = writeln!(std::io::stderr(), "{s}");
}

pub fn read_all() -> std::io::Result<Vec<u8>> {
    let mut io = std_io();
    let mut buf = Vec::new();
    io.inp.read_to_end(&mut buf)?;
    Ok(buf)
}

/// Read one line, without its `\n`; invalid UTF-8 becomes U+FFFD (§13.4).
pub fn read_line_from(r: &mut dyn BufRead) -> std::io::Result<Option<String>> {
    let mut buf = Vec::new();
    if r.read_until(b'\n', &mut buf)? == 0 {
        return Ok(None);
    }
    if buf.last() == Some(&b'\n') {
        buf.pop();
    }
    Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

pub fn read_line() -> Option<String> {
    let mut io = std_io();
    let _ = io.out.flush();
    read_line_from(&mut io.inp).ok().flatten()
}
