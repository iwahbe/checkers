//! Standard streams for native programs. Each terminal call holds the
//! output lock for its whole write, so calls are atomic (#559). Writes block
//! their thread; reading standard input doesn't (#607): its system calls run
//! on the blocking pool, under a lock that parks a waiting fiber.

use crate::fiber::{BlockingRead, FiberLock};
use std::io::{BufRead, BufReader, BufWriter, Stdin, Stdout, Write};
use std::sync::{Mutex, MutexGuard, OnceLock};

static OUT: OnceLock<Mutex<BufWriter<Stdout>>> = OnceLock::new();
static IN: OnceLock<Mutex<BufReader<BlockingRead<Stdin>>>> = OnceLock::new();
static IN_LOCK: FiberLock = FiberLock::new();

/// Standard output, locked.
pub fn stdout() -> MutexGuard<'static, BufWriter<Stdout>> {
    OUT.get_or_init(|| Mutex::new(BufWriter::new(std::io::stdout()))).lock().unwrap_or_else(|e| e.into_inner())
}

/// Read standard input with `f`, after what was written so far is out.
pub fn with_stdin<T>(f: impl FnOnce(&mut dyn BufRead) -> T) -> T {
    let _ = stdout().flush();
    IN_LOCK.lock();
    let r = {
        let mut inp = IN
            .get_or_init(|| Mutex::new(BufReader::with_capacity(1 << 16, BlockingRead(std::io::stdin()))))
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        f(&mut *inp)
    };
    IN_LOCK.unlock();
    r
}

pub fn flush() {
    if let Some(m) = OUT.get() {
        let _ = m.lock().unwrap_or_else(|e| e.into_inner()).flush();
    }
}

pub fn print_line(s: &str) {
    let _ = writeln!(stdout(), "{s}");
}

pub fn write(b: &[u8]) {
    let _ = stdout().write_all(b);
}

pub fn eprint_line(s: &str) {
    let mut out = stdout();
    let _ = out.flush();
    let _ = writeln!(std::io::stderr(), "{s}");
}

pub fn read_all() -> std::io::Result<Vec<u8>> {
    with_stdin(|r| {
        let mut buf = Vec::new();
        r.read_to_end(&mut buf)?;
        Ok(buf)
    })
}

/// The next line's bytes, without its `\n`; `None` at the end.
pub fn read_line_bytes(r: &mut dyn BufRead) -> std::io::Result<Option<Vec<u8>>> {
    let mut buf = Vec::new();
    if r.read_until(b'\n', &mut buf)? == 0 {
        return Ok(None);
    }
    if buf.last() == Some(&b'\n') {
        buf.pop();
    }
    Ok(Some(buf))
}
