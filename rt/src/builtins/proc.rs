//! Builtins of child processes (`std.proc`).

#[allow(unused_imports)]
use super::*;
use crate::fiber::blocking;
use crate::poll::PollFd;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.proc.exec", "ckb_proc_exec", ckb_proc_exec),
    ("std.proc.run", "ckb_proc_run", ckb_proc_run),
    ("std.proc.spawn", "ckb_proc_spawn", ckb_proc_spawn),
    ("std.proc.wait", "ckb_proc_wait", ckb_proc_wait),
];

/// An exit code: 128 + the signal, if a signal ended the child.
fn code_of(st: std::process::ExitStatus) -> usize {
    #[cfg(unix)]
    let signal = std::os::unix::process::ExitStatusExt::signal(&st);
    #[cfg(not(unix))]
    let signal: Option<i32> = None;
    match (st.code(), signal) {
        (Some(c), _) => c as usize,
        (None, Some(sig)) => 128 + sig as usize,
        (None, None) => 1,
    }
}

fn command(program: W, args: W) -> std::process::Command {
    let args: Vec<&str> = list_items(args).into_iter().map(s).collect();
    let mut c = std::process::Command::new(s(program));
    c.args(args);
    c
}

// Waiting for a child doesn't hold a behaviour's thread (D113).

builtin!(ckb_proc_exec, |a| {
    let mut c = command(a[0], a[1]);
    // Output written so far comes first.
    crate::io::flush();
    blocking(move || match c.status() {
        Ok(st) => ok(nat(code_of(st))),
        Err(e) => err(describe_io(&e)),
    })
});

builtin!(ckb_proc_run, |a| {
    let c = command(a[0], a[1]);
    let input = b(a[2]).to_vec();
    blocking(move || run_child(c, input))
});

fn run_child(mut c: std::process::Command, input: Vec<u8>) -> W {
    use std::process::Stdio;
    c.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = match c.spawn() {
        Ok(ch) => ch,
        Err(e) => return err(describe_io(&e)),
    };
    // The input is written on a thread of its own while the outputs are read.
    let mut pipe = child.stdin.take();
    let writer = std::thread::spawn(move || {
        if let Some(p) = pipe.as_mut() {
            let _ = p.write_all(&input);
        }
        drop(pipe);
    });
    let r = child.wait_with_output();
    let _ = writer.join();
    match r {
        Ok(o) => ok(output(code_of(o.status), &o.stdout, &o.stderr)),
        Err(e) => err(describe_io(&e)),
    }
}

builtin!(ckb_proc_spawn, |a| {
    use std::process::Stdio;
    let ss = a[2];
    let conns = [conn(field(ss, 0)), conn(field(ss, 1)), conn(field(ss, 2))];
    let stdio = |k: Conn| match k {
        Conn::Inherit => Stdio::inherit(),
        Conn::Pipe => Stdio::piped(),
        Conn::Discard => Stdio::null(),
    };
    let mut c = command(a[0], a[1]);
    c.stdin(stdio(conns[0])).stdout(stdio(conns[1])).stderr(stdio(conns[2]));
    // Output written so far comes before the child's.
    crate::io::flush();
    let mut child = match c.spawn() {
        Ok(ch) => ch,
        Err(e) => return err(describe_io(&e)),
    };
    // Our ends of the pipes wait in the poller, not on a thread (D113).
    let end_in = child.stdin.take().map(|p| new_file(FileState::Write(Box::new(std::io::BufWriter::new(PollFd::new(p.into()))))));
    let end_out = child.stdout.take().map(|p| new_file(FileState::Read(Box::new(std::io::BufReader::new(PollFd::new(p.into()))))));
    let end_err = child.stderr.take().map(|p| new_file(FileState::Read(Box::new(std::io::BufReader::new(PollFd::new(p.into()))))));
    let ch = new_obj(Obj::Child(Mutex::new(Some(child))));
    ok(spawned(ch, [end_in.unwrap_or(UNIT), end_out.unwrap_or(UNIT), end_err.unwrap_or(UNIT)]))
});

builtin!(ckb_proc_wait, |a| {
    let child = match obj(a[0]) {
        Some(Obj::Child(m)) => m.lock().unwrap_or_else(|e| e.into_inner()).take(),
        _ => bug("expected a child process"),
    };
    match child {
        Some(mut ch) => blocking(move || match ch.wait() {
            Ok(st) => ok(nat(code_of(st))),
            Err(e) => err(describe_io(&e)),
        }),
        None => err(io_err("this child was already waited for")),
    }
});
