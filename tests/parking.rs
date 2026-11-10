//! Blocking operations free the thread (M16, D113, SPEC §13.8): checks that
//! need a program's input to arrive after it has printed something.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn ckc() -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_ckc"));
    c.current_dir(Path::new(env!("CARGO_MANIFEST_DIR"))).env("CHECKERS_NO_CACHE", "1");
    c
}

/// Kill `child` if it is still running after `limit`: a thread held by a
/// waiting behaviour shows up as a program that never finishes.
fn watchdog(pid: u32, limit: Duration) {
    std::thread::spawn(move || {
        std::thread::sleep(limit);
        let _ = Command::new("kill").arg("-9").arg(pid.to_string()).status();
    });
}

#[test]
fn a_reader_of_standard_input_holds_no_thread() {
    for threads in ["1", "2"] {
        let mut child = ckc()
            .args(["run", "--threads", threads, "tests/parking/stdin_reader.ck"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run ckc");
        watchdog(child.id(), Duration::from_secs(60));
        let start = Instant::now();
        let mut out = BufReader::new(child.stdout.take().unwrap());
        let mut first = String::new();
        out.read_line(&mut first).unwrap();
        assert_eq!(first, "ping\n", "threads {threads}: the reader held the thread ({:?})", start.elapsed());
        let mut input = child.stdin.take().unwrap();
        input.write_all(b"hello\n").unwrap();
        drop(input);
        let mut second = String::new();
        out.read_line(&mut second).unwrap();
        assert_eq!(second, "got hello\n", "threads {threads}");
        assert!(child.wait().unwrap().success(), "threads {threads}");
    }
}

#[test]
fn readers_of_pipes_hold_no_thread() {
    // More waiting readers than threads (tests/run/waits.ck): the writer they
    // wait for still runs.
    for threads in ["1", "2", "3"] {
        let child = ckc()
            .args(["run", "--threads", threads, "tests/run/waits.ck"])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run ckc");
        watchdog(child.id(), Duration::from_secs(60));
        let out = child.wait_with_output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "b\"line 1\\n\" 0\nb\"line 2\\n\" 0\nb\"line 3\\n\" 0\nb\"line 4\\n\" 0\n",
            "threads {threads}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}
