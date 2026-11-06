//! Running a native program's `main` (§13.4).

use crate::apply::apply;
use crate::obj::*;
use crate::prog::*;
use crate::word::*;

/// The root capability (§13.4): a `System` record of capabilities.
fn system() -> W {
    let p = prog();
    let Some(c) = p.known.system else { return ERASED };
    let fields: Vec<W> = p
        .system_fields
        .iter()
        .map(|f| match f.as_str() {
            "term" => CAP_TERM,
            "fs" => CAP_FS,
            "env" => CAP_ENV,
            "proc" => CAP_PROC,
            "net" => CAP_NET,
            "clock" => CAP_CLOCK,
            "sched" => CAP_SCHED,
            _ => ERASED,
        })
        .collect();
    new_con(c, &fields)
}

/// The exit code `main`'s result stands for.
fn exit_code(r: W, owner: u32) -> i32 {
    let k = prog().known;
    let mut r = r;
    if let Some(Obj::Future(cell)) = obj(r) {
        let v = std::mem::replace(&mut *cell.v.lock().unwrap(), UNSET);
        if v == UNSET {
            error(owner, "`main`'s future was never filled");
        }
        drop_w(r);
        r = v;
    }
    let code = match con_of(r) {
        Some(c) if Some(c) == k.success => 0,
        Some(c) if Some(c) == k.failure => {
            let n = num_of(field(r, 0));
            match n.to_u32().filter(|n| (1..=255).contains(n)) {
                Some(n) => n as i32,
                None => error(owner, &format!("`Failure {n}`: an exit code must be between 1 and 255")),
            }
        }
        _ => error(owner, "`main` returned a value that is not an `ExitCode`"),
    };
    drop_w(r);
    code
}

/// Run `main` (a closure taking the arguments and the root capability) and
/// its behaviours; the exit code. Call on a thread with a large stack.
pub fn run_main(desc: &str, invoke: Invoke, main: W, owner: u32, args: &[String], threads: usize) -> i32 {
    install(desc, invoke);
    let track = std::env::var_os("CHECKERS_RC_CHECK").is_some();
    TRACK.store(track, std::sync::atomic::Ordering::Relaxed);
    crate::behav::start_pool(threads);
    let argv = list(args.iter().map(|a| new_str(a)).collect());
    let r = apply(dup(main), vec![argv, system()]);
    if threads > 1 {
        crate::behav::finish_pool();
    } else {
        crate::behav::run_fifo(owner);
    }
    let code = exit_code(r, owner);
    crate::io::flush();
    if track {
        // Constants keep their values for good.
        eprintln!("checkers runtime: {} objects live at exit", LIVE.load(std::sync::atomic::Ordering::Relaxed));
    }
    code
}

/// The number of threads: `CHECKERS_THREADS`, or the number of cores.
pub fn default_threads() -> usize {
    std::env::var("CHECKERS_THREADS")
        .ok()
        .and_then(|t| t.parse().ok())
        .filter(|t| *t >= 1)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// The entry of an executable written by `checkers build`: its generated
/// `main` calls this.
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_aot_main(
    argc: i32,
    argv: *const *const u8,
    desc: *const u8,
    desc_len: u64,
    invoke: Invoke,
    main: W,
    owner: u64,
) -> i32 {
    let args: Vec<String> = (1..argc.max(1) as usize)
        .map(|i| unsafe {
            let p = *argv.add(i);
            let s = std::ffi::CStr::from_ptr(p as *const std::ffi::c_char);
            s.to_string_lossy().into_owned()
        })
        .collect();
    let d = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(desc, desc_len as usize)) }.to_string();
    let main = main as usize;
    let threads = default_threads();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || run_main(&d, invoke, main as W, owner as u32, &args, threads))
        .expect("spawn the main thread")
        .join()
        .unwrap_or(70)
}
