//! The Checkers runtime (M8, SPEC §14).
//!
//! Native code represents every value as one 64-bit word (D73) and calls
//! this library for everything it doesn't do inline: allocation and freeing
//! (D74), big integers, builtins, `format`, behaviours and the scheduler,
//! and runtime errors with the interpreter's messages (D76). `num` and the
//! scheduler are also used by the interpreter.

pub mod apply;
pub mod behav;
pub mod builtins;
pub mod entry;
pub mod io;
pub mod num;
pub mod obj;
pub mod ops;
pub mod prog;
pub mod sched;
pub mod word;

pub use prog::{bug, fatal};

/// Every runtime function native code may call, by symbol, for the JIT.
pub fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut v: Vec<(&'static str, *const u8)> = vec![
        ("ck_alloc", word::ck_alloc as *const u8),
        ("ck_free", word::ck_free as *const u8),
        ("ck_dup", word::ck_dup as *const u8),
        ("ck_drop", word::ck_drop as *const u8),
        ("ck_add", ops::ck_add as *const u8),
        ("ck_sub", ops::ck_sub as *const u8),
        ("ck_natsub", ops::ck_natsub as *const u8),
        ("ck_mul", ops::ck_mul as *const u8),
        ("ck_div", ops::ck_div as *const u8),
        ("ck_rem", ops::ck_rem as *const u8),
        ("ck_neg", ops::ck_neg as *const u8),
        ("ck_cmp", ops::ck_cmp as *const u8),
        ("ck_eq", ops::ck_eq as *const u8),
        ("ck_ne", ops::ck_ne as *const u8),
        ("ck_concat", ops::ck_concat as *const u8),
        ("ck_len", ops::ck_len as *const u8),
        ("ck_index", ops::ck_index as *const u8),
        ("ck_format", ops::ck_format as *const u8),
        ("ck_big_lit", ops::ck_big_lit as *const u8),
        ("ck_fail", prog::ck_fail as *const u8),
        ("ck_error", prog::ck_error as *const u8),
        ("ck_nomatch", prog::ck_nomatch as *const u8),
        ("ck_caf", prog::ck_caf as *const u8),
        ("ck_apply", apply::ck_apply as *const u8),
        ("ck_when", behav::ck_when as *const u8),
        ("ck_fork", behav::ck_fork as *const u8),
        ("ck_join", behav::ck_join as *const u8),
        ("ck_par", behav::ck_par as *const u8),
        ("ck_aot_main", entry::ck_aot_main as *const u8),
    ];
    v.extend(builtins::addresses());
    v
}
