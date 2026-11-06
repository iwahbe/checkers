//! Applying a function value (eval/apply). Native code calls known
//! functions directly and closures of the right arity through their code
//! pointer; everything else (partial and over-application) comes here.
//!
//! Ownership: `apply` consumes the function and the arguments, as compiled
//! code does (D74). A closure's code receives the closure itself as its
//! environment, and consumes it.

use crate::prog::*;
use crate::word::*;

pub fn apply(f: W, args: Vec<W>) -> W {
    let mut f = f;
    let mut args = args;
    loop {
        if args.is_empty() {
            return f;
        }
        if f == ERASED {
            args.into_iter().for_each(drop_w);
            return ERASED;
        }
        if !is_ptr(f) {
            bug("applied a value that is not a function");
        }
        match kind(f) {
            K_CLO => {
                let arity = tag(f) as usize;
                if args.len() < arity {
                    return pap(f, &[], args);
                }
                let rest = args.split_off(arity);
                let code = slot(f, 0);
                let r = (prog().invoke)(code, f, args.as_ptr(), arity as u64);
                f = r;
                args = rest;
            }
            K_PAP => {
                let held: Vec<W> = (1..=nfields(f)).map(|i| dup(slot(f, i))).collect();
                let g = dup(slot(f, 0));
                drop_w(f);
                let mut all = held;
                all.append(&mut args);
                f = g;
                args = all;
            }
            _ => bug("applied a value that is not a function"),
        }
    }
}

/// `f` waiting for more arguments: holds `held ++ more` (owned).
fn pap(f: W, held: &[W], more: Vec<W>) -> W {
    let n = held.len() + more.len();
    let w = alloc_obj(info(K_PAP, n as u64, 0), HDR + 8 + 8 * n);
    set_slot(w, 0, f);
    for (i, a) in held.iter().chain(more.iter()).enumerate() {
        set_slot(w, 1 + i, *a);
    }
    w
}

/// From native code: `f a1 … an`, consuming `f` and the arguments.
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_apply(f: W, args: *const W, n: u64) -> W {
    let v = if n == 0 { Vec::new() } else { unsafe { std::slice::from_raw_parts(args, n as usize) }.to_vec() };
    apply(f, v)
}
