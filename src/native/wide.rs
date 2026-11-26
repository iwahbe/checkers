//! Arithmetic on 128-bit integers in generated code (§14): numbers past a
//! word but within 128 bits, held in two-word objects, and small integers'
//! operations that overflow a word. Cranelift adds, subtracts and compares
//! 128-bit values on every machine, but multiplies them without reporting
//! overflow and doesn't divide them; those are built here from 64-bit
//! operations.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I128, I64};
use cranelift_codegen::ir::{BlockArg, InstBuilder, Value};
use cranelift_frontend::FunctionBuilder;

/// The 128-bit value of a 64-bit one, sign extended.
pub fn of_i64(b: &mut FunctionBuilder, x: Value) -> Value {
    b.ins().sextend(I128, x)
}

/// The 128-bit value of an unsigned 64-bit one.
fn of_u64(b: &mut FunctionBuilder, x: Value) -> Value {
    b.ins().uextend(I128, x)
}

/// Whether `x` (128 bits) is negative: an `I8`.
fn negative(b: &mut FunctionBuilder, x: Value) -> Value {
    let (_, hi) = b.ins().isplit(x);
    b.ins().icmp_imm_s(IntCC::SignedLessThan, hi, 0)
}

/// `|x|` as an unsigned 128-bit value (`|-2^127|` is `2^127`), and whether
/// `x` was negative.
fn magnitude(b: &mut FunctionBuilder, x: Value) -> (Value, Value) {
    let neg = negative(b, x);
    let minus = b.ins().ineg(x);
    (b.ins().select(neg, minus, x), neg)
}

/// `x` if `!neg`, else `-x` (wrapping).
fn signed(b: &mut FunctionBuilder, x: Value, neg: Value) -> Value {
    let minus = b.ins().ineg(x);
    b.ins().select(neg, minus, x)
}

/// `x * y` and whether it overflowed 128 bits (an `I8`).
pub fn mul(b: &mut FunctionBuilder, x: Value, y: Value) -> (Value, Value) {
    let (ux, nx) = magnitude(b, x);
    let (uy, ny) = magnitude(b, y);
    let (xl, xh) = b.ins().isplit(ux);
    let (yl, yh) = b.ins().isplit(uy);
    // `(xh·2^64 + xl)(yh·2^64 + yl)`: with both high words nonzero it is
    // at least 2^128; otherwise the one nonzero high word `h` times the
    // other's low word `m` is the cross term, at 2^64.
    let xh0 = b.ins().icmp_imm_s(IntCC::NotEqual, xh, 0);
    let yh0 = b.ins().icmp_imm_s(IntCC::NotEqual, yh, 0);
    let both = b.ins().band(xh0, yh0);
    let h = b.ins().bor(xh, yh);
    let m = b.ins().select(xh0, yl, xl);
    let cross = b.ins().imul(h, m);
    let cross_hi = b.ins().umulhi(h, m);
    let cross_over = b.ins().icmp_imm_s(IntCC::NotEqual, cross_hi, 0);
    let lo = b.ins().imul(xl, yl);
    let lo_hi = b.ins().umulhi(xl, yl);
    let (hi, carry) = b.ins().uadd_overflow(lo_hi, cross);
    // The magnitude must be below 2^127, or exactly 2^127 for a negative
    // product.
    let neg = b.ins().bxor(nx, ny);
    let top = b.ins().icmp_imm_s(IntCC::SignedLessThan, hi, 0);
    let is_min_hi = b.ins().icmp_imm_s(IntCC::Equal, hi, i64::MIN);
    let lo0 = b.ins().icmp_imm_s(IntCC::Equal, lo, 0);
    let min = b.ins().band(is_min_hi, lo0);
    let min = b.ins().band(min, neg);
    let not_min = b.ins().bxor_imm_s(min, 1);
    let too_big = b.ins().band(top, not_min);
    let o = b.ins().bor(both, cross_over);
    let o = b.ins().bor(o, carry);
    let o = b.ins().bor(o, too_big);
    let mag = b.ins().iconcat(lo, hi);
    (signed(b, mag, neg), o)
}

/// Euclidean `x / y` and `x % y` (the remainder never negative), `y` not
/// zero, and whether the quotient overflowed 128 bits (only `-2^127 / -1`).
pub fn div_rem(b: &mut FunctionBuilder, x: Value, y: Value) -> (Value, Value, Value) {
    let (ux, nx) = magnitude(b, x);
    let (uy, ny) = magnitude(b, y);
    let (q, r) = udiv_rem(b, ux, uy);
    // `x = -(q|y| + r)` with `r > 0` is `-(q + 1)|y| + (|y| - r)`.
    let (rl, rh) = b.ins().isplit(r);
    let rz = b.ins().bor(rl, rh);
    let r_nonzero = b.ins().icmp_imm_s(IntCC::NotEqual, rz, 0);
    let adjust = b.ins().band(nx, r_nonzero);
    let step = b.ins().uextend(I128, adjust);
    let q1 = b.ins().iadd(q, step);
    let up = b.ins().isub(uy, r);
    let rem = b.ins().select(adjust, up, r);
    let neg = b.ins().bxor(nx, ny);
    let quot = signed(b, q1, neg);
    // `q1` is at most 2^127: positive, it doesn't fit.
    let top = negative(b, q1);
    let pos = b.ins().bxor_imm_s(neg, 1);
    let over = b.ins().band(top, pos);
    (quot, rem, over)
}

/// Unsigned `u / v` and `u % v` of 128-bit values, `v` not zero.
fn udiv_rem(b: &mut FunctionBuilder, u: Value, v: Value) -> (Value, Value) {
    let (ul, uh) = b.ins().isplit(u);
    let (vl, vh) = b.ins().isplit(v);
    let narrow_v = b.create_block();
    let wide_v = b.create_block();
    let one = b.create_block();
    let two = b.create_block();
    let done = b.create_block();
    let q = b.append_block_param(done, I128);
    let r = b.append_block_param(done, I128);
    let vh0 = b.ins().icmp_imm_s(IntCC::Equal, vh, 0);
    b.ins().brif(vh0, narrow_v, &[], wide_v, &[]);

    // A divisor of one word: the dividend's high word, then the rest.
    b.switch_to_block(narrow_v);
    let uh0 = b.ins().icmp_imm_s(IntCC::Equal, uh, 0);
    b.ins().brif(uh0, one, &[], two, &[]);
    b.switch_to_block(one);
    let q1 = b.ins().udiv(ul, vl);
    let qv = b.ins().imul(q1, vl);
    let r1 = b.ins().isub(ul, qv);
    let (q1, r1) = (of_u64(b, q1), of_u64(b, r1));
    b.ins().jump(done, &[BlockArg::Value(q1), BlockArg::Value(r1)]);
    b.switch_to_block(two);
    let qh = b.ins().udiv(uh, vl);
    let qv = b.ins().imul(qh, vl);
    let rh = b.ins().isub(uh, qv);
    let (ql, r2) = div_two_words(b, rh, ul, vl);
    let q2 = b.ins().iconcat(ql, qh);
    let r2 = of_u64(b, r2);
    b.ins().jump(done, &[BlockArg::Value(q2), BlockArg::Value(r2)]);

    // A divisor of two words: the quotient has one, estimated from the
    // divisor's top 64 bits and corrected by at most one (Hacker's Delight,
    // 2nd ed., §9-5).
    b.switch_to_block(wide_v);
    let n = b.ins().clz(vh);
    let n128 = of_u64(b, n);
    let vn = b.ins().ishl(v, n128);
    let (_, v1) = b.ins().isplit(vn);
    let u1 = b.ins().ushr_imm_s(u, 1);
    let (u1l, u1h) = b.ins().isplit(u1);
    let (est, _) = div_two_words(b, u1h, u1l, v1);
    let est = of_u64(b, est);
    let est = b.ins().ishl(est, n128);
    let est = b.ins().ushr_imm_s(est, 63);
    let (q0, _) = b.ins().isplit(est);
    let nz = b.ins().icmp_imm_s(IntCC::NotEqual, q0, 0);
    let dec = b.ins().uextend(I64, nz);
    let q0 = b.ins().isub(q0, dec);
    let q0w = of_u64(b, q0);
    let qv = b.ins().imul(q0w, v);
    let rest = b.ins().isub(u, qv);
    let more = b.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, rest, v);
    let inc = b.ins().uextend(I128, more);
    let q3 = b.ins().iadd(q0w, inc);
    let less = b.ins().isub(rest, v);
    let r3 = b.ins().select(more, less, rest);
    b.ins().jump(done, &[BlockArg::Value(q3), BlockArg::Value(r3)]);

    b.switch_to_block(done);
    (q, r)
}

/// `(u1·2^64 + u0) / v` and its remainder, one word each, `u1 < v` (so the
/// quotient fits a word): long division by 32-bit digits with 64-bit
/// divisions (Hacker's Delight, 2nd ed., §9-4, `divlu`).
fn div_two_words(b: &mut FunctionBuilder, u1: Value, u0: Value, v: Value) -> (Value, Value) {
    const DIGIT: i64 = 1 << 32;
    let s = b.ins().clz(v);
    let vn = b.ins().ishl(v, s);
    let vn1 = b.ins().ushr_imm_s(vn, 32);
    let vn0 = b.ins().band_imm_s(vn, DIGIT - 1);
    // `u0 >> (64 - s)`, nothing when `s` is 0 (where the shift would be by
    // 64, which shifts by 0).
    let sixty_four = b.ins().iconst(I64, 64);
    let back = b.ins().isub(sixty_four, s);
    let spill = b.ins().ushr(u0, back);
    let neg_s = b.ins().ineg(s);
    let mask = b.ins().sshr_imm_s(neg_s, 63);
    let spill = b.ins().band(spill, mask);
    let un32 = b.ins().ishl(u1, s);
    let un32 = b.ins().bor(un32, spill);
    let un10 = b.ins().ishl(u0, s);
    let un1 = b.ins().ushr_imm_s(un10, 32);
    let un0 = b.ins().band_imm_s(un10, DIGIT - 1);

    let q1 = digit(b, un32, un1, vn1, vn0);
    let q1v = b.ins().imul(q1, vn);
    let un21 = b.ins().ishl_imm_s(un32, 32);
    let un21 = b.ins().iadd(un21, un1);
    let un21 = b.ins().isub(un21, q1v);
    let q0 = digit(b, un21, un0, vn1, vn0);
    let q0v = b.ins().imul(q0, vn);
    let r = b.ins().ishl_imm_s(un21, 32);
    let r = b.ins().iadd(r, un0);
    let r = b.ins().isub(r, q0v);
    let r = b.ins().ushr(r, s);
    let q = b.ins().ishl_imm_s(q1, 32);
    let q = b.ins().bor(q, q0);
    (q, r)
}

/// One 32-bit digit of `div_two_words`' quotient: `(un·2^32 + next) / vn`
/// estimated from `un / vn1` and corrected, at most twice.
fn digit(b: &mut FunctionBuilder, un: Value, next: Value, vn1: Value, vn0: Value) -> Value {
    const DIGIT: i64 = 1 << 32;
    let q = b.ins().udiv(un, vn1);
    let qv = b.ins().imul(q, vn1);
    let rhat = b.ins().isub(un, qv);
    // Too big: a digit, or more than the dividend's next digit allows.
    let too_big = |b: &mut FunctionBuilder, q: Value, rhat: Value| -> Value {
        let over = b.ins().icmp_imm_s(IntCC::UnsignedGreaterThanOrEqual, q, DIGIT);
        let lhs = b.ins().imul(q, vn0);
        let rhs = b.ins().ishl_imm_s(rhat, 32);
        let rhs = b.ins().iadd(rhs, next);
        let more = b.ins().icmp(IntCC::UnsignedGreaterThan, lhs, rhs);
        b.ins().bor(over, more)
    };
    let c1 = too_big(b, q, rhat);
    let d1 = b.ins().uextend(I64, c1);
    let q = b.ins().isub(q, d1);
    let zero = b.ins().iconst(I64, 0);
    let add = b.ins().select(c1, vn1, zero);
    let rhat = b.ins().iadd(rhat, add);
    // Again only if `rhat` is still below a digit (else `rhat·2^32`
    // overflows, and the estimate is right).
    let small = b.ins().icmp_imm_s(IntCC::UnsignedLessThan, rhat, DIGIT);
    let c2 = too_big(b, q, rhat);
    let c2 = b.ins().band(c2, small);
    let c2 = b.ins().band(c2, c1);
    let d2 = b.ins().uextend(I64, c2);
    b.ins().isub(q, d2)
}

/// Whether 128-bit `x` is a small integer (fits in 63 bits), and its word
/// `2x + 1` if so.
pub fn small_word(b: &mut FunctionBuilder, x: Value) -> (Value, Value) {
    let (lo, hi) = b.ins().isplit(x);
    let twice = b.ins().ishl_imm_s(lo, 1);
    let back = b.ins().sshr_imm_s(twice, 1);
    let fits63 = b.ins().icmp(IntCC::Equal, back, lo);
    let sign = b.ins().sshr_imm_s(lo, 63);
    let fits64 = b.ins().icmp(IntCC::Equal, sign, hi);
    let fits = b.ins().band(fits63, fits64);
    (fits, b.ins().bor_imm_s(twice, 1))
}

/// A 128-bit zero.
pub fn zero(b: &mut FunctionBuilder) -> Value {
    let z = b.ins().iconst(I64, 0);
    of_u64(b, z)
}
