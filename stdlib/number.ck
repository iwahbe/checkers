# number.ck — whole numbers written in decimal, as bytes.
module std.number

import std.bytes

# Whether `c` is an ASCII digit, `0` to `9`.
export transparent fn is_digit c : c~U8
    '0' <= c and c <= '9'

# Whether every byte of `b` from `i` up to (not including) `j` is a digit:
# `True` if there are none (`j <= i`), `False` if `j` is past the end.
export transparent fn all_digits b i j -> r : b~Bytes, i~Nat, j~Nat, r~Bool
    decreasing j
    if j <= i
        True
    else if j <= len b
        all_digits b i (j - 1) and is_digit b[j - 1]
    else
        False

# The number the bytes of `b` from `i` up to `j` write in decimal. No bytes
# write `0`; a byte that isn't a digit counts as `0`, and so does a `j` past
# the end.
export transparent fn value_of b i j -> n : b~Bytes, i~Nat, j~Nat, n~Nat
    decreasing j
    if i < j and j <= len b
        let c = b[j - 1]
        value_of b i (j - 1) * 10 + (if is_digit c then c - '0' else 0)
    else
        0

# `n` in decimal: digits only (no sign, never an exponent), at least one, and
# no leading zero except in `0` itself.
export fn render_nat n -> r : n~Nat, r~Bytes, len r > 0, all_digits r 0 (len r),
                              r[0] == '0' implies len r == 1, value_of r 0 (len r) == n
    decreasing n
    if n < 10
        digit n
    else
        let a = render_nat (n / 10)
        let c = digit (n % 10)
        have prefix a c 0 (len a)
        have (a ++ c)[0] == a[0]
        a ++ c

# The number `b` writes in decimal, if `b` is one or more digits and nothing
# else. Leading zeros are allowed: `007` is `7`.
export fn parse_nat b -> r : b~Bytes, r~Option Nat,
                             r == (if len b > 0 and all_digits b 0 (len b) then Some (value_of b 0 (len b)) else None)
    if len b == 0 then None else parse_from b 0 0 0

# `parse_nat` reads back what `render_nat` writes.
export lemma parse_render_nat n : n~Nat
    ensures parse_nat (render_nat n) == Some n

# The digits of a number in `src` from `start` on: as many as there are (up to
# `stop`, the end or a byte that isn't a digit), at least one, and their value.
export record Digits src start : src~Bytes, start~Nat
    stop~Nat, start < stop, stop <= len src, stop == len src or not (is_digit src[stop])
    value~Nat, all_digits src start stop, value == value_of src start stop

# The number written in decimal in `src` from `start` on, and where its digits
# end; `None` if there is no digit at `start`. Leading zeros are allowed.
export fn read_nat src start -> r : src~Bytes, start~Nat, r~Option (Digits src start),
                                    (r == None) == (start >= len src or not (is_digit src[start]))
    if start < len src and is_digit src[start]
        Some (read_from src start (start + 1) (src[start] - '0'))
    else
        None

# `read_nat` reads back what `render_nat` writes, whatever is before it, and
# whatever is after it if that doesn't start with a digit.
export lemma read_render_nat n pre post : n~Nat, pre~Bytes, post~Bytes,
                                          len post == 0 or not (is_digit post[0])
    let src = pre ++ render_nat n ++ post
    let stop = len pre + len (render_nat n)
    ensures read_nat src (len pre) == Some (Digits stop n)
    proof
        let r = render_nat n
        have src[len pre] == r[0]
        have all_digits_shift pre r post (len r)
        have value_shift pre r post (len r)
        have stop == len src or src[stop] == post[0]
        let d = read_nat src (len pre)
        match d
            Some x ->
                if x.stop < stop
                    have middle_at pre r post (x.stop - len pre)
                    have all_digits_at r 0 (len r) (x.stop - len pre)
                else if x.stop > stop
                    have all_digits_at src (len pre) x.stop stop
                else
                    auto
            None   -> have all_digits_at r 0 (len r) 0

# `n` in decimal: `-` before the digits of a negative number, and otherwise as
# `render_nat` writes it.
export fn render_int n -> r : n~Int, r~Bytes, len r > 0,
                              r == (if n < 0 then b"-" ++ render_nat (-n) else render_nat n)
    if n < 0 then b"-" ++ render_nat (-n) else render_nat n

# The number `b` writes in decimal, if `b` is one or more digits, with or
# without a `-` before them, and nothing else. Leading zeros are allowed, and
# `-0` is `0`.
export fn parse_int b -> r : b~Bytes, r~Option Int,
                             r == (if len b > 0 and b[0] == '-'
                                   then (if len b > 1 and all_digits b 1 (len b) then Some (-value_of b 1 (len b)) else None)
                                   else (if len b > 0 and all_digits b 0 (len b) then Some (value_of b 0 (len b)) else None))
    if len b > 0 and b[0] == '-'
        if len b > 1
            match parse_from b 1 1 0
                Some n -> Some (-n)
                None   -> None
        else
            None
    else
        match parse_nat b
            Some n -> Some n
            None   -> None

# `parse_int` reads back what `render_int` writes.
export lemma parse_render_int n : n~Int
    ensures parse_int (render_int n) == Some n
    proof
        if n < 0
            let r = render_nat (-n)
            have all_digits_shift b"-" r b"" (len r)
            have value_shift b"-" r b"" (len r)
        else
            have parse_render_nat n

# Every byte of digits is a digit.
export lemma all_digits_at b i j k : b~Bytes, i~Nat, j~Nat, all_digits b i j, k~Nat, i <= k, k < j
    ensures k < len b and is_digit b[k]
    proof
        decreasing j
        if k + 1 < j
            have all_digits_at b i (j - 1) k
        else
            auto

# ── Proofs ───────────────────────────────────────────────────────────────────

# The digit `d`, as one byte.
fn digit d -> r : d~Nat, d < 10, r~Bytes, len r == 1, r[0] == '0' + d
    have bytes.slice_at b"0123456789" d (d + 1) 0
    bytes.slice b"0123456789" d (d + 1)

# The digits from `j` on, after `acc`, the value of those from `i` to `j`.
fn read_from src i j acc -> r : src~Bytes, i~Nat, j~Nat, i < j, j <= len src, acc~Nat,
                                all_digits src i j, acc == value_of src i j, r~Digits src i
    decreasing len src - j
    if j < len src and is_digit src[j]
        read_from src i (j + 1) (acc * 10 + (src[j] - '0'))
    else
        Digits j acc

# The digits of `b` from `j` on, after `acc`, the value of those from `i` to
# `j`.
fn parse_from b i j acc -> r : b~Bytes, i~Nat, j~Nat, i <= j, j <= len b, all_digits b i j,
                               acc~Nat, acc == value_of b i j,
                               r~Option Nat, r == (if all_digits b i (len b) then Some (value_of b i (len b)) else None)
    decreasing len b - j
    if j == len b
        Some acc
    else if is_digit b[j]
        parse_from b i (j + 1) (acc * 10 + (b[j] - '0'))
    else
        if all_digits b i (len b)
            have all_digits_at b i (len b) j
            None
        else
            None

# Bytes after `a` don't change what `a`'s bytes write.
lemma prefix a c i j : a~Bytes, c~Bytes, i~Nat, j~Nat, j <= len a
    ensures value_of (a ++ c) i j == value_of a i j and all_digits (a ++ c) i j == all_digits a i j
    proof
        decreasing j
        if i < j
            have prefix a c i (j - 1)
        else
            auto

# Byte `k` of `r` is where it was, between other bytes.
lemma middle_at pre r post k : pre~Bytes, r~Bytes, post~Bytes, k~Nat, k < len r
    ensures (pre ++ r ++ post)[len pre + k] == r[k]
    proof
        have bytes.slice_append pre r post
        have bytes.slice_at (pre ++ r ++ post) (len pre) (len pre + len r) k

# Bytes before and after `r` don't change what its bytes write.
lemma value_shift pre r post j : pre~Bytes, r~Bytes, post~Bytes, j~Nat, j <= len r
    ensures value_of (pre ++ r ++ post) (len pre) (len pre + j) == value_of r 0 j
    proof
        decreasing j
        if j > 0
            have value_shift pre r post (j - 1)
            have middle_at pre r post (j - 1)
        else
            auto

# Bytes before and after `r` don't change whether its bytes are digits.
lemma all_digits_shift pre r post j : pre~Bytes, r~Bytes, post~Bytes, j~Nat, j <= len r
    ensures all_digits (pre ++ r ++ post) (len pre) (len pre + j) == all_digits r 0 j
    proof
        decreasing j
        if j > 0
            have all_digits_shift pre r post (j - 1)
            have middle_at pre r post (j - 1)
        else
            auto

check render_nat 0 == b"0" and render_nat 7 == b"7" and render_nat 1234567890 == b"1234567890"
check render_nat 170141183460469231731687303715884105728 == b"170141183460469231731687303715884105728"
check parse_nat b"0" == Some 0 and parse_nat b"007" == Some 7 and parse_nat b"" == None
check parse_nat b"12a" == None and parse_nat b"-1" == None and parse_nat b" 1" == None
check read_nat b"x12y" 1 == Some (Digits 3 12) and read_nat b"x12" 1 == Some (Digits 3 12)
check read_nat b"x12" 0 == None and read_nat b"x12" 3 == None and read_nat b"x12" 9 == None
check render_int (-42) == b"-42" and render_int 0 == b"0"
check parse_int b"-42" == Some (-42) and parse_int b"-" == None and parse_int b"--1" == None
check parse_int b"42" == Some 42 and parse_int b"-0" == Some 0 and parse_int b"+1" == None
