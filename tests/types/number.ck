# What `std.number`'s signatures and lemmas let a caller prove.
module number

import std.number (Digits)
import std.number

# Its result is digits, at least one, with no leading zero.
fn rendered n -> r : n~Nat, r~Bytes, len r > 0, number.is_digit r[0], r[0] != '0' or len r == 1
    let r = number.render_nat n
    have number.all_digits_at r 0 (len r) 0
    r

# Every byte of it is a digit.
lemma rendered_digit n k : n~Nat, k~Nat, k < len (number.render_nat n)
    ensures number.is_digit (number.render_nat n)[k]
    proof
        have number.all_digits_at (number.render_nat n) 0 (len (number.render_nat n)) k

# Reading it back gives the number, as a `Nat` and as an `Int`.
lemma round_trip n m : n~Nat, m~Int
    ensures number.parse_nat (number.render_nat n) == Some n and number.parse_int (number.render_int m) == Some m
    proof
        have number.parse_render_nat n
        have number.parse_render_int m

# And from the middle of other bytes, up to a byte that isn't a digit.
lemma read_back n : n~Nat
    let src = b"x=" ++ number.render_nat n ++ b";"
    ensures number.read_nat src 2 == Some (Digits (2 + len (number.render_nat n)) n)
    proof
        have number.read_render_nat n b"x=" b";"

# Bytes with a byte that isn't a digit are no `Nat`.
lemma not_digits b k : b~Bytes, k~Nat, k < len b, not (number.is_digit b[k])
    ensures number.parse_nat b == None
    proof
        if number.all_digits b 0 (len b)
            have number.all_digits_at b 0 (len b) k
        else
            auto

# What a literal writes is known.
lemma literal
    ensures number.parse_nat b"042" == Some 42 and number.parse_int b"-7" == Some (-7)

# A reader gets where the digits end: here, the end.
fn whole src -> r : src~Bytes, r~Option Nat
    match number.read_nat src 0
        Some d -> if d.stop == len src then Some d.value else None
        None   -> None

# E0450: leading zeros are read, not refused.
lemma leading_zero_refused
    ensures number.parse_nat b"07" == None

# E0450: a `+` is no sign.
lemma plus_sign
    ensures number.parse_int b"+7" == Some 7
