# decimal.ck — exact decimal numbers.
module std.decimal

import std.array
import std.char
import std.parse (Parsable, Token, suffix, suffix_size, suffix_trans, token)
import std.string (Display, display)
import std.utf8

# An exact decimal number: an integer times a power of ten.
export abstract enum Decimal

# The integer `m` of `d`'s form `m × 10^e` that has no zero as its last
# digit: `mantissa (scaled 1250 (-3))` is `125`. Zero's is `0`.
export fn mantissa d -> m : d~Decimal, m~Int
    __builtin

# The `e` of `d`'s form `m × 10^e` that has no zero as the last digit of
# `m`: `exponent (scaled 1250 (-3))` is `-2`. Zero's is `0`.
export fn exponent d -> e : d~Decimal, e~Int
    __builtin

# The integer as a decimal.
export fn of_int n -> d : n~Int, d~Decimal
    __builtin

# `m × 10^e`: `scaled 125 (-2)` is `1.25`.
export fn scaled m e -> d : m~Int, e~Int, d~Decimal
    __builtin

check mantissa (scaled 1250 (-3)) == 125 and exponent (scaled 1250 (-3)) == -2
check mantissa (scaled 0 7) == 0 and exponent (scaled 0 7) == 0 and exponent (scaled (-1) 30) == 30

# `d` with exactly `places` digits after the point (and no point for 0),
# rounded half away from zero, never with an exponent: `2.345` with 2 is
# `2.35`.
fn fixed d places -> s : d~Decimal, places~Nat, s~String
    __builtin

# A decimal's options.
export enum DecimalOption
    Plus              # a `+` before a number that isn't negative
    Places n : n~Nat  # rounded to `n` digits after the point, half away from zero

# As `render` writes it, or as the options say.
instance Display Decimal
    type Options = DecimalOption
    fn display d os
        let (plus, places) = decimal_options os False None
        let s = match places
            None   -> render d
            Some n -> fixed d n
        let b = utf8.encode s
        if plus and (len b == 0 or b[0] != '-') then "+" ++ s else s

# Whether to write `+`, and how many places, as the options say.
fn decimal_options os plus places -> r : os~List DecimalOption, plus~Bool, places~Option Nat,
                                         r~(Bool, Option Nat)
    match os
        []        -> (plus, places)
        o :: rest ->
            match o
                Plus     -> decimal_options rest True places
                Places n -> decimal_options rest plus (Some n)

check display (of_int (-3)) [Places 2] == "-3.00" and display (of_int 7) [Plus] == "+7"

# ── Writing numbers ──────────────────────────────────────────────────────────

# The number as JSON writes it: `-12.5`, `0.001`, `1e30`. Its digits are
# `mantissa d`'s, with as many zeros after them as `exponent d` says when
# that is from 0 to 21, a point among or before them when it is negative
# and puts at most 6 zeros between the point and them, and otherwise an
# exponent: `1e22`, `1e-8`, and `-1.5e-9` is written `-15e-10`.
export fn render d -> s : d~Decimal, s~String
    let m = mantissa d
    let body = magnitude (if m < 0 then 0 - m else m) (exponent d)
    if m < 0 then "-" ++ body else body

# `a × 10^e` as `render` writes it, without a sign.
fn magnitude a e -> s : a~Nat, e~Int, s~String, len s.bytes > 0, char.is_digit s.bytes[0]
    if e >= 0 and e <= 21
        display (a * pow10 e) []
    else
        let ds = display a []
        if e < 0 and 0 - e <= len ds.bytes + 6
            let p = pow10 (0 - e)
            display (a / p) [] ++ "." ++ places (a % p) (0 - e)
        else
            ds ++ "e" ++ display e []

# `10^k`.
fn pow10 k -> p : k~Nat, p~Nat, p >= 1
    decreasing k
    if k == 0 then 1 else 10 * pow10 (k - 1)

# The `f` digits of `r`, zeros first if it has fewer: `places 5 3` is `005`.
fn places r f -> s : r~Nat, f~Nat, r < pow10 f, s~String, len s.bytes == f
    decreasing f
    if f == 0
        ""
    else
        let p = pow10 (f - 1)
        digit (r / p) ++ places (r % p) (f - 1)

# The digit `d`, as a string of one byte.
fn digit d -> s : d~Nat, d < 10, s~String, len s.bytes == 1, s.bytes[0] == '0' + d
    if d < 5
        if d == 0 then "0" else if d == 1 then "1" else if d == 2 then "2" else if d == 3 then "3" else "4"
    else
        if d == 5 then "5" else if d == 6 then "6" else if d == 7 then "7" else if d == 8 then "8" else "9"

check places 5 3 == "005" and places 1234 4 == "1234" and places 0 2 == "00"
check render (scaled 125 (-1)) == "12.5" and render (scaled (-1) (-3)) == "-0.001" and render (scaled 1 30) == "1e30"
check render (scaled 1 21) == "1000000000000000000000" and render (scaled 1 (-7)) == "0.0000001" and render (scaled 1 (-8)) == "1e-8"
check render (scaled 0 5) == "0" and render (scaled (-15) (-10)) == "-15e-10"

# ── Reading numbers ──────────────────────────────────────────────────────────

# Why no number could be read.
export enum DecimalError
    NotFound  # the tokens don't start with a number

# A number as JSON writes it (RFC 8259), from characters or bytes:
# `-12.5`, `0.001`, `1e30`. The longest such prefix is read, so `1.x` reads `1` and leaves `.x`, and `012`
# reads `0` and leaves `12`.
instance Parsable Decimal Int
    type Error = DecimalError
    fn parse xs a t
        match xs
            x :: rest ->
                if token x Int == '-'
                    match unsigned rest True
                        Ok (d, after) ->
                            have suffix_size after rest
                            Ok (d, after)
                        Err e         -> Err e
                else
                    unsigned xs False
            []        -> Err NotFound

# A number without its sign, negated if `neg`.
fn unsigned xs neg -> r : Seq s, Token (Seq.Elem s) Int, xs~s, neg~Bool, r~Result (Decimal, s) DecimalError,
                          match r
                              Ok (_, rest) -> suffix rest xs and Seq.size rest < Seq.size xs
                              Err _        -> True
    match xs
        x :: rest ->
            let c = token x Int
            if c == '0'
                let (d, after) = fraction rest 0 neg
                have suffix_size after rest
                Ok (d, after)
            else if c >= '1' and c <= '9'
                match Parsable.parse xs Int Int
                    Ok (m, after) ->
                        let (d, rest2) = fraction after m neg
                        have suffix_trans rest2 after xs
                        have suffix_size rest2 after
                        Ok (d, rest2)
                    Err _         -> Err NotFound
            else
                Err NotFound
        []        -> Err NotFound

# The digits at the front of a sequence.
record Digits s
    value~Int  # what they make, after the digits before them
    count~Nat  # how many there were
    rest~s     # what follows them

# The digits at the front of `xs`, after `n` digits making `m`.
fn digits xs m n -> r : Seq s, Token (Seq.Elem s) Int, xs~s, m~Int, n~Nat, r~Digits s,
                        suffix r.rest xs, r.count >= n, r.count == n or Seq.size r.rest < Seq.size xs
    match xs
        x :: rest ->
            let c = token x Int
            if c >= '0' and c <= '9'
                let ds = digits rest (m * 10 + (c - '0')) (n + 1)
                have suffix_size ds.rest rest
                ds
            else
                Digits m n xs
        []        -> Digits m n xs

# After the integer part `m`: an optional fraction, then an optional
# exponent. `1.` is the number `1` before a `.`.
fn fraction xs m neg -> r : Seq s, Token (Seq.Elem s) Int, xs~s, m~Int, neg~Bool, r~(Decimal, s),
                            match r
                                (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if token x Int == '.'
                let ds = digits rest m 0
                if ds.count == 0
                    (number m 0 neg, xs)
                else
                    let (d, after) = exponent_part ds.rest ds.value (0 - ds.count) neg
                    have suffix_trans after ds.rest rest
                    (d, after)
            else
                exponent_part xs m 0 neg
        []        -> (number m 0 neg, xs)

# After the digits `m × 10^e`: an optional exponent. `1e` is the number `1`
# before an `e`.
fn exponent_part xs m e neg -> r : Seq s, Token (Seq.Elem s) Int, xs~s, m~Int, e~Int, neg~Bool, r~(Decimal, s),
                                   match r
                                       (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if token x Int == 'e' or token x Int == 'E'
                match signed rest
                    Some (k, after) ->
                        have suffix_trans after rest xs
                        (number m (e + k) neg, after)
                    None            -> (number m e neg, xs)
            else
                (number m e neg, xs)
        []        -> (number m e neg, xs)

# A whole number with an optional `+` or `-` before its digits, and what
# follows it; `None` if there are no digits.
fn signed xs -> r : Seq s, Token (Seq.Elem s) Int, xs~s, r~Option (Int, s),
                    match r
                        Some (_, rest) -> suffix rest xs
                        None           -> True
    match xs
        x :: rest ->
            let c = token x Int
            if char.is_digit c or c == '-'
                match Parsable.parse xs Int Int
                    Ok (k, after) -> Some (k, after)
                    Err _         -> None
            else if c == '+'
                match rest
                    y :: _ ->
                        if char.is_digit (token y Int)
                            match Parsable.parse rest Int Int
                                Ok (k, after) ->
                                    have suffix_trans after rest xs
                                    Some (k, after)
                                Err _         -> None
                        else
                            None
                    []     -> None
            else
                None
        []        -> None

# `m × 10^e`, negated if `neg`.
fn number m e neg -> d : m~Int, e~Int, neg~Bool, d~Decimal
    scaled (if neg then 0 - m else m) e

# ── What `render` writes reads back ──────────────────────────────────────────

# Reading what `render` writes gives the number back, and leaves what
# follows if it can't continue a number: anything but a digit, `.`, `e` or
# `E`.
export lemma parse_render n post : n~Decimal, post~Bytes,
                                   len post == 0
                                   or not (char.is_digit post[0] or post[0] == '.' or post[0] == 'e' or post[0] == 'E')
    ensures Parsable.parse (utf8.encode (render n) ++ post) Decimal Int == Ok (n, post)
    proof
        let m = mantissa n
        let a = if m < 0 then 0 - m else m
        let t = (magnitude a (exponent n)).bytes
        have scaled_parts n
        have unsigned_magnitude a (exponent n) (m < 0) post
        if m < 0
            let b = b"-" ++ t ++ post
            have array.uncons_slice b
            have array.slice_append b"-" (t ++ post) b""
            have utf8.encode (render n) ++ post == b
            have Parsable.parse b Decimal Int == unsigned (t ++ post) True
        else
            have array.uncons_slice (t ++ post)
            have utf8.encode (render n) ++ post == t ++ post
            have (t ++ post)[0] != '-'
            have Parsable.parse (t ++ post) Decimal Int == unsigned (t ++ post) False

# A rendered number starts with `-` or a digit.
export lemma render_starts n : n~Decimal
    let b = utf8.encode (render n)
    ensures len b > 0 and (b[0] == '-' or (b[0] >= '0' and b[0] <= '9'))
    proof
        let m = mantissa n
        let t = (magnitude (if m < 0 then 0 - m else m) (exponent n)).bytes
        have char.is_digit t[0]
        if m < 0
            have b == b"-" ++ t
        else
            have b == t

# `unsigned` reads back what `magnitude` writes.
lemma unsigned_magnitude a e neg post : a~Nat, e~Int, neg~Bool, post~Bytes,
                                        len post == 0
                                        or not (char.is_digit post[0] or post[0] == '.' or post[0] == 'e'
                                                or post[0] == 'E')
    ensures unsigned ((magnitude a e).bytes ++ post) neg == Ok (scaled (if neg then 0 - a else a) e, post)
    proof
        if e >= 0 and e <= 21
            let v = a * pow10 e
            have (magnitude a e).bytes == (display v []).bytes
            have integer_part v post neg
            have fraction_other post v neg
            have exponent_end post v 0 neg
            have scaled ((if neg then 0 - a else a) * pow10 e) 0 == scaled (if neg then 0 - v else v) 0
            have scaled_pow (if neg then 0 - a else a) 0 e
        else
            let ds = (display a []).bytes
            if e < 0 and 0 - e <= len ds + 6
                let f = 0 - e
                let p = pow10 f
                let q = a / p
                let r = a % p
                let rest = b"." ++ (places r f).bytes ++ post
                have (magnitude a e).bytes ++ post == (display q []).bytes ++ rest
                have integer_part q rest neg
                have fraction_point q r f neg post
                have exponent_end post (q * p + r) (0 - f) neg
                have q * p + r == a
                have unsigned ((magnitude a e).bytes ++ post) neg == Ok (number a e neg, post)
            else
                let rest = b"e" ++ (display e []).bytes ++ post
                have (magnitude a e).bytes ++ post == ds ++ rest
                have integer_part a rest neg
                have fraction_other rest a neg
                have exponent_written a e neg post
                have unsigned ((magnitude a e).bytes ++ post) neg == Ok (number a e neg, post)

# `scaled (m × 10^k) e` is `scaled m (e + k)`.
lemma scaled_pow m e k : m~Int, e~Int, k~Nat
    ensures scaled (m * pow10 k) e == scaled m (e + k)
    proof
        decreasing k
        if k > 0
            have scaled_ten (m * pow10 (k - 1)) e
            have scaled_pow m (e + 1) (k - 1)
        else
            auto

# `unsigned` reads the digits `display v []` writes, and then the rest.
lemma integer_part v rest neg : v~Nat, rest~Bytes, neg~Bool, len rest == 0 or not (char.is_digit rest[0])
    ensures unsigned ((display v []).bytes ++ rest) neg == Ok (fraction rest v neg)
    proof
        let d = (display v []).bytes
        have array.uncons_slice (d ++ rest)
        if d[0] == '0'
            have array.slice_append b"0" rest b""
        else
            have string.parse_display v rest

# `fraction` at a point followed by `f` places writing `r`.
lemma fraction_point q r f neg post : q~Int, r~Nat, f~Nat, 0 < f, r < pow10 f, neg~Bool, post~Bytes,
                                      len post == 0 or not (char.is_digit post[0])
    ensures fraction (b"." ++ (places r f).bytes ++ post) q neg
        == exponent_part post (q * pow10 f + r) (0 - f) neg
    proof
        let w = (places r f).bytes
        have array.uncons_slice (b"." ++ w ++ post)
        have array.slice_append b"." (w ++ post) b""
        have digits_places r f q 0 post

# `digits` reads back what `places` writes.
lemma digits_places r f m n post : r~Nat, f~Nat, r < pow10 f, m~Int, n~Nat, post~Bytes,
                                   len post == 0 or not (char.is_digit post[0])
    ensures digits ((places r f).bytes ++ post) m n == Digits (m * pow10 f + r) (n + f) post
    proof
        decreasing f
        if f > 0
            let p = pow10 (f - 1)
            let c = (digit (r / p)).bytes
            let w = (places (r % p) (f - 1)).bytes
            have (places r f).bytes ++ post == c ++ w ++ post
            have array.uncons_slice (c ++ w ++ post)
            have array.slice_append c (w ++ post) b""
            have (c ++ w ++ post)[0] == '0' + r / p
            have array.slice (c ++ w ++ post) 1 (len (c ++ w ++ post)) == w ++ post
            have digits (c ++ w ++ post) m n == digits (w ++ post) (m * 10 + r / p) (n + 1)
            have digits_places (r % p) (f - 1) (m * 10 + r / p) (n + 1) post
            have (m * 10 + r / p) * p + r % p == m * pow10 f + r
        else
            have (places r f).bytes ++ post == post
            have m * pow10 f + r == m
            if len post > 0
                have array.uncons_slice post
            else
                auto

# `fraction` at anything but a point.
lemma fraction_other xs q neg : xs~Bytes, q~Int, neg~Bool, len xs == 0 or xs[0] != '.'
    ensures fraction xs q neg == exponent_part xs q 0 neg
    proof
        if len xs > 0
            have array.uncons_slice xs
        else
            auto

# `exponent_part` at anything but `e` or `E`.
lemma exponent_end xs m e neg : xs~Bytes, m~Int, e~Int, neg~Bool, len xs == 0 or (xs[0] != 'e' and xs[0] != 'E')
    ensures exponent_part xs m e neg == (number m e neg, xs)
    proof
        if len xs > 0
            have array.uncons_slice xs
        else
            auto

# `exponent_part` reads back an exponent as `render` writes it.
lemma exponent_written m x neg post : m~Int, x~Int, neg~Bool, post~Bytes, len post == 0 or not (char.is_digit post[0])
    ensures exponent_part (b"e" ++ (string.display x []).bytes ++ post) m 0 neg == (number m x neg, post)
    proof
        let w = (string.display x []).bytes
        have array.uncons_slice (b"e" ++ w ++ post)
        have array.slice_append b"e" (w ++ post) b""
        have array.uncons_slice (w ++ post)
        have string.parse_display x post
        if x < 0
            have w[0] == '-'
        else
            auto

# ── Facts about the primitives above, trusted like the primitives ────────────

# A number is its mantissa times ten to its exponent.
export lemma scaled_parts d : d~Decimal
    ensures scaled (mantissa d) (exponent d) == d
    proof
        __builtin

# A zero more after the digits is one more in the exponent: `m0 × 10^e` is
# `m × 10^(e + 1)`.
export lemma scaled_ten m e : m~Int, e~Int
    ensures scaled (m * 10) e == scaled m (e + 1)
    proof
        __builtin
