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
        let s = string.decimal (a * pow10 e)
        have string.all_digits_at s.bytes 0 (len s.bytes) 0
        s
    else
        let ds = string.decimal a
        if e < 0 and 0 - e <= len ds.bytes + 6
            let s = point a (0 - e)
            have string.all_digits_at s.bytes 0 (len s.bytes - (0 - e) - 1) 0
            s
        else
            have string.all_digits_at ds.bytes 0 (len ds.bytes) 0
            ds ++ "e" ++ display e []

# `10^k`.
fn pow10 k -> p : k~Nat, p~Nat
    decreasing k
    if k == 0 then 1 else 10 * pow10 (k - 1)

# `a × 10^(-f)` with `f` digits after the point: `point 1005 3` is `1.005`,
# `point 5 3` is `0.005`.
fn point a f -> s : a~Nat, f~Nat, s~String, len s.bytes >= f + 2, s.bytes[len s.bytes - f - 1] == '.',
                    string.all_digits s.bytes 0 (len s.bytes - f - 1),
                    s.bytes[0] == '0' implies len s.bytes - f - 1 == 1,
                    string.all_digits s.bytes (len s.bytes - f) (len s.bytes),
                    point_value s.bytes f == a
    decreasing f
    if f == 0
        let d = string.decimal a
        have string.decimal_prefix d.bytes b"." 0 (len d.bytes)
        d ++ "."
    else
        let q = point (a / 10) (f - 1)
        let c = string.digit (a % 10)
        let p = len q.bytes - f
        have string.decimal_prefix q.bytes c.bytes 0 p
        have string.decimal_prefix q.bytes c.bytes (p + 1) (len q.bytes)
        let m = string.decimal_value q.bytes 0 p
        have value_after_prefix q.bytes c.bytes m (p + 1) (len q.bytes)
        have point_value q.bytes (f - 1) == value_after m q.bytes (p + 1) (len q.bytes)
        have value_after m (q.bytes ++ c.bytes) (p + 1) (len q.bytes + 1)
            == value_after m q.bytes (p + 1) (len q.bytes) * 10 + a % 10
        have point_value (q.bytes ++ c.bytes) f == value_after m (q.bytes ++ c.bytes) (p + 1) (len q.bytes + 1)
        q ++ c

# The digits of `b`, which has a point before its last `f` bytes, as one
# number without the point.
fn point_value b f -> n : b~Bytes, f~Nat, len b >= f + 1, n~Int
    value_after (string.decimal_value b 0 (len b - f - 1)) b (len b - f) (len b)

# The number the bytes of `b` from `i` up to `j` write in decimal after the
# digits making `m`: `string.decimal_value` is this after none.
fn value_after m b i j -> n : m~Int, b~Bytes, i~Nat, j~Nat, n~Int
    decreasing j
    if i < j and j <= len b
        let c = b[j - 1]
        value_after m b i (j - 1) * 10 + (if char.is_digit c then c - '0' else 0)
    else
        m

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
                let ds = digits rest (c - '0') 0
                let (d, after) = fraction ds.rest ds.value neg
                have suffix_trans after ds.rest rest
                have suffix_size after rest
                Ok (d, after)
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
                let (eneg, after_sign) = sign rest
                let ds = digits after_sign 0 0
                if ds.count == 0
                    (number m e neg, xs)
                else
                    have suffix_trans ds.rest after_sign rest
                    (number m (if eneg then e - ds.value else e + ds.value) neg, ds.rest)
            else
                (number m e neg, xs)
        []        -> (number m e neg, xs)

# An optional `+` or `-`: whether it was `-`, and what follows.
fn sign xs -> r : Seq s, Token (Seq.Elem s) Int, xs~s, r~(Bool, s),
                  match r
                      (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if token x Int == '-'
                (True, rest)
            else if token x Int == '+'
                (False, rest)
            else
                (False, xs)
        []        -> (False, xs)

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
        else
            have array.uncons_slice (t ++ post)

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
            let t = (string.decimal v).bytes
            let b = t ++ post
            have string.decimal_prefix t post 0 (len t)
            have unsigned_bytes b (len t) neg
            have array.slice_append t post b""
            have fraction_other post v neg
            have exponent_end post v 0 neg
            have (magnitude a e).bytes == t
            have scaled ((if neg then 0 - a else a) * pow10 e) 0 == scaled (if neg then 0 - v else v) 0
            have scaled_pow (if neg then 0 - a else a) 0 e
        else
            let ds = (string.decimal a).bytes
            if e < 0 and 0 - e <= len ds + 6
                let f = 0 - e
                let t = (point a f).bytes
                let p = len t - f - 1
                let b = t ++ post
                have string.decimal_prefix t post 0 p
                have string.decimal_prefix t post (p + 1) (len t)
                have unsigned_bytes b p neg
                have value_after_prefix t post (string.decimal_value t 0 p) (p + 1) (len t)
                have fraction_point b p (len t) (string.decimal_value b 0 p) neg
                have array.slice_append t post b""
                have exponent_end post a (0 - f) neg
                have (magnitude a e).bytes == t
            else
                let rest = b"e" ++ (string.display e []).bytes ++ post
                let b = ds ++ rest
                have string.decimal_prefix ds rest 0 (len ds)
                have unsigned_bytes b (len ds) neg
                have array.slice_append ds rest b""
                have (magnitude a e).bytes ++ post == b
                have fraction_other rest a neg
                have exponent_written a e neg post

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

# `unsigned` on bytes starting with the digits of a number, which end at
# `p`: they make the number, and what follows them is read after it.
lemma unsigned_bytes b p neg : b~Bytes, p~Nat, neg~Bool, 0 < p, p <= len b, string.all_digits b 0 p,
                               b[0] == '0' implies p == 1, p == len b or not (char.is_digit b[p])
    ensures unsigned b neg == Ok (fraction (array.slice b p (len b)) (string.decimal_value b 0 p) neg)
    proof
        have array.uncons_slice b
        have string.all_digits_at b 0 p 0
        if b[0] == '0'
            auto
        else
            have digits_bytes b 0 0 1 0
            have parse.digits_end_at b 0 1 p
            have value_zero b 0 p

# `fraction` at a point followed by digits up to `k`.
lemma fraction_point b p k q neg : b~Bytes, p~Nat, k~Nat, q~Int, neg~Bool, p + 1 < k, k <= len b, b[p] == '.',
                                   string.all_digits b (p + 1) k, k == len b or not (char.is_digit b[k])
    ensures fraction (array.slice b p (len b)) q neg
        == exponent_part (array.slice b k (len b)) (value_after q b (p + 1) k) (0 - (k - p - 1)) neg
    proof
        have parse.uncons_from b p
        have digits_bytes b q (p + 1) (p + 1) 0
        have parse.digits_end_at b (p + 1) (p + 1) k

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
        if x < 0
            let r = (string.decimal (0 - x)).bytes
            have array.uncons_slice (b"-" ++ r ++ post)
            have array.slice_append b"-" (r ++ post) b""
            have digits_decimal (0 - x) post
        else
            let r = (string.decimal x).bytes
            have array.uncons_slice (r ++ post)
            have string.all_digits_at r 0 (len r) 0
            have digits_decimal x post

# `digits` reads back what `string.decimal` writes.
lemma digits_decimal v post : v~Nat, post~Bytes, len post == 0 or not (char.is_digit post[0])
    let r = (string.decimal v).bytes
    ensures digits (r ++ post) 0 0 == Digits v (len r) post
    proof
        let b = r ++ post
        have array.uncons_slice b
        have string.all_digits_at r 0 (len r) 0
        have string.decimal_prefix r post 0 (len r)
        have digits_bytes b 0 0 1 1
        have parse.digits_end_at b 0 1 (len r)
        have value_zero b 0 (len r)
        have array.slice_append r post b""

# `digits` on the bytes of `b` from `j` on, after digits making
# `value_after m b i j`.
lemma digits_bytes b m i j n : b~Bytes, m~Int, i~Nat, j~Nat, n~Nat, i <= j, j <= len b
    let k = parse.digits_end b j
    ensures digits (array.slice b j (len b)) (value_after m b i j) n
        == Digits (value_after m b i k) (n + (k - j)) (array.slice b k (len b))
    proof
        decreasing len b - j
        if j < len b
            have parse.uncons_from b j
            if char.is_digit b[j]
                have digits_bytes b m i (j + 1) (n + 1)
            else
                auto
        else
            auto

# After no digits, `value_after` is `string.decimal_value`.
lemma value_zero b i j : b~Bytes, i~Nat, j~Nat
    ensures value_after 0 b i j == string.decimal_value b i j
    proof
        decreasing j
        if i < j and j <= len b
            have value_zero b i (j - 1)
        else
            auto

# Bytes after `a` don't change what its bytes from `i` to `j` write.
lemma value_after_prefix a c m i j : a~Bytes, c~Bytes, m~Int, i~Nat, j~Nat, j <= len a
    ensures value_after m (a ++ c) i j == value_after m a i j
    proof
        decreasing j
        if i < j
            have value_after_prefix a c m i (j - 1)
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
