# decimal.ck — exact decimal numbers.
module std.decimal

import std.parse (Byte, Parsable, byte, suffix, suffix_size, suffix_trans)
import std.string (Display, display)
import std.utf8

# An exact decimal number: an integer times a power of ten.
export abstract enum Decimal

# The number as JSON writes it: `-12.5`, `0.001`, `1e30` (an exponent
# only when the number is very large or very small).
export fn render d -> s : d~Decimal, s~String
    __builtin

# The integer as a decimal.
export fn of_int n -> d : n~Int, d~Decimal
    __builtin

# `m × 10^e`: `scaled 125 (-2)` is `1.25`.
export fn scaled m e -> d : m~Int, e~Int, d~Decimal
    __builtin

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

# ── Reading numbers ──────────────────────────────────────────────────────────

# Why no number could be read.
export enum DecimalError
    NotFound  # the bytes don't start with a number

# A number as JSON writes it (RFC 8259): `-12.5`, `0.001`, `1e30`. The
# longest such prefix is read, so `1.x` reads `1` and leaves `.x`, and `012`
# reads `0` and leaves `12`.
instance Parsable Decimal s
    type Error = DecimalError
    fn parse xs a
        match xs
            x :: rest ->
                if byte x == '-'
                    match unsigned rest True
                        Ok (d, after) ->
                            have suffix_size after rest
                            Ok (d, after)
                        Err e         -> Err e
                else
                    unsigned xs False
            []        -> Err NotFound

# A number without its sign, negated if `neg`.
fn unsigned xs neg -> r : Seq s, Byte (Seq.Elem s), xs~s, neg~Bool, r~Result (Decimal, s) DecimalError,
                          match r
                              Ok (_, rest) -> suffix rest xs and Seq.size rest < Seq.size xs
                              Err _        -> True
    match xs
        x :: rest ->
            let c = byte x
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
fn digits xs m n -> r : Seq s, Byte (Seq.Elem s), xs~s, m~Int, n~Nat, r~Digits s,
                        suffix r.rest xs, r.count >= n, r.count == n or Seq.size r.rest < Seq.size xs
    match xs
        x :: rest ->
            let c = byte x
            if c >= '0' and c <= '9'
                let ds = digits rest (m * 10 + (c - '0')) (n + 1)
                have suffix_size ds.rest rest
                ds
            else
                Digits m n xs
        []        -> Digits m n xs

# After the integer part `m`: an optional fraction, then an optional
# exponent. `1.` is the number `1` before a `.`.
fn fraction xs m neg -> r : Seq s, Byte (Seq.Elem s), xs~s, m~Int, neg~Bool, r~(Decimal, s),
                            match r
                                (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if byte x == '.'
                let ds = digits rest m 0
                if ds.count == 0
                    (number m 0 neg, xs)
                else
                    let (d, after) = exponent ds.rest ds.value (0 - ds.count) neg
                    have suffix_trans after ds.rest rest
                    (d, after)
            else
                exponent xs m 0 neg
        []        -> (number m 0 neg, xs)

# After the digits `m × 10^e`: an optional exponent. `1e` is the number `1`
# before an `e`.
fn exponent xs m e neg -> r : Seq s, Byte (Seq.Elem s), xs~s, m~Int, e~Int, neg~Bool, r~(Decimal, s),
                              match r
                                  (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if byte x == 'e' or byte x == 'E'
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
fn sign xs -> r : Seq s, Byte (Seq.Elem s), xs~s, r~(Bool, s),
                  match r
                      (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            if byte x == '-'
                (True, rest)
            else if byte x == '+'
                (False, rest)
            else
                (False, xs)
        []        -> (False, xs)

# `m × 10^e`, negated if `neg`.
fn number m e neg -> d : m~Int, e~Int, neg~Bool, d~Decimal
    scaled (if neg then 0 - m else m) e

# ── Facts about the primitives above, trusted like the primitives ────────────

# A rendered number starts with `-` or a digit.
export lemma render_starts n : n~Decimal
    let b = utf8.encode (render n)
    ensures len b > 0 and (b[0] == '-' or (b[0] >= '0' and b[0] <= '9'))
    proof
        __builtin
