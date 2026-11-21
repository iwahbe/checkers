# decimal.ck — exact decimal numbers.
module std.decimal

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

# ── Facts about the primitives above, trusted like the primitives ────────────

# A rendered number starts with `-` or a digit.
export lemma render_starts n : n~Decimal
    let b = utf8.encode (render n)
    ensures len b > 0 and (b[0] == '-' or (b[0] >= '0' and b[0] <= '9'))
    proof
        __builtin
