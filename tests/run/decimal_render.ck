module decimal_render

# `render` on many numbers: each mantissa, normalized or not, at every
# exponent from -45 to 45 and at exponents past 64 bits.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.decimal (Decimal)

let MANTISSAS = [0, 1, -1, 7, -12, 10, -100, 25, 1005, 123456789, -987654321, 18446744073709551617,
                 -1000000000000000000000000000007, 12345678901234567890123]

let WIDE = [-18446744073709551616, -9223372036854775809, -9223372036854775808, 9223372036854775807, 9223372036854775808,
            18446744073709551616, -1000000000000000000000000000000, 1000000000000000000000000000000]

# `m` at `k` exponents from `e` up, one per line.
fn upto m e k term -> r : m~Int, e~Int, k~Nat, term~Term, r~Unit
    if k > 0
        terminal.print_line (decimal.render (decimal.scaled m e)) term
        upto m (e + 1) (k - 1) term
    else
        ()

fn each ms term -> r : ms~List Int, term~Term, r~Unit
    match ms
        []        -> ()
        m :: rest ->
            upto m (-45) 91 term
            at m WIDE term
            each rest term

fn at m es term -> r : m~Int, es~List Int, term~Term, r~Unit
    match es
        []        -> ()
        e :: rest ->
            terminal.print_line (decimal.render (decimal.scaled m e)) term
            at m rest term

export fn main args sys -> code
    let System { term } = sys
    each MANTISSAS term
    Success
