module known_bounds

# A value known at compile time (a call of total functions on known values,
# a named constant) is that value: as a bound, it bounds as the same number
# written as a literal does, and in code it is that number. Each function is
# too big to be inlined.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.math

let LIMIT = 1000

fn by_call a b -> r : a~Nat, a < math.pow 2 32, b~Nat, b < math.pow 2 32, r~Int
    (a + b) * 2 + (a - b) + (b - a) * 3

fn by_literal a b -> r : a~Nat, a < 4294967296, b~Nat, b < 4294967296, r~Int
    (a + b) * 2 + (a - b) + (b - a) * 3

fn by_name a b -> r : a~Nat, a < LIMIT, b~Nat, b < LIMIT, r~Int
    (a + b) * (a - b) + a * b * 7 - b

fn by_number a b -> r : a~Nat, a < 1000, b~Nat, b < 1000, r~Int
    (a + b) * (a - b) + a * b * 7 - b

fn with_name a -> r : a~U8, r~Int
    (a + LIMIT) * (a + LIMIT) - LIMIT * a + LIMIT

fn with_number a -> r : a~U8, r~Int
    (a + 1000) * (a + 1000) - 1000 * a + 1000

fn line n sys : n~Int, sys~System
    terminal.print_line (debug n) sys.term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    line (by_call 4294967295 4294967295) sys
    line (by_literal 4294967295 0) sys
    line (by_name 999 999) sys
    line (by_number 0 999) sys
    line (with_name 255) sys
    line (with_number 0) sys
    Success
