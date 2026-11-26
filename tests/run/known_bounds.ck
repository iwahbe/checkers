module known_bounds

# A value known at compile time (a call of total functions on known values,
# sealed or not, a named constant) is that value: as a bound, it bounds as
# the same number written as a literal does, and in code it is that number.
# Each function is too big to be inlined. `by_module`'s bound is computed by
# a function of this module.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.math
import std.array
import known.limits

let LIMIT = 1000

fn by_call a b -> r : a~Nat, a < math.pow 2 32, b~Nat, b < math.pow 2 32, r~Int
    (a + b) * 2 + (a - b) + (b - a) * 3

fn by_literal a b -> r : a~Nat, a < 4294967296, b~Nat, b < 4294967296, r~Int
    (a + b) * 2 + (a - b) + (b - a) * 3

fn by_name a b -> r : a~Nat, a < LIMIT, b~Nat, b < LIMIT, r~Int
    (a + b) * (a - b) + a * b * 7 - b

fn by_number a b -> r : a~Nat, a < 1000, b~Nat, b < 1000, r~Int
    (a + b) * (a - b) + a * b * 7 - b

fn by_std a b -> r : a~Nat, a < array.count 7 (array.repeat 256 7), b~Nat,
                     b < array.count 7 (array.repeat 256 7), r~Int
    (a + b) * (a - b) + a * b * 3 - b

fn by_own a b -> r : a~Nat, a < limits.power_of_two 8, b~Nat, b < limits.power_of_two 8, r~Int
    (a + b) * (a - b) + a * b * 3 - b

# A function of this module, proved on demand so that it can run.
fn own_size k -> r : k~Nat, r~Nat
    array.count 7 (array.repeat k 7)

fn by_module a b -> r : a~Nat, a < own_size 256, b~Nat, b < own_size 256, r~Int
    (a + b) * (a - b) + a * b * 3 - b

fn by_bytes a b -> r : a~Nat, a < 256, b~Nat, b < 256, r~Int
    (a + b) * (a - b) + a * b * 3 - b

# The prover sees a sealed function's postconditions only, not its value:
# callers establish the bounds by testing them.
fn call_std a b -> r : a~Nat, b~Nat, r~Int
    if a < array.count 7 (array.repeat 256 7) and b < array.count 7 (array.repeat 256 7)
        by_std a b
    else
        0

fn call_own a b -> r : a~Nat, b~Nat, r~Int
    if a < limits.power_of_two 8 and b < limits.power_of_two 8 then by_own a b else 0

fn call_module a b -> r : a~Nat, b~Nat, r~Int
    if a < own_size 256 and b < own_size 256 then by_module a b else 0

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
    line (call_std 255 0) sys
    line (call_own 0 255) sys
    line (call_module 255 1) sys
    line (by_bytes 255 255) sys
    line (with_name 255) sys
    line (with_number 0) sys
    Success
