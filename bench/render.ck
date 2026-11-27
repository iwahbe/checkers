module render

# Benchmark: `decimal.render` of a million numbers, mantissas of up to 10
# digits at exponents from -12 to 24, so every form is written (zeros after
# the digits, a point, an exponent). Compare before and after a change to
# `render` or to the code it compiles to.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format)
import std.decimal
import std.utf8
import std.hint (blackbox)

# The total length of what `render` writes for numbers `k` down to 1.
fn lengths k acc -> n : k~Nat, acc~Nat, n~Nat
    decreasing k
    if k == 0
        acc
    else
        let m = k * 9973 % 1000000007
        let d = decimal.scaled (if k % 2 == 0 then m else 0 - m) (k % 37 - 12)
        lengths (k - 1) (acc + len (utf8.encode (decimal.render d)))

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    # Given through `blackbox`, so the work is done when the program runs,
    # not when it is compiled.
    let n = lengths (blackbox 1000000) 0
    terminal.print_line format"bytes {n}" term
    Success
