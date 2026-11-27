module folded

# Known parts of code are computed when compiling, wherever they are: in
# `under`, `LIMIT * 2` is the number 2097152, as `under_number` writes it.
# A function called with a known argument is copied for it, and the copy
# computes with it: `scale 3 x` calls a copy of `scale` that is `by_hand`'s
# code. Each function is too big to be inlined, and is called with values
# given through `blackbox`, known only when the program runs.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.math
import std.hint (blackbox)

let LIMIT = math.pow 2 20

fn under x -> r : x~Int, r~Int
    if x < LIMIT * 2 then x * 3 + x * x - 7 else x * 5 - x * x + 11

fn under_number x -> r : x~Int, r~Int
    if x < 2097152 then x * 3 + x * x - 7 else x * 5 - x * x + 11

fn scale k x -> r : k~Int, x~Int, r~Int
    k * x + k * k * k + (x - k) * (k + 1) - k * 7

fn by_call x -> r : x~Int, r~Int
    scale 3 x

fn by_hand x -> r : x~Int, r~Int
    3 * x + 27 + (x - 3) * 4 - 21

fn line n sys : n~Int, sys~System
    terminal.print_line (debug n) sys.term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    line (under (blackbox 5)) sys
    line (under_number (blackbox 4000000)) sys
    line (by_call (blackbox 10)) sys
    line (by_hand (blackbox 10)) sys
    Success
