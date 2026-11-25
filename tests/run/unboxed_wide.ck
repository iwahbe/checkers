module unboxed_wide

# Results returned as their parts (§14), six to eight words wide: as many
# as some machines return in registers, and more than others do. Each is
# taken apart by its caller; where the machine returns fewer words, the
# result is a value.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

fn six n -> r : n~Int, r~(Int, Int, Int, Int, Int, Int)
    (n, n + 1, n + 2, n + 3, n + 4, n + 5)

fn seven n -> r : n~Int, r~(Int, Int, Int, Int, Int, Int, Int)
    (n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6)

fn eight n -> r : n~Int, r~(Int, Int, Int, Int, Int, Int, Int, Int)
    (n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7)

fn by_six n -> r : n~Int, r~Int
    let (a, b, c, d, e, f) = six n
    a + b * 10 + c * 100 + d * 1000 + e * 10000 + f * 100000

fn by_seven n -> r : n~Int, r~Int
    let (a, b, c, d, e, f, g) = seven n
    a + b + c + d + e + f + g * 1000

fn by_eight n -> r : n~Int, r~Int
    let (a, b, c, d, e, f, g, h) = eight n
    a + b + c + d + e + f + g + h * 1000

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (debug (by_six 1)) term
    line (debug (by_seven 1)) term
    line (debug (by_eight 1)) term
    Success
