module known_baked

# Constants known at compile time are static data: a list, a string and a
# record computed by functions are laid out when the program is compiled,
# so nothing is allocated for them and none is live at exit.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

record Pair
    left~Int
    right~String

fn upto n -> r : n~Nat, r~List Nat
    decreasing n
    if n == 0 then [] else n :: upto (n - 1)

fn twice s -> r : s~String, r~String
    s ++ s

let NUMBERS = upto 5

let WORD = twice "ab"

let PAIR = Pair 7 (twice "cd")

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug NUMBERS) term
    terminal.print_line WORD term
    terminal.print_line (debug PAIR) term
    Success
