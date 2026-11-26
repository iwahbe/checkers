module known_release

# A constant only code generation wants, past the work limit of a
# development build: compiled as a load of the value computed at run time
# here, and as its value in a release build. Either way the program prints
# the same.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)

fn spin n -> r : n~Nat, r~Int
    decreasing n
    if n == 0 then 0 else spin (n - 1)

let FAR = spin 20000000

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug FAR) sys.term
    Success
