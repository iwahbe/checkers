module stack_overflow

import std.system (System, ExitCode)

# Recursing deeper than the stack holds ends the program with a message and
# exit code 70. `/` after the call keeps the recursion from becoming a loop.

fn deep n -> r : n~Nat, r~Nat
    if n == 0 then 0 else deep (n - 1) / 2

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    if deep 100000000 == 0 then Success else Failure 1
