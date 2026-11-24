module par_join_stress

# A component of `par` joins a future not yet filled: it waits for it, on a
# thread of its own or not.

import std.system (System, ExitCode)
import std.terminal
import std.future
import std.string (debug)

fn slow n -> r : n~Nat, r~Nat
    decreasing n
    if n < 2 then n else slow (n - 1) + slow (n - 2)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let later = future.fork sys.sched (\_ -> slow 30)
    let (a, b) = par (future.join later, 1)
    terminal.print_line (debug (a + b)) sys.term
    Success
