module par_stress

# `par` inside a deep recursion: more parallel components than threads.
# The result is the sequential one.

import std.system (System, ExitCode)
import std.future (Future)
import std.terminal (Term)

fn fib n -> r : n~Nat, r~Nat
    decreasing n
    if n < 2
        n
    else
        let (a, b) = par (fib (n - 1), fib (n - 2))
        a + b

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term } = sys
    terminal.print_line ("fib 20 = " ++ format (fib 20)) term
    future.ready Success
