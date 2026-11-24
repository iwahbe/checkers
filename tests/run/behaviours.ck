module behaviours

# Behaviours run after `main` returns, in the order they were scheduled (D44).

import std.system (System, ExitCode)
import std.cown (Cown, Sched)
import std.future (Future)
import std.terminal (Term)
import std.string (debug)

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let counter = cown.new 0 sched
    when n = counter using sched
        terminal.print_line ("first sees " ++ debug n) term
        n + 1
    when n = counter using sched
        terminal.print_line ("second sees " ++ debug n) term
        when m = counter using sched
            terminal.print_line ("nested sees " ++ debug m) term
            m * 10
        n + 1
    terminal.print_line "main returns" term
    let a = future.fork sched $ \_ ->
        20
    let b = future.fork sched $ \_ ->
        22
    let sum = future.fork sched $ \_ ->
        let (x, y) = future.join (a, b)
        x + y
    # `main` may give a future of its exit code (D31).
    future.fork sched $ \_ ->
        let s = future.join sum
        terminal.print_line ("sum " ++ debug s) term
        if s == 42 then Failure 42 else Success
