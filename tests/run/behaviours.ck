module behaviours

# Behaviours run after `main` returns, in the order they were scheduled (D44).

import std.system (System, ExitCode)
import std.cown (Cown, Sched)
import std.future (Future)
import std.terminal (Term)

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let counter = cown.new 0 sched
    when n = counter using sched
        terminal.print_line ("first sees " ++ format n) term
        n + 1
    when n = counter using sched
        terminal.print_line ("second sees " ++ format n) term
        when m = counter using sched
            terminal.print_line ("nested sees " ++ format m) term
            m * 10
        n + 1
    terminal.print_line "main returns" term
    a <- fork using sched
        20
    b <- fork using sched
        22
    sum <- join x = a, y = b using sched
        x + y
    done <- join s = sum using sched
        terminal.print_line ("sum " ++ format s) term
        if s == 42 then Failure 42 else Success
    done
