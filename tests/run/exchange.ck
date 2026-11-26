module exchange

# A `when` holding two different cowns swaps their contents.

import std.system (System, ExitCode)
import std.cown (Cown, Sched)
import std.terminal (Term)

fn exchange x y sched -> r : x~Cown String, y~Cown String, x != y, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b, a)
    ()

fn show x y term sched -> r : x~Cown String, y~Cown String, x != y, term~Term, sched~Sched, r~Unit
    when a = x, b = y using sched
        terminal.print_line (a ++ " " ++ b) term
        (a, b)
    ()

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let c = cown.new "left" sched
    let d = cown.new "right" sched
    show c d term sched
    exchange c d sched
    show c d term sched
    Success
