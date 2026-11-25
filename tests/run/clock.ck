# Reading the clock: readings never go backwards, `since` is zero for a
# later reading taken from an earlier one, and `sleep` waits at least as
# long as it is asked.
module clock

import std.system (System, ExitCode)
import std.terminal (Term)
import std.time (Duration, now, since, add, sleep, millis)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, clock } = sys
    let a = now clock
    let b = now clock
    terminal.print_line (if a <= b then "readings go forwards" else "a reading went backwards") term
    terminal.print_line (if since a b == Duration 0 then "since saturates" else "since is negative") term
    terminal.print_line (if add a (since b a) == b then "add undoes since" else "add is wrong") term
    sleep clock (millis 20)
    let c = now clock
    terminal.print_line (if since c a >= millis 20 then "slept long enough" else "woke early") term
    terminal.print_line (if b < c then "time passed" else "time stood still") term
    Success
