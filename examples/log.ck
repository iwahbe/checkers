# log.ck — concurrency with cowns and `when` (SPEC §8.5).
#
# Two behaviours share the `log` cown. They run in the order they were
# scheduled (causal order), never at the same time, and can't deadlock.

module log

import system (System, ExitCode)
import terminal (Term)
import cown (Cown)

# The invariant lives in the type: every behaviour that touches the log must
# hand back a list of at most 100 entries.
type Log = entries~List String, len entries <= 100

fn append msg entries -> out : msg~String, entries~Log, out~Log
    if len entries < 100 then msg :: entries else entries

export fn main args sys -> code : args~List String, sys~own System, code~ExitCode
    let System { sched, term } = sys
    log <- cown.new [] sched
    screen <- cown.new term sched          # `term` moves into the cown
    when l = log using sched
        append "started" l
    when l = log, t = screen using sched
        _ <- terminal.print_line ("log has " ++ format (len l) ++ " entries") t
        (l, t)
    Success
