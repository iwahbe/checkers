# log.ck — concurrency with cowns and `when` (SPEC §8.5).
#
# Behaviours that share a cown run in the order they were scheduled
# (causal order), never at the same time, and can't deadlock.

module log

import system (System, ExitCode)
import terminal (Term)
import cown (Cown)

# The invariant lives in the type: every behaviour that touches the log must
# hand back a list of at most 100 entries.
type Log = entries~List String, len entries <= 100

fn append msg entries -> out : msg~String, entries~Log, out~Log
    if len entries < 100 then msg :: entries else entries

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { sched, term } = sys
    let log = cown.new [] sched
    let dropped = cown.new 0 sched
    when l = log using sched
        append "started" l
    when l = log, d = dropped using sched              # holds both cowns at once
        let full = len l == 100
        terminal.print_line ("log has " ++ format (len l) ++ " entries") term
        (append "checked" l, if full then d + 1 else d)
    Success
