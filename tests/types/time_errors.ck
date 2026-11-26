# The clock is read only with a `Clock`, durations are written with their
# unit, and an `Instant` comes only from `now`.
module time_errors

import std.system (System, Clock)
import std.terminal (Term)
import std.time (Instant, Duration, now, sleep)

fn without_clock t -> i : t~Term, i~Instant
    now t

fn bare_number c : c~Clock
    sleep c 5

fn made_up -> i : i~Instant
    Reading 5
