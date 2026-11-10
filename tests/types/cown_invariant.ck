module cown_invariant

# Inside `when`, a cown's contents have its content type, refinements
# included (§8.5): the invariant is a fact there, and must hold again on
# the way out.

import std.system (System, ExitCode)
import std.cown (Cown, Sched)

type Small = n~Nat, n < 10

fn small_cown sched -> c : sched~Sched, c~Cown Small
    cown.new 0 sched

fn bump n -> m : n~Small, m~Small
    if n + 1 < 10 then n + 1 else 0

fn uses_invariant c sched : c~Cown Small, sched~Sched
    when n = c using sched
        bump n                                  # needs n < 10: the invariant
    ()

fn breaks_invariant c sched : c~Cown Small, sched~Sched
    when n = c using sched
        n + 1                                   # may reach 10
    ()

# The initial contents must satisfy it too.
fn bad_cown sched -> c : sched~Sched, c~Cown Small
    cown.new 12 sched
