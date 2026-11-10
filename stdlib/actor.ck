# actor.ck — actors on top of cowns (SPEC §13.5, D70).
#
# An actor is a cown holding its state. A message is a function from the
# old state to the new one; messages to one actor are handled one at a
# time, in the order they were sent. An invariant on the state is a
# refinement on `s`, checked like any cown's (§8.5).
module std.actor

import std.cown (Cown, Sched)

export record Actor s : s~Type
    state~Cown s

# A new actor with state `init`.
export fn new init sched -> a : init~own s, sched~Sched, a~Actor s
    Actor (cown.new init sched)

# Schedule message `f` on actor `a`.
export fn send a f sched -> u : a~Actor s, f~(s -> s), sched~Sched, u~()
    when x = a.state using sched
        f x
    ()
