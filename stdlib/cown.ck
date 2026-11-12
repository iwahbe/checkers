# cown.ck — concurrent owners and the scheduler capability (SPEC §8.5).
module std.cown

# The capability to schedule behaviours (`when`, `fork`, `join`); part of
# `System`.
export abstract enum Sched
# A concurrent owner of a value of type `a`. Behaviours (`when`) that name
# it run one at a time, in the order they were scheduled. A cown handle can
# be copied and shared.
export abstract enum Cown a : a~Type

# A new cown owning `v`.
export fn new v sched -> c : v~own a, sched~Sched, c~Cown a
    __builtin
