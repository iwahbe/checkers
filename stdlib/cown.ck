# cown.ck — concurrent owners and the scheduler capability (SPEC §8.5).
module std.cown

export abstract enum Sched
export abstract enum Cown a : a~Type

export fn new v sched -> c : v~own a, sched~Sched, c~Cown a
    __builtin
