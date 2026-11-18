# future.ck — values computed by behaviours: `fork` and `join` (SPEC §8.6).
module std.future

import std.cown (Sched)

# A value that a behaviour will produce. Waiting for it (`join`) holds no
# thread. A future handle can be copied and shared.
export abstract enum Future +a : a~Type

# A list of types: the values a `join` waits for, one per future.
export enum Types
    Last t      : t~Type
    Then t rest : t~Type, rest~Types

# The futures of the values `ts`: a `Future`, or a tuple of them.
export transparent fn futures ts -> t : ts~Types, t~Type
    match ts
        Last a      -> Future a
        Then a rest -> (Future a, futures rest)

# The values themselves: one, or a tuple.
export transparent fn values ts -> t : ts~Types, t~Type
    match ts
        Last a      -> a
        Then a rest -> (a, values rest)

# A future that is already filled.
export fn ready v -> f : v~own a, f~Future a
    __builtin

# Runs `f` as a behaviour of its own and gives the future of its result.
# `f` may use resources from where it is made: it is called exactly once.
export fn fork sched f -> r : sched~Sched, f~own (Unit -> a), r~Future a
    __builtin

# The value of a future, or the values of a tuple of futures, once they are
# filled: `let (x, y) = join (a, b)`. Until then the behaviour waits,
# keeping its cowns, and its thread runs others. A future may be joined
# more than once; one holding a resource, exactly once.
export fn join x -> v : x~own futures ts, v~values ts
    __builtin
