# future.ck — values computed by behaviours: `fork`, `join` and `both`
# (SPEC §8.6).
module std.future

import std.cown (Sched)

# A value that a behaviour will produce. Waiting for it (`join`) holds no
# thread. A future handle can be copied and shared.
export abstract enum Future +a : a~Type

# A future that is already filled.
export fn ready v -> f : v~own a, f~Future a
    __builtin

# Runs `f` as a behaviour of its own and gives the future of its result.
# `f` may use resources from where it is made: it is called exactly once.
export fn fork sched f -> r : sched~Sched, f~own (Unit -> a), r~Future a
    __builtin

# Once `x` is filled, runs `f` on its value as a behaviour, and gives the
# future of the result. The behaviour is scheduled after the one that fills
# `x`, so it never waits. A future may be joined more than once; one holding
# a resource, exactly once.
export fn join x sched f -> r : x~own Future a, sched~Sched, f~own (v~own a -> b), r~Future b
    __builtin

# The future of both values, filled once `x` and `y` are: for joining
# several futures, `join (both x y) sched (\(a, b) -> …)`.
export fn both x y -> r : x~own Future a, y~own Future b, r~Future (a, b)
    __builtin
