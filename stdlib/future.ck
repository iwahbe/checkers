# future.ck — values produced by `fork` and `join` (SPEC §8.6).
module std.future

# A value that `fork` or `join` will produce. Waiting for it (`join`)
# holds no thread. A future handle can be copied and shared.
export abstract enum Future +a : a~Type

# A future that is already filled.
export fn ready v -> f : v~own a, f~Future a
    __builtin
