# future.ck — values produced by `fork` and `join` (SPEC §8.6).
module future

export abstract enum Future +a : a~Type

# A future that is already filled.
export fn ready v -> f : v~own a, f~Future a
    __builtin
