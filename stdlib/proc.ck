# proc.ck — running other programs (SPEC §8.1, D90, D97).
module std.proc

import std.system (Proc)
import std.files (IoError)

# Run `program` with `args`, sharing this program's standard input, output
# and error, and wait for it: its exit code (128 + the signal, if a signal
# ended it). A `program` without a `/` is looked up on `PATH`.
export fn exec program args p -> r : program~String, args~List String, p~Proc, r~Result Nat IoError
    __builtin
