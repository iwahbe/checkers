module call_span

# Errors found after type checking point at the call they are about, not
# at the enclosing function's name.

import std.files (File)
import std.cown (Cown, Sched)

fn give v -> r : v~own a, r~own a
    v

fn ignore v -> r : v~a, r~Unit
    ()

# The result of `give` must be used once, but `ignore` may drop it.
fn passed v -> r : v~own a, r~Unit
    ignore (give v)

# Returned, but the result isn't declared `own`.
fn returned v -> r : v~own a, r~a
    give v

# A cown can't hold a resource: at the call that puts it in one.
fn in_cown f s -> c : f~File, s~Sched, c~Cown File
    cown.new f s
