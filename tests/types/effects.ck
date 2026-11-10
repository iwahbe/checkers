module effects

import std.system (System, ExitCode)
import std.files (File)
import std.cown (Cown, Sched)
import std.future (Future)

fn bind_on_authority path fs -> r : path~String, fs~files.Fs, r~Nat
    contents <- files.read path fs
    0

fn try_not_tail x -> n : x~Option Nat, n~Nat
    let y =
        let z = try x
        z
    y

fn try_wrong x -> n : x~Option Nat, n~Nat
    let y = try x
    y

fn when_needs_cown n sched : n~Nat, sched~Sched
    when v = n using sched
        v
    ()

fn when_ok c sched : c~Cown Nat, sched~Sched
    when v = c using sched
        v + 1
    ()

fn fork_join_ok sched -> r : sched~Sched, r~Future Nat
    a <- fork using sched
        1
    b <- fork using sched
        2
    done <- join x = a, y = b using sched
        x + y
    done

fn not_sched x -> r : x~Nat, r~Future Nat
    f <- fork using x
        1
    f
