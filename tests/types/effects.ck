module effects

import std.system (System, ExitCode)
import std.files (File)
import std.cown (Cown, Sched)
import std.future (Future)

fn bind_on_authority path fs -> r : path~String, fs~files.Fs, r~Nat
    let (contents, fs) = files.read path fs
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

fn fork_join_ok sched -> r : sched~Sched, r~Nat
    let a = future.fork sched $ \_ ->
        1
    let b = future.fork sched $ \_ ->
        2
    let (x, y) = future.join (a, b)
    x + y

fn not_sched x -> r : x~Nat, r~Future Nat
    let f = future.fork x $ \_ ->
        1
    f
