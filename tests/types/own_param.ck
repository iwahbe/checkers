module own_param

# `own` marks generic parameters that may receive a resource (D45).

import std.files (Fs, File)
import std.cown (Cown, Sched)

fn keep x -> y : x~a, y~a
    x

fn keep_owned x -> y : x~own a, y~a
    x

fn twice_owned x -> p : x~own a, p~(a, a)
    (x, x)

fn generic_without_own f : f~File
    files.close (keep f)

fn generic_with_own f : f~File
    files.close (keep_owned f)

fn implied f : f~own File
    files.close f

fn pointless n -> m : n~own Nat, m~Nat
    n

# A cown owns its contents; the handle is shared freely (D39).
fn into_cown f sched : f~File, sched~Sched
    let c = cown.new f sched
    when g = c using sched
        g
    when g = c using sched
        g
    ()

# A function type whose parameter is a resource takes it exactly once.
fn call_once k f : k~(File -> Unit), f~File
    k f

fn closer f : f~File
    call_once files.close f
