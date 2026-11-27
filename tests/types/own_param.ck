module own_param

# `own` marks generic parameters that may receive a resource (#545).

import std.files (Fs, File)

fn keep x -> y : x~a, y~a
    x

fn keep_owned x -> y : x~own a, y~a
    x

fn twice_owned x -> p : x~own a, p~(a, a)
    (x, x)

fn generic_without_own f : f~File
    close (keep f)

fn generic_with_own f : f~File
    close (keep_owned f)

fn implied f : f~own File
    close f

fn pointless n -> m : n~own Nat, m~Nat
    n

# A function type whose parameter is a resource takes it exactly once.
fn call_once k f : k~(File -> Unit), f~File
    k f

fn closer f : f~File
    call_once close f

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
