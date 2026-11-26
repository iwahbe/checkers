module oneshot

# A closure that uses a resource, made with a lambda or by partly applying
# a function to one, must be called exactly once (D171): called where it is
# made, bound with `let` and called once, or passed to a parameter declared
# `own`. Anywhere else (passed to a parameter that isn't `own`, returned,
# called twice or never) is E0401.

import std.files (File)
import std.files

fn run f -> r : f~own (Unit -> Unit), r~Unit
    f ()

fn run_twice f -> r : f~own (Unit -> Unit), r~Unit
    f ()
    f ()

fn many f -> r : f~(Unit -> Unit), r~Unit
    f ()

fn ok1 file -> r : file~File, r~Unit
    run (\_ -> close file)

fn ok2 file -> r : file~File, r~Unit
    let k = \_ -> close file
    k ()

fn ok3 file -> r : file~File, r~Unit
    (\_ -> close file) ()

fn ok4 file -> r : file~File, r~Unit
    let k = \_ -> close file
    run k

fn bad1 file -> r : file~File, r~Unit
    many (\_ -> close file)

fn bad2 file -> r : file~File, r~Unit
    let k = \_ -> close file
    k ()
    k ()

fn bad3 file -> r : file~File, r~Unit
    let k = \_ -> close file
    ()

fn bad4 file -> k : file~File, k~(Unit -> Unit)
    \_ -> close file

fn bad5 file -> r : file~File, r~Unit
    let k = \_ -> close file
    many k

fn close_with f n -> r : f~File, n~Int, r~Unit
    close f

fn partial_twice file -> r : file~File, r~Unit
    let k = close_with file
    k 1
    k 2

fn mk file -> k : file~File, k~(Int -> Unit)
    close_with file

fn once file -> r : file~File, r~Unit
    let k = close_with file
    k 1

fn direct file -> r : file~File, r~Unit
    close_with file 1

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
