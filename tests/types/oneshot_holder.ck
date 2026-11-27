module oneshot_holder

# A value that holds a closure that must be called exactly once (one that
# uses a resource) must itself be used exactly once, and so must what is
# taken out of it: a constructor, a tuple, a list or a generic function
# doesn't let the closure be called twice, dropped or returned.

import std.files (File)
import std.files

fn by_some file -> r : file~File, r~Unit
    let k = \_ -> close file
    match Some k
        Some h ->
            h ()
            h ()
        None   -> ()

fn by_tuple file -> r : file~File, r~Unit
    let k = \_ -> close file
    let (h, _) = (k, 1)
    h ()
    h ()

fn by_list file -> r : file~File, r~Unit
    let k = \_ -> close file
    match [k]
        [h] ->
            h ()
            h ()
        _   -> ()

fn by_id file -> r : file~File, r~Unit
    let k = \_ -> close file
    let h = id k
    h ()
    h ()

fn holder_twice file -> r : file~File, r~Unit
    let k = \_ -> close file
    let p = Some k
    call p
    call p

fn discarded file -> r : file~File, r~Unit
    let k = \_ -> close file
    match Some k
        Some _ -> ()
        None   -> ()

fn returned file -> k : file~File, k~(Unit -> Unit)
    let k = \_ -> close file
    k

fn returned_some file -> r : file~File, r~Option (Unit -> Unit)
    let k = \_ -> close file
    Some k

fn own_twice x -> r : x~own a, r~(Option a, Option a)
    let p = Some x
    (p, p)

# Called once, wherever it went: no error.

fn once_some file -> r : file~File, r~Unit
    let k = \_ -> close file
    match Some k
        Some h -> h ()
        None   -> ()

fn once_tuple file -> r : file~File, r~Int
    let k = \_ -> close file
    let (h, n) = (k, 1)
    h ()
    n + n

fn once_id file -> r : file~File, r~Unit
    let k = \_ -> close file
    let h = id k
    h ()

fn own_once x -> r : x~own a, r~Option a
    Some x

fn call o -> r : o~own Option (Unit -> Unit), r~Unit
    match o
        Some h -> h ()
        None   -> ()

fn id x -> y : x~own a, y~a
    x

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
