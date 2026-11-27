module oneshot_holder

# A closure that uses a resource is a resource: it must be called exactly
# once, and a value that holds one must itself be used exactly once, and so
# must what is taken out of it. A constructor, a tuple, a list or a generic
# function doesn't let the closure be called twice or dropped. A function
# may return one if its result is declared `own`, and its caller then uses
# the result exactly once.

import std.files (File, Fs)
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

fn caller_twice file -> r : file~File, r~Unit
    let k = returned file
    k ()
    k ()

fn opened_twice path fs -> r : path~String, fs~Fs, r~Unit
    let k = opened path fs
    k ()
    k ()

fn opened_dropped path fs -> r : path~String, fs~Fs, r~Unit
    let _ = opened path fs
    ()

fn opened_passed path fs -> r : path~String, fs~Fs, r~Unit
    many (opened path fs)

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

fn returned file -> k : file~File, k~own (Unit -> Unit)
    let k = \_ -> close file
    k

fn returned_some file -> r : file~File, r~own Option (Unit -> Unit)
    let k = \_ -> close file
    Some k

fn caller_once file -> r : file~File, r~Unit
    let k = returned file
    k ()

fn opened_once path fs -> r : path~String, fs~Fs, r~Unit
    let k = opened path fs
    k ()

# A closure over a file it opens itself: only the result's `own` tells the
# caller to call it exactly once.
fn opened path fs -> k : path~String, fs~Fs, k~own (Unit -> Unit)
    match files.open path fs
        Ok f  -> \_ -> close f
        Err _ -> \_ -> ()

fn many f -> r : f~(Unit -> Unit), r~Unit
    f ()

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
