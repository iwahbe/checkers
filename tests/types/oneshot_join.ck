module oneshot_join

# A list of functions holds one to call exactly once if any of its elements
# is one, whatever comes first: then the list is a resource. So does the
# value of an `if` if a branch is one.

import std.files (File)
import std.files

fn later_dropped file -> r : file~File, r~Unit
    let ks = [\_ -> (), \_ -> close file]
    ()

fn later_kept file -> r : file~File, r~Unit
    match [\_ -> (), \_ -> close file]
        [a, b] ->
            a ()
            b ()
        others -> drop_all others

fn drop_all ks -> r : ks~List (own (Unit -> Unit)), r~Unit
    match ks
        []        -> ()
        k :: rest ->
            k ()
            drop_all rest

fn branch_later file c -> r : file~File, c~Bool, r~Unit
    let j = if c then done file else \_ -> close file
    j ()

fn branch_later_twice file c -> r : file~File, c~Bool, r~Unit
    let j = if c then done file else \_ -> close file
    j ()
    j ()

fn done file -> k : file~File, k~(Unit -> Unit)
    close file
    \_ -> ()

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
