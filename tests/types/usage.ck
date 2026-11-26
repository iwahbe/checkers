module usage

import std.files (File)

fn twice f : f~File
    close f
    close f

fn never f -> n : f~File, n~Nat
    0

fn one_branch f b : f~File, b~Bool
    if b then close f else ()

fn threaded f : f~File
    let (_, f) = files.write_line "hi" f
    close f

fn ghostly src -> n : src~ghost Bytes, n~Nat
    len src

fn ghost_ok src n -> m : src~ghost Bytes, n~Nat, n <= len src, m~Nat
    n

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
