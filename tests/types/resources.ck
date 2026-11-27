module resources

# Resources are linear by type (#533): no `own` needed on these binders.

import std.files (Fs, File, IoError)

fn never_closed path fs : path~String, fs~Fs
    match files.open path fs
        Ok f  -> ()
        Err _ -> ()

fn closed_on_one_path path fs b : path~String, fs~Fs, b~Bool
    match files.open path fs
        Ok f  -> if b then close f else ()
        Err _ -> ()

fn dropped_by_wildcard a b fs : a~String, b~String, fs~Fs
    match (files.open a fs, files.open b fs)
        (Ok _, Ok g) -> close g
        _            -> ()

fn dropped_by_let path fs : path~String, fs~Fs
    let _ = files.open path fs
    ()

fn closed_twice f : f~File
    close f
    close f

fn never_closed_after_try path fs -> r : path~String, fs~Fs, r~Result Unit IoError
    let f = try files.open path fs
    Ok ()

# Accepted: every file is consumed exactly once on every path.
fn fine a b fs : a~String, b~String, fs~Fs
    match (files.open a fs, files.open b fs)
        (Ok x, Ok y)   ->
            let (_, y) = files.write_line "hi" y
            close x
            close y
        (Ok x, Err _)  -> close x
        (Err _, Ok y)  -> close y
        (Err _, Err _) -> ()

fn wrapped f : f~File
    match Some f
        Some g -> close g
        None   -> ()

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
