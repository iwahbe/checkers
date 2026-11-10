# copy.ck — copy a file exactly, a block at a time. Shows resources (SPEC
# §8.4): an open `File` is linear, every operation threads it with `<-`, and
# forgetting to close one is a compile error.

module copy

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Fs, File, IoError)

# `partial` because it calls `copy_blocks`, which reads until end of file.
export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term } = sys
    match args
        [src, dst] ->
            match (files.open src fs, files.create dst fs)
                (Ok input, Ok output) ->
                    match copy_blocks src input dst output
                        Ok _          -> Success
                        Err (path, e) -> fail path e term
                (Ok input, Err e)     ->
                    files.close input                       # must close what was opened
                    fail dst e term
                (Err e, Ok output)    ->
                    files.close output
                    fail src e term
                (Err e, Err _)        -> fail src e term
        _          ->
            terminal.eprint_line "usage: copy SRC DST" term
            Failure 2

# How much to read at a time.
let BLOCK = 65536

# Both files are consumed on every path: each is read or written, and finally
# closed.
# An error comes with the path of the file it happened to.
partial fn copy_blocks src input dst output -> r : src~String, input~File, dst~String, output~File,
                                                   r~Result Unit (String, IoError)
    block <- files.read_some BLOCK input
    match block
        Ok b  ->
            if len b == 0
                files.close input
                files.close output
                Ok ()
            else
                written <- files.write_bytes b output
                match written
                    Ok _  -> copy_blocks src input dst output
                    Err e ->
                        files.close input
                        files.close output
                        Err (dst, e)
        Err e ->
            files.close input
            files.close output
            Err (src, e)

fn fail path e term -> code : path~String, e~IoError, term~Term, code~ExitCode
    terminal.eprint_line ("copy: " ++ path ++ ": " ++ files.describe e) term
    Failure 1
