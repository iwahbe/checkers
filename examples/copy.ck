# copy.ck — copy a file line by line. Shows resources (SPEC §8.4): an open
# `File` is linear, every operation threads it with `<-`, and forgetting to
# close one is a compile error.

module copy

import system (System, ExitCode)
import terminal (Term)
import files (Fs, File, IoError)

# `partial` because it calls `copy_lines`, which reads until end of file.
export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term } = sys
    match args
        [src, dst] ->
            match (files.open src fs, files.create dst fs)
                (Ok input, Ok output) ->
                    copy_lines input output
                    Success
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

# Both files are consumed on every path: each is read/written and finally closed.
partial fn copy_lines input output : input~File, output~File
    line <- files.read_line input
    match line
        None      ->
            files.close input
            files.close output
        Some text ->
            _ <- files.write_line text output
            copy_lines input output

fn fail path e term -> code : path~String, e~IoError, term~Term, code~ExitCode
    terminal.eprint_line ("copy: " ++ path ++ ": " ++ files.describe e) term
    Failure 1
