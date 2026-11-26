module files_test

# File operations (§8.3, §8.4, §13.4).

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Fs, File, IoError)
import std.string (debug)

partial fn print_lines f term : f~File, term~Term
    let (line, f) = files.read_line f
    match line
        Ok None     -> report (files.close f) term
        Ok (Some l) ->
            terminal.print_line ("> " ++ debug l) term
            print_lines f term
        Err e       ->
            terminal.print_line ("error: " ++ files.describe e) term
            report (files.close f) term

fn report r term : r~Result Unit IoError, term~Term
    match r
        Ok _  -> terminal.print_line "ok" term
        Err e -> terminal.print_line ("error: " ++ files.describe e) term

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term } = sys
    match files.create "lines.tmp" fs
        Ok out ->
            let (_, out) = files.write_line "alpha" out
            let (_, out) = files.write_line "beta" out
            report (files.close out) term
        Err e  -> terminal.print_line (files.describe e) term
    match files.open "lines.tmp" fs
        Ok f  -> print_lines f term
        Err e -> terminal.print_line (files.describe e) term
    report (files.write "whole.tmp" b"bytes!" fs) term
    match files.read "whole.tmp" fs
        Ok b  -> terminal.print_line (debug b) term
        Err e -> terminal.print_line (files.describe e) term
    let data = files.within "data" fs
    match files.read "one.txt" data
        Ok b  -> terminal.print_line (debug b) term
        Err e -> terminal.print_line (files.describe e) term
    match files.read "../wc_stdin.in" data
        Ok b  -> terminal.print_line (debug b) term
        Err e -> terminal.print_line (files.describe e) term
    Success
