module file_errors

# `read_line` tells the end of a file from a read that failed, keeping the
# file either way, and `close` reports what it couldn't write out.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (File, IoError)
import std.proc (Streams, Spawned, Pipe, Discard)
import std.string (debug)

fn closed what r term : what~String, r~Result Unit IoError, term~Term
    match r
        Ok _  -> terminal.print_line (what ++ ": closed") term
        Err e -> terminal.print_line (what ++ ": close failed: " ++ files.describe e) term

partial fn lines what f term : what~String, f~File, term~Term
    let (r, f) = files.read_line f
    match r
        Ok (Some l) ->
            terminal.print_line (what ++ ": " ++ debug l) term
            lines what f term
        Ok None     ->
            terminal.print_line (what ++ ": the end") term
            closed what (files.close f) term
        Err e       ->
            terminal.print_line (what ++ ": read failed: " ++ files.describe e) term
            closed what (files.close f) term

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term, proc = p } = sys
    let _ = files.write "errors.tmp" b"one\nbad \xff\nlast" fs
    match files.open "errors.tmp" fs
        Ok f  -> lines "file" f term
        Err e -> terminal.print_line (files.describe e) term
    # A directory opens, but reading it fails.
    match files.open "." fs
        Ok f  -> lines "directory" f term
        Err e -> terminal.print_line (files.describe e) term
    # What is written to a child that has ended goes nowhere: `close`, writing
    # it out, says so.
    match proc.spawn "true" [] (Streams Pipe Discard Discard) p
        Ok (Spawned child to () ()) ->
            let _ = proc.wait child
            let (_, to) = files.write_line "lost" to
            closed "pipe" (files.close to) term
        Err e                       -> terminal.print_line (files.describe e) term
    let (_, out) = files.write_line "through stdout" (terminal.stdout term)
    closed "stdout" (files.close out) term
    match files.create "errors.tmp" fs
        Ok f  ->
            let (_, f) = files.write_line "written" f
            closed "errors.tmp" (files.close f) term
        Err e -> terminal.print_line (files.describe e) term
    let _ = proc.exec "rm" ["errors.tmp"] p
    Success
