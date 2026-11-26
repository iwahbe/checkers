# `main` is a behaviour like any other (D123): when it waits, its thread runs
# the others. Here, on one thread, `main` waits for `cat` to echo what a
# behaviour scheduled before the wait writes to it. If `main` held its
# thread while waiting, that behaviour would never run.
module main_waits

import std.future
import std.system (System, ExitCode)
import std.terminal
import std.files
import std.files (File)
import std.string (debug)
import std.proc (Streams, Spawned, Pipe, Discard)

# Write a line to the file and close it.
fn send w : w~File
    let (_, w) = files.write_line "ping" w
    let _ = files.close w
    ()

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p, sched } = sys
    match proc.spawn "cat" [] (Streams Pipe Pipe Discard) p
        Err e                              ->
            terminal.print_line ("spawn failed: " ++ files.describe e) term
            Failure 1
        Ok (Spawned child input output ()) ->
            let _ = future.fork sched $ \_ ->
                send input
            let (line, output) = files.read_line output
            let _ = files.close output
            let _ = proc.wait child
            match line
                Ok (Some l) ->
                    terminal.print_line ("main read: " ++ debug l) term
                    Success
                _           ->
                    terminal.print_line "main read nothing" term
                    Failure 1
