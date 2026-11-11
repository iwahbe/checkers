# `main` is a behaviour like any other (D123): when it waits, its thread runs
# the others. Here, on one thread, `main` waits for `cat` to echo what a
# behaviour scheduled before the wait writes to it. If `main` held its
# thread while waiting, that behaviour would never run.
module main_waits

import std.system (System, ExitCode)
import std.terminal
import std.files
import std.files (File)
import std.proc (Streams, Spawned, Pipe, Discard)
import std.cown

# Write a line to each file and close it.
partial fn send ws -> r : ws~List File, r~List File
    match ws
        []        -> []
        w :: rest ->
            _ <- files.write_line "ping" w
            files.close w
            send rest

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p, sched } = sys
    match proc.spawn "cat" [] (Streams Pipe Pipe Discard) p
        Err e                              ->
            terminal.print_line ("spawn failed: " ++ files.describe e) term
            Failure 1
        Ok (Spawned child input output ()) ->
            let writer = cown.new [input] sched
            when ws = writer using sched
                send ws
            line <- files.read_line output
            files.close output
            let _ = proc.wait child
            match line
                Some l ->
                    terminal.print_line ("main read: " ++ l) term
                    Success
                None   ->
                    terminal.print_line "main read nothing" term
                    Failure 1
