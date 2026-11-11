# `proc.kill` ends a child that would otherwise run for a minute; the child
# must still be waited for, and its exit code says the signal ended it
# (128 + 9). Killing it again once it has been waited for does nothing.
module kill

import std.system (System, ExitCode)
import std.proc (Streams, Spawned, Discard)
import std.terminal
import std.files

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p } = sys
    match proc.spawn "sleep" ["60"] (Streams Discard Discard Discard) p
        Err e                       ->
            terminal.print_line ("spawn failed: " ++ files.describe e) term
            Failure 1
        Ok (Spawned child () () ()) ->
            let (child, k) = proc.killer child
            proc.kill k
            match proc.wait child
                Ok n  ->
                    proc.kill k
                    terminal.print_line ("exit " ++ format n) term
                    Success
                Err e ->
                    terminal.print_line ("wait failed: " ++ files.describe e) term
                    Failure 1
