# A variable named like an imported module hides it.
module shadowed_module

import std.system (System, ExitCode)
import std.proc

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { proc } = sys
    match proc.exec "true" [] proc
        Ok _  -> Success
        Err _ -> Failure 1
