module class_type_arg

# A class's parameter passed explicitly is erased: only the instance it
# chooses runs.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class TryFrom s t
    fn try_from x t -> r : x~s, t~ghost Type, r~Option t

instance TryFrom String Int
    fn try_from x t
        if x == "" then None else Some 123

instance TryFrom String Bool
    fn try_from x t
        if x == "yes" then Some True else None

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (try_from "123" Int)) term
    terminal.print_line (debug (try_from "yes" Bool)) term
    Success
