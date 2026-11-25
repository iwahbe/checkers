module class_qualified_before

# A class's function named by its class (`C.f`) above the class runs its
# instance.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal

fn five -> r : r~Int, r == 5
    Make.make 5

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u
        u

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug five) sys.term
    Success
