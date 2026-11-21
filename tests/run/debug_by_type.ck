module debug_by_type

# `debug` shows a value as its type says, not only as it is stored: a type
# stored as its one field shows its constructor, a string shows as text
# and bytes as bytes though both are bytes, in generic code too.

import std.array
import std.system (System, ExitCode)
import std.terminal
import std.string (Debug, debug)

record Meters
    m~Int

enum Box a : a~Type
    Box x : x~a

record Hidden a : a~Type
    value~a

instance Debug (Hidden a)
    fn debug h
        "Hidden (" ++ Debug.debug h.value ++ ")"

fn shown x -> s : x~a, s~String
    debug x

fn twice x -> s : x~a, s~String
    shown [x, x]

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (debug (Meters 3)) t
    terminal.print_line (shown (Box (Meters 5))) t
    terminal.print_line (twice (Some (Meters 7))) t
    terminal.print_line (shown (Meters 1, Box "x")) t
    terminal.print_line (shown (array.from_list [Meters 1, Meters 2])) t
    terminal.print_line (shown (Hidden (Box 4))) t
    terminal.print_line (shown ["text", "é"]) t
    terminal.print_line (shown (string.bytes "text")) t
    terminal.print_line (shown (array.from_list [1, 2])) t
    Success

check shown (Box (Meters 2)) == "Box (Meters 2)" and twice "a" == "[\"a\", \"a\"]"
