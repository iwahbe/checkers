module known_arrays

# Arrays known at compile time are static data laid out as the runtime
# lays them out: packed by their element type, or a word per element.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)
import std.array

fn wide n -> r : n~Nat, r~Int
    n * 10000000 - 70000

fn small xs -> r : xs~List U16, r~Array U16
    array.from_list xs

fn signed xs -> r : xs~List I32, r~Array I32
    array.from_list xs

fn bytes xs -> r : xs~List U8, r~Array U8
    array.from_list xs

let SMALL = small [1, 2, 300]

let FLAGS = array.from_list [True, False, True]

let SIGNED = signed [-5, 6, -7]

let LARGE = array.from_list [wide 1, wide 9223372036854]

let WORDS = array.from_list ["one", "two"]

let BYTES = bytes [1, 255]

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (array.set SMALL 0 9) ++ " " ++ debug SMALL) term
    terminal.print_line (debug FLAGS) term
    terminal.print_line (debug SIGNED) term
    terminal.print_line (debug LARGE) term
    terminal.print_line (debug (WORDS ++ WORDS) ++ " " ++ debug WORDS) term
    terminal.print_line (debug BYTES) term
    Success
