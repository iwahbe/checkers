module debug_by_type

# `debug` shows a value as its type says, not only as it is stored: a type
# stored as its one field shows its constructor, a string shows as text
# and bytes as bytes though both are bytes, in generic code too, and where
# the type comes from a dictionary, a type constructor parameter, an
# earlier field or a value the type is applied to.

import std.array
import std.bag
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

# A class's type, kept in its dictionary.
class Labelled a
    type Label
    fn label x -> l : x~a, l~Label

instance Labelled Int
    type Label = String
    fn label x
        "an int"

fn shown_label x -> s : Labelled a, x~a, s~String
    debug (label x)

# A type computed from an earlier field, or from a value the type is
# applied to.
record ByField
    is_text~Bool
    v~(if is_text then String else Int)

record ByParam b : b~Bool
    v~(if b then String else Int)

fn by_param -> r : r~ByParam True
    ByParam "p"

fn shown x -> s : x~a, s~String
    debug x

fn shown_in xs -> s : Functor f, xs~f String, s~String
    debug xs

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
    terminal.print_line (shown_label 3) t
    terminal.print_line (shown_in (Some "x")) t
    terminal.print_line (debug (ByField True "y", ByField False 2)) t
    terminal.print_line (debug [by_param]) t
    terminal.print_line (shown (bag.of ["a", "b", "a"])) t
    Success

check shown (Box (Meters 2)) == "Box (Meters 2)" and twice "a" == "[\"a\", \"a\"]"
