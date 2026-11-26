module class_type_default

# A class's type whose default uses the class's parameter, at run time:
# values of it made and shown in generic code, at each instance's type.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

class Cell a
    type Item = List a
    fn item x -> i : x~a, i~Item

instance Cell Int
    fn item x
        [x, x + 1]

instance Cell String
    fn item x
        [x ++ "!"]

record Box b
    inner~b

instance Cell (Box b)
    fn item x
        [x, Box x.inner]

instance Cell Bool
    type Item = Int
    fn item x
        if x then 1 else 0

fn row x n -> r : Cell a, x~a, n~Nat, r~Array (Cell.Item a), len r == n
    array.repeat n (Cell.item x)

fn shown x -> s : Cell a, x~a, s~String
    debug (array.to_list (row x 2))

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (shown 7) t
    terminal.print_line (shown "hi") t
    terminal.print_line (shown (Box "b")) t
    terminal.print_line (shown True) t
    terminal.print_line (debug (Cell.item 3 ++ [9])) t
    Success
