module known_closures

# Functions known at compile time are static data too: a definition's or a
# constructor's function, given some of its arguments or none, in a list or
# a record, is laid out as the runtime's closure, with nothing built when the
# program runs.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

record Step
    name~String
    run~(Int -> Int)

fn add a b -> r : a~Int, b~Int, r~Int
    a + b

fn scale k x -> r : k~Int, x~Int, r~Int
    k * x

let ADD_TEN = add (5 + 5)

let STEPS = [Step "add" (add 1), Step "scale" (scale 3)]

let WRAP = Some

fn apply_all steps x -> r : steps~List Step, x~Int, r~(String, Int)
    match steps
        []        -> ("", x)
        s :: rest ->
            let (names, y) = apply_all rest (s.run x)
            (s.name ++ " " ++ names, y)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (ADD_TEN 1)) term
    terminal.print_line (debug (apply_all STEPS 4)) term
    terminal.print_line (debug (WRAP 2)) term
    Success
