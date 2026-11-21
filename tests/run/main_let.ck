module main_let

# An exported `main` declared with `let`, its value a function that a call
# computes (D181).

import std.system (System, ExitCode)
import std.list
import std.terminal
import std.string (debug)

fn greet args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line ("arguments: " ++ debug (list.length args)) sys.term
    Failure 3

fn entry n -> f : n~Nat, f~(List String -> System -> ExitCode)
    greet

export let main = entry 0
