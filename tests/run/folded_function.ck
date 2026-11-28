module folded_function

# An operation computed when compiling whose value is a function is static
# data: `adder 1` and `adder 2` are each a lambda's closure laid out in the
# program, as the constants `by_hand` returns are; and so are
# `twice (plus 10)` and `twice (plus 20)`, a function given one argument, as
# the constants `by_hand_partial` returns are. Equal values are one object.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

fn adder n -> f : n~Int, f~(Int -> Int)
    \x -> x + n

fn pick b -> f : b~Bool, f~(Int -> Int)
    if b then adder 1 else adder 2

let ADD_ONE = adder 1

let ADD_TWO = adder 2

fn by_hand b -> f : b~Bool, f~(Int -> Int)
    if b then ADD_ONE else ADD_TWO

fn plus a b -> c : a~Int, b~Int, c~Int
    a + b

fn twice f -> g : f~(Int -> Int), g~(Int -> Int)
    f

fn pick_partial b -> f : b~Bool, f~(Int -> Int)
    if b then twice (plus 10) else twice (plus 20)

let PLUS_TEN = plus 10

let PLUS_TWENTY = plus 20

fn by_hand_partial b -> f : b~Bool, f~(Int -> Int)
    if b then PLUS_TEN else PLUS_TWENTY

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug ((pick (blackbox True)) 3)) sys.term
    terminal.print_line (debug ((pick_partial (blackbox False)) 3)) sys.term
    terminal.print_line (debug ((by_hand (blackbox True)) 3)) sys.term
    terminal.print_line (debug ((by_hand_partial (blackbox False)) 3)) sys.term
    Success
