module copy_params

# A function's copy for a known instance's dictionary takes neither the
# dictionary nor the type it is made for (§14): the results are those of
# the generic code, and nothing is left live at exit.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn lo x y -> r : Ord a, x~a, y~a, r~a
    if le x y then x else y

# Every parameter is put into the copy.
fn nothing -> r : Monoid a, r~a
    zero

fn plus_nothing x -> r : x~Int, r~Int
    x + nothing

# Partly applied: the copy is a function value.
fn pick f -> r : f~(Int -> Int), r~Int
    f 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    # Known only when the program runs (`n` is 0), or computed when compiling.
    let n = len args
    let (pear, apple) = if n == 0 then ("pear", "apple") else ("", "")
    terminal.print_line (debug (lo (n + 4) (n + 2))) sys.term
    terminal.print_line (lo pear apple) sys.term
    terminal.print_line (debug (lo [n + 2, 1] [1, 5])) sys.term
    terminal.print_line (debug (plus_nothing (n + 1))) sys.term
    terminal.print_line (debug (pick (lo 5))) sys.term
    Success
