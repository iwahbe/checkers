module instance_refined

# Instances' functions with signatures of their own run as without them:
# called directly at a known instance, through a dictionary in generic
# code, as a function value, and in a `check`.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Size a
    fn size x -> n : x~a, n~Int

instance Size Bool
    fn size b -> n : b~Bool, n~Nat, n <= 1
        if b then 1 else 0

instance Size (List a) : Size a
    fn size xs -> n : xs~List a, n~Int, n >= 0 or xs != []
        match xs
            []        -> 0
            x :: rest -> Size.size x + size rest

fn total xs -> n : Size a, xs~List a, n~Int
    match xs
        []        -> 0
        x :: rest -> size x + total rest

fn small b -> n : b~Bool, n~Int, n <= 1
    size b

check size [True, False, True] == 2 and small True == 1

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (debug (small True)) t
    terminal.print_line (debug (size [[True], [False, True]])) t
    terminal.print_line (debug (total [True, True, False])) t
    terminal.print_line (debug (fmap Size.size [True, False])) t
    Success
