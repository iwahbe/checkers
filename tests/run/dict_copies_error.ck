module dict_copies_error

# A runtime error in a copy of a function specialized to a known
# instance's dictionary (§14) names that function. The subtraction rests
# on an `admit`, so it is checked (§13.3).

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

lemma long xs : xs~List a
    ensures len xs >= 3
    proof
        admit

fn drop_three xs -> n : Ord a, xs~List a, n~Nat
    match xs
        x :: _ ->
            have long xs
            if le x x then len xs - 3 else 0
        []     -> 0

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (debug (drop_three [1, 2])) sys.term
    Success
