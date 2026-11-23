module dict_copies

# Functions called with known instances' dictionaries run as copies
# specialized to them (§14): the results are those of the generic code.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

# A clause's dictionary, passed on to a recursive call.
fn smallest x xs -> r : Ord a, x~a, xs~List a, r~a
    match xs
        []        -> x
        y :: rest -> if le y x then smallest y rest else smallest x rest

# Values of the type parameter shown by their type inside the copy.
fn show_smallest x xs -> s : Ord a, x~a, xs~List a, s~String
    debug (smallest x xs)

# A dictionary built from another at each call: one copy for each depth,
# until the copies stop and the dictionary is passed.
fn nest n x -> r : Ord a, n~Nat, x~a, r~Bool
    decreasing n
    if n == 0 then le x x else nest (n - 1) [x]

# A class over type constructors.
fn twice g xs -> r : Functor f, g~(a -> a), xs~f a, r~f a
    fmap g (fmap g xs)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (smallest 5 [3, 9, 1, 4])) sys.term
    terminal.print_line (debug (smallest [2, 1] [[2, 0], [1, 5], [3]])) sys.term
    terminal.print_line (show_smallest "q" ["x", "c", "m"]) sys.term
    terminal.print_line (show_smallest (Some "b") [None, Some "a"]) sys.term
    terminal.print_line (debug (nest 12 7)) sys.term
    terminal.print_line (debug (twice (\x -> x * 3) [1, 2])) sys.term
    terminal.print_line (debug (twice (\x -> x ++ "!") (Some "hi"))) sys.term
    Success
