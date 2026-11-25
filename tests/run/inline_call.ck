module inline_call

# A small function's body in place of its call, wherever the call is (§14):
# as an argument, in tail position, generic at a known instance, inside a
# lambda, and nested; and passed as a value, so still a function too.
# Arguments with effects are each computed once and in order, and an
# argument the body doesn't use is still computed. Each gives what the call
# gives.

import std.system (System, ExitCode)
import std.terminal
import std.terminal (Term)
import std.string (debug)
import std.list

fn smaller x y -> r : Ord a, x~a, y~a, r~a
    if x <= y then x else y

fn by_tail a b -> r : a~Int, b~Int, r~Int
    smaller a b

fn by_arg a b -> r : a~Int, b~Int, r~Int
    smaller a b + 1

fn nested a b c -> r : a~Int, b~Int, c~Int, r~Int
    smaller (smaller a b) (by_arg b c)

fn twice x -> r : x~Int, r~Int
    x + x

fn first x y -> r : x~Int, y~Int, r~Int
    x

# Prints `s`, then gives `n`.
fn say s n term -> r : s~String, n~Int, term~Term, r~Int
    terminal.print_line s term
    n

fn is_none o -> r : o~Option Int, r~Bool
    match o
        None   -> True
        Some _ -> False

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (by_tail 3 4)) term
    terminal.print_line (debug (by_arg 5 2)) term
    terminal.print_line (debug (nested 9 7 3)) term
    terminal.print_line (smaller "pear" "apple") term
    terminal.print_line (debug (list.map (\n -> smaller n 2) [1, 2, 3])) term
    terminal.print_line (debug (twice (say "once" 4 term))) term
    terminal.print_line (debug (list.map twice [1, 2])) term
    terminal.print_line (debug (first (say "a" 1 term) (say "b" 2 term))) term
    terminal.print_line (debug (is_none None)) term
    terminal.print_line (debug (is_none (Some 1))) term
    Success
