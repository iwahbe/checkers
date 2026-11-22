module inline_match

# A `match` on a small function's result, resolved at compile time (§14):
# an array taken apart by `[]` and `x :: rest`; `Option` and `Result`
# helpers matched on; arguments with effects, each computed once and in
# order; and an arm that would be in two places, left as it is. Each gives
# what the call gives.

import std.system (System, ExitCode)
import std.terminal
import std.terminal (Term)
import std.array
import std.string (debug)

fn walk xs acc -> n : xs~Array Int, acc~Int, n~Int
    match xs
        []        -> acc
        x :: rest -> walk rest (acc + x)

fn last xs -> r : xs~Array Int, r~Option Int
    match xs
        []        -> None
        [x]       -> Some x
        _ :: rest -> last rest

fn positive n -> r : n~Int, r~Option Int
    if n > 0 then Some n else None

fn digit n -> r : n~Int, r~Result Int String
    if n >= 0 and n < 10 then Ok n else Err ("not a digit: " ++ debug n)

fn by_option n -> s : n~Int, s~String
    match positive n
        None   -> "none"
        Some x -> "some " ++ debug x

fn by_result n -> s : n~Int, s~String
    match digit n
        Ok d  -> "digit " ++ debug d
        Err e -> e

# Prints `s`, then gives `n`.
fn say s n term -> r : s~String, n~Int, term~Term, r~Int
    terminal.print_line s term
    n

fn first a b -> r : a~Int, b~Int, r~Option Int
    if a > 0 then Some a else if b > 0 then Some b else None

fn ignore a -> r : a~Int, r~Option Int
    None

fn twice a -> r : a~Int, r~Option Int
    Some (a + a)

fn pick b x y -> r : b~Bool, x~Option Int, y~Option Int, r~Option Int
    if b then x else Some 1

fn by_pick b x -> s : b~Bool, x~Option Int, s~String
    match pick b x None
        None   -> "none"
        Some v -> "some " ++ debug v

export fn main args sys -> code
    let System { term } = sys
    let xs = array.from_list [1, 2, 3, 4]
    terminal.print_line (debug (walk xs 0)) term
    terminal.print_line (debug (walk (array.from_list []) 0)) term
    terminal.print_line (debug (last xs)) term
    terminal.print_line (by_option 5) term
    terminal.print_line (by_option -5) term
    terminal.print_line (by_result 7) term
    terminal.print_line (by_result 12) term
    let r = match first (say "a" 0 term) (say "b" 5 term)
        None   -> "none"
        Some x -> "first " ++ debug x
    terminal.print_line r term
    let s = match ignore (say "c" 1 term)
        None   -> "ignored"
        Some _ -> "kept"
    terminal.print_line s term
    let t = match twice (say "d" 4 term)
        None   -> "none"
        Some x -> "twice " ++ debug x
    terminal.print_line t term
    terminal.print_line (by_pick True (Some 3)) term
    terminal.print_line (by_pick True None) term
    terminal.print_line (by_pick False None) term
    Success
