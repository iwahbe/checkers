module ord_sort

# Benchmark (§14): insertion sort, generic over `Ord`, at `Int` and at
# `List Int` (whose instance is built from `Ord Int`, its context), and the
# same sort written for each type. `ord_sort generic` or `ord_sort mono`;
# both print the same.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format, debug)
import std.list

# `n` numbers, scrambled.
fn numbers n seed acc -> r : n~Nat, seed~Int, acc~List Int, r~List Int
    decreasing n
    if n == 0 then acc else numbers (n - 1) ((seed * 7919 + 13) % 10007) (seed :: acc)

# Each number as a list: its digits, from the last.
fn digit_lists xs -> r : xs~List Int, r~List (List Int)
    match xs
        []        -> []
        x :: rest -> [x % 10, x / 10 % 10, x / 100] :: digit_lists rest

# ── Generic ──

fn insert x xs -> r : Ord a, x~a, xs~List a, r~List a
    match xs
        []        -> [x]
        y :: rest -> if le x y then x :: xs else y :: insert x rest

fn isort xs -> r : Ord a, xs~List a, r~List a
    match xs
        []        -> []
        x :: rest -> insert x (isort rest)

# ── Written for each type ──

fn insert_int x xs -> r : x~Int, xs~List Int, r~List Int
    match xs
        []        -> [x]
        y :: rest -> if x <= y then x :: xs else y :: insert_int x rest

fn isort_int xs -> r : xs~List Int, r~List Int
    match xs
        []        -> []
        x :: rest -> insert_int x (isort_int rest)

fn le_list xs ys -> r : xs~List Int, ys~List Int, r~Bool
    match xs
        []      -> True
        x :: xr ->
            match ys
                []      -> False
                y :: yr -> x <= y and (not (y <= x) or le_list xr yr)

fn insert_list x xs -> r : x~List Int, xs~List (List Int), r~List (List Int)
    match xs
        []        -> [x]
        y :: rest -> if le_list x y then x :: xs else y :: insert_list x rest

fn isort_list xs -> r : xs~List (List Int), r~List (List Int)
    match xs
        []        -> []
        x :: rest -> insert_list x (isort_list rest)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let xs = numbers 4000 1 []
    let ls = digit_lists xs
    let (a, b) = match args
        ["mono"] -> (isort_int xs, isort_list ls)
        _        -> (isort xs, isort ls)
    terminal.print_line (debug (list.take 3 a) ++ " " ++ debug (list.take 2 b)) term
    Success
