module borrowed_params

# A parameter a function only reads and passes on unchanged is borrowed
# (§14): its caller keeps it alive over the call. Results are as with owned
# parameters, on numbers too big for a word and on strings, and nothing is
# left live at exit.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.list

# `n` is passed on unchanged: borrowed.
fn walk n k acc -> r : n~Int, k~Nat, acc~Int, r~Int
    decreasing k
    if k == 0 then acc else walk n (k - 1) (acc + n)

# `s` is only read; `rest` is stored.
fn keep s rest -> r : s~String, rest~List String, r~List String
    if len s > 3 then s :: rest else rest

# `s` is only read: borrowed; `rest` is stored.
fn note s rest -> r : s~String, rest~List String, r~List String
    if len s > 3 then "long" :: rest else rest

# The same value to a borrowed and an owned parameter of one call.
fn both s -> r : s~String, r~List String
    note s [s]

# Functions that borrow, kept in a list as values: called as closures.
fn long s -> r : s~String, r~Bool
    len s > 3

fn short s -> r : s~String, r~Bool
    len s < 3

fn tests fs s -> r : fs~List (String -> Bool), s~String, r~List Bool
    match fs
        []        -> []
        f :: rest -> f s :: tests rest s

fn add_to n m -> r : n~Int, m~Int, r~Int
    walk n 2 m

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let big = 9223372036854775807 * 4
    terminal.print_line (debug (walk big 3 0)) sys.term
    terminal.print_line (debug (walk 5 4 1)) sys.term
    terminal.print_line (debug (keep ("ab" ++ "cd") ["x"])) sys.term
    terminal.print_line (debug (both ("lo" ++ "ng"))) sys.term
    terminal.print_line (debug (tests [long, short] ("ab" ++ "cde"))) sys.term
    terminal.print_line (debug (list.map (add_to big) [1, 2])) sys.term
    Success
