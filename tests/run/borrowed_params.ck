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

# `s` is only read and passed on: borrowed. `xs`'s cells are reused for
# the result: owned.
fn longer s xs -> r : s~String, xs~List String, r~List String
    match xs
        []        -> []
        x :: rest -> if len x > len s then x :: longer s rest else longer s rest

# The same value to a borrowed and an owned parameter of one call.
fn both s -> r : s~String, r~List String
    longer s [s ++ "!", s]

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
    # Known only when the program runs (`n` is 0), or computed when compiling.
    let n = len args
    let big = 9223372036854775807 * 4 + n
    terminal.print_line (debug (walk big (n + 3) n)) sys.term
    terminal.print_line (debug (walk (n + 5) (n + 4) (n + 1))) sys.term
    let (ab, lo) = if n == 0 then ("ab", "lo") else ("", "")
    terminal.print_line (debug (keep (ab ++ "cd") ["x"])) sys.term
    terminal.print_line (debug (both (lo ++ "ng"))) sys.term
    terminal.print_line (debug (tests [long, short] (ab ++ "cde"))) sys.term
    terminal.print_line (debug (list.map (add_to big) [1, 2])) sys.term
    Success
