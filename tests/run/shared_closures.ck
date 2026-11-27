module shared_closures

# A function bound once is one closure wherever it is kept as a value
# (§14). The objects live at exit are the values of the definitions
# without parameters: each list's cells and one closure. Each captures a
# value not known when compiling, so its closure is built when it runs.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal
import std.hint (blackbox)

fn walk f k acc -> r : f~(Int -> Int), k~Nat, acc~List (Int -> Int), r~List (Int -> Int)
    decreasing k
    if k == 0 then acc else walk f (k - 1) (f :: acc)

fn apply f x -> r : f~(Int -> Int), x~Int, r~Int
    f x

fn sum fs -> r : fs~List (Int -> Int), r~Int
    match fs
        []        -> 0
        f :: rest -> f 1 + sum rest

fn int_of n -> r : n~Nat, r~Int
    n

# Kept by a `let` and called.
fn by_let -> r : r~List (Int -> Int)
    let n = int_of (len (blackbox [1, 2]))
    let f = \x -> x + n
    if apply f 1 == 3 then [f, f, f, f] else []

# Kept by the copy of a function it is passed to.
fn by_copy -> r : r~List (Int -> Int)
    let n = int_of (len (blackbox [1, 2]))
    walk (\x -> x + n) 10 []

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (sum by_let + sum by_copy)) sys.term
    Success
