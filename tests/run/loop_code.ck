module loop_code

# Loops over arrays: `walk` over bytes reads each element in place, takes
# each array's length from before the loop, branches on each comparison
# of the `and` (`i < len xs` making `i + 1` a plain add) and never drops
# the `Bool` it gives. `same`, the same loop at a type parameter, called
# at `Bytes`, is a copy for `U8`: the same code. `sum` reads the elements
# of an array of words.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)
import std.array
import std.hint (blackbox)

fn walk xs ys i -> r : xs~Bytes, ys~Bytes, i~Nat, i <= len xs, r~Nat
    decreasing len xs - i
    if i < len xs and i < len ys and xs[i] == ys[i] then walk xs ys (i + 1) else i

fn same xs ys i -> r : xs~Array a, ys~Array a, i~Nat, i <= len xs, r~Nat
    decreasing len xs - i
    if i < len xs and i < len ys and xs[i] == ys[i] then same xs ys (i + 1) else i

fn sum xs i acc -> r : xs~Array Int, i~Nat, i <= len xs, acc~Int, r~Int
    decreasing len xs - i
    if i < len xs then sum xs (i + 1) (acc + xs[i]) else acc

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (walk (blackbox b"abc") (blackbox b"abd") (blackbox 0))) sys.term
    terminal.print_line (debug (same (blackbox b"abc") (blackbox b"abd") (blackbox 0))) sys.term
    let xs = blackbox (array.from_list [1, 2, 3])
    terminal.print_line (debug (sum xs (blackbox 0) (blackbox 0))) sys.term
    Success
