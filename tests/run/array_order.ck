# Arrays ordered by `Ord (Array a)`: bytes from the arguments, so they are
# compared at run time; long arrays differing far from the start; arrays of
# one type stored in different layouts; sorting arrays of bytes and of
# numbers; and a generic function given the dictionary at run time.
module array_order

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array
import std.list
import std.string (debug)

fn show x term -> r : x~a, term~Term, r~Unit
    terminal.print_line (debug x) term

fn bytes_of args -> r : args~List String, r~List Bytes
    list.map (\s -> s.bytes) args

# Each pair of arguments in order, as `<`, `==` or `>`.
fn compare xs ys -> r : Ord a, xs~a, ys~a, r~String
    if xs < ys then "<" else if ys < xs then ">" else "=="

fn pairs bs term -> r : bs~List Bytes, term~Term, r~Unit
    match bs
        x :: y :: rest ->
            terminal.print_line (debug x ++ " " ++ compare x y ++ " " ++ debug y) term
            pairs rest term
        _              -> ()

# `n` sevens, stored a byte each.
fn sevens n -> r : n~Nat, r~Bytes, len r == n
    array.repeat n 7

# `xs` with its last element `x`: bytes used as an `Array U32` are widened
# when `x` needs more than a byte.
fn last_is xs x -> r : xs~Array U32, len xs > 0, x~U32, r~Array U32
    array.set xs (len xs - 1) x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let bs = bytes_of args
    pairs bs t
    show (list.sort bs) t
    show (array.sort (array.from_list bs)) t
    let long = sevens (100 + list.length args)
    let wide = last_is long 70000
    terminal.print_line (compare long wide) t
    terminal.print_line (compare wide long) t
    terminal.print_line (compare long (last_is wide 7)) t
    terminal.print_line (compare (last_is long 6) (last_is wide 7)) t
    let ns = [array.from_list [3, 1], array.from_list [-2, 5, 0], array.from_list [3], array.from_list []]
    show (list.sort ns) t
    terminal.print_line (compare (array.from_list ns) (array.from_list (list.sort ns))) t
    Success
