module seq_patterns

# One function over lists, arrays, bytes and strings, through their `Seq`
# instances; long arrays and strings are taken apart in linear time.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

fn count xs -> n : Seq s, xs~s, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + count rest

fn last xs -> r : Seq s, xs~s, r~Option (Seq.Elem s)
    match xs
        []        -> None
        [x]       -> Some x
        _ :: rest -> last rest

fn sum b acc -> n : b~Bytes, acc~Nat, n~Nat
    match b
        []        -> acc
        x :: rest -> sum rest (acc + x)

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (count [1, 2, 3])) term
    terminal.print_line (debug (count (array.from_list [10, 20]))) term
    terminal.print_line (debug (count "h€llo")) term
    terminal.print_line (debug (last "h€llo!")) term
    terminal.print_line (debug (last b"xyz")) term
    terminal.print_line (debug (last (array.from_list [True, False]))) term
    terminal.print_line (debug (count (array.repeat 1000000 7))) term
    terminal.print_line (debug (sum (array.repeat 1000000 2) 0)) term
    Success
