module type_eq_layout

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

fn first_two xs -> r : Seq s, Seq.Elem s == U8, xs~s, r~Array (Seq.Elem s)
    match xs
        x :: y :: _ -> array.from_list [x, y]
        _           -> array.from_list []

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (first_two b"\x01\x02\x03")) term
    terminal.print_line (debug (first_two (array.to_list b"\x04\x05"))) term
    Success
