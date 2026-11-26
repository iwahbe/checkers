module type_clause

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

record Packed s : Seq s, Seq.Elem s == U8
    bytes~s

fn first p -> r : p~Packed s, r~Option U8
    match p.bytes
        []     -> None
        x :: _ -> Some x

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (first (Packed [7, 8]))) term
    terminal.print_line (debug (first (Packed b"\x09\x0a"))) term
    terminal.print_line (debug (first (Packed b""))) term
    Success
