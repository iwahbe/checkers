module string_seq

# Strings taken apart from the front give the same characters and rests
# by a `match` at `String`, by generic `Seq` code and by `Seq.uncons`:
# multi-byte characters, one character, the empty string, a long string.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug, from_utf8)

fn by_match s -> r : s~String, r~List (Char, String)
    match s
        []        -> []
        c :: rest -> (c, rest) :: by_match rest

fn by_seq xs -> r : Seq s, xs~s, r~List (Seq.Elem s, s)
    match xs
        []        -> []
        x :: rest -> (x, rest) :: by_seq rest

fn walk s n -> r : s~String, n~Nat, r~Nat
    match s
        []        -> n
        _ :: rest -> walk rest (n + 1)

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (by_match "h€l😀")) term
    terminal.print_line (debug (by_seq "h€l😀")) term
    terminal.print_line (debug (Seq.uncons "€x")) term
    terminal.print_line (debug (Seq.uncons "a")) term
    terminal.print_line (debug (Seq.uncons "")) term
    terminal.print_line (debug (by_match "")) term
    terminal.print_line (debug (by_seq "x")) term
    match from_utf8 (array.repeat 1000000 0x61)
        Some s -> terminal.print_line (debug (walk s 0)) term
        None   -> terminal.print_line "not UTF-8" term
    match from_utf8 (array.concat [array.repeat 300000 0x61, b"\xE2\x82\xAC"])
        Some s -> terminal.print_line (debug (walk s 0)) term
        None   -> terminal.print_line "not UTF-8" term
    Success
