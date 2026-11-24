# Strings and arrays built a piece at a time by `++` (§14): their memory
# grows ahead of them, and is written in place only when no one else holds
# it. An empty side gives the other; a string of one character is shared.
# Every result is the one a copy would give.
module append_room

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array
import std.string (debug, from_char)

fn line s term : s~String, term~Term
    terminal.print_line s term

# `k` letters after `s`, a piece at a time.
fn grow s k -> r : s~String, k~Nat, r~String
    decreasing k
    if k == 0 then s else grow (s ++ from_char ('a' + k % 26)) (k - 1)

fn grow_array a k -> r : a~Array String, k~Nat, r~Array String
    decreasing k
    if k == 0 then a else grow_array (a ++ array.from_list [debug k]) (k - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let s = grow "" 40
    line s term
    # `s` has room now; both appends see it as it is.
    let t = s ++ "!"
    let u = s ++ "?"
    line (t ++ " " ++ u ++ " " ++ s) term
    # An empty side: the result is the other, which stays as it is.
    let v = "" ++ s
    let w = v ++ "+"
    line (debug (v == s) ++ " " ++ w) term
    let x = s ++ ""
    line (debug (x ++ "+" == w)) term
    # Characters: the same one again, after one was appended to.
    let y = from_char 'q' ++ "rs"
    line (y ++ " " ++ from_char 'q' ++ " " ++ from_char c'é' ++ "!") term
    line (debug (grow "" 2000 == grow "" 2000) ++ " " ++ debug (len (grow "x" 5000).bytes)) term
    let a = grow_array (array.from_list ["<"]) 20
    let b = a ++ array.from_list [">"]
    line (debug (array.to_list a)) term
    line (debug (len b) ++ " " ++ debug (len a)) term
    Success
