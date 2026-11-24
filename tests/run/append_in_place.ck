# `++` on a string or array no one else holds appends in place (§14): the
# results are those of a copy. A value still used after `++`, or one shared
# with another variable, keeps its elements.
module append_in_place

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

# `n` digits, the first appended to `"<"`.
fn grow n -> s : n~Nat, s~String
    decreasing n
    if n == 0 then "<" else grow (n - 1) ++ debug (n % 10)

fn grow_array n -> a : n~Nat, a~Array String
    decreasing n
    if n == 0 then array.from_list ["<"] else grow_array (n - 1) ++ array.from_list [debug n]

fn grow_bytes n -> a : n~Nat, a~Array Int
    decreasing n
    if n == 0 then array.from_list [0] else grow_bytes (n - 1) ++ array.from_list [n]

fn twice s -> r : s~String, r~String
    s ++ s

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let s = grow 20
    line s term
    # `s` is used again: the first `++` copies, the second may append.
    let t = s ++ "!"
    let u = s ++ "?"
    line (t ++ " " ++ u) term
    let shared = grow 3
    let other = shared
    let v = shared ++ "x"
    line (other ++ " " ++ v) term
    line (twice (grow 4)) term
    let a = grow_array 12
    line (debug (array.to_list a)) term
    let b = grow_bytes 9
    let c = array.drop 7 b ++ array.from_list [300]
    line (debug (array.to_list b) ++ " " ++ debug (array.to_list c)) term
    Success
