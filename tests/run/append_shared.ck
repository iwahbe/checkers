# `++` on a string or bytes appends in place only to memory no one else
# holds (§14); a left side someone else holds, a slice, or a literal is
# copied, with room to grow, and keeps its bytes. Every result is the one a
# copy would give.
module append_shared

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

# `s` with `k` copies of `t` after it, appended one at a time.
fn by s t k -> r : s~String, t~String, k~Nat, r~String
    decreasing k
    if k == 0 then s else by (s ++ t) t (k - 1)

fn by_bytes s t k -> r : s~Bytes, t~Bytes, k~Nat, r~Bytes
    decreasing k
    if k == 0 then s else by_bytes (s ++ t) t (k - 1)

# A literal, its last use on the left of `++`.
fn tag k -> r : k~Nat, r~String
    let l = "k"
    l ++ debug k

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    # Unique with room: in place. Then shared: each append copies.
    let s = by "" "ab" 10
    let t = s ++ "x"
    let u = s ++ "é"
    line (s ++ " " ++ t ++ " " ++ u) term
    # Long right sides, and an empty one.
    let w16 = by "<" "0123456789abcdef" 3
    let w17 = by "<" "0123456789abcdefg" 3
    line (w16 ++ "" ++ " " ++ debug (len w16.bytes) ++ " " ++ debug (len w17.bytes)) term
    line w17 term
    # Many appends of three bytes: every room, then full, then grown.
    let g = by "" "abc" 50
    line (debug (len g.bytes) ++ " " ++ debug (g == by "abc" "abc" 49)) term
    # A slice on the right: its bytes are where it points.
    let h = b"hello world"
    let r = by_bytes b"<" (array.slice h 6 11) 4
    line (debug r ++ " " ++ debug h) term
    # A slice on the left, no one else holding the slice: its array's
    # bytes after it stay.
    let q = by_bytes b"" b"xyz" 5
    let p = array.take 3 q
    let p2 = p ++ b"!"
    line (debug q ++ " " ++ debug p2) term
    # A literal on the left stays as it is, and so does its copy's room
    # when the copy is appended to.
    line (tag 1 ++ " " ++ tag 2 ++ " " ++ tag 3) term
    # A shared start: the first append copies it, the rest append to the
    # copy, past its room; the start stays as it is.
    let start = by "" "ab" 3
    let keep = start
    let grown = by start "!" 12
    line (keep ++ " " ++ grown) term
    # The same object on both sides, through two variables.
    let a = by "" "ab" 3
    let a2 = a
    let aa = a ++ a2
    line (aa ++ " " ++ a2) term
    Success
