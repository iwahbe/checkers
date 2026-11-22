module array_slices

# Slices share their array's storage: a slice of a slice, `set` on a slice,
# `==`, `++`, indexing and showing them behave as for a copy.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.bytes
import std.string (debug)

export fn main args sys -> code
    let System { term } = sys
    let xs = array.from_list [1, 2, 3, 4, 5]
    let mid = array.slice xs 1 4
    let inner = array.slice mid 1 3
    let changed = array.set mid 0 20
    terminal.print_line (debug (mid, inner, changed, xs)) term
    terminal.print_line (debug (mid == array.from_list [2, 3, 4], inner ++ mid)) term
    let b = b"hello, world"
    let w = bytes.slice b 7 12
    terminal.print_line (debug (w, w[0], len w, w == b"world")) term
    terminal.print_line (debug (array.slice xs 2 2, array.drop 3 xs, array.take 2 mid)) term
    Success
