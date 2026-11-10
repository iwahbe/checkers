module specialize

# A compile-time function that recurses on runtime values becomes one
# runtime function per set of compile-time arguments (SPEC §8.9, D64).

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string

fn count c src i -> n : c~comptime Nat, src~Bytes, i~Nat, i <= len src, n~Nat
    decreasing len src - i
    if i == len src
        0
    else if src[i] == c
        1 + count c src (i + 1)
    else
        count c src (i + 1)

# Two calls with the same byte share one function; another byte gets its own.
fn newlines src -> n : src~Bytes, n~Nat
    count 10 src 0

fn lines_and_spaces src -> n : src~Bytes, n~Nat
    count 10 src 0 + count 32 src 0

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let text = string.bytes "one two\nthree\n"
    terminal.print_line (format (newlines text) ++ " " ++ format (lines_and_spaces text)) sys.term
    Success
