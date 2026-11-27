module bounded_ints

# Integers whose types bound them, at the edges of those bounds: sums,
# differences, quotients and products that fit in a word, and products of
# `I32`s that reach 2^62, one past the largest integer a word holds inline.
# Each function is too big to be inlined into its caller.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.hint (blackbox)

fn add_bytes a b c d -> r : a~U8, b~U8, c~U8, d~U8, r~Nat
    (a + b) + (c + d) + (a + c) + (b + d)

fn spread a b -> r : a~Int, b~Int, 0 <= a, a < 1000, -1000 < b, b <= 0, r~Int
    a * a - 3 * b + (a - b) * (b - a)

fn halves a b -> r : a~U16, b~U16, 1 <= b, r~Int
    a / b + a % b - (-a) + a / b * (a % b)

fn take a b -> r : a~U16, b~U8, 256 <= a, r~Nat
    (a - b) * (a - b) + (a - b) * 2 + b

fn product a b -> r : a~I32, b~I32, r~Int
    a * b + (a + b) * (a - b) + 1

fn line n sys : n~Int, sys~System
    terminal.print_line (debug n) sys.term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    # Given through `blackbox`, or the calls would be computed when compiling.
    line (add_bytes (blackbox 0) (blackbox 0) (blackbox 0) (blackbox 0)) sys
    line (add_bytes (blackbox 255) (blackbox 255) (blackbox 255) (blackbox 255)) sys
    line (spread (blackbox 0) (blackbox 0)) sys
    line (spread (blackbox 999) (blackbox (-999))) sys
    line (halves (blackbox 65535) (blackbox 1)) sys
    line (halves (blackbox 65535) (blackbox 65535)) sys
    line (halves (blackbox 65534) (blackbox 65535)) sys
    line (halves (blackbox 0) (blackbox 7)) sys
    line (take (blackbox 65535) (blackbox 255)) sys
    line (take (blackbox 256) (blackbox 0)) sys
    line (product (blackbox 2147483647) (blackbox 2147483647)) sys
    line (product (blackbox (-2147483648)) (blackbox (-2147483648))) sys
    line (product (blackbox (-2147483648)) (blackbox 2147483647)) sys
    Success
