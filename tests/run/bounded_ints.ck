module bounded_ints

# Integers whose types bound them, at the edges of those bounds: sums,
# differences, quotients and products that fit in a word, and products of
# `I32`s that reach 2^62, one past the largest integer a word holds inline.
# Each function is too big to be inlined into its caller, and is given
# values known only when the program runs (`n` is 0), each within its
# bounds by a remainder, or the calls would be computed when compiling.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)

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
    let n = len args
    let (b0, b255) = (n % 256, (n + 255) % 256)
    line (add_bytes b0 b0 b0 b0) sys
    line (add_bytes b255 b255 b255 b255) sys
    line (spread (n % 1000) (-(n % 1000))) sys
    line (spread ((n + 999) % 1000) (-((n + 999) % 1000))) sys
    let (w65535, w65534, w0) = ((n + 65535) % 65536, (n + 65534) % 65536, n % 65536)
    line (halves w65535 (1 + n % 65535)) sys
    line (halves w65535 (1 + (n + 65534) % 65535)) sys
    line (halves w65534 (1 + (n + 65534) % 65535)) sys
    line (halves w0 (1 + (n + 6) % 65535)) sys
    line (take (256 + (n + 65279) % 65280) b255) sys
    line (take (256 + n % 65280) b0) sys
    let (top, bottom) = ((n + 2147483647) % 2147483648, -((n + 2147483648) % 2147483649))
    line (product top top) sys
    line (product bottom bottom) sys
    line (product bottom top) sys
    Success
