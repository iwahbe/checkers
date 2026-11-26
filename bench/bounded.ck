module bounded

# Benchmark (§14): the Adler-32 checksum of a mebibyte, 200 times. The sums
# stay below 65521, as the preconditions say, and the bytes below 256, as
# their type says, so adding them needs no small-integer test or overflow
# check.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.array

fn sums src i s1 s2 -> r : src~Bytes, i~Nat, i <= len src, s1~Nat, s1 < 65521, s2~Nat,
                           s2 < 65521, r~Nat
    decreasing len src - i
    if i == len src
        s2 * 65536 + s1
    else
        let t1 = (s1 + src[i]) % 65521
        sums src (i + 1) t1 ((s2 + t1) % 65521)

fn rounds src k acc -> r : src~Bytes, k~Nat, acc~Nat, r~Nat
    decreasing k
    if k == 0 then acc else rounds src (k - 1) ((acc + sums src 0 1 0) % 1000000007)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let src = array.init 1048576 (\i -> i * 7 % 256)
    terminal.print_line (debug (rounds src 200 0)) sys.term
    Success
