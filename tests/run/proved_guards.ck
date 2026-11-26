module proved_guards

# Guarded operations whose obligations are proved (§13.3): a `Nat`
# subtraction, a division, an index and a `when` on two cowns compile with
# no run-time check. A division by a divisor proved not zero is the same
# code as one whose bounds show it. Each function is too big to be inlined
# into its caller.

import std.system (System, ExitCode)
import std.cown (Cown, Sched)
import std.string (debug)
import std.terminal (Term)

fn nat_less a b -> r : a~Nat, b~Nat, b <= a, r~Nat
    (a - b) * (a - b) + (a - b) * 2 + b

fn nonzero a b -> r : a~Int, b~Int, b != 0, r~Int
    a / b + a % b - (-a) + a / b * (a % b)

fn positive a b -> r : a~Int, b~Int, 1 <= b, r~Int
    a / b + a % b - (-a) + a / b * (a % b)

fn byte_at bs i -> r : bs~Bytes, i~Nat, i < len bs, r~Nat
    bs[i] * bs[i] + bs[i] * 2 + i

fn swap x y sched -> r : x~Cown Nat, y~Cown Nat, x != y, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b + 1, a + 1)
    ()

fn line n term : n~Int, term~Term
    terminal.print_line (debug n) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    line (nat_less 10 3) term
    line (nonzero 17 (-5)) term
    line (positive 17 5) term
    line (byte_at b"abc" 1) term
    let c = cown.new 1 sched
    let d = cown.new 2 sched
    swap c d sched
    when a = c, b = d using sched
        terminal.print_line (debug a ++ " " ++ debug b) term
        (a, b)
    Success
