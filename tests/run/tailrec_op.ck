# An operator after a recursive call: `+` and `*`, and `++` with the call on
# its left, run in constant stack; the rest give the same results, and what
# the other operand does runs after the call.
module tailrec_op

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn sum n -> r : n~Nat, r~Nat
    if n == 0 then 0 else n + sum (n - 1)

# The call on the left.
fn sum_left n -> r : n~Nat, r~Nat
    if n == 0 then 0 else sum_left (n - 1) + n

fn product n -> r : n~Nat, r~Nat
    if n == 0 then 1 else n * product (n - 1)

fn by_append n -> r : n~Nat, r~String
    if n == 0 then "" else by_append (n - 1) ++ debug n

fn by_prepend n -> r : n~Nat, r~String
    if n == 0 then "" else debug n ++ by_prepend (n - 1)

fn lists n -> r : n~Nat, r~List Nat
    if n == 0 then [] else lists (n - 1) ++ [n, n]

fn alternate n -> r : n~Nat, r~Int
    if n == 0 then 0 else n - alternate (n - 1)

fn noisy n term -> r : n~Nat, term~Term, r~Nat
    terminal.print_line (debug n) term
    n

# The other operand does something: it runs after the call.
fn after n term -> r : n~Nat, term~Term, r~Nat
    if n == 0 then 0 else after (n - 1) term + noisy n term

# `+` through a class: not associative here.
record Diff
    value~Int

instance Add Diff
    fn add x y
        Diff (x.value - y.value)

fn diffs n -> r : n~Nat, r~Diff
    if n == 0 then Diff 0 else Diff n + diffs (n - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (sum 10000000)) term
    terminal.print_line (debug (sum_left 10000000)) term
    terminal.print_line (debug (product 30)) term
    terminal.print_line (by_append 12) term
    terminal.print_line (by_prepend 12) term
    terminal.print_line (debug (lists 3)) term
    terminal.print_line (debug (alternate 5)) term
    terminal.print_line (debug (after 3 term)) term
    terminal.print_line (debug (diffs 4).value) term
    Success
