module power

# Staging (SPEC §8.9): a compile-time function is expanded at each call;
# `if` on a compile-time value picks its branch, and recursion unrolls.

import terminal (Term)

fn power n x -> y : n~comptime Nat, x~Int, y~Int
    decreasing n
    if n == 0 then 1 else x * power (n - 1) x

fn cube x -> y : x~Int, y~Int
    power 3 x

# A runtime argument is computed once, before the expansion (D41).
fn square_of_sum a b -> y : a~Int, b~Int, y~Int
    power 2 (a + b)

# Compile-time values may be computed: `2 + 1` is 3 here.
fn from_let x -> y : x~Int, y~Int
    let k = 2 + 1
    power k x

# An effect in a runtime argument still happens exactly once, and first.
partial fn read_and_square term -> y : term~Term, y~Int
    power 2 (line_value (terminal.read_line term))

fn line_value l -> n : l~Option String, n~Int
    match l
        None -> 0
        Some _ -> 7

check cube 2 == 8
check square_of_sum 1 2 == 9
