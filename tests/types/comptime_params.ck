module comptime_params

# Compile-time parameters (SPEC §8.9, D59–D61): what is rejected.

import std.list (map)

fn power n x -> y : n~comptime Nat, x~Int, y~Int
    decreasing n
    if n == 0 then 1 else x * power (n - 1) x

# A compile-time argument known only at run time.
fn runtime_arg n x -> y : n~Nat, x~Int, y~Int
    power n x

# A compile-time function passed as a value, or partly applied.
fn as_value xs -> ys : xs~List Int, ys~List Int
    map (power 2) xs

fn bare -> f : f~(Nat -> Int -> Int)
    power

# Wrapping the call in a lambda is fine.
fn wrapped xs -> ys : xs~List Int, ys~List Int
    map (\x -> power 2 x) xs

# Compile-time code must end.
partial fn spin n : n~comptime Nat
    spin n

lemma about n : n~comptime Nat
    ensures n >= 0

# A `let` of compile-time values is a compile-time value; a parameter isn't.
fn via_let x -> y : x~Int, y~Int
    let k = 1 + 2
    power k x
