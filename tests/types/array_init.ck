# `array.init n f` calls `f` only with `i < n` (D186, #32), so the
# callback may index arrays of length `n` without checking.
module array_init

import std.array

# Each index is below `len xs`.
fn copy xs -> ys : xs~Array Nat, ys~Array Nat, len ys == len xs
    array.init (len xs) (\i -> xs[i])

# Neighbouring elements: `i + 1 < len xs` follows from `i < len xs - 1`.
fn sums xs -> ys : xs~Array Nat, len xs > 0, ys~Array Nat, len ys == len xs - 1
    array.init (len xs - 1) (\i -> xs[i] + xs[i + 1])

# A function whose precondition the bound implies (D85).
fn at xs i -> x : xs~Array Nat, i~Nat, i < len xs, x~Nat
    xs[i]

fn copy_by_name xs -> ys : xs~Array Nat, ys~Array Nat
    array.init (len xs) (at xs)

# A function for every `Nat` is still accepted.
fn square i -> r : i~Nat, r~Nat
    i * i

fn squares n -> r : n~Nat, r~Array Nat, len r == n
    array.init n square

# Past the bound: E0450.
fn shifted xs -> ys : xs~Array Nat, ys~Array Nat
    array.init (len xs) (\i -> xs[i + 1])
