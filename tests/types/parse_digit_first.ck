module parse_digit_first

# `Parsable.parse` reads a number that isn't negative from bytes that start
# with a digit, by `string.parse_digits`, so a reader that has seen a digit
# needs no `Err` arm, at `Nat` too. What is left is the bytes after the
# number, and doesn't start with a digit.

import std.parse (Parsable)
import std.array
import std.char
import std.string

fn at_nat b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~(Nat, Bytes)
    have string.parse_digits b
    match Parsable.parse b Nat Int
        Ok (n, after) -> (n, after)

fn at_int b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~Int, r >= 0
    have string.parse_digits b
    match Parsable.parse b Int Int
        Ok (n, _) -> n

# The rest is the bytes after at least one: those from the index of its
# first, on.
fn rest_at b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~Bytes, len r < len b,
                    r == array.slice b (len b - len r) (len b)
    have string.parse_digits b
    match Parsable.parse b Int Int
        Ok (_, after) -> after

# The rest doesn't start with a digit.
fn stops b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~Bool, r
    have string.parse_digits b
    match Parsable.parse b Int Int
        Ok (_, after) -> len after == 0 or not (char.is_digit after[0])
