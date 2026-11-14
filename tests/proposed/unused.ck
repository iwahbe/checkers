# D144 (proposed): unused code and unreachable branches.
#
# Expected, with the rest of the file clean:
#
# warning[W020]: `ping` is never used
#   --> unused.ck:45:12
#    = note: `ping` and `pong` only use each other; nothing `main` reaches uses either
#    = help: remove them, or export what is meant as API
# warning[W020]: `pong` is never used            (same note, at 50:12)
# warning[W020]: `Unused` is never used          (at 55:8)
# warning[W021]: this arm never matches
#   --> unused.ck:43:9
#    |
# 43 |         1 -> 2
#    |         ^ `_` on line 42 already matches everything
# warning[W022]: this branch never runs
#   --> unused.ck:37:19
#    |
# 37 |     if n < 0 then -1 else 1
#    |                   ^^ `n < 0` is false here: `n~Nat`
#    = help: remove the `if`, or write `impossible` as the branch's body
#
# `head`'s `[]` arm is `impossible`: proved (xs != []), no warning. Written
# as `[] -> 0` it would be W022; `impossible` where the prover can't show the
# branch never runs is E0456.

module unused

import std.system (System, ExitCode)

fn head xs -> r : xs~List Int, xs != [], r~Int
    match xs
        []     -> impossible
        x :: _ -> x

fn sign n -> r : n~Nat, r~Int
    if n < 0 then -1 else 1

fn pick n -> r : n~Int, r~Int
    match n
        0 -> 0
        _ -> 1
        1 -> 2

partial fn ping n -> r : n~Nat, r~Nat
    match n
        0 -> 0
        _ -> pong (n - 1)

partial fn pong n -> r : n~Nat, r~Nat
    match n
        0 -> 0
        _ -> ping (n - 1)

record Unused
    x~Int

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    if head [sign 3, pick 1] > 0 then Success else Failure 1
