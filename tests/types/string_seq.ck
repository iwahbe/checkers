module string_seq

# What the prover knows of a string taken apart from the front: `[]` only
# for the empty string, a rest with fewer bytes, and the characters the
# `check`s show; recursion on the rest needs no `decreasing`.

fn count s -> n : s~String, n~Nat
    match s
        []        -> 0
        _ :: rest -> 1 + count rest

check count "h€llo" == 5
check count "" == 0

# A non-empty string has no `[]` case.
fn first s -> c : s~String, len s.bytes > 0, c~Char
    match s
        c :: _ -> c

check first "€x" == c'€'

# The rest has fewer bytes.
fn rest_shorter s -> r : s~String, r~Bool, r
    match s
        []        -> True
        _ :: rest -> len rest.bytes < len s.bytes

# `Seq.uncons` keeps its postcondition at `String`.
fn uncons_empty s -> r : s~String, r~Bool, r
    match Seq.uncons s
        None           -> len s.bytes == 0
        Some (_, rest) -> Seq.size rest < Seq.size s

check Seq.uncons "a" == Some (c'a', "")
check Seq.uncons "" == None
