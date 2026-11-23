module datatype_refinements

# A datatype's fields keep what their types say, as a tuple's parts do: at a
# local, a field read, an array element, and a call's result, the callee
# recursive or not, with the type's arguments put in and nested inside other
# types. `sealed.boxes`'s functions are known by their signatures only.

import std.list (length)
import sealed.boxes (Box, Counted, boxed, counted, below, find, pair)

record Pair a b
    fst~a
    snd~b

# A refined type argument: `walk n (i + 1)` is a `Pair Nat (j~Nat, i <= j,
# j <= n)`, as it would be with a tuple.
fn walk n i -> r : n~Nat, i~Nat, i <= n, r~Pair Nat (j~Nat, i <= j, j <= n)
    decreasing n - i
    if i < n then walk n (i + 1) else Pair 0 i

fn by_match n i -> r : n~Nat, i~Nat, i <= n, r~(j~Nat, i <= j)
    match walk n i
        Pair _ j -> j

fn by_let n i -> r : n~Nat, i~Nat, i <= n, r~(j~Nat, i <= j)
    let Pair _ j = walk n i
    j

fn by_field n i -> r : n~Nat, i~Nat, i <= n, r~Int, i <= r, r <= n
    (walk n i).snd

# A field's own type, and the record's invariant, at a call's result.
fn size xs -> r : xs~List Int, r~Int, r >= 0, r == length (counted xs).items
    (counted xs).count

# Where the callee's precondition holds.
fn guarded n -> r : n~Nat, r~Int, r < n + 1
    (below 0 (n + 1)).item

# Nested: a record in a record in an `Option`, and a tuple in a record.
fn nested k -> r : k~Nat, r~Int, r > k
    match find k
        Some b -> b.item.item
        None   -> k + 1

fn tuple_part k -> r : k~Nat, r~Int, r > k
    let (_, s) = (pair k).item
    s

# Each constructor's fields, under its tester: `value r` is `v` only where
# `r` is an `Exact`.
enum Reading
    Exact v     : v~(n~Nat, n < 10)
    Range lo hi : lo~Nat, hi~Nat, lo <= hi

fn value r -> n : r~Reading, n~Int
    match r
        Exact v    -> v
        Range lo _ -> lo

fn is_exact r -> b : r~Reading, b~Bool
    match r
        Exact _ -> True
        _       -> False

lemma exact_small r : r~Reading
    ensures is_exact r implies value r < 10
    proof
        auto

# An array's element is a record whose field is refined.
fn element xs i -> r : xs~Array (Pair Bool (s~Nat, s > 3)), i~Nat, i < len xs, r~Int, r > 3
    xs[i].snd

# Only what the types say: `s > 3` doesn't give `s > 4`, a `Range` isn't
# below 10, and `boxed` is a `Box Nat`, not the `Box 3` its module makes.
fn wrong p -> r : p~Pair Bool (s~Nat, s > 3), r~Int, r > 4
    p.snd

lemma range_small lo hi : lo~Nat, hi~Nat, lo <= hi
    ensures value (Range lo hi) < 10
    proof
        auto

fn from_box -> r : r~Int, r >= 0
    boxed.item

fn sealed_box -> r : r~Int, r < 4
    boxed.item
