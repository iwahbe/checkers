# Arrays with equal lengths and equal elements are equal, so slices side
# by side make the slice spanning both, for bytes and arrays.
module joins

import std.bytes
import std.array

lemma join src i j k : src~Bytes, i~Nat, j~Nat, k~Nat, i <= j, j <= k, k <= len src
    ensures bytes.slice src i j ++ bytes.slice src j k == bytes.slice src i k
    proof
        have bytes.slice_join src i j k

lemma array_join xs i j k : xs~Array Nat, i~Nat, j~Nat, k~Nat, i <= j, j <= k, k <= len xs
    ensures array.slice xs i j ++ array.slice xs j k == array.slice xs i k
    proof
        have array.slice_join xs i j k

# A quote between two slices gives the whole back.
lemma around f k : f~Bytes, k~Nat, k < len f, f[k] == 34
    ensures bytes.slice f 0 k ++ b"\"" ++ bytes.slice f (k + 1) (len f) == f
    proof
        have bytes.slice_at f k (k + 1) 0
        have bytes.slice_join f k (k + 1) (len f)
        have bytes.slice_join f 0 k (len f)
        have bytes.slice_append b"" f b""

# Equal bytes at every index, from a lemma's `forall`, make equal arrays.
lemma by_forall xs ys : xs~Array Nat, ys~Array Nat, len xs == len ys,
                        same: forall k : k~Nat, k < len xs, xs[k] == ys[k]
    ensures xs == ys

# `ext` names it, for an equality that isn't the whole goal.
lemma by_ext xs ys : xs~Bytes, ys~Bytes, len xs == len ys,
                     same: forall k : k~Nat, k < len xs, xs[k] == ys[k]
    ensures xs == ys and len xs == len ys
    proof
        have bytes.ext xs ys

# Equal at all but the last index: E0450.
lemma short xs ys : xs~Bytes, ys~Bytes, len xs == len ys,
                    same: forall k : k~Nat, k + 1 < len xs, xs[k] == ys[k]
    ensures xs == ys

# Equal at a few indexes only: E0450.
lemma few xs ys : xs~Bytes, ys~Bytes, len xs == len ys,
                  same: forall k : k~(k~Int, k >= 0, k < 2), k < len xs, xs[k] == ys[k]
    ensures xs == ys
