# What `slice` and `concat` return is known to proofs, for bytes and
# arrays: each element of a slice, a slice of the middle of a join, and
# `concat` as `++`.
module slices

import std.bytes
import std.array

lemma bytes_at src i j k : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src, k~Nat, k < j - i
    ensures (bytes.slice src i j)[k] == src[i + k]
    proof
        have bytes.slice_at src i j k

lemma bytes_all src : src~Bytes
    ensures bytes.slice src 0 (len src) == src
    proof
        have bytes.slice_append b"" src b""

lemma bytes_middle pre mid post : pre~Bytes, mid~Bytes, post~Bytes
    ensures bytes.slice (pre ++ mid ++ post) (len pre) (len pre + len mid) == mid
    proof
        have bytes.slice_append pre mid post

lemma bytes_two a b : a~Bytes, b~Bytes
    ensures bytes.concat [a, b] == a ++ b
    proof
        have bytes.concat_cons a [b]
        have bytes.concat_cons b []
        have bytes.concat_nil

lemma array_at xs i j k : xs~Array Nat, i~Nat, j~Nat, i <= j, j <= len xs, k~Nat, k < j - i
    ensures (array.slice xs i j)[k] == xs[i + k]
    proof
        have array.slice_at xs i j k

lemma array_middle pre mid post : pre~Array Nat, mid~Array Nat, post~Array Nat
    ensures array.slice (pre ++ mid ++ post) (len pre) (len pre + len mid) == mid
    proof
        have array.slice_append pre mid post

lemma array_two xs ys : xs~Array Nat, ys~Array Nat
    ensures array.concat [xs, ys] == xs ++ ys
    proof
        have array.concat_cons xs [ys]
        have array.concat_cons ys []
        have array.concat_nil ys

# A slice says nothing about bytes outside it: E0450.
lemma beyond src i j : src~Bytes, i~Nat, j~Nat, i < j, j < len src
    ensures (bytes.slice src i j)[0] == src[j]
