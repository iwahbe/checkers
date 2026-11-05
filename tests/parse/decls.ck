module std.collections.vec_demo

import list (map, reverse)
import decimal as dec
import utf8

export enum Vec a n : a~Type, n~Nat
    Nil          : n == 0
    Cons x xs    : x~a, xs~Vec a m, n == m + 1

export abstract record Map k +v : k~Type, v~Type
    root~Tree k v
    size~Nat, size == count root

export record Error src : src~ghost Bytes
    pos~Nat, pos <= len src

type Small = n~Nat, n < 10

export let MAX_DEPTH = 512

partial fn serve socket : socket~own Socket
    serve socket

export transparent fn len2 xs -> n : xs~List a, n~Nat
    decreasing len xs
    match xs
        []      -> 0
        _ :: ys -> 1 + len2 ys

export lemma len2_nonneg xs : xs~List a
    let n = len2 xs
    ensures n >= 0
    proof
        have nat_nonneg n

lemma trivial
    ensures True
    proof
        admit

check len2 [1, 2, 3] == 3
