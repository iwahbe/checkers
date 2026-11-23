# parse.ck — values read from the front of a sequence of tokens.
module std.parse

import std.array
import std.char
import std.string

# An element of a sequence, read as a token of type `t`: `token x Int`.
# A type of tokens has an instance that reads its own values as they are.
export class Token x t
    fn token v t -> r : v~x, t~ghost Type, r~t

# Characters and bytes: `Char` and `U8` are `Int`s, so this covers
# `String`, `List Char`, `Bytes` and `List U8`.
instance Token Int Int
    fn token v t
        v

# Whether `rest` is what is left of `xs` after taking some elements off its
# front: `xs` itself, or what is left of its rest.
export transparent fn suffix rest xs -> b : Seq s, rest~s, xs~s, b~Bool
    decreasing Seq.size xs
    match xs
        []        -> rest == xs
        _ :: tail -> rest == xs or suffix rest tail

# Every sequence is what is left of itself.
export lemma suffix_refl xs : Seq s, xs~s
    ensures suffix xs xs
    proof
        match xs
            []     -> auto
            _ :: _ -> auto

# What is left of what is left of `c` is what is left of `c`.
export lemma suffix_trans a b c : Seq s, a~s, b~s, c~s, suffix a b, suffix b c
    ensures suffix a c
    proof
        match c
            []        -> auto
            _ :: rest -> if b == c then auto else have suffix_trans a b rest

# What is left is no longer than what it was left of.
export lemma suffix_size rest xs : Seq s, rest~s, xs~s, suffix rest xs
    ensures Seq.size rest <= Seq.size xs
    proof
        match xs
            []        -> auto
            _ :: tail -> if rest == xs then auto else have suffix_size rest tail

# Whether parsing `xs` gave `r` and read at least one element: what is left
# is a suffix of `xs`, and shorter. A failure says nothing.
export transparent fn consumed r xs -> b : Seq s, r~Result (a, s) e, xs~s, b~Bool
    match r
        Ok (_, rest) -> suffix rest xs and Seq.size rest < Seq.size xs
        Err _        -> True

# Whether what is left after `r` is a suffix of `xs`, maybe all of it.
export transparent fn within r xs -> b : Seq s, r~Result (a, s) e, xs~s, b~Bool
    match r
        Ok (_, rest) -> suffix rest xs
        Err _        -> True

# A type `a` whose values can be read from the front of a sequence of
# tokens of type `t`: `Parsable.parse xs Decimal Int`.
export class Parsable a t
    # Why nothing could be read.
    type Error
    # A value read from the front of `xs`, and what is left of `xs` after
    # it: a suffix of `xs`, and shorter, since a value takes at least one
    # token. A type that may take none (an optional field) reports that as
    # an error.
    fn parse xs a t -> r : Seq s, Token (Seq.Elem s) t, xs~s, a~ghost Type, t~ghost Type,
                           r~Result (a, s) Error, consumed r xs

# ── Combinators ──────────────────────────────────────────────────────────────
#
# A parser here is a function from a sequence to a `Result (a, s) e` that
# reads at least one element when it succeeds (`consumed`). Each combinator
# says, in its parameters' types, how much input it gives each parser: no
# more than it was given (`<=`), or less (`<`). That lets a recursive rule
# be passed to them through `fix`.

# One element for which `f` is true, or `Err e`.
export fn satisfy f e xs -> r : Seq s, f~(Seq.Elem s -> Bool), e~err, xs~s,
                                r~Result (Seq.Elem s, s) err, consumed r xs
    match xs
        x :: rest -> if f x then Ok (x, rest) else Err e
        []        -> Err e

# Nothing, if `xs` is empty; else `Err e`.
export fn at_end e xs -> r : Seq s, e~err, xs~s, r~Result (Unit, s) err, within r xs
    match xs
        []     ->
            have suffix_refl xs
            Ok ((), xs)
        _ :: _ -> Err e

# `p`, with `f` applied to what it reads.
export fn map f p xs -> r : Seq s, f~(a -> b),
                            p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys), xs~s,
                            r~Result (b, s) e, consumed r xs
    match p xs
        Ok (v, rest) -> Ok (f v, rest)
        Err x        -> Err x

# `p`, then `q` on what is left: both values.
export fn both p q xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                             q~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size xs, within qr ys), xs~s,
                             r~Result ((a, b), s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (u, mid) ->
            match q mid
                Err x        -> Err x
                Ok (v, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok ((u, v), rest)

# `p`, or else `q` from the same place.
export fn or_else p q xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                q~(ys~s -> qr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed qr ys), xs~s,
                                r~Result (a, s) e, consumed r xs
    match p xs
        Ok v  -> Ok v
        Err _ -> q xs

# `p` if it applies; never fails, and may read nothing.
export fn optional p xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                               xs~s, r~Result (Option a, s) e, within r xs
    match p xs
        Ok (v, rest) -> Ok (Some v, rest)
        Err _        ->
            have suffix_refl xs
            Ok (None, xs)

# `p` as many times as it applies, maybe none; never fails.
export fn many p xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                           xs~s, r~Result (List a, s) e, within r xs
    decreasing Seq.size xs
    match p xs
        Err _       ->
            have suffix_refl xs
            Ok ([], xs)
        Ok (v, mid) ->
            match many p mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    Ok (v :: vs, rest)
                Err x         -> Err x

# `p` at least once.
export fn many1 p xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                            xs~s, r~Result (List a, s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match many p mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (v :: vs, rest)
                Err x         -> Err x

# `p` once, then `p` after each `sep`, keeping only `p`'s values: `1, 2, 3`.
export fn sep_by1 p sep xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                  sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size xs, consumed qr ys), xs~s,
                                  r~Result (List a, s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match sep_rest p sep mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (v :: vs, rest)
                Err x         -> Err x

# Each `sep p` at the front of `xs`, until there is none.
fn sep_rest p sep xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys < Seq.size xs, consumed pr ys),
                            sep~(ys~s -> qr~Result (b, s) e, Seq.size ys <= Seq.size xs, consumed qr ys), xs~s,
                            r~Result (List a, s) e, within r xs
    decreasing Seq.size xs
    match sep xs
        Err _       ->
            have suffix_refl xs
            Ok ([], xs)
        Ok (_, mid) ->
            match p mid
                Err _         ->
                    have suffix_refl xs
                    Ok ([], xs)
                Ok (v, after) ->
                    match sep_rest p sep after
                        Ok (vs, rest) ->
                            have suffix_trans after mid xs
                            have suffix_trans rest after xs
                            Ok (v :: vs, rest)
                        Err x         -> Err x

# `p`, then any number of `sep p`, combined from the left with `f`: with `+`
# as `sep`, `1 + 2 + 3` is `f (f 1 2) 3`.
export fn chain_left p sep f xs -> r : Seq s,
                                       p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                       sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size xs, consumed qr ys),
                                       f~(a -> a -> a), xs~s, r~Result (a, s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match chain_rest p sep f v mid
                Ok (w, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (w, rest)
                Err x        -> Err x

# After `acc`: each `sep p` folded into it, until there is none.
fn chain_rest p sep f acc xs -> r : Seq s,
                                    p~(ys~s -> pr~Result (a, s) e, Seq.size ys < Seq.size xs, consumed pr ys),
                                    sep~(ys~s -> qr~Result (b, s) e, Seq.size ys <= Seq.size xs, consumed qr ys),
                                    f~(a -> a -> a), acc~a, xs~s, r~Result (a, s) e, within r xs
    decreasing Seq.size xs
    match sep xs
        Err _       ->
            have suffix_refl xs
            Ok (acc, xs)
        Ok (_, mid) ->
            match p mid
                Err _         ->
                    have suffix_refl xs
                    Ok (acc, xs)
                Ok (v, after) ->
                    match chain_rest p sep f (f acc v) after
                        Ok (w, rest) ->
                            have suffix_trans after mid xs
                            have suffix_trans rest after xs
                            Ok (w, rest)
                        Err x        -> Err x

# `p`, which must read all of `xs`; `Err left` if anything is left.
export fn complete p left xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                    left~e, xs~s, r~Result a e
    match p xs
        Err x        -> Err x
        Ok (v, rest) ->
            match rest
                []     -> Ok v
                _ :: _ -> Err left

# A rule that refers to itself: `body` gets the input and `self`, the rule,
# which it may call only on less input than it was given. So a bracketed
# term may contain a whole sum again, and the grammar still ends: each
# `self` call is on what is left after the opening bracket.
export fn fix body xs -> r : Seq s, xs~s,
                             body~(zs~s -> (self~(ys~s -> sr~Result (a, s) e, Seq.size ys < Seq.size zs,
                                                  consumed sr ys)
                                            -> br~Result (a, s) e, consumed br zs)),
                             r~Result (a, s) e, consumed r xs
    decreasing Seq.size xs
    body xs (\ys -> fix body ys)

# ── Whole numbers ────────────────────────────────────────────────────────────

# Why no number could be read.
export enum NumberError
    NotFound  # the tokens don't start with a number

# A whole number in decimal at the front of `xs`: one or more digits, as
# many as there are. Leading zeros are allowed: `007` reads `7`.
export fn natural xs -> r : Seq s, Token (Seq.Elem s) Int, xs~s, r~Result (Nat, s) NumberError,
                            consumed r xs
    match xs
        x :: rest ->
            let c = token x Int
            if char.is_digit c
                let (n, after) = more_digits rest (c - '0')
                have suffix_size after rest
                Ok (n, after)
            else
                Err NotFound
        []        -> Err NotFound

# The digits at the front of `xs`, after digits making `acc`: what they all
# make, and what follows them.
fn more_digits xs acc -> r : Seq s, Token (Seq.Elem s) Int, xs~s, acc~Nat, r~(Nat, s),
                             match r
                                 (_, rest) -> suffix rest xs
    match xs
        x :: rest ->
            let c = token x Int
            if char.is_digit c
                let (n, after) = more_digits rest (acc * 10 + (c - '0'))
                (n, after)
            else
                have suffix_refl xs
                (acc, xs)
        []        ->
            have suffix_refl xs
            (acc, xs)

# A whole number in decimal, with `-` before it if it is negative: what
# `display n []` writes, and also `-0`, which is `0`, and leading zeros.
# `natural` reads one without a sign, as a `Nat`.
instance Parsable Int Int
    type Error = NumberError
    fn parse xs a t
        match xs
            x :: rest ->
                if token x Int == '-'
                    match natural rest
                        Ok (n, after) ->
                            have suffix_size after rest
                            Ok (-n, after)
                        Err e         -> Err e
                else
                    match natural xs
                        Ok (n, after) -> Ok (n, after)
                        Err e         -> Err e
            []        -> Err NotFound

# Where the digits of `b` from `i` on end: the first index from `i` whose
# byte isn't a digit, or the end.
export transparent fn digits_end b i -> k : b~Bytes, i~Nat, i <= len b, k~Nat, i <= k, k <= len b
    decreasing len b - i
    if i < len b and char.is_digit b[i] then digits_end b (i + 1) else i

# `natural` on bytes: the digits from the start up to `digits_end b 0`, if
# there is one, and the bytes after them.
export lemma natural_bytes b : b~Bytes
    let k = digits_end b 0
    ensures natural b == (if k == 0 then Err NotFound else Ok (string.decimal_value b 0 k, array.slice b k (len b)))
    proof
        if len b > 0
            have array.uncons_slice b
            if char.is_digit b[0]
                have more_digits_bytes b 0 1
            else
                auto
        else
            auto

# `natural` reads back what `string.decimal` writes, and leaves what follows
# if it doesn't start with a digit.
export lemma natural_decimal n post : n~Nat, post~Bytes, len post == 0 or not (char.is_digit post[0])
    ensures natural ((string.decimal n).bytes ++ post) == Ok (n, post)
    proof
        let r = (string.decimal n).bytes
        let b = r ++ post
        have string.decimal_prefix r post 0 (len r)
        have digits_end_at b 0 0 (len r)
        have natural_bytes b
        have array.slice_append r post b""

# `Parsable.parse` at `Int` reads back what `display n []` writes, and
# leaves what follows if it doesn't start with a digit.
export lemma parse_display n post : n~Int, post~Bytes, len post == 0 or not (char.is_digit post[0])
    ensures Parsable.parse ((string.display n []).bytes ++ post) Int Int == Ok (n, post)
    proof
        if n < 0
            let r = (string.decimal (-n)).bytes
            let b = b"-" ++ r ++ post
            have array.uncons_slice b
            have array.slice_append b"-" (r ++ post) b""
            have natural_decimal (-n) post
        else
            let r = (string.decimal n).bytes
            have array.uncons_slice (r ++ post)
            have string.all_digits_at r 0 (len r) 0
            have natural_decimal n post

# `more_digits` on bytes from `j` on, after the digits from `i` to `j`.
lemma more_digits_bytes b i j : b~Bytes, i~Nat, j~Nat, i <= j, j <= len b, string.all_digits b i j
    let k = digits_end b j
    ensures more_digits (array.slice b j (len b)) (string.decimal_value b i j)
        == (string.decimal_value b i k, array.slice b k (len b))
    proof
        decreasing len b - j
        if j < len b
            have uncons_from b j
            if char.is_digit b[j]
                have more_digits_bytes b i (j + 1)
            else
                auto
        else
            auto

# `x :: rest` on the bytes of `b` from `j` on: byte `j`, and the bytes
# after it.
lemma uncons_from b j : b~Bytes, j~Nat, j < len b
    ensures Seq.uncons (array.slice b j (len b)) == Some (b[j], array.slice b (j + 1) (len b))
    proof
        have array.uncons_slice (array.slice b j (len b))
        have array.slice_at b j (len b) 0
        have array.slice_join b j (j + 1) (len b)
        have array.slice_append (array.slice b j (j + 1)) (array.slice b (j + 1) (len b)) b""

# Where digits from `i` to `k` stop at `k`, the digits from any `j` between
# them end at `k`.
lemma digits_end_at b i j k : b~Bytes, i~Nat, j~Nat, k~Nat, i <= j, j <= k, k <= len b, string.all_digits b i k,
                              k == len b or not (char.is_digit b[k])
    ensures digits_end b j == k
    proof
        decreasing k - j
        if j < k
            have string.all_digits_at b i k j
            have digits_end_at b i (j + 1) k
        else
            auto

check natural b"0" == Ok (0, b"") and natural b"007x" == Ok (7, b"x") and natural b"x" == Err NotFound
check natural "12 34" == Ok (12, " 34") and natural "-1" == Err NotFound and natural "" == Err NotFound
check Parsable.parse b"-42," Int Int == Ok (-42, b",") and Parsable.parse b"-0" Int Int == Ok (0, b"")
check Parsable.parse b"-" Int Int == Err NotFound and Parsable.parse b"+1" Int Int == Err NotFound
check Parsable.parse "123" Int Int == Ok (123, "")
