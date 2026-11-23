# parse.ck — values read from the front of a sequence of tokens.
module std.parse

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
        [] ->
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
                Err x -> Err x

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
                Err x -> Err x

# `p` once, then `p` after each `sep`, keeping only `p`'s values: `1, 2, 3`.
export fn sep_by1 p sep xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                  sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size xs, consumed qr ys), xs~s,
                                  r~Result (List a, s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match sep_rest p sep xs mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (v :: vs, rest)
                Err x -> Err x

# Each `sep p` at the front of `xs`, until there is none; `xs` is less
# than `top`, what the parsers may be given less of.
fn sep_rest p sep top xs -> r : Seq s, p~(ys~s -> pr~Result (a, s) e, Seq.size ys < Seq.size top, consumed pr ys),
                                sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size top, consumed qr ys),
                                top~ghost s, xs~s, Seq.size xs < Seq.size top, r~Result (List a, s) e, within r xs
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
                    match sep_rest p sep top after
                        Ok (vs, rest) ->
                            have suffix_trans after mid xs
                            have suffix_trans rest after xs
                            Ok (v :: vs, rest)
                        Err x -> Err x

# `p`, then any number of `sep p`, combined from the left with `f`: with `+`
# as `sep`, `1 + 2 + 3` is `f (f 1 2) 3`.
export fn chain_left p sep f xs -> r : Seq s,
                                       p~(ys~s -> pr~Result (a, s) e, Seq.size ys <= Seq.size xs, consumed pr ys),
                                       sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size xs, consumed qr ys),
                                       f~(a -> a -> a), xs~s, r~Result (a, s) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match chain_rest p sep f xs v mid
                Ok (w, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (w, rest)
                Err x -> Err x

# After `acc`: each `sep p` folded into it, until there is none; `xs` is
# less than `top`, what the parsers may be given less of.
fn chain_rest p sep f top acc xs -> r : Seq s,
                                        p~(ys~s -> pr~Result (a, s) e, Seq.size ys < Seq.size top, consumed pr ys),
                                        sep~(ys~s -> qr~Result (b, s) e, Seq.size ys < Seq.size top, consumed qr ys),
                                        f~(a -> a -> a), top~ghost s, acc~a, xs~s, Seq.size xs < Seq.size top,
                                        r~Result (a, s) e, within r xs
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
                    match chain_rest p sep f top (f acc v) after
                        Ok (w, rest) ->
                            have suffix_trans after mid xs
                            have suffix_trans rest after xs
                            Ok (w, rest)
                        Err x -> Err x

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
# which it may call only on less input than it was given.
#
#     fn sum xs -> r : …, consumed r xs
#         fix (\zs self -> chain_left digit plus Add zs) xs
export fn fix body xs -> r : Seq s, xs~s,
                             body~(zs~s -> (self~(ys~s -> sr~Result (a, s) e, Seq.size ys < Seq.size zs,
                                                  consumed sr ys)
                                   -> br~Result (a, s) e, consumed br zs)),
                             r~Result (a, s) e, consumed r xs
    decreasing Seq.size xs
    body xs (\ys -> fix body ys)
