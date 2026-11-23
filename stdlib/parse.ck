# parse.ck — values read from the front of a sequence of bytes.
module std.parse

# An element of a sequence of bytes, as a number. `Bytes` and `List U8`
# have `U8` elements, which are `Int`s, so this instance covers both.
export class Byte e
    fn byte x -> r : x~e, r~Int

instance Byte Int
    fn byte x
        x

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

# A type whose values can be read from the front of a sequence of bytes.
export class Parsable a s
    # Why nothing could be read.
    type Error
    # A value read from the front of `xs`, and what is left of `xs` after
    # it: a suffix of `xs`, and shorter, since a value takes at least one
    # byte. A type that may take none (an optional field) reports that as
    # an error.
    fn parse xs a -> r : Seq s, Byte (Seq.Elem s), xs~s, a~ghost Type, r~Result (a, s) Error,
                         match r
                             Ok (_, rest) -> suffix rest xs and Seq.size rest < Seq.size xs
                             Err _        -> True
