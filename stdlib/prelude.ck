# prelude.ck — imported into every module.
module std.prelude

# The type of types: `a~Type` says that `a` is a type, so `List a` is a
# list of any type `a`. Built into the compiler (D132).
export abstract enum Type

# Built-in types; their values come from literals and primitives.
export abstract enum Int
# Text: UTF-8, immutable. The prover sees a string as its UTF-8 bytes.
export abstract enum String
# An immutable array: `len xs` and `xs[i]` take constant time. Arrays of
# fixed-width numbers are packed (D133); `std.array` has its functions.
export abstract enum Array +a : a~Type

# `False` or `True`.
export enum Bool
    False
    True

# The type with one value, `()`.
export type Unit = u~()

# A value of type `a`, or nothing.
export enum Option a : a~Type
    None
    Some x : x~a

# A value of type `a` (`Ok`) or an error of type `e` (`Err`).
export enum Result a e : a~Type, e~Type
    Ok x  : x~a
    Err x : x~e

# An immutable singly linked list: `[]` or `x :: xs`.
export enum List a : a~Type
    Nil
    Cons x xs : x~a, xs~List a

# The natural numbers are a refinement of the integers (D121).
export type Nat = n~Int, n >= 0

# Fixed-width numbers are refinements of Nat and Int (D6).
export type U8 = n~Nat, n < 256

# A sequence of bytes, immutable: an array of `U8`, packed (D133).
# `src[i]` is the byte at `i`.
export type Bytes = b~Array U8

# An unsigned 16-bit number.
export type U16 = n~Nat, n < 65536
# An unsigned 32-bit number.
export type U32 = n~Nat, n < 4294967296
# An unsigned 64-bit number.
export type U64 = n~Nat, n < 18446744073709551616
# A signed 8-bit number.
export type I8 = n~Int, -128 <= n, n < 128
# A signed 32-bit number.
export type I32 = n~Int, -2147483648 <= n, n < 2147483648
# A signed 64-bit number.
export type I64 = n~Int, -9223372036854775808 <= n, n < 9223372036854775808

# A Unicode scalar value.
export type Char = n~Nat, n < 0x110000, (n < 0xD800 or 0xE000 <= n)

# Logical negation.
export transparent fn not b -> r : b~Bool, r~Bool
    if b then False else True

# ── Order (D136, D138) ───────────────────────────────────────────────────────

# A total order: `le x y` says `x` comes before `y`, or with it. Sorting
# (`std.sort`, `array.sort`) uses one. Each instance proves the lemmas.
export class Ord a
    # Whether `x` comes before `y` or with it.
    fn le x y -> r : x~a, y~a, r~Bool
    # Coming before is transitive.
    lemma trans x y z : x~a, y~a, z~a, le x y, le y z
        ensures le x z
    # Any two values are in order one way or the other.
    lemma total x y : x~a, y~a
        ensures le x y or le y x
    # Two values each before the other are equal.
    lemma antisym x y : x~a, y~a, le x y, le y x
        ensures x == y

# Every value comes with itself.
export lemma refl x : Ord a, x~a
    ensures le x x
    proof
        have total x x

# Numbers, by size; this is also the order of `Nat`, `Char` and the
# fixed-width numbers.
instance Ord Int
    fn le x y
        x <= y

# `False` before `True`.
instance Ord Bool
    fn le x y
        not x or y

# Strings by their characters' scalar values, which is the order of their
# UTF-8 bytes.
instance Ord String
    fn le x y
        string_le x y
    lemma trans x y z
        proof
            __builtin
    lemma total x y
        proof
            __builtin
    lemma antisym x y
        proof
            __builtin

# Lists by their first elements where they differ; a list before any longer
# one that starts with it.
instance Ord (List a) : Ord a
    fn le xs ys
        match xs
            []      -> True
            x :: xr ->
                match ys
                    []      -> False
                    y :: yr -> Ord.le x y and (not (Ord.le y x) or le xr yr)
    lemma trans xs ys zs
        proof
            match xs
                []      -> auto
                x :: xr ->
                    match ys
                        []      -> auto
                        y :: yr ->
                            match zs
                                []      -> auto
                                z :: zr ->
                                    have Ord.trans x y z
                                    if Ord.le z x
                                        have Ord.trans y z x
                                        have Ord.trans z x y
                                        have trans xr yr zr
                                    else
                                        auto
    lemma total xs ys
        proof
            match xs
                []      -> auto
                x :: xr ->
                    match ys
                        []      -> auto
                        y :: yr ->
                            have Ord.total x y
                            have total xr yr
    lemma antisym xs ys
        proof
            match xs
                []      -> auto
                x :: xr ->
                    match ys
                        []      -> auto
                        y :: yr ->
                            have Ord.antisym x y
                            have antisym xr yr

# `None` before every `Some`, which are ordered by what they hold.
instance Ord (Option a) : Ord a
    fn le p q
        match p
            None   -> True
            Some x ->
                match q
                    None   -> False
                    Some y -> Ord.le x y
    lemma trans p q r
        proof
            match p
                None   -> auto
                Some x ->
                    match q
                        None   -> auto
                        Some y ->
                            match r
                                None   -> auto
                                Some z -> have Ord.trans x y z
    lemma total p q
        proof
            match p
                None   -> auto
                Some x ->
                    match q
                        None   -> auto
                        Some y -> have Ord.total x y
    lemma antisym p q
        proof
            match p
                None   -> auto
                Some x ->
                    match q
                        None   -> auto
                        Some y -> have Ord.antisym x y

# Whether `x` comes before `y` by their bytes (`Ord String`).
fn string_le x y -> r : x~String, y~String, r~Bool
    __builtin
