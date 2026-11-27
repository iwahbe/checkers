# prelude.ck — imported into every module.
module std.prelude

# The type of types: `a~Type` says that `a` is a type, so `List a` is a
# list of any type `a`. Built into the compiler.
export abstract enum Type

# Built-in types; their values come from literals and primitives.
export abstract enum Int

# Text: immutable bytes that are valid UTF-8. A string is stored as its
# bytes, so `s.bytes` costs nothing, and the prover sees it as them.
export record String
    bytes~Bytes, valid_utf8 bytes

# Whether `b` is well-formed UTF-8 (RFC 3629): no overlong forms, no
# surrogates, nothing above U+10FFFF.
export fn valid_utf8 b -> r : b~Bytes, r~Bool
    __builtin

check valid_utf8 b"h\xE2\x82\xAC" and valid_utf8 b""
check not (valid_utf8 b"\xC0\x80") and not (valid_utf8 b"\xED\xA0\x80") and not (valid_utf8 b"\x80")
# An immutable array: `len xs` and `xs[i]` take constant time. Arrays of
# fixed-width numbers are packed; `std.array` has its functions.
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

# The natural numbers are a refinement of the integers.
export type Nat = n~Int, n >= 0

# Fixed-width numbers are refinements of Nat and Int.
export type U8 = n~Nat, n < 256

# A sequence of bytes, immutable: an array of `U8`, packed.
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

# ── Order ────────────────────────────────────────────────────────────────────

# A total order: `le x y` says `x` comes before `y`, or with it. Sorting
# (`list.sort`, `array.sort`) uses one. Each instance proves the lemmas.
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
    transparent fn le x y
        x <= y

# `False` before `True`.
instance Ord Bool
    transparent fn le x y
        not x or y

# Strings by their characters' scalar values, which is the order of their
# UTF-8 bytes.
instance Ord String
    transparent fn le x y
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
    transparent fn le xs ys
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
    transparent fn le p q
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

# Arrays by their first elements where they differ; an array before any
# longer one that starts with it. `Bytes` are ordered by byte.
instance Ord (Array a) : Ord a
    transparent fn le xs ys
        array_le_from xs ys (array_mismatch xs ys)
    lemma trans xs ys zs
        proof
            have array_le_skip xs ys 0
            have array_le_skip ys zs 0
            have array_le_skip xs zs 0
            have array_le_trans xs ys zs 0
    lemma total xs ys
        proof
            have array_le_skip xs ys 0
            have array_le_skip ys xs 0
            have array_le_total xs ys 0
    lemma antisym xs ys
        proof
            have array_le_skip xs ys 0
            have array_le_skip ys xs 0
            have array_le_len xs ys 0
            have array_le_same xs ys 0

# Whether `xs` comes before `ys` or with it, comparing from index `i` on.
fn array_le_from xs ys i -> r : Ord a, xs~Array a, ys~Array a, i~Nat, i <= len xs, r~Bool
    decreasing len xs - i
    if len xs <= i
        True
    else if len ys <= i
        False
    else
        Ord.le xs[i] ys[i] and (not (Ord.le ys[i] xs[i]) or array_le_from xs ys (i + 1))

# The first index where two arrays differ, or the shorter one's length.
fn array_mismatch xs ys -> i : xs~Array a, ys~Array a, i~Nat, i <= len xs, i <= len ys,
                               (i < len xs and i < len ys) implies not (xs[i] == ys[i])
    __builtin

# Before the first index where they differ, two arrays are equal.
lemma array_mismatch_same xs ys k : xs~Array a, ys~Array a, k~Nat, k < array_mismatch xs ys
    ensures xs[k] == ys[k]
    proof
        __builtin

# Elements that are equal don't decide the order: comparing from `i` is
# comparing from where the arrays first differ.
lemma array_le_skip xs ys i : Ord a, xs~Array a, ys~Array a, i~Nat, i <= array_mismatch xs ys
    ensures array_le_from xs ys i == array_le_from xs ys (array_mismatch xs ys)
    proof
        decreasing array_mismatch xs ys - i
        if i == array_mismatch xs ys
            auto
        else
            have array_mismatch_same xs ys i
            have refl xs[i]
            have array_le_skip xs ys (i + 1)

lemma array_le_trans xs ys zs i : Ord a, xs~Array a, ys~Array a, zs~Array a, i~Nat,
                                  i <= len xs, i <= len ys, array_le_from xs ys i, array_le_from ys zs i
    ensures array_le_from xs zs i
    proof
        decreasing len xs - i
        if len xs <= i or len ys <= i or len zs <= i
            auto
        else
            have Ord.trans xs[i] ys[i] zs[i]
            if Ord.le zs[i] xs[i]
                have Ord.trans ys[i] zs[i] xs[i]
                have Ord.trans zs[i] xs[i] ys[i]
                have array_le_trans xs ys zs (i + 1)
            else
                auto

lemma array_le_total xs ys i : Ord a, xs~Array a, ys~Array a, i~Nat, i <= len xs,
                               i <= len ys
    ensures array_le_from xs ys i or array_le_from ys xs i
    proof
        decreasing len xs - i
        if len xs <= i or len ys <= i
            auto
        else
            have Ord.total xs[i] ys[i]
            have array_le_total xs ys (i + 1)

lemma array_le_len xs ys i : Ord a, xs~Array a, ys~Array a, i~Nat, i <= len xs, i <= len ys,
                             array_le_from xs ys i, array_le_from ys xs i
    ensures len xs == len ys
    proof
        decreasing len xs - i
        if len xs <= i or len ys <= i
            auto
        else
            have Ord.antisym xs[i] ys[i]
            have array_le_len xs ys (i + 1)

lemma array_le_same xs ys i : Ord a, xs~Array a, ys~Array a, i~Nat, i <= len xs, i <= len ys,
                              array_le_from xs ys i, array_le_from ys xs i
    ensures forall k : k~Nat, i <= k, k < len xs, xs[k] == ys[k]
    proof
        decreasing len xs - i
        if len xs <= i or len ys <= i
            auto
        else
            have Ord.antisym xs[i] ys[i]
            if k == i
                auto
            else
                have array_le_same xs ys (i + 1) k

# ── Operators (M24) ──────────────────────────────────────────────────────────
# On numbers, `+ - *`, negation and comparisons are built in. On another
# type they are its instance's: `x + y` is `add x y`, `-x` is `neg x`, and
# `x <= y` is `le x y` (`x < y` is `not (le y x)`).

# Values with `+`.
export class Add a
    fn add x y -> r : x~a, y~a, r~a

# Values with `-`.
export class Sub a
    fn sub x y -> r : x~a, y~a, r~a

# Values with `*`.
export class Mul a
    fn mul x y -> r : x~a, y~a, r~a

# Values with negation, `-x`.
export class Neg a
    fn neg x -> r : x~a, r~a

# Values with an associative `+` and a `zero` it leaves alone.
export class Monoid a
    fn zero -> r : r~a
    # Adding three values doesn't depend on which two come first.
    lemma assoc x y z : Add a, x~a, y~a, z~a
        ensures (x + y) + z == x + (y + z)
    # `zero` on the left changes nothing.
    lemma zero_add x : Add a, x~a
        ensures zero + x == x
    # `zero` on the right changes nothing.
    lemma add_zero x : Add a, x~a
        ensures x + zero == x

instance Add Int
    transparent fn add x y
        x + y

instance Sub Int
    transparent fn sub x y
        x - y

instance Mul Int
    transparent fn mul x y
        x * y

instance Neg Int
    transparent fn neg x
        0 - x

instance Monoid Int
    transparent fn zero
        0

# ── Functors (M25) ───────────────────────────────────────────────────────────

# A container whose elements a function can be applied to, keeping its
# shape: `List`, `Option`, and `Array` (in `std.array`).
export class Functor f
    # `g` applied to each element.
    fn fmap g xs -> ys : g~(a -> b), xs~f a, ys~f b
    # Applying the identity changes nothing.
    lemma fmap_id xs : xs~f a
        ensures fmap (\x -> x) xs == xs
    # Applying `h` then `g` is applying both at once.
    lemma fmap_comp g h xs : g~(b -> c), h~(a -> b), xs~f a
        ensures fmap (\x -> g (h x)) xs == fmap g (fmap h xs)

instance Functor List
    transparent fn fmap g xs
        match xs
            []        -> []
            x :: rest -> g x :: fmap g rest
    lemma fmap_id xs
        proof
            match xs
                []        -> auto
                _ :: rest -> have fmap_id rest
    lemma fmap_comp g h xs
        proof
            match xs
                []        -> auto
                _ :: rest -> have fmap_comp g h rest

instance Functor Option
    transparent fn fmap g o
        match o
            None   -> None
            Some x -> Some (g x)

# ── Sequences ────────────────────────────────────────────────────────────────
# On a type with a `Seq` instance other than `List`, `[]` in a `match` means
# `uncons` gave `None`, and `x :: rest` that it gave `Some (x, rest)`.

# A sequence that can be taken apart from the front: `[]`, `x :: rest` and
# `[p1, …, pn]` in a `match` on one.
export class Seq s
    # The elements' type.
    type Elem
    # How many elements: what recursion on the rest makes smaller.
    fn size xs -> n : xs~s, n~Nat
    # The first element and the rest, which is smaller; `None` only when
    # there are none.
    fn uncons xs -> r : xs~s, r~Option (Elem, s),
                        match r
                            None           -> size xs == 0
                            Some (_, rest) -> size rest < size xs

# A list's `match` is built in; this instance is for generic code.
instance Seq (List a)
    type Elem = a
    transparent fn size xs
        match xs
            []        -> 0
            _ :: rest -> 1 + size rest
    transparent fn uncons xs
        match xs
            []        -> None
            x :: rest -> Some (x, rest)

# The rest is a slice of the array: constant time.
instance Seq (Array a)
    type Elem = a
    transparent fn size xs
        len xs
    transparent fn uncons xs
        if len xs == 0 then None else Some (xs[0], array_rest xs)

# By characters; the size is the number of bytes.
instance Seq String
    type Elem = Char
    transparent fn size s
        len s.bytes
    transparent fn uncons s
        if len s.bytes == 0 then None else Some (string_first s, string_rest s)

# All but the first element: a slice sharing the array's storage.
fn array_rest xs -> r : xs~Array a, len xs > 0, r~Array a, len r + 1 == len xs
    __builtin

# A non-empty string's first character.
fn string_first s -> c : s~String, len s.bytes > 0, c~Char
    __builtin

# All but a non-empty string's first character: a slice sharing its bytes.
fn string_rest s -> r : s~String, len s.bytes > 0, r~String,
                        len r.bytes < len s.bytes
    __builtin

check string_first "€x" == c'€'
check string_rest "€x" == "x"
check string_first "a" == c'a'
check string_rest "a" == ""
check uncons "" == None
check uncons "€x" == Some (c'€', "x")
check array_rest b"abc" == b"bc"

# Whether `x` comes before `y` by their bytes (`Ord String`).
fn string_le x y -> r : x~String, y~String, r~Bool
    __builtin
