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
