# prelude.ck — imported into every module.
module prelude

# Built-in types; their values come from literals and primitives.
export abstract enum Nat
export abstract enum Int
export abstract enum String
export abstract enum Bytes

export enum Bool
    False
    True

export type Unit = u~()

export enum Option a : a~Type
    None
    Some x : x~a

export enum Result a e : a~Type, e~Type
    Ok x : x~a
    Err x : x~e

export enum List a : a~Type
    Nil
    Cons x xs : x~a, xs~List a

# Fixed-width numbers are refinements of Nat and Int (D6).
export type U8 = n~Nat, n < 256
export type U16 = n~Nat, n < 65536
export type U32 = n~Nat, n < 4294967296
export type U64 = n~Nat, n < 18446744073709551616
export type I8 = n~Int, -128 <= n, n < 128
export type I32 = n~Int, -2147483648 <= n, n < 2147483648
export type I64 = n~Int, -9223372036854775808 <= n, n < 9223372036854775808

# A Unicode scalar value.
export type Char = n~Nat, n < 0x110000, (n < 0xD800 or 0xE000 <= n)

export fn not b -> r : b~Bool, r~Bool
    if b then False else True
