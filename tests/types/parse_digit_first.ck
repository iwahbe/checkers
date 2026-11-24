module parse_digit_first

# `Parsable.parse` at `Int` reads a number, not a negative one, from bytes
# that start with a digit, by the instance's own signature; what is left is
# the bytes after the digits, by `string.parse_digits`.

import std.parse (Parsable)
import std.array
import std.char
import std.string

fn by_signature b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~(Nat, Bytes)
    match Parsable.parse b Nat Int
        Ok (n, after) -> (n, after)

fn by_lemma b -> r : b~Bytes, len b > 0, char.is_digit b[0], r~Bytes,
                     r == array.slice b (string.digits_end b 0) (len b)
    have string.parse_digits b
    match Parsable.parse b Int Int
        Ok (_, after) -> after
