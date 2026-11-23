module parse_render_lemma

# What `decimal.render` writes, `Parsable.parse` reads back, for every number
# and whatever follows that can't continue a number; and it starts with `-`
# or a digit.

import std.decimal (Decimal, DecimalError)
import std.parse (Parsable)
import std.char
import std.utf8

fn read_back n post -> r : n~Decimal, post~Bytes, len post == 0 or post[0] == ',' or post[0] == ']',
                           r~Result (Decimal, Bytes) DecimalError, r == Ok (n, post)
    have decimal.parse_render n post
    Parsable.parse (utf8.encode (decimal.render n) ++ post) Decimal Int

fn first n -> c : n~Decimal, c~U8, c == '-' or char.is_digit c
    have decimal.render_starts n
    (utf8.encode (decimal.render n))[0]

# Not after a digit, which would continue the number.
fn read_digit n -> r : n~Decimal, r~Result (Decimal, Bytes) DecimalError, r == Ok (n, b"0")
    have decimal.parse_render n b"0"
    Parsable.parse (utf8.encode (decimal.render n) ++ b"0") Decimal Int
