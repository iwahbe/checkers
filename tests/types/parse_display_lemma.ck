module parse_display_lemma

# What `display` writes, `Parsable.parse` reads back, for every number and
# whatever follows that doesn't start with a digit; and `string.decimal`'s
# digits, `parse.natural`.

import std.parse (Parsable, NumberError)
import std.string (display)

fn read_back n -> r : n~Int, r~Result (Int, Bytes) NumberError, r == Ok (n, b",")
    have parse.parse_display n b","
    Parsable.parse ((display n []).bytes ++ b",") Int Int

fn read_natural n post -> r : n~Nat, post~Bytes, len post == 0 or post[0] == ' ',
                              r~Result (Nat, Bytes) NumberError, r == Ok (n, post)
    have parse.natural_decimal n post
    parse.natural ((string.decimal n).bytes ++ post)
