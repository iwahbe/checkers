module parse_display_lemma

# What `display` writes, `Parsable.parse` reads back: by `display`'s own
# signature without options, and with whatever follows that doesn't start
# with a digit by `string.parse_display`.

import std.parse (Parsable)
import std.string (NumberError, display)

fn alone n -> r : n~Int, r~Result (Int, Bytes) NumberError, r == Ok (n, b"")
    Parsable.parse (display n []).bytes Int Int

fn read_back n -> r : n~Int, r~Result (Int, Bytes) NumberError, r == Ok (n, b",")
    have string.parse_display n b","
    Parsable.parse ((display n []).bytes ++ b",") Int Int
