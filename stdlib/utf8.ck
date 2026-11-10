# utf8.ck — UTF-8 encoding and decoding.
module std.utf8

import std.cursor (Parsed)

export fn decode_at src k -> r : src~Bytes, k~Nat, k <= len src, r~Option (Parsed Char src k)
    __builtin

export fn encode s -> b : s~String, b~Bytes
    __builtin

# The prover sees a string as its UTF-8 bytes (§7.3), so this is immediate.
export lemma encode_append a b : a~String, b~String
    ensures encode (a ++ b) == encode a ++ encode b
    proof
        auto
