# utf8.ck — UTF-8 encoding and decoding.
module utf8

import cursor (Parsed)

export fn decode_at src k -> r : src~Bytes, k~Nat, k <= len src, r~Option (Parsed Char src k)
    __builtin

export fn encode s -> b : s~String, b~Bytes
    __builtin
