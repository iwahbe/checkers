# utf8.ck — UTF-8 encoding and decoding.
module std.utf8

import std.cursor (Parsed)
import std.string

export fn decode_at src k -> r : src~Bytes, k~Nat, k <= len src, r~Option (Parsed Char src k)
    __builtin

export fn encode s -> b : s~String, b~Bytes
    __builtin

# The prover sees a string as its UTF-8 bytes (§7.3), so this is immediate.
export lemma encode_append a b : a~String, b~String
    ensures encode (a ++ b) == encode a ++ encode b
    proof
        auto

# Decoding a character's own bytes gives it back (D56, D119).
export lemma decode_from_char c pre post : c~Char, pre~Bytes, post~Bytes
    let src = pre ++ string.bytes (string.from_char c) ++ post
    ensures decode_at src (len pre) == Some (Parsed c (len pre + len (string.bytes (string.from_char c))))
    proof
        __builtin

# The axiom on a few characters, against the builtins themselves.
fn decoded src k -> r : src~Bytes, k~Nat, k <= len src, r~Option (Char, Nat)
    match decode_at src k
        Some p -> Some (p.value, p.stop)
        None   -> None

check decoded (b"x" ++ string.bytes (string.from_char c'€') ++ b"\x80") 1 == Some (c'€', 4)
check decoded (string.bytes (string.from_char c'😀')) 0 == Some (c'😀', 4)
