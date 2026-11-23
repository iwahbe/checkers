module string_record

# A string is a record of its bytes, which are UTF-8: the prover knows it.

import std.string

fn never_lone s -> r : s~String, r~Bool, r
    s.bytes != b"\x80" and string.bytes s != b"\xC0\x80"

fn rebuilt s -> t : s~String, t~String, t == s
    String s.bytes

fn unpacked s -> b : s~String, b~Bytes, valid_utf8 b
    match s
        String x -> x

fn checked b -> r : b~Bytes, r~Option String
    if valid_utf8 b then Some (String b) else None

fn unchecked b -> r : b~Bytes, r~String
    String b                                    # error E0450

check checked b"\xFF" == None and checked b"ok" == Some "ok" and rebuilt "é" == "é"
