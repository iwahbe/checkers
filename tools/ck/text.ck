# text.ck — positions in a document for the language server (SPEC §15.5):
# lines, columns in bytes or UTF-16 code units, and `file:` URIs.

module ck.text

import std.string
import std.bytes
import std.list

# The byte offset where line `line` (from 0) starts, if the text has it.
export partial fn line_start text line -> r : text~Bytes, line~Nat, r~Option Nat
    starts text 0 line

partial fn starts text i line -> r : text~Bytes, i~Nat, line~Nat, r~Option Nat
    if line == 0
        if i <= len text then Some i else None
    else if i >= len text
        None
    else if text[i] == '\n'
        starts text (i + 1) (line - 1)
    else
        starts text (i + 1) line

# The bytes of line `line`, without its line break; empty past the end.
export partial fn line_at text line -> r : text~Bytes, line~Nat, r~Bytes
    match line_start text line
        Some i if i <= len text -> bytes.slice text i (line_end text i)
        _ -> b""

partial fn line_end text i -> r : text~Bytes, i~Nat, i <= len text, r~Nat, i <= r, r <= len text
    if i < len text and text[i] != '\n' and text[i] != '\r'
        line_end text (i + 1)
    else
        i

# How many lines the text has (a final line break ends a line, not starts one).
export partial fn line_count text -> n : text~Bytes, n~Nat
    count_breaks text 0 0 + (if len text > 0 and text[len text - 1] != '\n' then 1 else 0)

partial fn count_breaks text i acc -> n : text~Bytes, i~Nat, acc~Nat, n~Nat
    if i >= len text
        acc
    else
        count_breaks text (i + 1) (if text[i] == '\n' then acc + 1 else acc)

# UTF-16 code units of the character starting with byte `b` (0 for a byte
# inside a character).
fn units b -> n : b~U8, n~Nat
    if b < 0x80 then 1 else if b < 0xC0 then 0 else if b < 0xF0 then 1 else 2

# The UTF-16 column of byte column `col` in `line`.
export partial fn utf16_of line col -> n : line~Bytes, col~Nat, n~Nat
    count16 line 0 col 0

partial fn count16 line i col acc -> n : line~Bytes, i~Nat, col~Nat, acc~Nat, n~Nat
    if i >= col or i >= len line
        acc + (if col > len line then col - len line else 0)
    else
        count16 line (i + 1) col (acc + units line[i])

# The byte column of UTF-16 column `col` in `line` (past the end: beyond it,
# one byte per unit, as clients may ask for).
export partial fn byte_of line col -> n : line~Bytes, col~Nat, n~Nat
    find_byte line 0 col

partial fn find_byte line i left -> n : line~Bytes, i~Nat, left~Nat, n~Nat
    if i >= len line
        i + left
    else if left == 0 and units line[i] > 0
        i
    else
        let u = units line[i]
        if u > left then i else find_byte line (i + 1) (left - u)

# ── URIs ─────────────────────────────────────────────────────────────────────

fn hex_value b -> n : b~U8, n~Nat
    if b >= '0' and b <= '9'
        b - '0'
    else if b >= 'a' and b <= 'f'
        b - 'a' + 10
    else if b >= 'A' and b <= 'F'
        b - 'A' + 10
    else
        0

fn is_hex b : b~U8
    (b >= '0' and b <= '9') or (b >= 'a' and b <= 'f') or (b >= 'A' and b <= 'F')

# `%XX` escapes decoded.
partial fn unescape b i acc -> r : b~Bytes, i~Nat, acc~List Bytes, r~Bytes
    if i >= len b
        bytes.concat (list.reverse acc)
    else if b[i] == '%' and i + 2 < len b and is_hex b[i + 1] and is_hex b[i + 2]
        let v = hex_value b[i + 1] * 16 + hex_value b[i + 2]
        unescape b (i + 3) (byte v :: acc)
    else
        unescape b (i + 1) (bytes.slice b i (i + 1) :: acc)

# A one-byte `Bytes`.
fn byte v -> r : v~Nat, r~Bytes
    let table = b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7f\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7\xc8\xc9\xca\xcb\xcc\xcd\xce\xcf\xd0\xd1\xd2\xd3\xd4\xd5\xd6\xd7\xd8\xd9\xda\xdb\xdc\xdd\xde\xdf\xe0\xe1\xe2\xe3\xe4\xe5\xe6\xe7\xe8\xe9\xea\xeb\xec\xed\xee\xef\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9\xfa\xfb\xfc\xfd\xfe\xff"
    if v < 256 then bytes.slice table v (v + 1) else b""

# The path of a `file:` URI, if it is one.
export partial fn path_of uri -> r : uri~String, r~Option String
    let b = string.bytes uri
    let scheme = b"file://"
    if bytes.matches_at b 0 scheme
        string.from_utf8 (unescape (bytes.slice b (len scheme) (len b)) 0 [])
    else
        None

fn plain b : b~U8
    (b >= 'a' and b <= 'z') or (b >= 'A' and b <= 'Z') or (b >= '0' and b <= '9')
        or b == '/' or b == '-' or b == '_' or b == '.' or b == '~'

fn hex_digit n -> r : n~Nat, r~Bytes
    let digits = b"0123456789ABCDEF"
    if n < 16 then bytes.slice digits n (n + 1) else b""

partial fn escape b i acc -> r : b~Bytes, i~Nat, acc~List Bytes, r~Bytes
    if i >= len b
        bytes.concat (list.reverse acc)
    else if plain b[i]
        escape b (i + 1) (bytes.slice b i (i + 1) :: acc)
    else
        escape b (i + 1) (hex_digit (b[i] % 16) :: hex_digit (b[i] / 16) :: b"%" :: acc)

# The `file:` URI of an absolute path.
export partial fn uri_of path -> r : path~String, r~String
    match string.from_utf8 (escape (string.bytes path) 0 [b"file://"])
        Some u -> u
        None   -> "file://" ++ path
