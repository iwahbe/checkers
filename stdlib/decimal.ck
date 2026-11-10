# decimal.ck — exact decimal numbers.
module std.decimal

import std.cursor (Parsed)
import std.utf8

export abstract enum Decimal

# Scan an RFC 8259 number starting at `i`.
export fn scan_json src i -> r : src~Bytes, i~Nat, i <= len src, r~Option (Parsed Decimal src i)
    __builtin

export fn render d -> s : d~Decimal, s~String
    __builtin

export fn of_int n -> d : n~Int, d~Decimal
    __builtin

# ── Facts about the primitives above, trusted like the primitives (D56) ──────

# A byte that could continue a number (`1` then `.5` would scan as `1.5`).
export transparent fn continues_number b -> r : b~U8, r~Bool
    (b >= '0' and b <= '9') or b == '.' or b == 'e' or b == 'E'

# Scanning a rendered number gives it back, wherever it sits.
export lemma scan_json_render n pre post : n~Decimal, pre~Bytes, post~Bytes,
                                           len post == 0 or not (continues_number post[0])
    let src = pre ++ utf8.encode (render n) ++ post
    ensures scan_json src (len pre) == Some (Parsed n (len pre + len (utf8.encode (render n))))
    proof
        __builtin

# A rendered number starts with `-` or a digit.
export lemma render_starts n : n~Decimal
    let b = utf8.encode (render n)
    ensures len b > 0 and (b[0] == '-' or (b[0] >= '0' and b[0] <= '9'))
    proof
        __builtin
