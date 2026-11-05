# decimal.ck — exact decimal numbers.
module decimal

import cursor (Parsed)

export abstract enum Decimal

# Scan an RFC 8259 number starting at `i`.
export fn scan_json src i -> r : src~Bytes, i~Nat, i <= len src, r~Option (Parsed Decimal src i)
    __builtin

export fn render d -> s : d~Decimal, s~String
    __builtin

export fn of_int n -> d : n~Int, d~Decimal
    __builtin
