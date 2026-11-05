# char.ck — Unicode scalar values.
module char

export fn code c -> n : c~Char, n~Nat
    __builtin

export fn from_scalar n -> c : n~Nat, n < 0x110000, (n < 0xD800 or 0xE000 <= n), c~Char
    __builtin

export fn from_ascii b -> c : b~U8, b < 128, c~Char
    __builtin

export fn from_surrogates hi lo -> c : hi~Nat, lo~Nat, 0xD800 <= hi, hi < 0xDC00,
                                       0xDC00 <= lo, lo < 0xE000, c~Char
    __builtin
