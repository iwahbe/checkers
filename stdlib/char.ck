# char.ck — Unicode scalar values. A `Char` is its code (a refined `Nat`,
# prelude), so these are ordinary functions the prover sees through (D119).
module std.char

export transparent fn code c -> n : c~Char, n~Nat
    c

export transparent fn from_scalar n -> c : n~Nat, n < 0x110000, (n < 0xD800 or 0xE000 <= n), c~Char
    n

export transparent fn from_ascii b -> c : b~U8, b < 128, c~Char
    b

export transparent fn from_surrogates hi lo -> c : hi~Nat, lo~Nat, 0xD800 <= hi, hi < 0xDC00,
                                                   0xDC00 <= lo, lo < 0xE000, c~Char
    0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
