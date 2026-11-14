# decimal.ck — exact decimal numbers.
module std.decimal

import std.utf8

# An exact decimal number: an integer times a power of ten.
export abstract enum Decimal

# The number as JSON writes it: `-12.5`, `0.001`, `1e30` (an exponent
# only when the number is very large or very small).
export fn render d -> s : d~Decimal, s~String
    __builtin

# The integer as a decimal.
export fn of_int n -> d : n~Int, d~Decimal
    __builtin

# ── Facts about the primitives above, trusted like the primitives (D56) ──────

# A rendered number starts with `-` or a digit.
export lemma render_starts n : n~Decimal
    let b = utf8.encode (render n)
    ensures len b > 0 and (b[0] == '-' or (b[0] >= '0' and b[0] <= '9'))
    proof
        __builtin
