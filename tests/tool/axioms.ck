module axioms

# The ledger lists every use of an axiom, also one its module makes before
# declaring it (`std.decimal`'s `scaled_parts`, used by `parse_render`).

import std.decimal (Decimal)

fn same n -> b : n~Decimal, b~Bool
    have decimal.parse_render n b""
    True
