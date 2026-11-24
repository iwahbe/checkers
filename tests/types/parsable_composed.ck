module parsable_composed

# A parser made of two others: what is left after both is a suffix of the
# input, by `suffix_trans`, and shorter.

import std.decimal (Decimal, DecimalError)
import std.parse (Parsable, suffix_trans)

record Span
    low~Decimal
    high~Decimal

instance Parsable Span Int
    type Error = DecimalError
    fn parse xs a t
        match Parsable.parse xs Decimal Int
            Err e         -> Err e
            Ok (low, mid) ->
                match Parsable.parse mid Decimal Int
                    Err e           -> Err e
                    Ok (high, rest) ->
                        have suffix_trans rest mid xs
                        Ok (Span low high, rest)

check match Parsable.parse b"1-2.5," Span Int
    Ok (r, rest) -> decimal.render r.high == "-2.5" and len rest == 1
    Err _        -> False
