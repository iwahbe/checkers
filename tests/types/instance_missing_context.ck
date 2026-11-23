module instance_missing_context

# An instance's function using a class at the instance's variable: the
# clause goes in the instance's context, not in a signature.

class Measure m
    fn measure x -> n : x~m, n~Nat

instance Measure (List a)
    fn measure xs
        match xs
            x :: y :: _ -> if le x y then 1 else 2
            _           -> 0

instance Measure (Option a) : Measure a
    fn measure o
        match o
            Some x -> if le x x then Measure.measure x else 0
            None   -> 0
