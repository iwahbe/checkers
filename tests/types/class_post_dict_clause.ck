module class_post_dict_clause

# A class function with a clause on a class's type (`Tag (Seq.Elem s)`),
# called through a dictionary in an instance: its postcondition still
# reaches the prover.

class Tag e
    fn tag x -> r : x~e, r~Int

class Pick a s
    fn pick x a -> r : Seq s, Tag (Seq.Elem s), x~s, a~ghost Type, r~Option (a, s),
                       match r
        Some (_, y) -> Seq.size y <= Seq.size x
        None        -> True

instance Pick (a, b) s : Pick a s, Pick b s
    fn pick x t
        match Pick.pick x a
            None         -> None
            Some (u, y1) ->
                match Pick.pick y1 b
                    None         -> None
                    Some (v, y2) -> Some ((u, v), y2)
