module class_post_known_pinned

# A class function with a clause of its own (`Seq s`) that takes the
# class's type as an argument (`a~ghost Type`), called at a known
# instance: its postcondition still reaches the prover.

class Pick a s
    fn pick xs a -> r : Seq s, xs~s, a~ghost Type, r~Option (a, s),
                        match r
                            Some (_, rest) -> Seq.size rest < Seq.size xs
                            None           -> True

instance Pick Bool s
    fn pick xs a
        match xs
            _ :: rest -> Some (True, rest)
            []        -> None

fn shrinks xs -> r : Seq s, xs~s, r~Bool, r
    match Pick.pick xs Bool
        None           -> True
        Some (_, rest) -> Seq.size rest < Seq.size xs
