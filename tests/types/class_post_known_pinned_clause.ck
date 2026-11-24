module class_post_known_pinned_clause

# A class function whose own clause (`Tok (Seq.Elem s) t`) mentions a
# class's type it takes as an argument (`t~ghost Type`), called at a known
# instance: its postcondition still reaches the prover.

class Tok x t
    fn token v t -> r : v~x, t~ghost Type, r~t

instance Tok Int Int
    fn token v t
        v

class Pick a t
    fn pick xs a t -> r : Seq s, Tok (Seq.Elem s) t, xs~s, a~ghost Type, t~ghost Type, r~Option (a, s),
                          match r
                              Some (_, rest) -> Seq.size rest < Seq.size xs
                              None           -> True

instance Pick Bool Int
    fn pick xs a t
        match xs
            _ :: rest -> Some (True, rest)
            []        -> None

fn shrinks xs -> r : Seq s, Tok (Seq.Elem s) Int, xs~s, r~Bool, r
    match Pick.pick xs Bool Int
        None           -> True
        Some (_, rest) -> Seq.size rest < Seq.size xs
