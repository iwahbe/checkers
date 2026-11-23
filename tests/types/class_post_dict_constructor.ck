module class_post_dict_constructor

# A class over a type constructor (`f`) whose function's result mentions
# the class's type (`Error`), called through a dictionary in an instance:
# its postcondition still reaches the prover.

class Sized f
    fn count xs -> n : xs~f Int, n~Nat

class Pick a f
    type Error
    fn pick x a -> r : Sized f, x~f Int, a~ghost Type, r~Result (a, f Int) Error,
                       match r
        Ok (_, y) -> Sized.count y <= Sized.count x
        Err _     -> True

instance Pick (a, b) f : Pick a f, Pick b f
    type Error = Unit
    fn pick x t
        match Pick.pick x a
            Err _      -> Err ()
            Ok (u, y1) ->
                match Pick.pick y1 b
                    Err _      -> Err ()
                    Ok (v, y2) -> Ok ((u, v), y2)
