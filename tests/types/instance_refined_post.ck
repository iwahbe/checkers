module instance_refined_post

# An instance's function may promise more than its class: a call at the
# known instance gets the stronger postcondition, which needs induction
# and so doesn't follow from the body alone.

class Size a
    fn size x -> n : x~a, n~Int

instance Size (List a)
    fn size xs -> n : xs~List a, n~Int, n >= 0
        match xs
            []        -> 0
            _ :: rest -> 1 + size rest

fn known xs -> r : xs~List Int, r~Int, r >= 0
    Size.size xs
